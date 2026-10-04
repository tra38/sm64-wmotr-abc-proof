import copy
import json
from pathlib import Path
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

from chunk_ledger import ChunkLedger, seal, atomic_json
from compact_store import ProductCodec, open_product
from test_chunk_ledger import signature,record,populate
from product_sweep import validate_record as product_validate,run as product_run
from reverse_scattershot import (initial_aux,next_ticket,proposal,advance_aux,retain,open_store,
                                sampled_input,permutation,continuous,GameBudgetReached,
                                ScatterCodec,Input,DISAPPEARED,END_FIELDS,FIRST_APPLY,bits)
from search import number
from work_limits import WorkLimits,LimitReached


def scatter_signature():
    p=dict(movement=[bits(-2200),bits(768),bits(-1024)],
           collision=[bits(-2200),bits(768),bits(-1024)],
           display=[bits(-2200),1156733869,bits(-1024)],
           depth=bits(0),vy=bits(0),action=0x0C400201,actionState=0,actionTimer=0,actionArg=0)
    return dict(seed=20261003,scheduler='scattershot',depth=3,archiveLimit=4,maxTrials=5000,
                jobOrder=[dict(setup='original',move='retry',patch=p,targets=['original'],family='retry')],
                order='seeded-strata-v1',aMode='released',initialAux=initial_aux())


def scatter_row(aux,sig,case,accepted=True,status=None):
    c=proposal(aux,sig); controls=c['controls']; p=c['patch']
    obs=copy.deepcopy(p); obs['rng']=123; obs['platform']=-1
    entry=dict(id=case,frame=492-c['depth']+1,depth=c['depth'],patch=p,controls=controls,
               checkpoints=c['checkpoints'],targets=c['targets'],observation=obs,
               family=c['family'],move=c['move'],attempts=0,parent=c['ticket']['parent'])
    return dict(case=case,jobId=c['jobId'],inputIndex=c['inputIndex'],setup='original',
                status=status or ('accepted-projection' if accepted else 'rejected'),
                detail=dict(ticket=c['ticket'],proposal=c,entry=entry if accepted else None,
                            updates=c['depth']+23 if accepted else 1))


class CompactTests(unittest.TestCase):
    def test_old_and_new_records_decode_identically(self):
        with tempfile.TemporaryDirectory() as d:
            root=Path(d); populate(root/'old')
            sig=signature()
            with ChunkLedger(root/'new',sig,1000,product_validate(sig),codec=ProductCodec(sig),chunk_records=3) as s:
                for i in range(9): s.append(record(i))
                s.commit()
            for path in (root/'old',root/'new'):
                manifest=json.loads((path/'manifest.json').read_text())['payload']
                with open_product(path,manifest,read_only=True) as s:
                    self.assertEqual(list(s.records()),[record(i) for i in range(9)])
            for f in (root/'new').rglob('retained.jsonl.gz'):
                import gzip
                self.assertTrue(all(isinstance(json.loads(line),list) and len(json.loads(line))==1
                                    for line in gzip.decompress(f.read_bytes()).splitlines()))

    def test_compressed_truncation_corruption_and_bomb_are_rejected(self):
        import gzip,hashlib
        for damage in ('truncate','flip','extra','bomb'):
            with self.subTest(damage=damage),tempfile.TemporaryDirectory() as d:
                root=Path(d)/'ledger'; sig=signature()
                with ChunkLedger(root,sig,1000,product_validate(sig),codec=ProductCodec(sig),chunk_records=3) as s:
                    for i in range(6):s.append(record(i))
                    s.commit()
                f=root/'chunks/000000/0000000000/trials.jsonl.gz'; raw=f.read_bytes()
                if damage=='truncate':raw=raw[:-1]
                if damage=='flip':raw=raw[:25]+bytes([raw[25]^1])+raw[26:]
                if damage=='extra':raw+=b'\n'
                if damage=='bomb':raw=gzip.compress(b'x'*(5*1024*1024))
                f.write_bytes(raw)
                if damage=='bomb':
                    meta_path=f.parent/'commit.json'; meta=json.loads(meta_path.read_text())['payload']
                    meta['trials'].update(bytes=len(raw),sha256=hashlib.sha256(raw).hexdigest())
                    atomic_json(meta_path,seal(meta))  # decoded bound rejects even resealed input
                with self.assertRaises(ValueError):
                    open_product(root,json.loads((root/'manifest.json').read_text())['payload'])

    def test_each_commit_interruption_recovers_aux_counts_and_references(self):
        sig=scatter_signature()
        for stage in ('after_trial_write','after_retained_write','before_payload_sync','after_payload_sync',
                      'after_commit_metadata','after_chunk_rename','before_head_replace','after_head_replace'):
            with self.subTest(stage=stage),tempfile.TemporaryDirectory() as d:
                root=Path(d)/'ledger'
                with open_store(root,sig,chunk_records=3) as s:
                    for i in range(3):s.append(scatter_row(s.state['aux'],sig,i))
                    s.commit()
                def fail(at):
                    if at==stage:raise RuntimeError('injected')
                s=open_store(root,sig,resume=True,chunk_records=3,fault=fail)
                with self.assertRaises(RuntimeError):
                    s.append(scatter_row(s.state['aux'],sig,3));s.commit()
                s.close()
                with open_store(root,sig,resume=True,chunk_records=3) as s:
                    start=s.state['nextCase'];self.assertEqual(start,4 if stage=='after_head_replace' else 3)
                    for i in range(start,12):s.append(scatter_row(s.state['aux'],sig,i))
                    s.commit()
                with open_store(root,sig,resume=True,chunk_records=3) as s:
                    self.assertEqual([r['case'] for r in s.records()],list(range(12)))
                    expected=initial_aux()
                    for i in range(12):expected=advance_aux(expected,scatter_row(expected,sig,i),sig)
                    self.assertEqual(s.state['aux'],expected)

    def test_partial_compressed_pending_never_advances_sampling(self):
        sig=scatter_signature()
        with tempfile.TemporaryDirectory() as d:
            root=Path(d)/'ledger'
            with open_store(root,sig) as s:
                s.append(scatter_row(s.state['aux'],sig,0));s.commit()
                expected=copy.deepcopy(s.state)
                s.append(scatter_row(s.state['aux'],sig,1))
            (root/'pending'/'trials.jsonl.gz').write_bytes(b'\x1f\x8bpartial')
            with open_store(root,sig,resume=True) as s:self.assertEqual(s.state,expected)

    def test_full_checks_older_compressed_content_latest_explicitly_does_not(self):
        with tempfile.TemporaryDirectory() as d:
            root=Path(d)/'ledger';sig=signature()
            with ChunkLedger(root,sig,1000,product_validate(sig),codec=ProductCodec(sig),chunk_records=3) as s:
                for i in range(9):s.append(record(i))
                s.commit()
            f=root/'chunks/000000/0000000000/trials.jsonl.gz';f.write_bytes(b'corrupted old chunk')
            manifest=json.loads((root/'manifest.json').read_text())['payload']
            with open_product(root,manifest,verify='latest',read_only=True) as s:self.assertEqual(s.state['nextCase'],9)
            with self.assertRaises(ValueError):open_product(root,manifest,read_only=True)

    def test_incompatible_sampler_rejected(self):
        with tempfile.TemporaryDirectory() as d:
            root=Path(d)/'ledger';sig=scatter_signature()
            with open_store(root,sig):pass
            for field,value in (('seed',7),('depth',2),('archiveLimit',12),('scheduler','menu-first')):
                changed=copy.deepcopy(sig);changed[field]=value
                with self.assertRaises(ValueError):open_store(root,changed,resume=True)


class SchedulingTests(unittest.TestCase):
    def test_lazy_permutations_without_replacement_and_resume(self):
        for n in (1,7,289,65536):
            values=[permutation(i,n,99,'test') for i in range(n)]
            self.assertEqual(len(set(values)),n)
        sig=scatter_signature(); aux=initial_aux(); seen=set(); kinds=set()
        for i in range(100):
            c=proposal(aux,sig);key=(c['ticket']['parent'],c['move'],c['inputIndex'])
            self.assertNotIn(key,seen);seen.add(key);kinds.add(c['ticket']['kind'])
            aux=advance_aux(aux,scatter_row(aux,sig,i),sig)
        self.assertEqual(kinds,{'fresh','extend'})
        self.assertEqual(proposal(aux,sig),proposal(json.loads(json.dumps(aux)),sig))

    def test_short_branches_survive_long_chain_retention(self):
        sig=scatter_signature();aux=initial_aux()
        for i in range(30):aux=advance_aux(aux,scatter_row(aux,sig,i),sig)
        self.assertLessEqual(len(aux['archive']),4)
        self.assertTrue(any(e['depth']==1 for e in aux['archive']))
        self.assertTrue(any(e['depth']>1 for e in aux['archive']))
        # Equal position buckets retain separate inputs/provenance when space permits.
        e=copy.deepcopy(aux['archive'][0]);f=copy.deepcopy(e);f['id']=100;f['controls'][0]['stick']=[7,8]
        result=retain([e,f],4);self.assertEqual(len(result),2)

    def test_unfinished_attempt_does_not_consume_the_pending_proposal(self):
        sig=scatter_signature();aux=initial_aux();ticket=next_ticket(aux,sig)
        r=scatter_row(aux,sig,0,False,status='incomplete-budget');r['detail']['updates']=2
        after=advance_aux(aux,r,sig)
        self.assertEqual(next_ticket(after,sig),ticket);self.assertEqual(after['updates'],2)

    def test_meaningful_buttons_and_all_encoded_rectangles_exist(self):
        controls=[sampled_input(i,22,'key','released') for i in range(63)]
        self.assertEqual(len({x[2] for x in controls}),7)
        self.assertEqual(len({x[3] for x in controls}),9)
        self.assertTrue(all(not x[1].buttons&0x8f20 for x in controls))


class LimitsTests(unittest.TestCase):
    def test_verification_does_not_consume_search_allowance(self):
        clock=[0.];limits=WorkLimits(20,20,60,clock=lambda:clock[0])
        clock[0]=10;limits.enter('verification');clock[0]=25;limits.enter('search')
        clock[0]=84;limits.check();clock[0]=85
        with self.assertRaises(LimitReached):limits.check()
        self.assertEqual(limits.finish()['totalSeconds'],85)

    def test_interrupted_verification_does_not_recover_or_modify_head(self):
        sig=scatter_signature()
        with tempfile.TemporaryDirectory() as d:
            root=Path(d)/'ledger'
            with open_store(root,sig) as s:s.append(scatter_row(s.state['aux'],sig,0));s.commit()
            head=(root/'HEAD.json').read_bytes();(root/'pending').mkdir();(root/'pending'/'partial').write_bytes(b'x')
            calls=[]
            def stop():
                calls.append(1)
                if len(calls)==8:raise LimitReached('verification')
            with self.assertRaises(LimitReached):open_store(root,sig,resume=True,check=stop)
            self.assertEqual(len(calls),8)
            self.assertEqual((root/'HEAD.json').read_bytes(),head);self.assertTrue((root/'pending').exists())

    def test_setup_limit_reports_incomplete_not_gameplay_failure(self):
        with tempfile.TemporaryDirectory() as d:
            args=SimpleNamespace(output=Path(d)/'report.json',resume=False,benchmark=False,seconds=60,setup_seconds=0)
            with patch('product_sweep.make_jobs') as game:
                r=product_run(args);game.assert_not_called()
            self.assertEqual(r['status'],'setup incomplete');self.assertEqual(r['thisBatch']['tested'],0)


class FakeBackend:
    def __init__(self):
        self.f=0;self.ops=[];self.game=self;self.observer=self
        self.endpoint={k:0 for k in END_FIELDS};self.endpoint.update(movement=[1,2,3],collision=[4,5,6],display=[1,2,3])
    def frame(self):return self.f
    def read(self,path):
        return {'gGlobalTimer':self.f,'gCurrAreaIndex':1}[path]
    def restore(self,s):self.f=s.frame;self.ops.append('restore')
    def patch(self,p):self.ops.append('patch')
    def capture(self):return SimpleNamespace(frame=self.f,observation=self.observe(),state=object())
    def observe(self):
        r=copy.deepcopy(self.endpoint);r.update(timer=self.f,area=1,buttonDown=0,buttonPressed=0,platform=61)
        if self.f>=3:r.update(area=2,movement=FIRST_APPLY)
        return r
    def advance(self,c):self.f+=1;self.ops.append('advance')
    def frame_log(self):
        return [dict(type='FLT_EXECUTE_ACTION',action=DISAPPEARED,
                     pos=[number(v) for v in FIRST_APPLY] if self.f>=3 else [0.,0.,0.])]


class ContinuousTests(unittest.TestCase):
    def test_shared_execution_keeps_different_display_requirements(self):
        b=FakeBackend();context=b.capture();b.f=1;end=b.observe();b.f=0
        low=[4,5,6];high=[4,99,6]
        targets={'variant':dict(movement=[0,0,0],collision=low,display=low),
                 'hybrid':dict(movement=[0,0,0],collision=low,display=high)}
        report,earlier=continuous(b,context,dict(collision=low,display=low),[Input()],[],targets,
                                 {'variant':end,'hybrid':end},'released')
        self.assertEqual(report['matched'],['variant'])
        self.assertFalse(report['targets']['hybrid']['conditionalPrefixMatches'])
        self.assertIn('not independently observed',report['targets']['variant']['pending'])

    def test_two_edges_and_retention_have_only_earliest_patch(self):
        b=FakeBackend();context=b.capture();b.f=1;middle=b.observe();b.f=2;end=b.observe();b.f=0
        targets={'original':dict(movement=[0,0,0])}
        report,earlier=continuous(b,context,{},[Input(),Input()],[middle],targets,{'original':end},'released')
        self.assertEqual(report['status'],'accepted-projection');self.assertEqual(report['updates'],25)
        self.assertEqual(b.ops,['restore','patch']+['advance']*25)

    def test_invalid_parent_is_rejected_and_budget_interruption_is_not_a_rejection(self):
        b=FakeBackend();context=b.capture();wrong=b.observe();wrong['timer']=999
        report,earlier=continuous(b,context,{},[Input(),Input()],[wrong],{}, {},'released')
        self.assertEqual(report['stage'],'parent');self.assertIsNone(earlier)
        b=FakeBackend();context=b.capture();b.f=1;end=b.observe();b.f=0
        with self.assertRaises(GameBudgetReached) as raised:
            continuous(b,context,{},[Input()],[],{'original':dict(movement=[0,0,0])},{'original':end},'released',update_limit=3)
        self.assertEqual(raised.exception.updates,3)


if __name__=='__main__':unittest.main()
