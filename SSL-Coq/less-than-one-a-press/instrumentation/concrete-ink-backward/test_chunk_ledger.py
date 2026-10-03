"""Crash, integrity, sampling, retained-recipe and counter integration tests."""
import copy
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

from chunk_ledger import ChunkLedger, atomic_json, seal, encoded, replace_with_retry
from product_sweep import decode_input, ordered_input, validate_record, run, audit_output


def signature():
    return dict(aMode='released',inputSpace={'buttonsMode':'stock-gameplay'},order='mixed',
                jobOrder=[dict(setup=n,move='pose-'+n,patch={'movement':[0,0,0]})
                          for n in ('original','variant','hybrid')])


def record(case):
    sig=signature()
    ordinal,job=divmod(case,3)
    index=ordered_input(ordinal,'stock-gameplay','mixed')
    return dict(case=case,jobId=job,inputIndex=index,setup=sig['jobOrder'][job]['setup'],
                pose=sig['jobOrder'][job]['move'],input=decode_input(index,'released','stock-gameplay').record(),
                status='accepted-projection' if case%2==0 else 'rejected-event',detail={'test':case})


def open_store(root,**kw):
    return ChunkLedger(root,signature(),1000,validate_record(signature()),chunk_records=3,**kw)


def populate(root,count=9):
    with open_store(root) as store:
        for case in range(count):
            store.append(record(case))
            if store.ready(): store.commit()
        store.commit()


def stored_records(store,kind='trials'):
    result=[]
    for g in range(store.generation+1):
        with (store._chunk(g)/(kind+'.jsonl')).open() as f:
            result.extend(json.loads(line) for line in f)
    return result


class ChunkTests(unittest.TestCase):
    def setUp(self):
        self.temp=tempfile.TemporaryDirectory()
        self.root=Path(self.temp.name)/'result.ledger'

    def tearDown(self): self.temp.cleanup()

    def test_clean_resume_and_exact_retained_subsequence(self):
        populate(self.root)
        with open_store(self.root,resume=True) as s:
            self.assertEqual(s.state['nextCase'],9)
            self.assertEqual(s.state['sampling'],{'nextInputOrdinal':3,'nextJobId':0,'order':'mixed'})
            self.assertEqual(stored_records(s),[record(c) for c in range(9)])
            self.assertEqual(stored_records(s,'retained'),[record(c) for c in range(0,9,2)])
            self.assertEqual(s.state['retained'],5)
            for c in range(9,14): s.append(record(c))
            s.commit()
        with open_store(self.root,resume=True) as s:
            self.assertEqual(stored_records(s),[record(c) for c in range(14)])

    def test_partial_pending_write_is_preserved_and_replayed_once(self):
        with open_store(self.root) as s:
            for c in range(3): s.append(record(c))
            s.commit()
            s.append(record(3))
        with (self.root/'pending'/'trials.jsonl').open('ab') as f: f.write(b'{"case":4')
        with open_store(self.root,resume=True) as s:
            self.assertEqual(s.state['nextCase'],3)
            self.assertTrue(s.recovered)
            self.assertTrue(any(p.is_dir() for p in (self.root/'recovery').iterdir()))
            for c in range(3,8): s.append(record(c))
            s.commit()
        with open_store(self.root,resume=True) as s:
            self.assertEqual([r['case'] for r in stored_records(s)],list(range(8)))

    def test_partial_or_stale_head_temp_is_never_authoritative(self):
        populate(self.root,3)
        (self.root/'HEAD.json.tmp').write_bytes(b'{broken')
        with open_store(self.root,resume=True) as s:
            self.assertEqual(s.state['nextCase'],3)
            self.assertEqual(len(s.recovered),1)

    def test_committed_truncation_partial_line_and_corruption_are_rejected(self):
        for kind in ('trials','retained'):
            for damage in ('truncation','partial-line','corruption'):
                with self.subTest(kind=kind,damage=damage), tempfile.TemporaryDirectory() as d:
                    root=Path(d)/'store'; populate(root)
                    path=root/'chunks/000000/0000000000'/(kind+'.jsonl')
                    data=path.read_bytes()
                    if damage=='truncation': data=data[:-1]
                    elif damage=='partial-line': data=data[:len(data)//2]
                    else: data=data.replace(b'"test":0',b'"test":9',1)
                    path.write_bytes(data)
                    with self.assertRaises((ValueError,json.JSONDecodeError)):
                        open_store(root,resume=True)

    def test_full_resume_detects_old_corruption_latest_explicitly_does_not(self):
        populate(self.root,12)
        path=self.root/'chunks/000000/0000000000/trials.jsonl'
        path.write_bytes(path.read_bytes().replace(b'"test":0',b'"test":8',1))
        with open_store(self.root,resume=True,verify='latest') as s:
            self.assertEqual(s.state['nextCase'],12)
        with self.assertRaises(ValueError): open_store(self.root,resume=True)

    def test_metadata_counts_sampling_manifest_and_chain_corruption(self):
        for damage in ('checksum','cursor','sampling','counts','manifest','chain'):
            with self.subTest(damage=damage), tempfile.TemporaryDirectory() as d:
                root=Path(d)/'store'; populate(root)
                path=root/'HEAD.json'
                value=json.loads(path.read_text())
                if damage=='checksum': value['sha256']='0'*64
                else:
                    payload=value['payload']
                    if damage=='cursor': payload['state']['nextCase']=10
                    elif damage=='sampling': payload['state']['sampling']['nextJobId']=1
                    elif damage=='counts': payload['state']['counts']['original']['accepted-projection']+=1
                    elif damage=='manifest': payload['manifestSha256']='0'*64
                    else: payload['commitSha256']='0'*64
                    value=seal(payload)
                atomic_json(path,value)
                with self.assertRaises(ValueError): open_store(root,resume=True)

    def test_incompatible_configuration_rejected_without_changing_head(self):
        populate(self.root)
        before=(self.root/'HEAD.json').read_bytes()
        for field in ('aMode','order','jobOrder','sourceHashes'):
            sig=copy.deepcopy(signature()); sig[field]='changed'
            with self.assertRaises(ValueError):
                ChunkLedger(self.root,sig,1000,validate_record(signature()),resume=True,chunk_records=3)
        with self.assertRaises(ValueError):
            ChunkLedger(self.root,signature(),1000,validate_record(signature()),resume=True,chunk_records=4)
        self.assertEqual((self.root/'HEAD.json').read_bytes(),before)

    def test_missing_chunk_or_archive_and_extra_archive_rejected(self):
        for target in ('commit.json','trials.jsonl','retained.jsonl'):
            with self.subTest(target=target), tempfile.TemporaryDirectory() as d:
                root=Path(d)/'store'; populate(root)
                (root/'chunks/000000/0000000000'/target).unlink()
                with self.assertRaises((ValueError,FileNotFoundError)): open_store(root,resume=True)
        populate(self.root)
        with (self.root/'chunks/000000/0000000002/retained.jsonl').open('ab') as f: f.write(b'{}\n')
        with self.assertRaises(ValueError): open_store(self.root,resume=True)

    def test_each_interrupted_checkpoint_rolls_back_or_commits_atomically(self):
        stages=('before_payload_sync','after_payload_sync','after_commit_metadata','after_chunk_rename',
                'before_head_replace','after_head_replace')
        for stage in stages:
            with self.subTest(stage=stage), tempfile.TemporaryDirectory() as d:
                root=Path(d)/'store'; populate(root,3)
                def fail(at):
                    if at==stage: raise RuntimeError('simulated interruption')
                with open_store(root,resume=True,fault=fail) as s:
                    for c in range(3,6): s.append(record(c))
                    with self.assertRaises(RuntimeError): s.commit()
                expected=6 if stage=='after_head_replace' else 3
                with open_store(root,resume=True) as s:
                    self.assertEqual(s.state['nextCase'],expected)
                    for c in range(expected,9): s.append(record(c))
                    s.commit()
                with open_store(root,resume=True) as s:
                    self.assertEqual(stored_records(s),[record(c) for c in range(9)])
                    self.assertEqual(stored_records(s,'retained'),[record(c) for c in range(0,9,2)])

    def test_failed_partial_append_cannot_be_checkpointed(self):
        for stage in ('after_trial_write','after_retained_write'):
            with self.subTest(stage=stage), tempfile.TemporaryDirectory() as d:
                root=Path(d)/'store'
                def fail(at):
                    if at==stage: raise RuntimeError('partial append')
                with open_store(root,fault=fail) as s:
                    with self.assertRaises(RuntimeError): s.append(record(0))
                    with self.assertRaises(ValueError): s.commit()
                with open_store(root,resume=True) as s:
                    self.assertEqual(s.state['nextCase'],0)
                    s.append(record(0)); s.commit()

    def test_real_process_exit_and_os_lock_release(self):
        populate(self.root,3)
        script="""import os,sys
sys.path.insert(0,sys.argv[3])
from test_chunk_ledger import open_store,record
stage=sys.argv[2]
def fail(at):
    if at==stage: os._exit(37)
with open_store(sys.argv[1],resume=True,fault=fail) as s:
    for c in range(3,6): s.append(record(c))
    s.commit()
"""
        for stage,expected in [('after_chunk_rename',3),('after_head_replace',6)]:
            result=subprocess.run([sys.executable,'-c',script,str(self.root),stage,str(Path(__file__).parent)],cwd=Path(__file__).parent)
            self.assertEqual(result.returncode,37)
            with open_store(self.root,resume=True) as s: self.assertEqual(s.state['nextCase'],expected)

    def test_single_writer_lock_and_bounded_latest_reads(self):
        populate(self.root,99)
        with open_store(self.root,resume=True,verify='latest') as s:
            self.assertLess(s.io['bytesRead'],20000)
            with self.assertRaises(ValueError): open_store(self.root,resume=True)

    def test_skipped_duplicate_wrong_input_or_status_refused(self):
        with open_store(self.root) as s:
            bad=record(0); bad['case']=1
            with self.assertRaises(ValueError): s.append(bad)
        with open_store(self.root,resume=True) as s:
            s.append(record(0)); s.commit()
            with self.assertRaises(ValueError): s.append(record(0))

    def test_semantic_enumeration_and_archive_checks_survive_resealed_envelopes(self):
        import hashlib
        for damage in ('input','case','status','archive'):
            with self.subTest(damage=damage), tempfile.TemporaryDirectory() as d:
                root=Path(d)/'store'; populate(root,3)
                chunk=root/'chunks/000000/0000000000'
                file=chunk/('retained.jsonl' if damage=='archive' else 'trials.jsonl')
                rows=[json.loads(line) for line in file.read_text().splitlines()]
                if damage=='input': rows[0]['input']['stick'][0]=0
                elif damage=='case': rows[0]['case']=1
                elif damage=='status': rows[0]['status']='unknown'
                else: rows.pop(0)
                data=b''.join(encoded(r) for r in rows); file.write_bytes(data)
                meta=json.loads((chunk/'commit.json').read_text())['payload']
                key='retained' if damage=='archive' else 'trials'
                meta[key]=dict(bytes=len(data),records=len(rows),sha256=hashlib.sha256(data).hexdigest())
                atomic_json(chunk/'commit.json',seal(meta))
                head=json.loads((root/'HEAD.json').read_text())['payload']
                head['commitSha256']=seal(meta)['sha256']; atomic_json(root/'HEAD.json',seal(head))
                with self.assertRaises(ValueError): open_store(root,resume=True)

    @unittest.skipUnless(os.name=='nt','Windows sharing retry policy')
    def test_windows_sharing_retry_is_bounded_and_permanent_errors_abort(self):
        source=Path(self.temp.name)/'source'; destination=Path(self.temp.name)/'destination'
        source.write_bytes(b'checked')
        error=PermissionError('busy'); error.winerror=32
        real_replace=os.replace
        calls=[]
        def occasionally_busy(src,dst):
            calls.append(1)
            if len(calls)<3: raise error
            real_replace(src,dst)
        with patch('chunk_ledger.os.replace',side_effect=occasionally_busy),patch('chunk_ledger.time.sleep'):
            replace_with_retry(source,destination)
        self.assertEqual(destination.read_bytes(),b'checked')
        with patch('chunk_ledger.os.replace',side_effect=error) as replace,patch('chunk_ledger.time.sleep'):
            with self.assertRaises(PermissionError): replace_with_retry(source,destination)
            self.assertEqual(replace.call_count,8)


class CounterIntegrationTests(unittest.TestCase):
    def test_benchmark_timeout_preserves_elapsed_time_and_diagnostics(self):
        import benchmark_chunks
        with tempfile.TemporaryDirectory() as d:
            output=Path(d)/'new'
            argv=['benchmark_chunks','--output',str(output),'--sizes','3','--process-timeout','20']
            failure=subprocess.TimeoutExpired('test command',20,output=b'partial stdout',stderr=b'partial stderr')
            with patch('sys.argv',argv),patch('benchmark_chunks.subprocess.run',side_effect=failure):
                with self.assertRaises(RuntimeError): benchmark_chunks.main()
            attempt=json.loads((output/'attempt-3.json').read_text())
            self.assertTrue(attempt['timedOut'])
            self.assertGreaterEqual(attempt['processWallSeconds'],0)
            self.assertIn('partial stdout',(output/'batch-3.stdout.log').read_text())
            self.assertIn('HEAD',(output/'batch-3.stderr.log').read_text())

    def fake_jobs(self,*args):
        sig=signature()
        jobs=[dict(setup=j['setup'],move=SimpleNamespace(name=j['move'])) for j in sig['jobOrder']]
        meta=dict(jobOrder=sig['jobOrder'],inputSpace=sig['inputSpace'],frame=492,buttonDown=0,totalCases=1000)
        return jobs,meta

    def test_missing_receipt_resume_exact_cursor_and_offline_audit(self):
        with tempfile.TemporaryDirectory() as d:
            args=SimpleNamespace(output=Path(d)/'report.json',resume=False,benchmark=False,order='mixed',
                                 a_mode='released',buttons='stock-gameplay',chunk_records=3,
                                 resume_verify='full',cases=5,seconds=30)
            with patch('product_sweep.make_jobs',self.fake_jobs),patch('product_sweep.compare_reference',return_value=0),\
                 patch('product_sweep.hash_file',return_value='checked'),\
                 patch('product_sweep.cached_trial',return_value=('accepted-projection',{})):
                self.assertEqual(run(args)['nextCase'],5)
                args.output.unlink()  # HEAD, not the convenience receipt, controls resume.
                args.resume=True; args.cases=7
                result=run(args)
                self.assertEqual(result['thisBatch']['tested'],7)
                self.assertEqual(result['nextCase'],12)
                self.assertEqual(result['ledger']['retained'],12)
                self.assertTrue(result['integrity']['historicalContentVerified'])
            with patch('product_sweep.make_jobs') as game:
                self.assertEqual(audit_output(args)['verifiedCases'],12)
                game.assert_not_called()


if __name__=='__main__': unittest.main()
