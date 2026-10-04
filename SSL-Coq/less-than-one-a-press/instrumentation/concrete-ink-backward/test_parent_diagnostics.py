import copy
from types import SimpleNamespace
import unittest
import json
from pathlib import Path
import tempfile
from unittest.mock import patch

from parent_diagnostics import histogram,replay_actual_suffix
from reverse_scattershot import bits,number,Input,DISAPPEARED,FIRST_APPLY,GameBudgetReached
from search import differences,IDLE


def fixture():
    low=[bits(-2200),bits(768),bits(-1024)]; high=[low[0],1156733869,low[2]]
    parent=dict(movement=low,collision=low,display=high,action=IDLE,actionArg=0,
                actionState=0,actionTimer=0,depth=bits(0),vy=bits(0),usedSlot=-1,
                floorHeight=bits(38),floorOwner=-1,floorNull=0,platform=-1,rng=1,
                area=1,pad=[0,0,0],buttonDown=0,buttonPressed=0)
    actual=copy.deepcopy(parent);actual.update(movement=[low[0],bits(2000),low[2]],rng=2,floorHeight=bits(1280))
    end=copy.deepcopy(parent);end.update(movement=high,collision=high,display=high,
             action=DISAPPEARED,actionArg=0x40002,usedSlot=64,platform=61,floorOwner=61,floorHeight=1156733869)
    last=copy.deepcopy(end);last.update(area=2,movement=FIRST_APPLY,collision=low,display=low,action=IDLE,usedSlot=-1,platform=-1)
    c=dict(ticket=dict(kind='extend',parent=0),patch=parent,controls=[Input().record()]*2,
           checkpoints=[parent],targets=['original'],family='ground',move='fixture')
    row=dict(case=1,status='rejected',detail=dict(proposal=c,stage='parent',differences=differences(actual,parent,tuple(parent))))
    sig=dict(aMode='released',targets=dict(original=dict(movement=high,collision=low,display=high)),
             endpoints=dict(original=end),entryRecordContract='Explicit pending frame',retentionSuffix=dict(updates=23))
    return parent,actual,end,last,row,sig


class Fake:
    def __init__(self,break_a=False):
        parent,actual,end,last,_,_=fixture()
        self.base=parent;self.states=[actual,end]+[end]*22+[last];self.i=0;self.ops=[];self.current=copy.deepcopy(parent)
        self.raw=[0,0];self.break_a=break_a;self.game=self;self.observer=SimpleNamespace(slot=lambda x:x)
    def restore(self,context):self.i=0;self.current=copy.deepcopy(self.base);self.ops.append('restore')
    def patch(self,values):self.current.update(copy.deepcopy(values));self.ops.append('patch')
    def observe(self):return copy.deepcopy(self.current)
    def frame(self):return 10+self.i
    def advance(self,c):
        self.current=copy.deepcopy(self.states[self.i]);self.i+=1;self.raw=[c.x,c.y]
        self.current['buttonDown']=c.buttons|(0x8000 if self.break_a else 0)
        self.current['buttonPressed']=0;self.ops.append('advance')
    def read(self,path):
        if path=='gGlobalTimer':return self.frame()
        if path=='gCurrAreaIndex':return self.current['area']
        if path=='gMarioState.pos':return [number(x) for x in self.current['movement']]
        if path=='gMarioObject.header.gfx.pos':return [number(x) for x in self.current['display']]
        if path.startswith('gMarioObject.oPos'):return number(self.current['collision']['XYZ'.index(path[-1])])
        if path=='gMarioPlatform':return self.current['platform']
        if path=='gMarioState.usedObj':return self.current['usedSlot']
        if path.startswith('gMarioState.'):return self.current[path.split('.')[-1]]
        if path=='gControllers[0].rawStickX':return self.raw[0]
        if path=='gControllers[0].rawStickY':return self.raw[1]
        if path.startswith('gControllers[0].'):return self.current[path.split('.')[-1]]
        raise AssertionError(path)
    def frame_log(self):return [dict(type='FLT_EXECUTE_ACTION',action=self.current['action'],pos=[number(x) for x in self.current['movement']])]


class ParentDiagnosticsTests(unittest.TestCase):
    def test_histogram_counts_overlapping_fields_and_controller_separately(self):
        _,_,_,_,row,_=fixture();h=histogram([row])
        self.assertEqual(h['selectedAttempts'],1);self.assertEqual(h['positionMismatchAttempts'],1)
        self.assertEqual(h['controllerMismatchAttempts'],0)
        self.assertEqual(h['fieldMismatchCounts'],dict(floorHeight=1,movement=1,rng=1))

    def test_different_parent_still_replays_entire_suffix_once(self):
        _,_,_,_,row,sig=fixture();b=Fake()
        r=replay_actual_suffix(b,None,row,sig,Input(),update_limit=25)
        self.assertFalse(r['strictParentMatched']);self.assertTrue(r['selectedLastUpdateContinuation'])
        self.assertTrue(r['checkedKnownPayoff']);self.assertEqual(r['updates'],25)
        self.assertEqual(b.ops,['restore','patch']+['advance']*25)

    def test_changed_saved_differences_stop_reproduction(self):
        _,_,_,_,row,sig=fixture();row['detail']['differences']={}
        with self.assertRaisesRegex(RuntimeError,'saved attempt'):
            replay_actual_suffix(Fake(),None,row,sig,Input())

    def test_warp_argument_can_decrement_before_end_observation(self):
        _,_,_,_,row,sig=fixture();b=Fake();b.states[1]=copy.deepcopy(b.states[1])
        b.states[1]['actionArg']=0x40001
        r=replay_actual_suffix(b,None,row,sig,Input(),update_limit=25)
        self.assertTrue(r['checkedKnownPayoff'])
        self.assertEqual(r['disappearedTransitions'][0]['endActionArg'],0x40001)
        self.assertTrue(r['disappearedTransitions'][0]['actionEntryObserved'])

    def test_native_budget_stops_without_false_gameplay_verdict(self):
        _,_,_,_,row,sig=fixture();b=Fake()
        with self.assertRaises(GameBudgetReached) as c:
            replay_actual_suffix(b,None,row,sig,Input(),update_limit=2)
        self.assertEqual(c.exception.updates,2)
        self.assertEqual(b.ops,['restore','patch','advance','advance'])

    def test_a_or_controller_mismatch_is_not_ignored(self):
        _,_,_,_,row,sig=fixture()
        with self.assertRaisesRegex(RuntimeError,'Controller readback'):
            replay_actual_suffix(Fake(break_a=True),None,row,sig,Input())

    def test_verification_limit_preserves_source_and_constructs_no_game(self):
        from parent_diagnostics import run
        from test_compact_scattershot import scatter_signature,scatter_row
        from reverse_scattershot import open_store
        with tempfile.TemporaryDirectory() as d:
            root=Path(d)/'old';sig=scatter_signature()
            with open_store(root,sig,chunk_records=3) as s:
                for i in range(3):s.append(scatter_row(s.state['aux'],sig,i))
                s.commit()
            head=(root/'HEAD.json').read_bytes()
            args=SimpleNamespace(ledger=root,output=Path(d)/'diagnostic.json',game_updates=5000,
                                 setup_seconds=30,verification_seconds=0,search_seconds=30,
                                 wall_seconds=90,replay_suffix=True,verbose=False)
            with patch('parent_diagnostics.make_scene') as game,patch('builtins.print'):
                r=run(args)
            game.assert_not_called();self.assertEqual(r['status'],'verification incomplete')
            self.assertEqual(r['replay'],[]);self.assertEqual((root/'HEAD.json').read_bytes(),head)


if __name__=='__main__':unittest.main()
