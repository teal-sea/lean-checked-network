"""Toy/source/authentic metadata tests only; not Lean/kernel evidence."""
import argparse,copy,json,re,tempfile,unittest,zipfile,os
from pathlib import Path
from unittest.mock import patch
from contextlib import ExitStack
import rawgrange_generate as g
import rawgrange_restore as c
import rawgrange_runner as runner
ROOT=None
ARCHIVES=None
PATHS={}
class Range(unittest.TestCase):
    def test_selection_templates_and_qualified_inventories_non_kernel(self):
        all_modules=[];all_names=[]
        for start,count in ((1,4),(507,4),(509,2)):
            rows=g.rows_for(start,count);modules,names,controls=g.inventory(start,count)
            texts,negative=g.batch_sources(start,count,{r:7 for r in rows});all_modules+=modules;all_names+=names+controls
            self.assertEqual(list(texts),modules);self.assertEqual(len(names),10*count);self.assertEqual(len(controls),4)
            self.assertEqual(g.scope(start,count)['G_rows'],rows);self.assertFalse(g.scope(start,count)['full_G_field'])
            self.assertIn(f'if i = {start} ∧ d = 0',texts[modules[1]])
            self.assertIn(f'G {start} 0 = frozenG 0',negative);self.assertIn('import '+modules[1],negative)
            self.assertEqual(texts[modules[0]].count('theorem packed_cert :'),count)
            self.assertEqual(texts[modules[0]].count('theorem carry_bound :'),count)
            self.assertEqual(texts[modules[0]].count('theorem input_bound ('),count)
            self.assertEqual(texts[modules[0]].count('theorem target_bound ('),count)
            with tempfile.TemporaryDirectory()as tmp,patch.object(g,'HERE',Path(tmp)):
                for module,expected in zip(modules,(names,controls)):
                    p=Path(tmp)/(module.replace('.','/')+'.lean');p.parent.mkdir(parents=True,exist_ok=True);p.write_text(texts[module]);g.check_declarations(module,expected)
                    with self.assertRaises(ValueError):g.check_declarations(module,expected+expected[:1])
            for bad in ({},{rows[0]:7},{r:7 for r in reversed(rows)},{**{r:7 for r in rows},511:7}):
                with self.assertRaises(ValueError):g.batch_sources(start,count,bad)
        self.assertEqual(len(set(all_modules)),len(all_modules));self.assertEqual(len(set(all_names)),len(all_names))
        for start,count in ((0,4),(511,1),(510,2),(1,0),(1,5),(True,1),(1,True),('1',4),(1,None)):
            with self.assertRaises(ValueError):g.rows_for(start,count)
            with patch.object(g,'cloud_only',side_effect=AssertionError('validation too late')),self.assertRaises(ValueError):g.production_witness(start,count)

    def test_actual_endpoints_cu_and_earlier_metadata_non_kernel(self):
        c.validate_identities(c.identities());self.assertEqual(len(c.identities()),39)
        full=c.previous.previous;earlier=full.previous;base=earlier.base
        for item in c.pin()['endpoints']:
            with zipfile.ZipFile(PATHS[item['identity']['artifact_id']])as z:data=c.read_endpoint(z,item)
            self.assertEqual(c.validate_endpoint(data,item),item['objects'])
            for key in ('scope','candidate','compiler_binary_sha256','fresh_compiled_replayed','negative_actual_Wout_change'):
                bad=dict(data);a=json.loads(bad['G_ROW_ACCEPTED.json']);a[key]=None;bad['G_ROW_ACCEPTED.json']=json.dumps(a)
                with self.assertRaises((ValueError,TypeError)):c.validate_endpoint(bad,item)
            for label in item['audits']:
                bad=dict(data);bad[label+'.out']+='\nunknown diagnostic\n'
                with self.assertRaises(ValueError):c.validate_endpoint(bad,item)
            for exitcode in (0,124):
                bad=dict(data);steps=[json.loads(s)for s in bad['steps.jsonl'].splitlines()];steps[-1]['exit']=exitcode;bad['steps.jsonl']='\n'.join(json.dumps(s)for s in steps)
                with self.assertRaises(ValueError):c.validate_endpoint(bad,item)
        with zipfile.ZipFile(PATHS[c.previous.pin()['cu']['artifact_id']])as z:c.previous.validate_cu(c.previous.read_cu(z))
        identities=c.identities();packed={}
        if ARCHIVES:
            with zipfile.ZipFile(PATHS[identities[0]['artifact_id']])as z:packed=base.old.read_metadata(z,identities[0])
        else:
            for name,value in identities[0]['metadata_sha256'].items():
                raw=(ROOT/'retained-metadata'/Path(name).name).read_bytes();self.assertEqual(c.digest(raw),value);packed[Path(name).name]=raw.decode()
        records,source,_=base.old.validate_metadata(packed,identities[0]);base.verify_sources(source)
        for item,reader,validator in ((identities[1],base.read_ci,base.validate_ci),(identities[2],earlier.boundary.read_row0,earlier.boundary.validate_row0),(identities[3],earlier.read_row127,earlier.validate_row127)):
            with zipfile.ZipFile(PATHS[item['artifact_id']])as z:records+=validator(reader(z))
        for item in full.range_lock():
            with zipfile.ZipFile(PATHS[item['artifact_id']])as z:records+=full.validate_range(full.read_range(z,item),item)
        self.assertEqual(records,full.pin()['objects'])
        for bad in (identities[:-1],identities+[identities[-1]],list(reversed(identities))):
            with self.assertRaises(ValueError):c.validate_identities(bad)

    def test_endpoint_physical_inventory_corruption_and_scoped_logs_non_kernel(self):
        class View:
            def __init__(self,z,extra=(),missing=(),corrupt=None):self.z=z;self.extra=extra;self.missing=missing;self.corrupt=corrupt
            def infolist(self):return [i for i in self.z.infolist()if i.filename not in self.missing]+[zipfile.ZipInfo(n)for n in self.extra]
            def read(self,n):return self.z.read(n)+(b'corruption'if n==self.corrupt else b'')
        for item in c.pin()['endpoints']:
            with zipfile.ZipFile(PATHS[item['identity']['artifact_id']])as z:
                for name in ('../unsafe','/absolute','rawgpilot-out/steps.jsonl','TransformerBridge/Unknown.lean','.lake/build/lib/lean/Unknown.olean','rawgpilot-out/foreign.tsv'):
                    with self.assertRaises(ValueError):c.read_endpoint(View(z,extra=[name]),item)
                for name in ('rawgpilot-out/generation.json','RawGPilot-checkpoint.json',item['objects'][0]['module'].replace('.','/')+'.lean','.lake/build/lib/lean/'+item['objects'][0]['module'].replace('.','/')+'.olean'):
                    with self.assertRaises(ValueError):c.read_endpoint(View(z,corrupt=name),item)
                    with self.assertRaises(ValueError):c.read_endpoint(View(z,missing=[name]),item)
        # Authentic endpoint timing envelopes differ and are validated under separate identities.
        entries=c.pin()['endpoints'];name='rawgpilot-out/steps.jsonl'
        self.assertNotEqual(entries[0]['files'][name],entries[1]['files'][name])
        with zipfile.ZipFile(PATHS[entries[0]['identity']['artifact_id']])as z,self.assertRaises(ValueError):c.read_endpoint(z,entries[1])

    def test_exact_new_projection_and_unknown_drift_non_kernel(self):
        raw=(c.ROOT/'.github/workflows/transformer.yml').read_text();self.assertEqual(c.digest(c.inverse_workflow(raw).encode()),c.pin()['workflow_projection']['accepted_sha256'])
        with self.assertRaises(ValueError):c.inverse_workflow(raw+'\n')
        for path,rule in c.pin()['nonproof_projections'].items():
            raw=(c.ROOT/path).read_bytes();self.assertEqual(c.digest(c.project_current(path,raw)),rule['accepted_sha256'])
            with self.assertRaises(ValueError):c.project_current(path,raw+b'\n')

    def test_mocked_two_process_orchestrator_and_exit_gates_non_kernel(self):
        for failure in (None,'Batch','negative'):
            with self.subTest(failure=failure),tempfile.TemporaryDirectory()as tmp,ExitStack()as s:
                here=Path(tmp);out=here/'out';calls=[]
                for tool in ('lean','lake','leanchecker'):
                    path=here/'bin'/tool;path.parent.mkdir(exist_ok=True);path.write_bytes(b'FAKE never executed')
                compiler={t:c.sha(here/'bin'/t)for t in ('lean','lake','leanchecker')}
                s.enter_context(patch.dict(os.environ,{'GITHUB_REPOSITORY':'teal-sea/lean-checked-network','LEAN_NUM_THREADS':'2'}))
                for target,name,value in ((runner,'HERE',here),(runner,'OUT',out),(g,'HERE',here)):s.enter_context(patch.object(target,name,value))
                s.enter_context(patch.object(runner,'cloud_only'));s.enter_context(patch.object(g,'cloud_only'));s.enter_context(patch.object(runner,'snapshot',return_value={}))
                s.enter_context(patch.object(c,'restore',return_value={'objects':[],'selected_names':[]}))
                s.enter_context(patch.object(c.previous.previous,'pin',return_value={'compiler_binary_sha256':compiler}));s.enter_context(patch.object(c.previous.previous,'range_lock',return_value=[]))
                s.enter_context(patch.object(g,'production_witness',return_value={'bounds':{str(r):7 for r in (1,2,3,4)},'negative':{'field':'Wout','coordinate':[1,0],'old':5,'new':6,'delta':1}}))
                s.enter_context(patch.object(runner.common,'audit',side_effect=lambda label,imports,names:len(names)))
                def compile(module):
                    calls.append(module)
                    if failure and module.endswith('.'+failure):raise ValueError('FAKE compile/replay failure')
                    stem=module.replace('.','/');obj=here/'.lake/build/lib/lean'/(stem+'.olean');obj.parent.mkdir(parents=True,exist_ok=True);obj.write_bytes(b'FAKE object')
                    record={'module':module,'source_sha256':c.sha(here/(stem+'.lean')),'olean_sha256':c.sha(obj)}
                    for filename in ('compiled.jsonl','replayed.jsonl'):
                        with(out/filename).open('a')as f:f.write(json.dumps(record)+'\n')
                    for phase in ('fresh_compile_','fresh_replay_'):
                        label=phase+module;runner.common.runner.STEPS[label]={'seconds':.01};(out/(label+'.time')).write_text('Maximum resident set size (kbytes): 1\n')
                    return record
                def run(label,args,seconds=60,negative=False):
                    if label=='compiler-version':return 'version 4.35.0 commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc'
                    if label=='compiler-prefix':return str(here)
                    if negative and failure=='negative':raise ValueError('FAKE exit0/syntax/timeout rejection')
                    return ''
                s.enter_context(patch.object(runner.common,'fresh_compile',side_effect=compile));s.enter_context(patch.object(runner.common.runner,'run',side_effect=run))
                if failure:
                    with self.assertRaises(ValueError):runner.main(None,1,4)
                    self.assertFalse((out/'G_RANGE_ACCEPTED.json').exists())
                else:
                    runner.main(None,1,4);a=json.loads((out/'G_RANGE_ACCEPTED.json').read_text());self.assertEqual(a['scope'],g.scope(1,4));self.assertEqual(len(calls),2);self.assertEqual(a['generation']['declarations'],g.inventory(1,4)[1]+g.inventory(1,4)[2])

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--archives',type=Path);p.add_argument('--fixture-root',type=Path);a=p.parse_args();ROOT=a.fixture_root;ARCHIVES=a.archives
    for index,item in enumerate(c.identities()):
        aid=item['artifact_id'];run=item.get('source_run',item.get('run'))
        if ARCHIVES:path=ARCHIVES/(str(aid)+'.zip')
        elif index==0:continue
        elif index==1:path=ROOT/f'ci-{run}/ci.zip'
        elif index==2:path=ROOT/f'u-row0-{run}/u-row0.zip'
        elif index==3:path=ROOT/f'u-row127-{run}/u-row127.zip'
        elif index<36:path=ROOT/f'u-range-{run}/u-range.zip'
        elif index==36:path=ROOT/f'cu-full-{run}/cu-full.zip'
        else:path=ROOT/f'g-pilot-{run}/g-pilot.zip'
        c.require(c.stream_sha(path)==item['zip_sha256'],'actual archive SHA');PATHS[aid]=path
    if ARCHIVES:c.preflight(ARCHIVES) # Full real39 seam before any kernel stage, including original packed ZIP.
    unittest.main(argv=[__file__],verbosity=2)
