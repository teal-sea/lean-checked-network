"""Source/toy/authenticated metadata regressions; NO local kernel evidence."""
import argparse,copy,json,re,unittest,zipfile
from pathlib import Path
from unittest.mock import patch
import rawgpilot_generate as g
import rawgpilot_restore as c
import rawgpilot_runner as runner
CU_ARCHIVE=None
class G(unittest.TestCase):
    def test_endpoint_identities_disjoint_non_kernel(self):
        # Real symbolic templates, toy bound0; no production coefficients or kernel work.
        zero,negative0=g.sources(0,0);last,negative511=g.sources(511,0)
        def declarations(texts):
            result=[]
            for text in texts.values():
                namespace=re.search(r'^namespace ([A-Za-z0-9_.]+)$',text,re.M).group(1)
                result += [namespace+'.'+n for n in re.findall(r'^(?:def|theorem) (\w+)',text,re.M)]
            return result
        self.assertTrue(set(zero).isdisjoint(last),'endpoint module identities collide')
        self.assertTrue(set(declarations(zero)).isdisjoint(declarations(last)),'endpoint constants collide')
        self.assertEqual(len(declarations(zero)),14);self.assertEqual(len(declarations(last)),14)
        for row,texts,negative in ((0,zero,negative0),(511,last,negative511)):
            prefix=g.PREFIX+f'.Row{row:03d}';namespace=g.NS+f'.Row{row:03d}'
            self.assertEqual(list(texts),[prefix+'.'+stage for stage in g.DECLARATIONS])
            for stage,text in zip(g.DECLARATIONS,texts.values()):
                self.assertIn('namespace '+namespace+'\n',text)
                for module in re.findall(r'^import ([A-Za-z0-9_.]+)$',text,re.M):
                    if module.startswith(g.PREFIX+'.'):self.assertIn(module,texts)
            self.assertIn('import '+prefix+'.Control\n',negative)
            self.assertIn('namespace '+namespace+'\n',negative)
            self.assertIn(f'G {row} 0 = frozenG 0',negative)
            self.assertEqual(g.scope(row)['G_rows'],[row])

    def test_endpoints_and_toy_emission_non_kernel(self):
        for row in (0,511):
            sources,negative=g.sources(row,7)
            prefix,namespace=g.identities(row)
            self.assertEqual(list(sources),[prefix+'.'+s for s in g.DECLARATIONS])
            self.assertEqual(g.scope(row),{'G_rows':[row],'G_components':113,'full_G_field':False,'full_hT':False,'finalraw':False})
            for stage,names in g.DECLARATIONS.items():
                self.assertEqual(re.findall(r'^(?:def|theorem) (\w+)',sources[prefix+'.'+stage],re.M),names)
            self.assertIn(f'weights.Wout {row} d',sources[prefix+'.Parameters'])
            self.assertIn('urows_bound',sources[prefix+'.Row'])
            self.assertIn('2 * (128 * Ko * KU)',sources[prefix+'.PackedG'])
            self.assertIn('contract_update',sources[prefix+'.Control'])
            self.assertIn(f'G {row} 0 = frozenG 0',negative)
            self.assertNotIn('G_field',sources[prefix+'.Row'])
            self.assertIn('Fin 1',sources[prefix+'.Representative'])
        for row in (-1,1,510,512,True,'0',None):
            with self.assertRaises(ValueError):g.sources(row,7)
            with patch.object(g,'cloud_only',side_effect=AssertionError('must validate first')),self.assertRaises(ValueError):g.production_witness(row)
        with self.assertRaises(ValueError):g.sources(0,-1)
        with patch.object(g,'cloud_only',side_effect=ValueError('cloud required')),self.assertRaises(ValueError):g.production_witness(0)

    def test_actual_cu_metadata_and_projection_non_kernel(self):
        with zipfile.ZipFile(CU_ARCHIVE)as z:
            data=c.read_cu(z)
        self.assertEqual(c.validate_cu(data),c.pin()['cu_objects'])
        self.assertEqual(len(c.pin()['objects']),301);self.assertEqual(len(c.pin()['selected_names']),3246)
        self.assertEqual(len(set(c.pin()['selected_names'])),3246)
        self.assertEqual(len(c.identities()),37)
        c.previous.validate_lock(c.previous.range_lock())
        self.assertEqual(len({r['module']for r in c.pin()['objects']}),301)
        for label in ('compiler_binary_sha256','fresh_compiled_replayed','restored_objects','candidate','exact_production_audit_names','negative_actual_bout_change'):
            bad=dict(data);a=json.loads(bad['CU113_ACCEPTED.json']);a[label]=None;bad['CU113_ACCEPTED.json']=json.dumps(a)
            with self.subTest(label=label),self.assertRaises((ValueError,TypeError)):c.validate_cu(bad)
        for label in c.pin()['cu_audits']:
            bad=dict(data);bad[label+'.out']+='\ngarbage\n'
            with self.assertRaises(ValueError):c.validate_cu(bad)
        for code in (0,124):
            bad=dict(data);steps=[json.loads(s)for s in bad['steps.jsonl'].splitlines()];steps[-1]['exit']=code;bad['steps.jsonl']='\n'.join(json.dumps(s)for s in steps)
            with self.assertRaises(ValueError):c.validate_cu(bad)
        workflow=(c.ROOT/'.github/workflows/transformer.yml').read_text()
        old=c.inverse_workflow(workflow)
        self.assertEqual(c.digest(old.encode()),c.pin()['workflow_projection']['accepted_sha256'])
        with self.assertRaises(ValueError):c.inverse_workflow(workflow+'\n')
        for path,rule in c.pin()['nonproof_projections'].items():
            raw=(c.ROOT/path).read_bytes()
            self.assertEqual(c.digest(c.project_current(path,raw)),rule['accepted_sha256'])
            with self.assertRaises(ValueError):c.project_current(path,raw+b'\n')

    def test_actual_cu_inventory_and_byte_corruption_non_kernel(self):
        class View:
            def __init__(self,z,extra=(),missing=(),corrupt=None):self.z=z;self.extra=extra;self.missing=missing;self.corrupt=corrupt
            def infolist(self):return [i for i in self.z.infolist()if i.filename not in self.missing]+[zipfile.ZipInfo(n)for n in self.extra]
            def read(self,n):return self.z.read(n)+(b'bad'if n==self.corrupt else b'')
        with zipfile.ZipFile(CU_ARCHIVE)as z:
            for name in ('../unsafe','/absolute','rawcufull-out/unknown.time','TransformerBridge/Unknown.lean','.lake/build/lib/lean/Unknown.olean','rawcufull-out/steps.jsonl'):
                with self.subTest(name=name),self.assertRaises(ValueError):c.read_cu(View(z,extra=[name]))
            for name in ('rawcufull-out/steps.jsonl','RawCUFull-checkpoint.json',next(n for n in c.pin()['cu_files']if n.endswith('.olean'))):
                with self.assertRaises(ValueError):c.read_cu(View(z,corrupt=name))
                with self.assertRaises(ValueError):c.read_cu(View(z,missing=[name]))

    def test_mocked_orchestrator_stage_and_exit_gates_non_kernel(self):
        import tempfile,os
        from contextlib import ExitStack
        for row,failure in ((row,failure) for row in (0,511) for failure in (None,'Parameters','Representative','negative')):
            with self.subTest(row=row,failure=failure),tempfile.TemporaryDirectory()as tmp,ExitStack()as s:
                here=Path(tmp);out=here/'out';calls=[]
                for tool in ('lean','lake','leanchecker'):
                    path=here/'bin'/tool;path.parent.mkdir(exist_ok=True);path.write_bytes(b'FAKE never executed')
                compiler={tool:c.sha(here/'bin'/tool)for tool in ('lean','lake','leanchecker')}
                s.enter_context(patch.dict(os.environ,{'GITHUB_REPOSITORY':'teal-sea/lean-checked-network','LEAN_NUM_THREADS':'2'}))
                for target,name,value in ((runner,'HERE',here),(runner,'OUT',out),(g,'HERE',here)):
                    s.enter_context(patch.object(target,name,value))
                s.enter_context(patch.object(runner,'cloud_only'));s.enter_context(patch.object(g,'cloud_only'))
                s.enter_context(patch.object(runner,'snapshot',return_value={}))
                s.enter_context(patch.object(c,'restore',return_value={'objects':[],'selected_names':[]}))
                s.enter_context(patch.object(c.previous,'pin',return_value={'compiler_binary_sha256':compiler}))
                s.enter_context(patch.object(c.previous,'range_lock',return_value=[]))
                s.enter_context(patch.object(g,'production_witness',return_value={'Ko':7}))
                s.enter_context(patch.object(runner.common,'check_declarations'))
                s.enter_context(patch.object(runner.common,'audit',side_effect=lambda label,imports,names:len(names)))
                def compile(module):
                    stage=module.rsplit('.',1)[-1];calls.append(stage)
                    if failure==stage:raise ValueError('FAKE compile/replay failure')
                    if stage=='PackedG':self.assertEqual(calls[:2],['Parameters','Representative'])
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
                    if negative:
                        self.assertEqual(label,'negative-actual-Wout-change')
                        if failure=='negative':raise ValueError('FAKE exit0/syntax/timeout rejection')
                    return ''
                s.enter_context(patch.object(runner.common,'fresh_compile',side_effect=compile))
                s.enter_context(patch.object(runner.common.runner,'run',side_effect=run))
                if failure is None:
                    runner.main(None,row);a=json.loads((out/'G_ROW_ACCEPTED.json').read_text());self.assertEqual(a['scope'],g.scope(row));self.assertFalse(a['scope']['full_G_field'])
                    prefix,namespace=g.identities(row)
                    self.assertEqual(a['generation']['modules'],[prefix+'.'+stage for stage in g.DECLARATIONS])
                    self.assertEqual(a['generation']['declarations'],[namespace+'.'+name for names in g.DECLARATIONS.values() for name in names])
                    self.assertEqual(set(a['generation']['outputs']),{module.replace('.','/')+'.lean' for module in a['generation']['modules']})
                else:
                    with self.assertRaises(ValueError):runner.main(None,row)
                    self.assertFalse((out/'G_ROW_ACCEPTED.json').exists())

    def test_strict_audit_and_invalid_producers_non_kernel(self):
        check=c.check_correspondence_axioms
        good="'A' depends on axioms: [propext, Classical.choice, Quot.sound]\n"
        self.assertEqual(check(good,['A']),1)
        for text,names in ((good,['A','A']),(good+good,['A']),(good.replace('Quot.sound','Unknown'),['A']),('warning\n'+good,['A']),(good+'garbage',['A']),('', ['A']),(good,['B'])):
            with self.assertRaises(ValueError):check(text,names)
        api={'id':12132480691,'expired':False,'workflow_run':{'id':39114961411,'head_sha':c.pin()['source_sha']}}
        for field in ('id','expired','workflow_run'):
            bad=copy.deepcopy(api);bad[field]=None
            with self.assertRaises((ValueError,AttributeError)):c.previous.previous.base.api_identity(bad,c.pin()['cu'])
        with patch.object(runner.gen,'endpoint',side_effect=ValueError('bad row')),patch.object(runner,'cloud_only',side_effect=AssertionError('too late')),self.assertRaises(ValueError):runner.main(None,1)

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--archives',type=Path);p.add_argument('--fixture-root',type=Path);a=p.parse_args()
    CU_ARCHIVE=(a.archives/'12132480691.zip')if a.archives else a.fixture_root/'cu-full-39114961411/cu-full.zip'
    c.require(c.stream_sha(CU_ARCHIVE)==c.pin()['cu']['zip_sha256'],'actual CU ZIP')
    unittest.main(argv=[__file__],verbosity=2)
