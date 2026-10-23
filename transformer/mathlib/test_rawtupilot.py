"""Source/toy/authentic metadata only. NON_KERNEL; no production parsing on Ghost."""
import argparse,copy,json,re,tempfile,unittest,zipfile,os
from pathlib import Path
from contextlib import ExitStack
from unittest.mock import patch
import rawtupilot_generate as g
import rawtupilot_restore as c
import rawtupilot_runner as runner
CU_ARCHIVE=None
class TU(unittest.TestCase):
    def test_fixed_site_all113_and_real_U_control_templates_non_kernel(self):
        for d in (0,5,127):
            texts,negative=g.sources(d)
            self.assertEqual(list(texts),[g.PREFIX+'.'+s for s in g.DECLARATIONS])
            for stage,names in g.DECLARATIONS.items():self.assertEqual(re.findall(r'^(?:def|theorem) (\w+)',texts[g.PREFIX+'.'+stage],re.M),names)
            self.assertIn('(weights.rawTables 256).TU 0 0 0 k',texts[g.PREFIX+'.Site'])
            self.assertIn('Ko KU urows_eq input_bound urows_bound target_bound carry_bound packed_cert k',texts[g.PREFIX+'.Site'])
            self.assertIn('input_bound',texts[g.PREFIX+'.Parameters']);self.assertIn(':= o_bound e',texts[g.PREFIX+'.Parameters'])
            self.assertIn('Fin 1',texts[g.PREFIX+'.Representative'])
            self.assertIn('2 * (128 * Ko * KU)',texts[g.PREFIX+'.PackedTU'])
            self.assertIn(f'weights.U e k + if e = {d} ∧ k = 0 then 1 else 0',texts[g.PREFIX+'.Control'])
            self.assertIn(f'proposedO {d} ≠ 0 := by decide +kernel',texts[g.PREFIX+'.Control'])
            self.assertIn('TU_U_update weights 256 0 0 0',texts[g.PREFIX+'.Control'])
            self.assertIn('(changedWeights.rawTables 256).TU 0 0 0 0 = frozenTU 0',negative)
            self.assertIn('set_option maxRecDepth 100000',negative);self.assertIn('set_option maxHeartbeats 4000000',negative)
            self.assertNotRegex(negative,r'\b(False|sorry|admit|native_decide|unsafe|axiom)\b')
        self.assertEqual(len(g.HELPER_NAMES)+sum(map(len,g.DECLARATIONS.values()))+3246,3261)
        self.assertFalse(g.SCOPE['full_TU_field']);self.assertEqual(g.SCOPE['TU_components'],113)
        for bad in (-1,128,True,'0',None):
            with self.assertRaises(ValueError):g.sources(bad)

    def test_closed_O_parser_and_nonzero_blocker_non_kernel(self):
        vector='['+', '.join(['(.ofNat 0)']*127+['(.negSucc 2)'])+']'
        source='def proposedV (l : Fin 32) : Int := unused\ndef proposedO (d : Fin 128) : Int := TransformerCore.nth 0 '+vector+' d.val\n'
        values=g.parse_o(source);self.assertEqual(g.choose_nonzero(values),127)
        for text in (source+source,source.replace('(.negSucc 2)','arbitrary'),source.replace('Fin 128','Fin 127'),source+'def foreign : Int := 0\n'):
            with self.assertRaises(ValueError):g.parse_o(text)
        with self.assertRaises(ValueError):g.choose_nonzero([0]*128)
        with self.assertRaises(ValueError):g.choose_nonzero([False]*128)
        with patch.object(g,'cloud_only',side_effect=ValueError('no production work here')),self.assertRaises(ValueError):g.production_witness()

    def test_generic_support_inventory_and_data_independence_non_kernel(self):
        text=(c.HERE/'TransformerBridge/RawTUUpdate.lean').read_text()
        self.assertEqual(re.findall(r'^theorem (\w+)',text,re.M),['contract_update_right','TU_U_update'])
        self.assertIn('TransformerBridge.RawCUUpdate.contract_update w x d',text)
        self.assertIn('have hU : (fun e : Fin 128 => changed.U e k)',text)
        self.assertIn('W.U e l + if e = d ∧ l = k then 1 else 0',text)
        self.assertNotRegex(text,r'\b(weights|Net|native_decide|sorry|admit|unsafe|axiom|set_option)\b')

    def test_actual_CU_metadata_and_latest_layered_compatibility_non_kernel(self):
        self.assertEqual(len(c.identities()),37);self.assertEqual(len(c.pin()['objects']),301);self.assertEqual(len(c.pin()['selected_names']),3246)
        self.assertEqual(c.pin()['objects'],c.previous.pin()['objects'])
        for module in ('TransformerBridge.RawPacked.Generated.OAll','TransformerBridge.RawPacked.Generated.PackedTI','TransformerBridge.RawPacked.Generated.Vectors','TransformerBridge.RawCorrespondence.CUFullGenerated.UAll'):
            self.assertIn(module,{r['module']for r in c.pin()['objects']})
        with zipfile.ZipFile(CU_ARCHIVE)as z:data=c.previous.read_cu(z)
        self.assertEqual(c.previous.validate_cu(data),c.previous.pin()['cu_objects'])
        for field in ('compiler_binary_sha256','fresh_compiled_replayed','candidate','negative_actual_bout_change'):
            bad=dict(data);a=json.loads(bad['CU113_ACCEPTED.json']);a[field]=None;bad['CU113_ACCEPTED.json']=json.dumps(a)
            with self.assertRaises((ValueError,TypeError)):c.previous.validate_cu(bad)
        for row in (0,1):
            bad={'id':-1,'expired':False,'workflow_run':{'id':row,'head_sha':'wrong'}}
            with self.assertRaises(ValueError):c.previous.previous.previous.base.api_identity(bad,c.identities()[0])
        for path,rule in c.pin()['nonproof_projections'].items():
            raw=(c.ROOT/path).read_bytes();self.assertEqual(c.digest(c.project_current(path,raw)),rule['accepted_sha256'])
            with self.assertRaises(ValueError):c.project_current(path,raw+b'\n')
        raw=(c.ROOT/'.github/workflows/transformer.yml').read_text();self.assertEqual(c.digest(c.inverse_workflow(raw).encode()),c.pin()['workflow_projection']['accepted_sha256'])
        with self.assertRaises(ValueError):c.inverse_workflow(raw+'\n')

    def test_strict_audit_and_corrupt_object_rejection_non_kernel(self):
        check=__import__('rawcorrespondence_runner').check_correspondence_axioms
        good="'A' depends on axioms: [propext, Classical.choice, Quot.sound]\n"
        for raw,names in ((good,['A','A']),(good+good,['A']),(good+'garbage',['A']),(good.replace('Quot.sound','Unknown'),['A']),('warning\n'+good,['A']),(good,['B'])):
            with self.assertRaises(ValueError):check(raw,names)
        class View:
            def __init__(self,z,extra=(),corrupt=None):self.z=z;self.extra=extra;self.corrupt=corrupt
            def infolist(self):return self.z.infolist()+[zipfile.ZipInfo(n)for n in self.extra]
            def read(self,n):return self.z.read(n)+(b'corruption'if n==self.corrupt else b'')
        with zipfile.ZipFile(CU_ARCHIVE)as z:
            for name in ('../unsafe','/absolute','.lake/build/lib/lean/Unknown.olean','rawcufull-out/steps.jsonl'):
                with self.assertRaises(ValueError):c.previous.read_cu(View(z,extra=[name]))
            name=next(n for n in c.previous.pin()['cu_files']if n.endswith('.olean'))
            with self.assertRaises(ValueError):c.previous.read_cu(View(z,corrupt=name))

    def test_mocked_support_first_and_negative_exit_gates_non_kernel(self):
        support=(c.HERE/'TransformerBridge/RawTUUpdate.lean').read_text()
        for failure in (None,'support','negative'):
            with self.subTest(failure=failure),tempfile.TemporaryDirectory()as tmp,ExitStack()as s:
                here=Path(tmp);out=here/'out';calls=[]
                path=here/'TransformerBridge/RawTUUpdate.lean';path.parent.mkdir(parents=True);path.write_text(support)
                for tool in ('lean','lake','leanchecker'):
                    path=here/'bin'/tool;path.parent.mkdir(exist_ok=True);path.write_bytes(b'FAKE never executed')
                compiler={t:c.sha(here/'bin'/t)for t in ('lean','lake','leanchecker')}
                s.enter_context(patch.dict(os.environ,{'GITHUB_REPOSITORY':'teal-sea/lean-checked-network','LEAN_NUM_THREADS':'2'}))
                for target,name,value in ((runner,'HERE',here),(runner,'OUT',out),(g,'HERE',here),(runner.common,'HERE',here)):s.enter_context(patch.object(target,name,value))
                s.enter_context(patch.object(runner,'cloud_only'));s.enter_context(patch.object(g,'cloud_only'));s.enter_context(patch.object(runner,'snapshot',return_value={}))
                s.enter_context(patch.object(c,'restore',return_value={'objects':[],'selected_names':[]}));s.enter_context(patch.object(c.previous.previous,'pin',return_value={'compiler_binary_sha256':compiler}))
                def witness():
                    self.assertEqual(calls,[g.HELPER]);return {'d':5,'nonzero_O_value':3,'negative':{'field':'U','coordinate':[5,0],'old':2,'new':3,'delta':1}}
                s.enter_context(patch.object(g,'production_witness',side_effect=witness))
                s.enter_context(patch.object(runner.common,'audit',side_effect=lambda label,imports,names:len(names)))
                def compile(module):
                    calls.append(module)
                    if failure=='support'and module==g.HELPER:raise ValueError('FAKE support compile/replay failure')
                    stem=module.replace('.','/');obj=here/'.lake/build/lib/lean'/(stem+'.olean');obj.parent.mkdir(parents=True,exist_ok=True);obj.write_bytes(b'FAKE object');record={'module':module,'source_sha256':c.sha(here/(stem+'.lean')),'olean_sha256':c.sha(obj)}
                    for filename in ('compiled.jsonl','replayed.jsonl'):
                        with(out/filename).open('a')as f:f.write(json.dumps(record)+'\n')
                    for phase in ('fresh_compile_','fresh_replay_'):
                        label=phase+module;runner.common.runner.STEPS[label]={'seconds':.01};(out/(label+'.time')).write_text('Maximum resident set size (kbytes): 1\n')
                    return record
                def run(label,args,seconds=60,negative=False):
                    if label=='compiler-version':return 'version 4.35.0 commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc'
                    if label=='compiler-prefix':return str(here)
                    if negative and failure=='negative':raise ValueError('FAKE exit0/syntax/timeout rejected')
                    return ''
                s.enter_context(patch.object(runner.common,'fresh_compile',side_effect=compile));s.enter_context(patch.object(runner.common.runner,'run',side_effect=run))
                if failure:
                    with self.assertRaises(ValueError):runner.main(None)
                    self.assertFalse((out/'TU_SITE_ACCEPTED.json').exists())
                else:
                    runner.main(None);a=json.loads((out/'TU_SITE_ACCEPTED.json').read_text());self.assertEqual(len(calls),6);self.assertTrue(a['scope']['TU_site']);self.assertFalse(a['scope']['full_TU_field']);self.assertEqual(a['generation']['declarations'],g.HELPER_NAMES+[g.NS+'.'+n for names in g.DECLARATIONS.values()for n in names])

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--archives',type=Path);p.add_argument('--fixture-root',type=Path);a=p.parse_args();CU_ARCHIVE=(a.archives/'12132480691.zip')if a.archives else a.fixture_root/'cu-full-39114961411/cu-full.zip'
    c.require(c.stream_sha(CU_ARCHIVE)==c.previous.pin()['cu']['zip_sha256'],'actual CU ZIP identity')
    if a.archives:c.preflight(a.archives)
    unittest.main(argv=[__file__],verbosity=2)
