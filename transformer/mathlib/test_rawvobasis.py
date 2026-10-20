"""Source/toy/authentic metadata only. NON_KERNEL; no production parsing on Ghost."""
import argparse,copy,json,re,tempfile,unittest,zipfile,os
from pathlib import Path
from contextlib import ExitStack
from unittest.mock import patch
import rawvobasis_generate as g
import rawvobasis_restore as c
import rawvobasis_runner as runner
CU_ARCHIVE=None
class VO(unittest.TestCase):
    def test_split_scalar_chunks_inventory_and_real_control_non_kernel(self):
        values={'tokenV':[1]*32,'positionV':[2]*32,'tokenO':[3]*128,'positionO':[4]*128}
        texts,negative=g.sources(values,0,'token');modules,names=g.inventory()
        self.assertEqual(list(texts),modules)
        for module,text in texts.items():
            self.assertEqual([g.NS+'.'+n for n in re.findall(r'^(?:def|theorem) (\w+)',text,re.M)],names[module])
        self.assertEqual(len(modules),25);self.assertEqual(len(g.HELPER_NAMES)+sum(map(len,names.values())),346)
        for kind,prefix,width in g.KINDS:
            certs=[n for module in modules if module.startswith(g.PREFIX+'.'+kind) for n in names[module]]
            self.assertEqual(certs,[g.NS+'.'+prefix+f'_cert_{i:03d}'for i in range(width)])
            for module in modules:
                if module.startswith(g.PREFIX+'.'+kind):self.assertEqual(len(names[module]),16)
        self.assertLess(modules.index(g.PREFIX+'.First'),modules.index(g.PREFIX+'.TokenV000'))
        self.assertLess(modules.index(g.PREFIX+'.VAll'),modules.index(g.PREFIX+'.TokenO000'))
        self.assertIn('weights.ovec 0 0 0 d = tokenO d + positionO d',texts[g.PREFIX+'.OAll'])
        self.assertIn('(ovec_split_eq d).symm.trans (o_eq d)',texts[g.PREFIX+'.OAll'])
        self.assertIn('WO := fun h i d => weights.WO h i d + if h = 0 ∧ i = 0 ∧ d = 0 then 1 else 0',texts[g.PREFIX+'.Control'])
        self.assertIn('proposedV 0 ≠ 0 := by decide +kernel',texts[g.PREFIX+'.Control'])
        self.assertIn('tokenV 0 ≠ 0 := by decide +kernel',texts[g.PREFIX+'.Control'])
        self.assertIn('changedWeights.ovec 0 0 0 0 = proposedO 0',negative)
        for option in ('maxRecDepth 100000','maxHeartbeats 4000000'):self.assertIn('set_option '+option,negative)
        self.assertNotRegex(''.join(texts.values())+negative,r'\b(False|sorry|admit|native_decide|unsafe|axiom)\b')
        for key in ('full_basis','fullTU','fullTI','sc','hT','finalraw'):self.assertFalse(g.SCOPE[key])
        for bad in (-1,32,True,'0',None):
            with self.assertRaises(ValueError):g.sources(values,bad,'token')
        for mutation in ('missing','extra','wrongwidth','bool'):
            bad=copy.deepcopy(values)
            if mutation=='missing':del bad['tokenV']
            elif mutation=='extra':bad['foreign']=[]
            elif mutation=='wrongwidth':bad['tokenV'].pop()
            else:bad['tokenV'][0]=False
            with self.assertRaises(ValueError):g.sources(bad,0,'token')

    def test_selected_witness_must_be_sensitive_non_kernel(self):
        values={'tokenV':[0]*32,'positionV':[0]*32,'tokenO':[0]*128,'positionO':[0]*128}
        with self.assertRaises(ValueError):g.sources(values,0,'token')
        values['positionV'][0]=1
        with self.assertRaises(ValueError):g.sources(values,0,'token')
        self.assertEqual(g.select_witness(values['tokenV'],values['positionV']),(0,'position'))
        g.sources(values,0,'position')

    def test_closed_parser_and_cloud_boundary_non_kernel(self):
        text='def tok_0 : List Int := [(.ofNat 1), (.negSucc 1)]\n'
        self.assertEqual(g.parse_vectors(text,'tok',0,1,2),[[1,-2]])
        for bad in (text+text,text.replace('tok_0','tok_1'),text.replace('(.ofNat 1)','untrusted'),text.replace('(.negSucc 1)','(.ofNat 1), (.ofNat 2)')):
            with self.assertRaises(ValueError):g.parse_vectors(bad,'tok',0,1,2)
        with self.assertRaises(ValueError):g.select_witness([0]*32,[0]*32)
        with self.assertRaises(ValueError):g.select_witness([1]*32,[-1]*32)
        with patch.object(g,'cloud_only',side_effect=ValueError('no production work here')),self.assertRaises(ValueError):g.production_witness()

    def test_generic_support_inventory_and_data_independence_non_kernel(self):
        text=(c.HERE/'TransformerBridge/RawVOBasis.lean').read_text()
        self.assertEqual([g.HELPER+'.'+n for n in re.findall(r'^theorem (\w+)',text,re.M)],g.HELPER_NAMES)
        self.assertIn('TransformerBridge.RawCUUpdate.contract_update w x i',text)
        self.assertIn('vvec_split',text);self.assertIn('contract_add_left vt vp',text)
        self.assertIn('have hv (l : Fin 32)',text);self.assertIn('have hw : (fun l : Fin 32',text)
        self.assertNotRegex(text,r'\b(weights|Net|native_decide|sorry|admit|unsafe|axiom|set_option)\b')

    def test_actual_CU_metadata_and_latest_layered_compatibility_non_kernel(self):
        self.assertEqual(len(c.identities()),37);self.assertEqual(len(c.pin()['objects']),301);self.assertEqual(len(c.pin()['selected_names']),3246)
        self.assertEqual(c.pin()['objects'],c.previous.pin()['objects'])
        for module in ('TransformerBridge.RawPacked.Generated.OAll','TransformerBridge.RawPacked.Generated.PackedTI','TransformerBridge.RawPacked.Generated.Vectors','TransformerBridge.RawCorrespondence.CUFullGenerated.UAll'):
            self.assertIn(module,{r['module']for r in c.pin()['objects']})
        with zipfile.ZipFile(CU_ARCHIVE)as z:data=c.previous.previous.read_cu(z)
        self.assertEqual(c.previous.previous.validate_cu(data),c.previous.previous.pin()['cu_objects'])
        for field in ('compiler_binary_sha256','fresh_compiled_replayed','candidate','negative_actual_bout_change'):
            bad=dict(data);a=json.loads(bad['CU113_ACCEPTED.json']);a[field]=None;bad['CU113_ACCEPTED.json']=json.dumps(a)
            with self.assertRaises((ValueError,TypeError)):c.previous.previous.validate_cu(bad)
        for row in (0,1):
            bad={'id':-1,'expired':False,'workflow_run':{'id':row,'head_sha':'wrong'}}
            with self.assertRaises(ValueError):c.previous.previous.previous.previous.base.api_identity(bad,c.identities()[0])
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
                with self.assertRaises(ValueError):c.previous.previous.read_cu(View(z,extra=[name]))
            name=next(n for n in c.previous.previous.pin()['cu_files']if n.endswith('.olean'))
            with self.assertRaises(ValueError):c.previous.previous.read_cu(View(z,corrupt=name))

    def test_mocked_support_first_and_negative_exit_gates_non_kernel(self):
        support=(c.HERE/'TransformerBridge/RawVOBasis.lean').read_text()
        for failure in (None,'support','first','negative'):
            with self.subTest(failure=failure),tempfile.TemporaryDirectory()as tmp,ExitStack()as s:
                here=Path(tmp);out=here/'out';calls=[]
                path=here/'TransformerBridge/RawVOBasis.lean';path.parent.mkdir(parents=True);path.write_text(support)
                for tool in ('lean','lake','leanchecker'):
                    path=here/'bin'/tool;path.parent.mkdir(exist_ok=True);path.write_bytes(b'FAKE never executed')
                compiler={t:c.sha(here/'bin'/t)for t in ('lean','lake','leanchecker')}
                s.enter_context(patch.dict(os.environ,{'GITHUB_REPOSITORY':'teal-sea/lean-checked-network','LEAN_NUM_THREADS':'2'}))
                for target,name,value in ((runner,'HERE',here),(runner,'OUT',out),(g,'HERE',here),(runner.common,'HERE',here)):s.enter_context(patch.object(target,name,value))
                s.enter_context(patch.object(runner,'cloud_only'));s.enter_context(patch.object(g,'cloud_only'));s.enter_context(patch.object(runner,'snapshot',return_value={}))
                s.enter_context(patch.object(c,'restore',return_value={'objects':[],'selected_names':[]}));s.enter_context(patch.object(c.previous.previous.previous,'pin',return_value={'compiler_binary_sha256':compiler}))
                def witness():
                    self.assertEqual(calls,[g.HELPER]);return {'values':{'tokenV':[1]*32,'positionV':[2]*32,'tokenO':[3]*128,'positionO':[4]*128},'l':0,'basis':'token','negative':{'field':'WO','coordinate':[0,0,0],'old':2,'new':3,'delta':1}}
                s.enter_context(patch.object(g,'production_witness',side_effect=witness))
                s.enter_context(patch.object(runner.common,'audit',side_effect=lambda label,imports,names:len(names)))
                def compile(module):
                    calls.append(module)
                    if (failure=='support'and module==g.HELPER)or(failure=='first'and module==g.PREFIX+'.First'):raise ValueError('FAKE support compile/replay failure')
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
                    self.assertFalse((out/'VO_BASIS_ACCEPTED.json').exists())
                else:
                    runner.main(None);a=json.loads((out/'VO_BASIS_ACCEPTED.json').read_text());self.assertEqual(len(calls),26);self.assertTrue(a['scope']['pilot_basis_consistency']);self.assertFalse(a['scope']['full_basis']);self.assertEqual(a['generation']['declarations'],g.HELPER_NAMES+[n for names in g.inventory()[1].values()for n in names])

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--archives',type=Path);p.add_argument('--fixture-root',type=Path);a=p.parse_args();CU_ARCHIVE=(a.archives/'12132480691.zip')if a.archives else a.fixture_root/'cu-full-39114961411/cu-full.zip'
    c.require(c.stream_sha(CU_ARCHIVE)==c.previous.previous.pin()['cu']['zip_sha256'],'actual CU ZIP identity')
    if a.archives:c.preflight(a.archives)
    unittest.main(argv=[__file__],verbosity=2)
