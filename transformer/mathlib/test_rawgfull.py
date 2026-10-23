"""Symbolic/source/authentic retained metadata only; NO new kernel verification."""
import argparse,copy,json,re,tempfile,unittest,zipfile,os,hashlib
from pathlib import Path
from unittest.mock import patch
from contextlib import ExitStack
import rawgfull_generate as g
import rawgfull_restore as c
import rawgfull_runner as runner
PATHS={}
ARCHIVES=None
ACCEPTED_NEGATIVE_ARCHIVE=None
class Full(unittest.TestCase):
    def test_negative_exact_accepted_endpoint_source_non_kernel(self):
        # Exact historical source identity only; successor rejection needs public kernel CI.
        import rawgpilot_generate as endpoint
        texts,negative=g.sources(c.range_lock());accepted,old_negative=endpoint.sources(0,0)
        self.assertEqual(negative,old_negative)
        self.assertEqual(hashlib.sha256(negative.encode()).hexdigest(),'5f63be4c7c38724c17e8dc85e92cf815f2ba20efb0af67923a20cdf309ae21d0')
        self.assertEqual(re.findall(r'^import (\S+)$',negative,re.M),['TransformerBridge.RawCorrespondence.GPilotGenerated.Row000.Control'])
        self.assertEqual(re.findall(r'^namespace (\S+)$',negative,re.M),['TransformerBridge.RawCorrespondence.GPilotCanonical.Row000'])
        self.assertEqual(re.findall(r'^set_option (\S+) (\S+)$',negative,re.M),[('maxRecDepth','100000'),('maxHeartbeats','4000000')])
        self.assertIn('example : (changedWeights.rawTables 256).G 0 0 = frozenG 0 := by\n  rw [G_of_contract]\n  decide +kernel\n',negative)
        self.assertNotRegex(negative,r'\b(False|sorry|admit|native_decide|unsafe|axiom)\b')
        self.assertEqual({m:hashlib.sha256(s.encode()).hexdigest()for m,s in texts.items()},{'TransformerBridge.RawCorrespondence.GFullGenerated.Assembly':'c53d807791512995de95b4a8411b099767e23bae59ea3a0ff3f9ae4bba1bc32c','TransformerBridge.RawCorrespondence.GFullGenerated.Control':'7ff17983cf069027eca60937534202c72dc170441433f5edc28ec7336fc6106f'})
        prefix,_=endpoint.identities(0)
        self.assertIn('def frozenG (k : Fin 113) : Int := (TransformerBridge.toTables TransformerCore.Net.tab).G 0 k',accepted[prefix+'.Parameters'])
        self.assertIn('weights.Wout i d + if i = 0 ∧ d = 0 then 1 else 0',accepted[prefix+'.Control'])
        if ACCEPTED_NEGATIVE_ARCHIVE is not None:
            with zipfile.ZipFile(ACCEPTED_NEGATIVE_ARCHIVE)as z:
                self.assertEqual(negative.encode(),z.read('rawgpilot-out/changed-Wout.lean'))

    def test_index_transport_goal_sensitive_cleanup_non_kernel(self):
        # Symbolic templates only: offset0 dsimp can close the goal by itself.
        texts,_=g.sources(c.range_lock())
        final=texts[g.MODULES[0]].split('theorem G_field :',1)[1]
        transports=re.findall(r'(?ms)^([ ]+)have hi : .*? := by\n(.*?)^\1have h := G_block_(\d{3}) j$',final)
        self.assertEqual([offset for _,_,offset in transports],['000','128','256','384'])
        self.assertNotIn('<;>',final)
        for _,body,offset in transports:
            with self.subTest(offset=offset):
                tactics=[line.strip() for line in body.splitlines() if line.strip()]
                expected=['apply Fin.ext','dsimp [j]']
                if offset!='000':expected.append('omega')
                self.assertEqual(tactics,expected)
        self.assertEqual(len(re.findall(r'dsimp \[j\]\n[ ]+omega',final)),3)

    def test_bounded_fin128_blocks_and_preserved_control_non_kernel(self):
        # Real symbolic emission only; no local Lean or kernel verdict.
        texts,negative=g.sources(c.range_lock());body=texts[g.MODULES[0]]
        self.assertNotIn('fin_cases i',body,'old512-way recursion-prone case split remains')
        offsets=(0,128,256,384)
        self.assertEqual(re.findall(r'^theorem (G_block_\d{3}) \(j : Fin 128\)',body,re.M),[f'G_block_{offset:03d}'for offset in offsets])
        self.assertEqual(body.count('  fin_cases j\n'),4)
        rows=g.row_inventory(c.range_lock());covered=[]
        for offset in offsets:
            block=body.split(f'theorem G_block_{offset:03d} ',1)[1].split('\ntheorem ',1)[0]
            refs=re.findall(r'^  · exact (\S+)$',block,re.M)
            self.assertEqual(refs,[row['proof']for row in rows[offset:offset+128]])
            self.assertIn(f'j.val + {offset}',block);covered+=refs
        self.assertEqual(len(covered),len(set(covered)));self.assertEqual(len(covered),512)
        self.assertIn('theorem G_field : (TransformerBridge.toTables TransformerCore.Net.tab).G =\n    (TransformerBridge.RawPackedPilot.weights.rawTables 256).G'+' := by',body)
        self.assertEqual(hashlib.sha256(texts[g.MODULES[1]].encode()).hexdigest(),'7ff17983cf069027eca60937534202c72dc170441433f5edc28ec7336fc6106f')
        self.assertEqual(hashlib.sha256(negative.encode()).hexdigest(),'5f63be4c7c38724c17e8dc85e92cf815f2ba20efb0af67923a20cdf309ae21d0')
        actual=[g.NS+'.'+n for n in re.findall(r'^theorem (\w+)',body,re.M)]
        self.assertEqual(actual,g.ASSEMBLY_NAMES)
        self.assertEqual(g.NAMES,g.ASSEMBLY_NAMES+g.CONTROL_NAMES)
        self.assertEqual(len(g.NAMES)+8886,8894)
        self.assertEqual(body.count('rw [hi] at h'),4)
        self.assertNotRegex(body,r'\b(set_option|sorry|admit|native_decide|unsafe|axiom)\b')

    def test_symbolic_exact512_coverage_and_model_imports_non_kernel(self):
        items=c.range_lock();rows=g.row_inventory(items);self.assertEqual([r['row']for r in rows],list(range(512)))
        texts,negative=g.sources(items);self.assertEqual(list(texts),g.MODULES)
        body=texts[g.MODULES[0]];proofs=re.findall(r'^  · exact (\S+)$',body,re.M)
        self.assertEqual(proofs,[r['proof']for r in rows]);self.assertEqual(len(set(proofs)),512)
        for imp in ('Mathlib','Transformer.Raw','TransformerBridge.Bridge'):self.assertIn('import '+imp+'\n',body)
        self.assertIn('funext i\n  by_cases h128',body);self.assertIn('(TransformerBridge.RawPackedPilot.weights.rawTables 256).G',body)
        self.assertNotRegex(body,r'\b(sorry|admit|native_decide|unsafe|set_option|decide)\b')
        self.assertIn('namespace '+g.ENDPOINT+'\n',negative);self.assertIn('(changedWeights.rawTables 256).G 0 0 = frozenG 0',negative);self.assertIn('decide +kernel',negative)
        for bad in (items[:-1],items+[items[-1]],list(reversed(items))):
            with self.assertRaises(ValueError):g.row_inventory(bad)
        for key,value in (('run',1),('source_sha','wrong'),('G_rows',[1,3,4,5]),('objects',[])):
            bad=copy.deepcopy(items);bad[0][key]=value
            with self.assertRaises(ValueError):c.validate_lock(bad)
        self.assertEqual(len(c.pin()['objects']),567);self.assertEqual(len(c.pin()['selected_names']),8886)
        self.assertEqual(len(c.identities()),167)
        self.assertEqual([group for group,_ in c.archive_groups()],['prior']*39+['ranges']*128)

    def test_all128_actual_range_bytes_receipts_and_union_non_kernel(self):
        items=c.range_lock();records=[]
        for item in items:
            with zipfile.ZipFile(PATHS[item['artifact_id']])as z:data=c.read_range(z,item)
            records+=c.validate_range(data,item)
        self.assertEqual(c.previous.pin()['objects']+records,c.pin()['objects'])
        with ExitStack()as stack:
            zs=[stack.enter_context(zipfile.ZipFile(PATHS[i['artifact_id']]))for i in items];c.validate_range_union(zs,items)
        for item in (items[0],items[64],items[-1]):
            with zipfile.ZipFile(PATHS[item['artifact_id']])as z:data=c.read_range(z,item)
            for key in ('scope','compiler_binary_sha256','candidate','fresh_compiled_replayed','negative_actual_Wout_range_change'):
                bad=dict(data);a=json.loads(bad['G_RANGE_ACCEPTED.json']);a[key]=None;bad['G_RANGE_ACCEPTED.json']=json.dumps(a)
                with self.assertRaises((ValueError,TypeError)):c.validate_range(bad,item)
            for label in ('batch-axioms','control-axioms','complete-G-range-axioms'):
                bad=dict(data);bad[label+'.out']+='\nunknown axiom garbage\n'
                with self.assertRaises(ValueError):c.validate_range(bad,item)
            for code in (0,124):
                bad=dict(data);steps=[json.loads(s)for s in data['steps.jsonl'].splitlines()];steps[-1]['exit']=code;bad['steps.jsonl']='\n'.join(json.dumps(s)for s in steps)
                with self.assertRaises(ValueError):c.validate_range(bad,item)

    def test_actual_physical_inventory_and_source_object_mutations_non_kernel(self):
        class View:
            def __init__(self,z,extra=(),corrupt=None):self.z=z;self.extra=extra;self.corrupt=corrupt
            def infolist(self):return self.z.infolist()+[zipfile.ZipInfo(n)for n in self.extra]
            def read(self,n):return self.z.read(n)+(b'corruption'if n==self.corrupt else b'')
        items=c.range_lock()
        for item in (items[0],items[64],items[-1]):
            with zipfile.ZipFile(PATHS[item['artifact_id']])as z:
                for name in ('../unsafe','/absolute','rawgrange-out/steps.jsonl','TransformerBridge/Unknown.lean','.lake/build/lib/lean/Unknown.olean','rawgrange-out/foreign.tsv'):
                    with self.assertRaises(ValueError):c.read_range(View(z,extra=[name]),item)
                for name in ('RawGRange-checkpoint.json','rawgrange-out/generation.json',item['objects'][0]['module'].replace('.','/')+'.lean','.lake/build/lib/lean/'+item['objects'][0]['module'].replace('.','/')+'.olean'):
                    with self.assertRaises(ValueError):c.read_range(View(z,corrupt=name),item)
        self.assertNotEqual(c.pin()['range_files'][str(items[0]['run'])]['rawgrange-out/steps.jsonl'],c.pin()['range_files'][str(items[-1]['run'])]['rawgrange-out/steps.jsonl'])

    def test_strict39_directory_routing_and_layered_inverses_non_kernel(self):
        with tempfile.TemporaryDirectory()as tmp:
            folder=Path(tmp);(folder/'prior').mkdir();(folder/'ranges').mkdir()
            for i in c.identities():(folder/(str(i['artifact_id'])+'.zip')).touch()
            with self.assertRaisesRegex(ValueError,'missing/extra archive ZIPs'):c.previous.preflight(folder)
            with patch.object(c.previous,'preflight',return_value=[])as prior,self.assertRaisesRegex(ValueError,'exact128 range ZIPs'):c.preflight(folder)
            prior.assert_called_once_with(folder/'prior')
        raw=(c.ROOT/'.github/workflows/transformer.yml').read_text();self.assertEqual(c.digest(c.inverse_workflow(raw).encode()),c.pin()['workflow_projection']['accepted_sha256'])
        with self.assertRaises(ValueError):c.inverse_workflow(raw+'\n')
        for path,rule in c.pin()['nonproof_projections'].items():
            raw=(c.ROOT/path).read_bytes();self.assertEqual(c.digest(c.project_current(path,raw)),rule['accepted_sha256'])
            with self.assertRaises(ValueError):c.project_current(path,raw+b'\n')

    def test_mocked_full_orchestrator_gates_non_kernel(self):
        for failure in (None,'Assembly','negative'):
            with self.subTest(failure=failure),tempfile.TemporaryDirectory()as tmp,ExitStack()as s:
                here=Path(tmp);out=here/'out';calls=[]
                for tool in ('lean','lake','leanchecker'):
                    p=here/'bin'/tool;p.parent.mkdir(exist_ok=True);p.write_bytes(b'FAKE never executed')
                compiler={t:c.sha(here/'bin'/t)for t in ('lean','lake','leanchecker')}
                s.enter_context(patch.dict(os.environ,{'GITHUB_REPOSITORY':'teal-sea/lean-checked-network','LEAN_NUM_THREADS':'2'}))
                for target,name,value in ((runner,'HERE',here),(runner,'OUT',out),(g,'HERE',here)):s.enter_context(patch.object(target,name,value))
                s.enter_context(patch.object(runner,'cloud_only'));s.enter_context(patch.object(g,'cloud_only'));s.enter_context(patch.object(runner,'snapshot',return_value={}))
                s.enter_context(patch.object(c,'restore',return_value={'objects':[],'selected_names':[]}))
                s.enter_context(patch.object(c.previous.previous.previous,'pin',return_value={'compiler_binary_sha256':compiler}))
                s.enter_context(patch.object(runner.common,'check_declarations'))
                def audit(label,imports,names):
                    self.assertEqual(names,{'batch':g.ASSEMBLY_NAMES,'control':g.CONTROL_NAMES,'complete-G-field':g.NAMES}[label])
                    return len(names)
                s.enter_context(patch.object(runner.common,'audit',side_effect=audit))
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
                    if negative and failure=='negative':raise ValueError('FAKE false-control exit0/syntax/timeout')
                    return ''
                s.enter_context(patch.object(runner.common,'fresh_compile',side_effect=compile));s.enter_context(patch.object(runner.common.runner,'run',side_effect=run))
                if failure:
                    with self.assertRaises(ValueError):runner.main(None)
                    self.assertFalse((out/'G_FIELD_ACCEPTED.json').exists())
                else:
                    runner.main(None);a=json.loads((out/'G_FIELD_ACCEPTED.json').read_text());self.assertTrue(a['scope']['G_field']);self.assertFalse(a['scope']['full_hT']);self.assertEqual(len(calls),2);self.assertEqual(a['generation']['negative_sha256'],hashlib.sha256(g.sources(c.range_lock())[1].encode()).hexdigest())

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--archives',type=Path);p.add_argument('--fixture-root',type=Path);a=p.parse_args();ARCHIVES=a.archives
    ACCEPTED_NEGATIVE_ARCHIVE=(ARCHIVES/'prior/12132623178.zip')if ARCHIVES else a.fixture_root/'g-pilot-39117822541/g-pilot.zip'
    for item in c.range_lock():
        path=(ARCHIVES/'ranges'/(str(item['artifact_id'])+'.zip'))if ARCHIVES else a.fixture_root/('g-range-'+str(item['run']))/'g-range.zip'
        c.require(c.stream_sha(path)==item['zip_sha256'],'actual G range ZIP identity');PATHS[item['artifact_id']]=path
    if ARCHIVES:c.preflight(ARCHIVES) # Complete real167 BEFORE new proof writes; old strict39 preserved.
    unittest.main(argv=[__file__],verbosity=2)
