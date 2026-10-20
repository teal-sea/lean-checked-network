"""NON_KERNEL source/toy/actual metadata tests; no production vectors emitted locally."""
import argparse,copy,json,re,tempfile,unittest,zipfile,os
from pathlib import Path
from contextlib import ExitStack
from unittest.mock import patch
import rawvoboundary_generate as g
import rawvoboundary_restore as c
import rawvoboundary_runner as runner
FIXTURE_ROOT=None
ARCHIVES=None
VALUES={'tokenV':[1]*32,'positionV':[2]*32,'tokenO':[3]*128,'positionO':[4]*128}
class Boundary(unittest.TestCase):
    def test_endpoint_templates_bounds_control_and_complete_inventory_non_kernel(self):
        texts,negative=g.sources(VALUES,127,7);modules,names=g.inventory()
        self.assertEqual(list(texts),modules);self.assertEqual(len(modules),29)
        self.assertEqual(sum(map(len,names.values())),349)
        for module,text in texts.items():
            self.assertEqual([g.NS+'.'+n for n in re.findall(r'^(?:def|theorem) (\w+)',text,re.M)],names[module])
            self.assertIn('H003Tk113J002',module)
        for kind,prefix,width in g.KINDS:
            selected=[n for m in modules if m.startswith(g.PREFIX+'.'+kind)for n in names[m]]
            self.assertEqual(selected,[g.NS+'.'+prefix+f'_cert_{i:03d}'for i in range(width)])
            self.assertTrue(all(len(names[m])==16 for m in modules if m.startswith(g.PREFIX+'.'+kind)))
        self.assertIn('weights.tok 113',texts[g.PREFIX+'.First']);self.assertIn('weights.pos 2',texts[g.PREFIX+'.First'])
        self.assertIn('weights.WV 3',texts[g.PREFIX+'.First']);self.assertIn('weights.WO 3',texts[g.PREFIX+'.First'])
        self.assertIn('weights.ovec 3 113 2 d = boundaryO d',texts[g.PREFIX+'.OAll'])
        params=texts[g.PREFIX+'.TUParameters']
        self.assertIn('def Kboundary : Nat := 7',params)
        self.assertIn('boundaryO e ≤ Kboundary := by\n  revert e\n  decide +kernel',params)
        self.assertNotRegex(''.join(texts.values()),r'\b(proposedO|o_bound|Ko)\b')
        self.assertIn('(weights.rawTables 256).TU 3 2 113',texts[g.PREFIX+'.Site'])
        self.assertIn('Kboundary KU urows_eq input_bound urows_bound target_bound carry_bound packed_cert k',texts[g.PREFIX+'.Site'])
        self.assertIn('Fin 1',texts[g.PREFIX+'.Representative'])
        self.assertIn('2 * (128 * Kboundary * KU)',texts[g.PREFIX+'.PackedTU'])
        self.assertIn('boundaryO 127 ≠ 0 := by decide +kernel',texts[g.PREFIX+'.Control'])
        self.assertIn('weights.U e k + if e = 127 ∧ k = 0 then 1 else 0',texts[g.PREFIX+'.Control'])
        self.assertIn('TU_U_update weights 256 3 113 2 127 0',texts[g.PREFIX+'.Control'])
        self.assertIn('(changedWeights.rawTables 256).TU 3 2 113 0 = frozenTU 0',negative)
        self.assertIn('boundaryO (fun e => boundary_o_eq e)',negative)
        for option in ('maxRecDepth 100000','maxHeartbeats 4000000'):self.assertIn('set_option '+option,negative)
        self.assertNotRegex(''.join(texts.values())+negative,r'\b(False|sorry|admit|native_decide|unsafe|axiom)\b')
        for key in ('full_basis','fullTU','fullTI','sc','hT','finalraw'):self.assertFalse(g.SCOPE[key])
        import rawvobasis_generate as old
        self.assertTrue(set(modules).isdisjoint(old.inventory()[0]))
        self.assertTrue({n for ns in names.values()for n in ns}.isdisjoint({n for ns in old.inventory()[1].values()for n in ns}))

    def test_selection_and_cloud_guard_non_kernel(self):
        for d,ko in ((-1,7),(128,7),(True,7),(0,-1),(0,True),(0,6)):
            with self.assertRaises(ValueError):g.sources(VALUES,d,ko)
        bad=copy.deepcopy(VALUES);bad['tokenO']=[-4]*128
        with self.assertRaises(ValueError):g.sources(bad,0,0)
        for key in VALUES:
            bad=copy.deepcopy(VALUES);bad[key].pop()
            with self.assertRaises(ValueError):g.sources(bad,0,7)
        with patch.object(g,'cloud_only',side_effect=ValueError('no local production work')),self.assertRaises(ValueError):g.production_witness()
        self.assertIn("fields['tok'][113]",Path(g.__file__).read_text())
        self.assertIn("fields['pos'][2]",Path(g.__file__).read_text())
        self.assertIn("fields['WV'][3*32+l]",Path(g.__file__).read_text())
        self.assertIn("fields['WO'][3*128+d]",Path(g.__file__).read_text())

    def test_exact_top_layer_inverses_and_unknown_drift_non_kernel(self):
        raw=(c.ROOT/'.github/workflows/transformer.yml').read_text()
        self.assertEqual(c.digest(c.inverse_workflow(raw).encode()),c.pin()['workflow_projection']['accepted_sha256'])
        with self.assertRaises(ValueError):c.inverse_workflow(raw+'\n')
        for path,rule in c.pin()['nonproof_projections'].items():
            raw=(c.ROOT/path).read_bytes();self.assertEqual(c.digest(c.project_current(path,raw)),rule['accepted_sha256'])
            with self.assertRaises(ValueError):c.project_current(path,raw+b'\n')
        self.assertEqual(len(c.identities()),39);self.assertEqual(len(c.pin()['objects']),333);self.assertEqual(len(c.pin()['selected_names']),3607)

    def test_actual_two_continuations_and_corruption_reds_non_kernel(self):
        if FIXTURE_ROOT is None and ARCHIVES is None:self.skipTest('actual archives supplied by CLI only')
        for item in c.pin()['continuations']:
            folder='vo-basis-39380863776'if item['kind']=='VO'else'tu-pilot-39375551094'
            file='vo-basis.zip'if item['kind']=='VO'else'tu-pilot.zip'
            path=(ARCHIVES/'pilots'/(str(item['identity']['artifact_id'])+'.zip'))if ARCHIVES else FIXTURE_ROOT/folder/file
            self.assertEqual(c.stream_sha(path),item['identity']['zip_sha256'])
            with zipfile.ZipFile(path)as z:
                data=c.read_continuation(z,item);self.assertEqual(c.validate_continuation(data,item),item['objects'])
                class View:
                    def __init__(self,extra=None,corrupt=None):self.extra=extra;self.corrupt=corrupt
                    def infolist(self):return z.infolist()+([zipfile.ZipInfo(self.extra)]if self.extra else[])
                    def read(self,n):return z.read(n)+(b'corrupt'if n==self.corrupt else b'')
                for name in ('../unsafe','/absolute','foreign.lean',next(iter(item['files']))):
                    with self.assertRaises(ValueError):c.read_continuation(View(extra=name),item)
                for name in (next(n for n in item['files']if n.endswith('.olean')),next(n for n in item['files']if n.endswith('checkpoint.json')),item['out']+'/generation.json'):
                    with self.assertRaises(ValueError):c.read_continuation(View(corrupt=name),item)
            for field in ('compiler_binary_sha256','fresh_compiled_replayed','candidate',item['negative_key']):
                bad=dict(data);a=json.loads(bad[item['acceptance']]);a[field]=None;bad[item['acceptance']]=json.dumps(a)
                with self.assertRaises((ValueError,TypeError)):c.validate_continuation(bad,item)
            bad=dict(data);steps=json.loads(json.dumps(item['steps']));steps[-1]['exit']=0;bad['steps.jsonl']='\n'.join(map(json.dumps,steps))
            with self.assertRaises(ValueError):c.validate_continuation(bad,item)
            label=next(iter(item['audits']));bad=dict(data);bad[label+'.out']='warning\n'+bad[label+'.out']
            with self.assertRaises(ValueError):c.validate_continuation(bad,item)
            api_path=(ARCHIVES/'pilots'/(str(item['identity']['artifact_id'])+'.json'))if ARCHIVES else FIXTURE_ROOT/folder/'artifact-api.json'
            api=json.loads(api_path.read_text())
            for field in ('id','expired','workflow_run'):
                bad=copy.deepcopy(api);bad[field]=None
                with self.assertRaises((ValueError,TypeError,AttributeError)):c.base.api_identity(bad,item['identity'])
        with tempfile.TemporaryDirectory()as tmp:
            tmp=Path(tmp)
            for item in c.pin()['continuations']:
                folder='vo-basis-39380863776'if item['kind']=='VO'else'tu-pilot-39375551094';file='vo-basis.zip'if item['kind']=='VO'else'tu-pilot.zip';aid=str(item['identity']['artifact_id'])
                archive=(ARCHIVES/'pilots'/(aid+'.zip'))if ARCHIVES else FIXTURE_ROOT/folder/file
                api=(ARCHIVES/'pilots'/(aid+'.json'))if ARCHIVES else FIXTURE_ROOT/folder/'artifact-api.json'
                (tmp/(aid+'.zip')).symlink_to(archive);(tmp/(aid+'.json')).write_bytes(api.read_bytes())
            self.assertEqual(len(c.continuation_preflight(tmp)),32)
            (tmp/'extra.zip').touch()
            with self.assertRaises(ValueError):c.continuation_preflight(tmp)
            (tmp/'extra.zip').unlink();next(tmp.glob('*.zip')).unlink()
            with self.assertRaises(ValueError):c.continuation_preflight(tmp)

    def test_actual39_repo_source_storage_and_object_reds_non_kernel(self):
        if ARCHIVES is None:self.skipTest('full actual39 archive view supplied by --archives')
        records=c.pin()['objects'];items=c.identities()
        with ExitStack()as stack:
            zs=[stack.enter_context(zipfile.ZipFile(ARCHIVES/('prior'if i<37 else'pilots')/(str(item['artifact_id'])+'.zip')))for i,item in enumerate(items)]
            indexes=[set(z.namelist())for z in zs]
            repo_only=[r for r in records if not any(r['module'].replace('.','/')+'.lean'in names for names in indexes)]
            self.assertEqual({r['module']for r in repo_only},{'Transformer.'+n for n in ('ExpFix','Program','Logits','Compose','Raw')}|{'TransformerBridge.Bridge'})
            for r in repo_only:
                path=c.HERE/(r['module'].replace('.','/')+'.lean')
                self.assertEqual(c.sha(path),r['source_sha256'])
            # Actual byte hashes/imports/object presence; no compiler or numeric interpretation.
            c.verify_canonical_storage(zs,records)
            record=repo_only[0];src=record['module'].replace('.','/')+'.lean';obj='.lake/build/lib/lean/'+record['module'].replace('.','/')+'.olean'
            class View:
                def __init__(self,z,missing=False,corrupt=False,foreign_source=False):self.z=z;self.missing=missing;self.corrupt=corrupt;self.foreign_source=foreign_source
                def namelist(self):return [n for n in self.z.namelist()if not(self.missing and n==obj)]+([src]if self.foreign_source else[])
                def read(self,n):
                    if self.foreign_source and n==src:return b'NON_KERNEL corrupt archived source overlap'
                    return self.z.read(n)+(b'NON_KERNEL corrupt object'if self.corrupt and n==obj else b'')
            for mutation in ('missing','corrupt'):
                views=[View(z,missing=mutation=='missing',corrupt=mutation=='corrupt')for z in zs]
                with self.assertRaisesRegex(ValueError,'^missing union object$'if mutation=='missing'else'^boundary physical canonical overlap$'):c.verify_canonical_storage(views,records)
            with self.assertRaisesRegex(ValueError,'^union source/overlap identity: '+re.escape(src)+'$'):c.verify_canonical_storage([View(zs[0],foreign_source=True)]+zs[1:],records)
            target=c.HERE/src;original_read=Path.read_bytes
            def corrupt_repository(path):return b'NON_KERNEL corrupt repo source'if path==target else original_read(path)
            with patch.object(Path,'read_bytes',new=corrupt_repository),self.assertRaisesRegex(ValueError,'^union source/overlap identity: '+re.escape(src)+'$'):c.verify_canonical_storage(zs,records)
            original_exists=Path.exists
            def missing_repository(path):return False if path==target else original_exists(path)
            with patch.object(Path,'exists',new=missing_repository),self.assertRaisesRegex(ValueError,'^union source/overlap identity: '+re.escape(src)+'$'):c.verify_canonical_storage(zs,records)

    def test_strict_audit_unknown_diagnostic_and_names_non_kernel(self):
        check=runner.common.check_correspondence_axioms;raw="'A' depends on axioms: [propext, Classical.choice, Quot.sound]\n"
        for body,names in ((raw,['A','A']),(raw+raw,['A']),(raw+'garbage',['A']),(raw.replace('Quot.sound','Unknown'),['A']),('warning\n'+raw,['A']),(raw,['B'])):
            with self.assertRaises(ValueError):check(body,names)

    def test_mocked_support_first_and_negative_exit_gates_non_kernel(self):
        retained=c.pin();retained_modules=[r['module']for r in retained['objects']]
        self.assertEqual(len(retained_modules),333);self.assertEqual(len(retained['selected_names']),3607)
        for failure in (None,'first','representative','negative'):
            with self.subTest(failure=failure),tempfile.TemporaryDirectory()as tmp,ExitStack()as s:
                here=Path(tmp);out=here/'out';calls=[]
                for tool in ('lean','lake','leanchecker'):
                    path=here/'bin'/tool;path.parent.mkdir(exist_ok=True);path.write_bytes(b'FAKE never executed')
                compiler={t:c.sha(here/'bin'/t)for t in ('lean','lake','leanchecker')}
                s.enter_context(patch.dict(os.environ,{'GITHUB_REPOSITORY':'teal-sea/lean-checked-network','LEAN_NUM_THREADS':'2'}))
                for target,name,value in ((runner,'HERE',here),(runner,'OUT',out),(g,'HERE',here),(runner.common,'HERE',here)):s.enter_context(patch.object(target,name,value))
                s.enter_context(patch.object(runner,'cloud_only'));s.enter_context(patch.object(g,'cloud_only'));s.enter_context(patch.object(runner,'snapshot',return_value={}))
                # Fake file bytes only at I/O boundaries; exact retained module/name inventories.
                restored_records=[]
                for module in retained_modules:
                    stem=module.replace('.','/');src=here/(stem+'.lean');obj=here/'.lake/build/lib/lean'/(stem+'.olean')
                    src.parent.mkdir(parents=True,exist_ok=True);src.write_bytes(b'NON_KERNEL mock restored source')
                    obj.parent.mkdir(parents=True,exist_ok=True);obj.write_bytes(b'NON_KERNEL mock restored object')
                    restored_records.append({'module':module,'source_sha256':c.sha(src),'olean_sha256':c.sha(obj)})
                s.enter_context(patch.object(c,'restore',return_value={'objects':restored_records,'selected_names':retained['selected_names']}));s.enter_context(patch.object(c,'pin',return_value={**retained,'compiler_binary_sha256':compiler}))
                def witness():
                    self.assertEqual(calls,[]);return {'values':{'tokenV':[1]*32,'positionV':[2]*32,'tokenO':[3]*128,'positionO':[4]*128},'d':0,'ko':7,'negative':{'field':'U','coordinate':[0,0],'old':2,'new':3,'delta':1}}
                s.enter_context(patch.object(g,'production_witness',side_effect=witness))
                def audit(label,imports,names):
                    if label=='complete-VO-boundary':
                        self.assertEqual(calls,g.inventory()[0])
                        self.assertEqual(imports,retained_modules+calls)
                        self.assertEqual(names,retained['selected_names']+[n for ns in g.inventory()[1].values()for n in ns]);self.assertEqual(len(names),3956)
                    return len(names)
                s.enter_context(patch.object(runner.common,'audit',side_effect=audit))
                def compile(module):
                    calls.append(module)
                    if (failure=='representative'and module==g.PREFIX+'.Representative')or(failure=='first'and module==g.PREFIX+'.First'):raise ValueError('FAKE support compile/replay failure')
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
                    self.assertFalse((out/'VO_BOUNDARY_ACCEPTED.json').exists())
                else:
                    runner.main(None);a=json.loads((out/'VO_BOUNDARY_ACCEPTED.json').read_text());self.assertEqual(len(calls),29);self.assertTrue(a['scope']['boundary_basis_and_TU_site']);self.assertFalse(a['scope']['full_basis']);self.assertEqual(a['generation']['declarations'],[n for names in g.inventory()[1].values()for n in names])

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--archives',type=Path);p.add_argument('--fixture-root',type=Path);a=p.parse_args();FIXTURE_ROOT=a.fixture_root;ARCHIVES=a.archives
    if a.archives:
        c.preflight(a.archives)
        # Cloud folders contain authentic retained continuations; validate_continuation ran in preflight.
    unittest.main(argv=[__file__],verbosity=2)
