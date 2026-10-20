"""NON_KERNEL source/toy/retained-metadata tests. Production emission is cloud-only."""
import argparse,copy,json,re,tempfile,unittest,zipfile,os
from pathlib import Path
from contextlib import ExitStack
from unittest.mock import patch
import rawvorange_generate as g
import rawvorange_restore as c
import rawvorange_runner as runner
FIXTURE_ROOT=None
ARCHIVES=None
def toy(sel):return [{'index':i,'V':[i+1]*32,'O':[i+2]*128}for i in sel['indices']]
class Range(unittest.TestCase):
    def test_closed_selectors_and_exact_proposal_rows_non_kernel(self):
        for args in ((True,'token',1,4),(0,'TOKEN',1,4),(4,'token',1,4),(0,'token',-1,4),(0,'token',1,0),(0,'token',1,5),(0,'token',112,4),(0,'position',1,3),(0,'token',0,1),(3,'token',113,1),(3,'position',2,1)):
            with self.assertRaises(ValueError):g.selection(*args)
        for bad in ('01','+1',' 1','1;echo bad','True','1.0',True,None):
            with self.assertRaises(ValueError):g.uint(bad)
        self.assertEqual(g.uint('0'),0);self.assertEqual(g.uint('113'),113)
        sel=g.selection();values=toy(sel);values[0]['index']=True
        with self.assertRaises(ValueError):g.sources(sel,values,0)
        for change in ('duplicate','gap','extra','missing','boolcoef'):
            values=toy(sel)
            if change=='duplicate':values[1]['index']=values[0]['index']
            elif change=='gap':values[1]['index']=42
            elif change=='extra':values.append(values[-1])
            elif change=='missing':values.pop()
            else:values[0]['V'][0]=False
            with self.assertRaises(ValueError):g.sources(sel,values,0)
        with patch.object(g,'cloud_only',side_effect=ValueError('no local production')),self.assertRaises(ValueError):g.production_witness(sel)

    def test_first_last_both_kind_disjoint_inventory_and_real_control_non_kernel(self):
        seen_modules=set();seen_names=set()
        for args in ((0,'token',1,4),(0,'token',110,4),(0,'position',1,2),(3,'token',109,4),(3,'position',0,2),(1,'token',0,4),(2,'position',0,3)):
            sel=g.selection(*args);texts,negative=g.sources(sel,toy(sel),31);modules,names=g.inventory(sel)
            self.assertEqual(list(texts),modules);self.assertEqual(len(modules),15*sel['count']+1)
            self.assertEqual(sum(map(len,names.values())),172*sel['count']+5)
            self.assertTrue(seen_modules.isdisjoint(modules));seen_modules.update(modules)
            decls={n for ns in names.values()for n in ns};self.assertTrue(seen_names.isdisjoint(decls));seen_names.update(decls)
            for module,text in texts.items():
                self.assertEqual([g.module_namespace(sel,module)+'.'+n for n in re.findall(r'^(?:def|theorem) (\w+)',text,re.M)],names[module])
                for dep in re.findall(r'^import (.+)$',text,re.M):self.assertTrue(dep in modules or dep in {r['module']for r in c.pin()['objects']},dep)
            for i in sel['indices']:
                p=g.prefix(sel)+'.'+g.group(sel,i);tk,j=g.site(sel,i)
                self.assertLess(modules.index(p+'.First'),modules.index(p+'.V000'))
                for stage,width in (('V',32),('O',128)):
                    for block in range(width//16):self.assertEqual(len(names[p+f'.{stage}{block:03d}']),16)
                self.assertIn(f'weights.ovec {sel["head"]} {tk} {j} d = actualO d',texts[p+'.Assembly'])
            if sel['head']==0:
                self.assertIn(g.OLD+('.positionV'if sel['kind']=='token'else'.tokenV'),texts[g.prefix(sel)+'.'+g.group(sel,sel['start'])+'.Assembly'])
            h=sel['head'];tk,j=g.site(sel,sel['start']);control=texts[g.prefix(sel)+'.Control']
            self.assertIn('actualV 31 ≠ 0 := by decide +kernel',control)
            self.assertIn(f'weights.WO a e d + if a = {h} ∧ e = 31 ∧ d = 0 then 1 else 0',control)
            self.assertIn(f'ovec_WO_update weights {h} {tk} {j} 31 0',control)
            self.assertIn(f'changedWeights.ovec {h} {tk} {j} 0 = actualO 0',negative)
            self.assertIn('actualV (fun l => actual_v_eq l)',negative)
            self.assertIn('set_option maxRecDepth 100000',negative);self.assertIn('set_option maxHeartbeats 4000000',negative)
            self.assertNotRegex(''.join(texts.values())+negative,r'\b(False|sorry|admit|native_decide|unsafe|axiom)\b')
            for key in ('full_basis','fullTI','fullTU','sc','hT','finalraw'):self.assertFalse(g.scope(sel)[key])
            self.assertEqual(len(g.scope(sel)['basis_groups']),sel['count'])
        text=Path(g.__file__).read_text();self.assertIn("fields['tok'][tk][e]+fields['pos'][j][e]",text)

    def test_exact_inverses_and_retained362_inventory_non_kernel(self):
        raw=(c.ROOT/'.github/workflows/transformer.yml').read_text()
        self.assertEqual(c.digest(c.inverse_workflow(raw).encode()),c.pin()['workflow_projection']['accepted_sha256'])
        with self.assertRaises(ValueError):c.inverse_workflow(raw+'\n')
        for path,rule in c.pin()['nonproof_projections'].items():
            raw=(c.ROOT/path).read_bytes();self.assertEqual(c.digest(c.project_current(path,raw)),rule['accepted_sha256'])
            with self.assertRaises(ValueError):c.project_current(path,raw+b'\n')
        self.assertEqual(len(c.identities()),40);self.assertEqual(len(c.pin()['objects']),362);self.assertEqual(len(c.pin()['selected_names']),3956)

    def test_actual_boundary_archive_and_metadata_reds_non_kernel(self):
        if FIXTURE_ROOT is None and ARCHIVES is None:self.skipTest('authentic fixture path supplied by CLI')
        item=c.pin()['continuation'];aid=str(item['identity']['artifact_id'])
        path=ARCHIVES/'boundary'/(aid+'.zip')if ARCHIVES else FIXTURE_ROOT/'vo-boundary-39386773719/vo-boundary.zip'
        self.assertEqual(c.stream_sha(path),item['identity']['zip_sha256'])
        with zipfile.ZipFile(path)as z:
            data=c.read_boundary(z);self.assertEqual(c.validate_boundary(data),item['objects'])
            class View:
                def __init__(self,extra=None,corrupt=None):self.extra=extra;self.corrupt=corrupt
                def infolist(self):return z.infolist()+([zipfile.ZipInfo(self.extra)]if self.extra else[])
                def read(self,n):return z.read(n)+(b'NON_KERNEL corrupt'if n==self.corrupt else b'')
            for name in ('../unsafe','/absolute','Unknown.lean',next(iter(item['files']))):
                with self.assertRaises(ValueError):c.read_boundary(View(extra=name))
            for name in (next(n for n in item['files']if n.endswith('.olean')),next(n for n in item['files']if n.endswith('.lean')),item['out']+'/generation.json'):
                with self.assertRaises(ValueError):c.read_boundary(View(corrupt=name))
        for field in ('compiler_binary_sha256','candidate','fresh_compiled_replayed','negative_actual_U_change'):
            bad=dict(data);a=json.loads(bad['VO_BOUNDARY_ACCEPTED.json']);a[field]=None;bad['VO_BOUNDARY_ACCEPTED.json']=json.dumps(a)
            with self.assertRaises((ValueError,TypeError)):c.validate_boundary(bad)
        bad=dict(data);steps=copy.deepcopy(item['steps']);steps[-1]['exit']=0;bad['steps.jsonl']='\n'.join(map(json.dumps,steps))
        with self.assertRaises(ValueError):c.validate_boundary(bad)
        label=next(iter(item['audits']));bad=dict(data);bad[label+'.out']='warning\n'+bad[label+'.out']
        with self.assertRaises(ValueError):c.validate_boundary(bad)
        api_path=ARCHIVES/'boundary'/(aid+'.json')if ARCHIVES else FIXTURE_ROOT/'vo-boundary-39386773719/artifact-api.json'
        api=json.loads(api_path.read_text())
        for key in ('id','expired','workflow_run'):
            bad=copy.deepcopy(api);bad[key]=None
            with self.assertRaises((ValueError,TypeError,AttributeError)):c.base.api_identity(bad,item['identity'])

    def test_actual40_storage_full_closure_fault_reasons_non_kernel(self):
        if ARCHIVES is None:self.skipTest('complete authentic40 view supplied by --archives')
        records=c.pin()['objects']
        with ExitStack()as stack:
            zs=[stack.enter_context(zipfile.ZipFile(c.archive_path(ARCHIVES,n,i)))for n,i in enumerate(c.identities())]
            c.previous.verify_canonical_storage(zs,records)
            record=next(r for r in records if r['module']=='Transformer.ExpFix');src=record['module'].replace('.','/')+'.lean';obj='.lake/build/lib/lean/'+record['module'].replace('.','/')+'.olean'
            class View:
                def __init__(self,z,missing=False,corrupt=False,overlap=False):self.z=z;self.missing=missing;self.corrupt=corrupt;self.overlap=overlap
                def namelist(self):return [n for n in self.z.namelist()if not(self.missing and n==obj)]+([src]if self.overlap else[])
                def read(self,n):
                    if self.overlap and n==src:return b'NON_KERNEL corrupt overlap'
                    return self.z.read(n)+(b'NON_KERNEL object corruption'if self.corrupt and n==obj else b'')
            for missing,reason in ((True,'^missing union object$'),(False,'^boundary physical canonical overlap$')):
                with self.assertRaisesRegex(ValueError,reason):c.previous.verify_canonical_storage([View(z,missing=missing,corrupt=not missing)for z in zs],records)
            with self.assertRaisesRegex(ValueError,'^union source/overlap identity: '+re.escape(src)+'$'):c.previous.verify_canonical_storage([View(zs[0],overlap=True)]+zs[1:],records)
            target=c.HERE/src;original=Path.read_bytes
            def corrupt(path):return b'NON_KERNEL corrupt repository source'if path==target else original(path)
            with patch.object(Path,'read_bytes',new=corrupt),self.assertRaisesRegex(ValueError,'^union source/overlap identity: '+re.escape(src)+'$'):c.previous.verify_canonical_storage(zs,records)
            original_exists=Path.exists
            def missing(path):return False if path==target else original_exists(path)
            with patch.object(Path,'exists',new=missing),self.assertRaisesRegex(ValueError,'^union source/overlap identity: '+re.escape(src)+'$'):c.previous.verify_canonical_storage(zs,records)

    def test_strict_audit_rejects_unknown_diagnostics_and_names_non_kernel(self):
        raw="'A' depends on axioms: [propext, Classical.choice, Quot.sound]\n";check=runner.common.check_correspondence_axioms
        for text,names in ((raw,['A','A']),(raw+raw,['A']),(raw+'garbage',['A']),(raw.replace('Quot.sound','Unknown'),['A']),('warning\n'+raw,['A']),(raw,['B'])):
            with self.assertRaises(ValueError):check(text,names)

    def test_mocked_support_first_and_negative_exit_gates_non_kernel(self):
        sel=g.selection();retained=c.pin();retained_modules=[r['module']for r in retained['objects']]
        self.assertEqual(len(retained_modules),362);self.assertEqual(len(retained['selected_names']),3956)
        for failure in (None,'first','negative'):
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
                def witness(selected):
                    self.assertEqual(selected,sel)
                    self.assertEqual(calls,[]);return {'selection':sel,'values':toy(sel),'l':0,'negative':{'field':'WO','coordinate':[0,0,0],'old':2,'new':3,'delta':1}}
                s.enter_context(patch.object(g,'production_witness',side_effect=witness))
                def audit(label,imports,names):
                    if label=='complete-VO-range':
                        self.assertEqual(calls,g.inventory(sel)[0])
                        self.assertEqual(imports,retained_modules+calls)
                        self.assertEqual(names,retained['selected_names']+[n for ns in g.inventory(sel)[1].values()for n in ns]);self.assertEqual(len(names),4649)
                    return len(names)
                s.enter_context(patch.object(runner.common,'audit',side_effect=audit))
                def compile(module):
                    calls.append(module)
                    if failure=='first'and module==g.prefix(sel)+'.Token001.First':raise ValueError('FAKE support compile/replay failure')
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
                    with self.assertRaises(ValueError):runner.main(None,sel)
                    self.assertFalse((out/'VO_RANGE_ACCEPTED.json').exists())
                else:
                    runner.main(None,sel);a=json.loads((out/'VO_RANGE_ACCEPTED.json').read_text());self.assertEqual(len(calls),61);self.assertEqual(a['scope']['covered_basis_groups'],4);self.assertFalse(a['scope']['full_basis']);self.assertEqual(a['generation']['declarations'],[n for names in g.inventory(sel)[1].values()for n in names])

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--archives',type=Path);p.add_argument('--fixture-root',type=Path);a=p.parse_args();ARCHIVES=a.archives;FIXTURE_ROOT=a.fixture_root
    if ARCHIVES:c.preflight(ARCHIVES)
    unittest.main(argv=[__file__],verbosity=2)
