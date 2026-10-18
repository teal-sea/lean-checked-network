#!/usr/bin/env python3
"""Source/toy/actual retained metadata controls only. KERNEL_NOT_RUN."""
import argparse
import copy
import json
import os
from pathlib import Path
import re
import tempfile
import unittest
from unittest.mock import patch
import zipfile
import rawcufull_restore as c
import rawcufull_generate as g
import rawcufull_runner as r

RANGES=[]
BASE=[]
ARCHIVE_CASES=[]


class CU(unittest.TestCase):
    def test_actual_projected_multi_archive_seam_and_corruption_reds(self):
        from contextlib import ExitStack
        import io
        class View:
            # Test-only read view: original whole-ZIP authentication is separately checked.
            def __init__(self,z,changed=None,extra=(),missing=()):
                self.z=z;self.filename=z.filename;self.changed=changed or {};self.extra=extra;self.missing=set(missing)
            def infolist(self):return [i for i in self.z.infolist() if i.filename not in self.missing]+[zipfile.ZipInfo(n)for n in self.extra]
            def namelist(self):return [i.filename for i in self.infolist()]
            def read(self,n):return self.changed.get(n,self.z.read(n))
            def getinfo(self,n):return self.z.getinfo(n)
        with ExitStack()as stack:
            identities=[i for _,i in ARCHIVE_CASES]
            zs=[stack.enter_context(zipfile.ZipFile(path))for path,_ in ARCHIVE_CASES]
            # Historical operation is the actual RED, retained without weakening its old use.
            with self.assertRaisesRegex(ValueError,'overlap mismatch: rawurange-out/U-range-scan.time'):
                c.previous.boundary.check_overlaps(zs)
            result=c.validate_projected_union(zs,identities,c.pin()['objects'])
            self.assertGreater(len(result['scoped_envelopes']),1500)
            ranges=c.range_lock();first=next(n for n,i in enumerate(identities)if i['artifact_id']==ranges[0]['artifact_id'])
            original=zs[first];item=identities[first]
            source=item['objects'][0]['module'].replace('.','/')+'.lean'
            obj='.lake/build/lib/lean/'+item['objects'][0]['module'].replace('.','/')+'.olean'
            for name in (source,obj,'RawURange-checkpoint.json','rawurange-out/generation.json'):
                bad=list(zs);bad[first]=View(original,{name:original.read(name)+b' corruption'})
                with self.subTest(name=name),self.assertRaises(ValueError):c.validate_projected_union(bad,identities,c.pin()['objects'])
            for name in ('../unsafe','/absolute','rawurange-out/U-range-scan.time','TransformerBridge/Unknown.lean',
                         '.lake/build/lib/lean/Unknown.olean','rawurange-out/unknown.time'):
                bad=list(zs);bad[first]=View(original,extra=[name])
                with self.subTest(name=name),self.assertRaises(ValueError):c.validate_projected_union(bad,identities,c.pin()['objects'])
            bad=list(zs);bad[first]=View(original,missing=['rawurange-out/U-range-scan.time'])
            with self.assertRaises(ValueError):c.validate_projected_union(bad,identities,c.pin()['objects'])
            for field,value in (('run',0),('artifact_id',0),('source_sha','wrong')):
                bad=copy.deepcopy(identities);bad[first][field]=value
                with self.assertRaises(ValueError):c.validate_projected_union(zs,bad,c.pin()['objects'])
            with self.assertRaises(ValueError):c.validate_projected_union(zs[:-1],identities[:-1],c.pin()['objects'])
            with self.assertRaises(ValueError):c.validate_projected_union(zs+[original],identities+[item],c.pin()['objects'])
            with patch.object(c,'stream_sha',return_value='bad'),self.assertRaises(ValueError):
                c.validate_projected_union(zs,identities,c.pin()['objects'])

    def test_actual_all32_range_metadata_and_coverage(self):
        items=c.range_lock();self.assertEqual(len(items),32);self.assertEqual(len(c.pin()['objects']),294)
        self.assertEqual(len(c.selected_names()),3097)
        packed,ci,row0,row127=BASE
        records,source,_=c.previous.base.old.validate_metadata(packed,json.loads(c.previous.base.old.PIN_PATH.read_text()))
        c.previous.base.verify_sources(source)
        self.assertEqual(len(records+c.previous.base.validate_ci(ci)+c.previous.boundary.validate_row0(row0)+c.previous.validate_row127(row127)),230)
        for item,data in RANGES:self.assertEqual(c.validate_range(data,item),item['objects'])
        for bad in (items[:-1],items+[items[-1]],list(reversed(items)),[items[0]]*32):
            with self.assertRaises(ValueError):c.validate_lock(bad)
        for key,value in [('run',39109225616),('source_sha','wrong'),('U_rows',[1,3,4,5]),('objects',[])]:
            bad=copy.deepcopy(items);bad[0][key]=value
            with self.assertRaises(ValueError):c.validate_lock(bad)
        for item,data in (RANGES[0],RANGES[-1]):
            for name,value in [('replayed.jsonl',''),('negative-actual-U-range-change.out','syntax error'),('complete-U-range-axioms.out',data['complete-U-range-axioms.out']+'warning: extra\n')]:
                bad=dict(data);bad[name]=value
                with self.assertRaises(ValueError):c.validate_range(bad,item)
            steps=[json.loads(s)for s in data['steps.jsonl'].splitlines()]
            for code in (0,124):
                bad=copy.deepcopy(steps);bad[-1]['exit']=code;d=dict(data);d['steps.jsonl']='\n'.join(json.dumps(s)for s in bad)
                with self.assertRaises(ValueError):c.validate_range(d,item)

    def test_symbolic_assembly_and_all_CU_source_templates_non_kernel(self):
        items=c.range_lock();text=g.assembly(items)
        self.assertEqual(len(re.findall(r'^import ',text,re.M)),34)
        self.assertEqual(len(re.findall(r'^theorem KU_le_',text,re.M)),128)
        self.assertEqual(len(re.findall(r'^  · exact .*\.1$',text,re.M)),128)
        self.assertIn('theorem urows_eq (d : Fin 128)',text);self.assertIn('theorem urows_bound (d : Fin 128) (k : Fin 113)',text)
        self.assertNotIn('revert d\n  decide +kernel',text)
        sources,neg=g.numeric_sources(7,3,2) # Toy source only, no learned coefficient evaluation.
        self.assertIn('weights.bout i + if i = 3 then 1 else 0',sources[g.PREFIX+'.Control'])
        self.assertIn('weights.U 3 2 ≠ 0',sources[g.PREFIX+'.Control'])
        self.assertIn('by rfl',sources[g.PREFIX+'.Control'])
        self.assertIn('fun _ : Fin 1',sources[g.PREFIX+'.Representative'])
        self.assertIn('target_bound',sources[g.PREFIX+'.PackedCU']);self.assertIn('2 * (128 * Kinput * KU)',sources[g.PREFIX+'.PackedCU'])
        self.assertIn('contract cuInput packedURows = pack frozenCU',sources[g.PREFIX+'.PackedCU'])
        self.assertIn('(TransformerBridge.toTables TransformerCore.Net.tab).CU = (weights.rawTables 256).CU',sources[g.PREFIX+'.CU'])
        self.assertIn('decide +kernel',neg);self.assertIn('CU 2 = frozenCU 2',neg)
        for name,text in {g.PREFIX+'.UAll':text,**sources}.items():
            found=re.findall(r'^(?:def|theorem) (\w+)',text,re.M)
            self.assertEqual(found,g.DECLARATIONS[name.rsplit('.',1)[1]])
        with patch.dict(os.environ,{},clear=True),self.assertRaises(ValueError):g.production_witness()
        for bad in ('[1, 2]','[(.ofNat 1), arbitrary]','[(.ofNat 1)]'):
            with self.assertRaises(ValueError):g.literal_vector('def x : List Int := '+bad+'\n','x',2)
        self.assertEqual(g.literal_vector('def x : List Int := [(.ofNat 1), (.negSucc 2)]\n','x',2),[1,-3])

    def test_layered_source_policy_and_audit_drift(self):
        workflow=(c.ROOT/'.github/workflows/transformer.yml').read_text()
        self.assertEqual(c.digest(c.inverse_workflow(workflow).encode()),c.previous.pin()['workflow_projection']['current_sha256'])
        with self.assertRaises(ValueError):c.inverse_workflow(workflow+'# drift\n')
        for path,rule in c.pin()['nonproof_projections'].items():
            raw=(c.ROOT/path).read_bytes();self.assertEqual(c.digest(c.project_current(path,raw)),rule['accepted_sha256'])
            with self.assertRaises(ValueError):c.project_current(path,raw+b' ')
        policy=json.loads((c.HERE/'input_policy.json').read_text())
        for path,value in policy['sources'].items():self.assertEqual(c.sha(c.HERE/path),value)
        good="'Mock.a' depends on axioms: [propext,\n Classical.choice, Quot.sound]\n"
        self.assertEqual(c.check_correspondence_axioms(good,['Mock.a']),1)
        for bad in ('',good+'garbage',good.replace('propext','sorryAx'),'warning: bad\n'+good,good*2):
            with self.assertRaises(ValueError):c.check_correspondence_axioms(bad,['Mock.a'])
        with patch.object(c,'cloud_only'),patch.object(c,'sha',return_value='bad'),self.assertRaises(ValueError):c.restore(Path('/no-archive'),{})

    def test_mocked_staged_orchestrator_non_kernel(self):
        actual_pin=c.pin()
        for fail in (None,'helper','assembly','Representative','PackedCU','negative'):
            with self.subTest(fail=fail),tempfile.TemporaryDirectory()as tmp,patch.dict(os.environ,{'GITHUB_REPOSITORY':'teal-sea/lean-checked-network','LEAN_NUM_THREADS':'2'}):
                from contextlib import ExitStack
                with ExitStack()as s:
                    here=Path(tmp);out=here/'out';s.enter_context(patch.object(r,'HERE',here));s.enter_context(patch.object(r,'OUT',out));s.enter_context(patch.object(r,'cloud_only'));s.enter_context(patch.object(r,'snapshot',return_value={}))
                    s.enter_context(patch.object(c,'restore',return_value={'objects':[],'selected_names':[]}));s.enter_context(patch.object(c,'PIN_PATH',here/'pin'));(here/'pin').write_text('FAKE')
                    for n in ('lean','lake','leanchecker'):
                        p=here/'bin'/n;p.parent.mkdir(exist_ok=True);p.write_bytes(b'FAKE compiler never executed')
                    s.enter_context(patch.object(c,'pin',return_value={**actual_pin,'compiler_binary_sha256':{n:c.sha(here/'bin'/n)for n in ('lean','lake','leanchecker')}}))
                    s.enter_context(patch.object(g,'write_sources'));called=[]
                    def witness():
                        self.assertEqual(called[:2],[g.HELPER,g.PREFIX+'.UAll']);return {'Kinput':7,'d':3,'k':2}
                    s.enter_context(patch.object(g,'production_witness',side_effect=witness))
                    def compile(module):
                        if (fail=='helper'and module==g.HELPER)or(fail=='assembly'and module.endswith('UAll'))or(fail and module.endswith('.'+fail)):raise ValueError('FAKE compile/replay failure')
                        called.append(module);stem=module.replace('.','/');p=here/(stem+'.lean');p.parent.mkdir(parents=True,exist_ok=True);p.write_text('FAKE source')
                        obj=here/'.lake/build/lib/lean'/(stem+'.olean');obj.parent.mkdir(parents=True,exist_ok=True);obj.write_bytes(b'FAKE object')
                        row={'module':module,'source_sha256':c.sha(p),'olean_sha256':c.sha(obj)}
                        for file in ('compiled.jsonl','replayed.jsonl'):
                            with(out/file).open('a')as f:f.write(json.dumps(row)+'\n')
                        for phase in ('fresh_compile_','fresh_replay_'):
                            label=phase+module;r.common.runner.STEPS[label]={'seconds':.01};(out/(label+'.time')).write_text('Maximum resident set size (kbytes): 12\n')
                        return row
                    s.enter_context(patch.object(r.common,'fresh_compile',side_effect=compile));s.enter_context(patch.object(r.common,'check_declarations'));s.enter_context(patch.object(r.common,'audit',side_effect=lambda label,imports,names:len(names)))
                    def run(label,args,seconds=60,negative=False):
                        if label=='compiler-version':return 'version 4.35.0 commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc'
                        if label=='compiler-prefix':return str(here)
                        if fail=='negative'and negative:raise ValueError('FAKE negative exit0/syntax/timeout')
                        return ''
                    s.enter_context(patch.object(r.common.runner,'run',side_effect=run))
                    if fail is None:
                        r.main(None);self.assertTrue(json.loads((out/'CU113_ACCEPTED.json').read_text())['CU_field'])
                    else:
                        with self.assertRaises(ValueError):r.main(None)
                        self.assertFalse((out/'CU113_ACCEPTED.json').exists())


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--archives',type=Path);p.add_argument('--fixture-root',type=Path);p.add_argument('--metadata-dir',type=Path);args=p.parse_args();items=c.range_lock();locks=c.base_locks()
    def path(item,index=None):
        if args.archives:return args.archives/(str(item['artifact_id'])+'.zip')
        if index==0:return None
        if index==1:return args.fixture_root/('ci-'+str(item['source_run']))/'ci.zip'
        if index==2:return args.fixture_root/('u-row0-'+str(item['source_run']))/'u-row0.zip'
        if index==3:return args.fixture_root/('u-row127-'+str(item['source_run']))/'u-row127.zip'
        return args.fixture_root/('u-range-'+str(item['run']))/'u-range.zip'
    if args.archives:
        ARCHIVE_CASES.append((path(locks[0],0),locks[0]))
        with zipfile.ZipFile(path(locks[0],0))as z:packed=c.previous.base.old.read_metadata(z,locks[0])
    else:
        packed={}
        for name,value in locks[0]['metadata_sha256'].items():
            raw=(args.metadata_dir/Path(name).name).read_bytes();c.require(c.digest(raw)==value,'actual packed metadata');packed[Path(name).name]=raw.decode()
    BASE.append(packed)
    for index,reader in [(1,c.previous.base.read_ci),(2,c.previous.boundary.read_row0),(3,c.previous.read_row127)]:
        f=path(locks[index],index);ARCHIVE_CASES.append((f,locks[index]));c.require(c.stream_sha(f)==locks[index]['zip_sha256'],'actual base ZIP')
        with zipfile.ZipFile(f)as z:BASE.append(reader(z))
    for item in items:
        f=path(item);ARCHIVE_CASES.append((f,item));c.require(c.stream_sha(f)==item['zip_sha256'],'actual range ZIP')
        with zipfile.ZipFile(f)as z:RANGES.append((item,c.read_range(z,item)))
    unittest.main(argv=[__file__],verbosity=2)
