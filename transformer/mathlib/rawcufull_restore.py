"""Closed accepted U128 artifact union for CU; no mathematical acceptance from labels."""
from contextlib import ExitStack
import json
from pathlib import Path
import re
import zipfile
import rawurange_restore as previous
import rawurange_generate as batches
from rawpilot_data import HERE,ROOT,sha
from rawpilot_generate import cloud_only
from rawcorrespondence_runner import check_correspondence_axioms

PIN_PATH=HERE/'RawCUFull-checkpoint.json'
require=previous.require
digest=previous.digest
stream_sha=previous.stream_sha


def pin():return json.loads(PIN_PATH.read_text())


def inverse_workflow(text):
    rule=pin()['workflow_projection'];require(digest(text.encode())==rule['current_sha256'],'unknown CU workflow drift')
    for fragment in rule['insertions']:
        require(text.count(fragment)==1,'CU inverse occurrence');text=text.replace(fragment,'',1)
    require(text.count(rule['exclusion'])==3,'CU exclusion count');text=text.replace(rule['exclusion'],'')
    require(digest(text.encode())==rule['accepted_sha256'],'CU accepted workflow differs');return text


def project_current(path,data):
    rule=pin()['nonproof_projections'].get(path)
    if rule is None:return data
    require(digest(data)==rule['current_sha256'],'unknown CU source drift: '+path)
    for e in rule['edits']:
        a,b=e['current'].encode(),e['accepted'].encode();require(data.count(a)==1,'CU source inverse count');data=data.replace(a,b,1)
    require(digest(data)==rule['accepted_sha256'],'CU source inverse identity');return data


def verify_candidate(candidate,expected):
    require(candidate==expected,'range candidate inventory differs')
    for rel,value in candidate.items():
        path=(HERE/rel).resolve();data=path.read_bytes()
        if path==ROOT/'.github/workflows/transformer.yml':data=inverse_workflow(data.decode()).encode()
        else:data=project_current(str(path.relative_to(ROOT)),data)
        require(digest(data)==value,'range candidate source drift: '+rel)


def validate_lock(lock):
    require(type(lock) is list and len(lock)==32,'exact32 range archives required')
    rows=[];ids=[];runs=[];modules=[]
    for item in lock:
        require(set(item)=={'run','source_sha','U_rows','artifact_id','zip_sha256','api_sha256','objects'},'range lock schema')
        r=item['U_rows'];require(type(r) is list and r and all(type(x)is int for x in r),'range rows type')
        require(r==batches.rows_for(r[0],len(r)),'range rows/order')
        expected=batches.inventory(r[0],len(r))[0]
        require([x['module'] for x in item['objects']]==expected,'range object modules')
        require(type(item['run'])is int and type(item['artifact_id'])is int and item['source_sha']==pin()['source_sha'],'range producer identity')
        require(all(re.fullmatch('[0-9a-f]{64}',item[k]) for k in ('zip_sha256','api_sha256')),'range hash schema')
        rows+=r;ids.append(item['artifact_id']);runs.append(item['run']);modules+=expected
    require(rows==list(range(1,127)) and len(set(ids))==32 and len(set(runs))==32 and len(set(modules))==64,'range exact coverage/duplicates')
    require(39109225616 not in runs and 39109387180 in runs,'failed run/retry identity')
    return lock


def range_lock():
    p=pin();require(digest(p['range_lock_text'].encode())==p['range_lock_sha256'],'range lock bytes')
    return validate_lock(json.loads(p['range_lock_text']))


def base_locks():
    return [json.loads(previous.base.old.PIN_PATH.read_text()),previous.base.pin()['ci'],previous.boundary.pin()['row0'],previous.pin()['row127']]


def read_range(z,item):
    previous.base.old.archive_index(z);result={}
    rule=pin()['range_metadata'][str(item['run'])]
    for name,value in rule['hashes'].items():
        require(z.getinfo(name).file_size<1_000_000,'oversized range metadata');raw=z.read(name)
        require(digest(raw)==value,'range metadata hash');result[Path(name).name]=raw.decode()
    return result


def validate_range(data,item):
    load=lambda n:json.loads(data[n]);rows=item['U_rows'];start=rows[0];count=len(rows)
    modules,row_names,control_names=batches.inventory(start,count)
    records=[json.loads(s) for s in data['compiled.jsonl'].splitlines()]
    require(records==item['objects'] and data['compiled.jsonl']==data['replayed.jsonl'],'range compiled/replayed identities')
    accepted=load('U_RANGE_ACCEPTED.json');generation=load('generation.json')
    require(accepted['kernel_verdict']=='KERNEL_ACCEPTED' and accepted['scope']==batches.scope(start,count) and
        accepted['fresh_compiled_replayed']==records and accepted['negative_actual_U_range_change']=='KERNEL_DECIDE_FALSE_EXIT_1' and
        accepted['compiler_binary_sha256']==pin()['compiler_binary_sha256'] and accepted['checkpoint_sha256']==sha(previous.PIN_PATH) and
        accepted['fanout']=='NOT_AUTHORIZED','range acceptance/compiler/checkpoint')
    require(generation==accepted['generation'] and generation['scope']==batches.scope(start,count) and generation['modules']==modules and
        generation['declarations']==row_names+control_names and generation['outputs']=={r['module'].replace('.','/')+'.lean':r['source_sha256'] for r in records},'range generation/source')
    prefix=pin()['base_objects'];require(accepted['restored_objects']==load('restored-union.json')['objects']==prefix,'range230 prefix')
    require(load('restored-union.json')['archive_sha256']==[x['zip_sha256'] for x in base_locks()],'range earlier ZIP chain')
    verify_candidate(accepted['candidate'],pin()['range_metadata'][str(item['run'])]['candidate'])
    expected=previous.boundary.historical_names()+previous.boundary.row0.NAMES+previous.row127.NAMES+row_names+control_names
    require(accepted['exact_production_audit_names']==len(expected),'range actual audit count')
    for label,names in [('batch',row_names),('control',control_names),('complete-U-range',expected)]:
        require(load(label+'-axioms.expected.json')==names and check_correspondence_axioms(data[label+'-axioms.out'],names)==len(names),'range strict complete audit')
    _,negative=batches.batch_sources(start,count,{r:[0]*113 for r in rows})
    neg=generation['negative'];require(neg['field']=='U' and neg['coordinate']==[start,0] and type(neg['old'])is int and
        neg['new']==neg['old']+1 and neg['delta']==1 and data['changed-U-range.lean']==negative and digest(negative.encode())==neg['negative_sha256'],'range real changed-U control')
    steps=[json.loads(s) for s in data['steps.jsonl'].splitlines()];require(len({s['name'] for s in steps})==len(steps),'duplicate range process')
    def step(name):
        found=[s for s in steps if s['name']==name];require(len(found)==1,'missing range process');return found[0]
    for module in modules:
        stem=module.replace('.','/');s=step('fresh_compile_'+module);cmd=s['command']
        require(s['exit']==0 and len(cmd)==6 and cmd[:4]==['lake','env','lean','-o'] and cmd[4].endswith('/.lake/build/lib/lean/'+stem+'.olean') and cmd[5]==stem+'.lean','range compile producer')
        s=step('fresh_replay_'+module);require(s['exit']==0 and s['command']==['lake','env','leanchecker',module],'range replay producer')
    for label in ('batch-axioms','control-axioms','complete-U-range-axioms','negative-actual-U-range-change'):
        s=step(label);cmd=s['command'];negproc=label.startswith('negative');file='changed-U-range.lean' if negproc else label+'.lean'
        require(len(cmd)==4 and cmd[:3]==['lake','env','lean'] and cmd[3].endswith('/rawurange-out/'+file) and s['exit']==(1 if negproc else 0),'range audit/control producer')
    require(re.search(r'decide[\s\S]*false',data['negative-actual-U-range-change.out'])is not None,'range negative diagnostic')
    return records


def selected_names():
    names=previous.boundary.historical_names()+previous.boundary.row0.NAMES+previous.row127.NAMES
    for item in range_lock():
        _,a,b=batches.inventory(item['U_rows'][0],len(item['U_rows']));names+=a+b
    require(len(names)==len(set(names)),'duplicate selected declaration');return names


def restore(folder,binaries):
    cloud_only();folder=Path(folder);lock=pin();items=range_lock();identities=base_locks()+items
    require({n:sha(p) for n,p in binaries.items()}==lock['compiler_binary_sha256'] and sha(HERE/'lean-toolchain')==lock['toolchain_sha256'] and sha(HERE/'lake-manifest.json')==lock['lake_manifest_sha256'],'CU compiler/toolchain drift')
    for name,value in lock['earlier_checkpoint_sha256'].items():require(sha(HERE/name)==value,'earlier immutable lock changed')
    for identity in identities:
        aid=str(identity['artifact_id']);require(stream_sha(folder/(aid+'.zip'))==identity['zip_sha256'],'CU archive digest')
        previous.base.api_identity(json.loads((folder/(aid+'.json')).read_text()),{**identity,'source_run':identity.get('source_run',identity.get('run'))})
    for project in ('Transformer','TransformerCore','TransformerBridge'):
        path=HERE/'.lake/build/lib/lean'/project;require(not list(path.rglob('*.olean')) and not path.with_suffix('.olean').exists(),'preexisting CU proof objects')
    with ExitStack() as stack:
        archives=[stack.enter_context(zipfile.ZipFile(folder/(str(i['artifact_id'])+'.zip'))) for i in identities]
        for z in archives:previous.base.old.archive_index(z)
        a,b,c,d=archives[:4];packed,source,_=previous.base.old.validate_metadata(previous.base.old.read_metadata(a,identities[0]),identities[0]);previous.base.verify_sources(source)
        base=packed+previous.base.validate_ci(previous.base.read_ci(b))+previous.boundary.validate_row0(previous.boundary.read_row0(c))+previous.validate_row127(previous.read_row127(d))
        require(base==lock['base_objects'],'CU base230 identity')
        fresh=[]
        for z,item in zip(archives[4:],items):fresh+=validate_range(read_range(z,item),item)
        records=base+fresh;require(records==lock['objects'] and len({r['module'] for r in records})==len(records),'CU closed object union')
        previous.boundary.check_overlaps(archives);previous.base.verify_union_sources(archives,records)
        for r in records:
            stem=r['module'].replace('.','/');rel=stem+'.lean';zs=[z for z in archives if rel in z.namelist()]
            if zs:previous.base.old.write_exact(HERE/rel,zs[0].read(rel))
            obj='.lake/build/lib/lean/'+stem+'.olean';zs=[z for z in archives if obj in z.namelist()];require(zs,'missing CU union object')
            previous.base.restore_object(zs[0],obj,HERE/obj,r['olean_sha256'])
    return {'status':'RESTORED_EXACT_U128_CERTIFICATE_UNION','objects':records,'selected_names':selected_names(),'range_lock_sha256':lock['range_lock_sha256']}


if __name__=='__main__':
    import argparse
    p=argparse.ArgumentParser();p.add_argument('--artifact-ids',action='store_true');args=p.parse_args()
    if args.artifact_ids:
        for item in base_locks()+range_lock():print(item['artifact_id'])
