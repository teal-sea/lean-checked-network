"""Exact167-archive G assembly continuation, with a separate strict39 prior folder."""
from contextlib import ExitStack
import json,re,zipfile
from pathlib import Path
import rawgrange_restore as previous
import rawgrange_generate as ranges
from rawpilot_data import HERE,ROOT,sha
from rawpilot_generate import cloud_only
from rawcorrespondence_runner import check_correspondence_axioms
require=previous.require
digest=previous.digest
stream_sha=previous.stream_sha
PIN_PATH=HERE/'RawGFull-checkpoint.json'
def pin():return json.loads(PIN_PATH.read_text())
def inverse_workflow(text):
    from rawtupilot_restore import inverse_workflow as tu_inverse
    text=tu_inverse(text)
    rule=pin()['workflow_projection'];require(digest(text.encode())==rule['current_sha256'],'unknown full G workflow drift')
    for fragment in rule['insertions']:
        require(text.count(fragment)==1,'full G workflow inverse count');text=text.replace(fragment,'',1)
    require(text.count(rule['exclusion'])==3,'full G exclusion count');text=text.replace(rule['exclusion'],'')
    require(digest(text.encode())==rule['accepted_sha256'],'full G workflow accepted identity');return text

def project_current(path,data):
    from rawtupilot_restore import project_current as tu_project
    data=tu_project(path,data)
    rule=pin()['nonproof_projections'].get(path)
    if rule is None:return data
    require(digest(data)==rule['current_sha256'],'unknown full G source drift: '+path)
    for edit in rule['edits']:
        a,b=edit['current'].encode(),edit['accepted'].encode();require(data.count(a)==1,'full G inverse occurrence');data=data.replace(a,b,1)
    require(digest(data)==rule['accepted_sha256'],'full G source inverse identity');return data

def verify_candidate(candidate):
    require(candidate==pin()['range_candidate'],'full G archived candidate inventory')
    for rel,value in candidate.items():
        path=(HERE/rel).resolve();data=path.read_bytes()
        data=inverse_workflow(data.decode()).encode()if path==ROOT/'.github/workflows/transformer.yml'else project_current(str(path.relative_to(ROOT)),data)
        require(digest(data)==value,'full G archived source map drift: '+rel)

def validate_lock(items):
    require(type(items)is list and len(items)==128 and items==json.loads(pin()['range_lock_text']),'G exact128 pinned range lock')
    rows=[];ids=[];runs=[];modules=[]
    for item in items:
        require(set(item)=={'run','source_sha','G_rows','artifact_id','zip_sha256','api_sha256','objects'},'G range lock schema')
        selected=item['G_rows'];require(type(selected)is list and selected and all(type(r)is int for r in selected)and selected==ranges.rows_for(selected[0],len(selected)),'G range rows/gaps/order')
        require(item['source_sha']==pin()['range_source_sha']and type(item['run'])is int and type(item['artifact_id'])is int,'G range producer identity')
        require(all(re.fullmatch('[0-9a-f]{64}',item[k])for k in ('zip_sha256','api_sha256')),'G range lock hashes')
        expected=ranges.inventory(selected[0],len(selected))[0];require([r['module']for r in item['objects']]==expected,'G range object modules')
        rows+=selected;ids.append(item['artifact_id']);runs.append(item['run']);modules+=expected
    require(rows==list(range(1,511))and len(set(ids))==len(set(runs))==128 and len(set(modules))==256,'G full exact coverage/duplicates')
    return items

def range_lock():
    p=pin();require(digest(p['range_lock_text'].encode())==p['range_lock_sha256'],'G range lock bytes');return validate_lock(json.loads(p['range_lock_text']))
def identities():return previous.identities()+range_lock()
def archive_groups():return [('prior',i)for i in previous.identities()]+[('ranges',i)for i in range_lock()]
def read_range(z,item):
    previous.previous.previous.previous.base.old.archive_index(z);files=pin()['range_files'][str(item['run'])]
    require({i.filename for i in z.infolist()if not i.filename.endswith('/')}==set(files),'G range physical inventory')
    for name,value in files.items():require(digest(z.read(name))==value,'G range source/object/scoped envelope drift: '+name)
    return {Path(n).name:z.read(n).decode()for n in files if n.startswith('rawgrange-out/')and n.endswith(('.json','.jsonl','.out','.lean','.time'))}

def validate_range(data,item):
    load=lambda n:json.loads(data[n]);rows=item['G_rows'];start=rows[0];count=len(rows);modules,names,controls=ranges.inventory(start,count);a=load('G_RANGE_ACCEPTED.json');generation=load('generation.json')
    require(a['fanout']=='NOT_AUTHORIZED'and a['kernel_verdict']=='KERNEL_ACCEPTED'and a['scope']==ranges.scope(start,count)and a['fresh_compiled_replayed']==item['objects']and a['restored_objects']==previous.pin()['objects'],'G range accepted scope/objects')
    compiler=previous.previous.previous.pin()['compiler_binary_sha256']
    require(a['compiler_binary_sha256']==compiler and a['checkpoint_sha256']==sha(previous.PIN_PATH)and a['negative_actual_Wout_range_change']=='KERNEL_DECIDE_FALSE_EXIT_1'and a['exact_production_audit_names']==len(previous.pin()['selected_names'])+len(names+controls),'G range compiler/control/audit')
    require(data['compiled.jsonl']==data['replayed.jsonl']and[json.loads(s)for s in data['compiled.jsonl'].splitlines()]==item['objects'],'G range compile/replay identities')
    require(a['generation']==generation and generation['scope']==ranges.scope(start,count)and generation['modules']==modules and generation['declarations']==names+controls and generation['outputs']=={r['module'].replace('.','/')+'.lean':r['source_sha256']for r in item['objects']},'G range exact generation')
    require(load('restored-union.json')=={'objects':previous.pin()['objects'],'selected_names':previous.pin()['selected_names'],'archive_sha256':[i['zip_sha256']for i in previous.identities()]},'G range311 prefix')
    verify_candidate(a['candidate'])
    for label,expected in [('batch-axioms',names),('control-axioms',controls),('complete-G-range-axioms',previous.pin()['selected_names']+names+controls)]:
        require(load(label+'.expected.json')==expected and check_correspondence_axioms(data[label+'.out'],expected)==len(expected),'G range strict complete audit')
        require(re.findall(r'^#print axioms (\S+)$',data[label+'.lean'],re.M)==expected,'G range audit source')
    steps=[json.loads(s)for s in data['steps.jsonl'].splitlines()];expected=['compiler-version','compiler-prefix']
    for module,label in zip(modules,('batch','control')):expected +=[label+'-scan','fresh_compile_'+module,'fresh_replay_'+module,label+'-axioms']
    expected+=['negative-scan','complete-G-range-axioms','negative-actual-Wout-range-change'];require([s['name']for s in steps]==expected,'G range producers/order')
    for step in steps:require(step['exit']==(1 if step['name']=='negative-actual-Wout-range-change'else 0),'G range process exit')
    byname={s['name']:s for s in steps}
    for module,label in zip(modules,('batch','control')):
        stem=module.replace('.','/');s=byname['fresh_compile_'+module];cmd=s['command'];require(len(cmd)==6 and cmd[:4]==['lake','env','lean','-o']and cmd[4].endswith('/.lake/build/lib/lean/'+stem+'.olean')and cmd[5]==stem+'.lean','G range compile command')
        require(byname['fresh_replay_'+module]['command']==['lake','env','leanchecker',module]and byname[label+'-scan']['command']==['../lean/scan_sources.sh',stem+'.lean'],'G range replay/scan producer')
        for phase in ('fresh_compile_','fresh_replay_'):
            require(not re.search(r'(?im)^.*\b(?:warning|error):',data[phase+module+'.out'])and'Exit status: 0'in data[phase+module+'.time'],'G range positive diagnostics')
    for label in ('batch-axioms','control-axioms','complete-G-range-axioms','negative-actual-Wout-range-change'):
        cmd=byname[label]['command'];filename='changed-Wout-range.lean'if label.startswith('negative')else label+'.lean'
        require(len(cmd)==4 and cmd[:3]==['lake','env','lean']and cmd[3].endswith('/rawgrange-out/'+filename),'G range audit/negative command')
    negative=generation['witness']['negative'];require(negative['field']=='Wout'and negative['coordinate']==[start,0]and type(negative['old'])is int and negative['new']==negative['old']+1 and negative['delta']==1 and negative['nonzero_U_coordinate']==[0,0]and negative['output']==[start,0],'G range learned perturbation')
    require(digest(data['changed-Wout-range.lean'].encode())==generation['negative_sha256']and re.search(r'decide[\s\S]*false',data['negative-actual-Wout-range-change.out'])is not None,'G range genuine false diagnostic')
    return item['objects']

def validate_range_union(archives,items):
    require(len(archives)==len(items)==128,'G exact128 range union')
    base=previous.previous.previous.previous.base;allowed={r['module']for r in pin()['objects']};seen={}
    for z,item in zip(archives,items):
        require(digest(z.read('RawGRange-checkpoint.json'))==sha(previous.PIN_PATH),'G range shared checkpoint overlap')
        for record in item['objects']:
            stem=record['module'].replace('.','/');source=z.read(stem+'.lean');base.check_imports(source,allowed)
            require(digest(source)==record['source_sha256'],'G range union source overlap')
            obj='.lake/build/lib/lean/'+stem+'.olean';require(digest(z.read(obj))==record['olean_sha256'],'G range union object overlap')
            require(record['module']not in seen,'G duplicate union module');seen[record['module']]=record
    require(list(seen.values())==[r for i in items for r in i['objects']],'G exact range union')

def validate_union(archives,records):
    base=previous.previous.previous.previous.base
    base.verify_union_sources(archives,records)
    canonical={'RawGRange-checkpoint.json':sha(previous.PIN_PATH)}
    full=previous.previous.previous
    canonical.update(full.pin()['earlier_checkpoint_sha256']);canonical.update({'RawCUFull-checkpoint.json':sha(full.PIN_PATH),'RawGPilot-checkpoint.json':sha(previous.previous.PIN_PATH)})
    for r in records:
        stem=r['module'].replace('.','/');canonical[stem+'.lean']=r['source_sha256'];canonical['.lake/build/lib/lean/'+stem+'.olean']=r['olean_sha256']
    indexes=[set(z.namelist())for z in archives]
    for name,value in canonical.items():
        found=[z for z,index in zip(archives,indexes)if name in index]
        if name.endswith('.olean'):require(found,'G full missing proof object')
        for z in found:require(digest(z.read(name))==value,'G full canonical overlap/hash: '+name)

def preflight(folder):
    folder=Path(folder);items=range_lock();records=previous.preflight(folder/'prior') # EXACT39 invariant unchanged.
    require({p.name for p in (folder/'ranges').glob('*.zip')}=={str(i['artifact_id'])+'.zip'for i in items},'G full exact128 range ZIPs')
    base=previous.previous.previous.previous.base
    for item in items:
        stem=folder/'ranges'/str(item['artifact_id']);require(stream_sha(stem.with_suffix('.zip'))==item['zip_sha256'],'G full range ZIP identity')
        api=json.loads(stem.with_suffix('.json').read_text());base.api_identity(api,{**item,'source_run':item['run']})
        require(api['name']=='transformer-raw-g-range-'+str(item['run'])and api['digest']=='sha256:'+item['zip_sha256']and api['size_in_bytes']==stem.with_suffix('.zip').stat().st_size,'G full API bytes/name')
    with ExitStack()as stack:
        archives=[stack.enter_context(zipfile.ZipFile(folder/group/(str(i['artifact_id'])+'.zip')))for group,i in archive_groups()]
        for z,item in zip(archives[39:],items):records+=validate_range(read_range(z,item),item)
        require(records==pin()['objects']and len({r['module']for r in records})==567,'G full exact567 union')
        validate_range_union(archives[39:],items)
        validate_union(archives,records)
    return records

def restore(folder,binaries):
    cloud_only();folder=Path(folder);require(sha(previous.PIN_PATH)==pin()['previous_checkpoint_sha256'],'G range immutable lock')
    records=preflight(folder) # Full167 preflight before any proof/source writes.
    result=previous.restore(folder/'prior',binaries) # Never pass the128 new ZIPs into strict39.
    base=previous.previous.previous.previous.base
    for item in range_lock():
        with zipfile.ZipFile(folder/'ranges'/(str(item['artifact_id'])+'.zip'))as z:
            for r in item['objects']:
                stem=r['module'].replace('.','/');rel=stem+'.lean';base.old.write_exact(HERE/rel,z.read(rel));obj='.lake/build/lib/lean/'+stem+'.olean';base.restore_object(z,obj,HERE/obj,r['olean_sha256'])
    require(result['objects']+[r for i in range_lock()for r in i['objects']]==records,'G full restored567 identity')
    return {'objects':records,'selected_names':pin()['selected_names'],'archive_sha256':[i['zip_sha256']for i in identities()]}

if __name__=='__main__':
    import argparse
    p=argparse.ArgumentParser();p.add_argument('--artifact-map',action='store_true');a=p.parse_args()
    if a.artifact_map:
        for group,item in archive_groups():print(group,item['artifact_id'])
