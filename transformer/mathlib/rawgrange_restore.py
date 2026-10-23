"""Authenticate39 accepted archives; restore311 objects without rebuilding."""
from contextlib import ExitStack
import json,zipfile
from pathlib import Path
import rawgpilot_restore as previous
from rawpilot_data import HERE,ROOT,sha
from rawpilot_generate import cloud_only
from rawcorrespondence_runner import check_correspondence_axioms
require=previous.require
digest=previous.digest
stream_sha=previous.stream_sha
PIN_PATH=HERE/'RawGRange-checkpoint.json'
def pin():return json.loads(PIN_PATH.read_text())
def inverse_workflow(text):
    from rawgfull_restore import inverse_workflow as full_inverse
    text=full_inverse(text)
    rule=pin()['workflow_projection'];require(digest(text.encode())==rule['current_sha256'],'unknown G range workflow drift')
    for fragment in rule['insertions']:
        require(text.count(fragment)==1,'G range inverse occurrence');text=text.replace(fragment,'',1)
    require(text.count(rule['exclusion'])==3,'G range exclusion count');text=text.replace(rule['exclusion'],'')
    require(digest(text.encode())==rule['accepted_sha256'],'G range workflow accepted identity');return text

def project_current(path,data):
    from rawgfull_restore import project_current as full_project
    data=full_project(path,data)
    rule=pin()['nonproof_projections'].get(path)
    if rule is None:return data
    require(digest(data)==rule['current_sha256'],'unknown G range source drift: '+path)
    for edit in rule['edits']:
        a,b=edit['current'].encode(),edit['accepted'].encode();require(data.count(a)==1,'G range source inverse count');data=data.replace(a,b,1)
    require(digest(data)==rule['accepted_sha256'],'G range source inverse identity');return data

def verify_candidate(candidate,expected):
    require(candidate==expected,'G endpoint candidate inventory')
    for rel,value in candidate.items():
        path=(HERE/rel).resolve();raw=path.read_bytes()
        raw=inverse_workflow(raw.decode()).encode()if path==ROOT/'.github/workflows/transformer.yml'else project_current(str(path.relative_to(ROOT)),raw)
        require(digest(raw)==value,'G endpoint archived source drift: '+rel)

def identities():return previous.identities()+[i['identity']for i in pin()['endpoints']]
def read_endpoint(z,item):
    paths=previous.previous.previous.base.old.archive_index(z)
    require({n for n in paths if not n.endswith('/')}==set(item['files']),'endpoint exact physical inventory')
    for name,value in item['files'].items():require(digest(z.read(name))==value,'endpoint source/object/scoped envelope drift: '+name)
    return {Path(n).name:z.read(n).decode()for n in item['files']if n.startswith('rawgpilot-out/')and n.endswith(('.json','.jsonl','.out','.lean'))}

def validate_endpoint(data,item):
    import rawgpilot_generate as endpoint
    load=lambda n:json.loads(data[n]);a=load('G_ROW_ACCEPTED.json');row=item['row'];prefix,namespace=endpoint.identities(row)
    names=[namespace+'.'+n for names in endpoint.DECLARATIONS.values()for n in names]
    require(a['kernel_verdict']=='KERNEL_ACCEPTED'and a['scope']==endpoint.scope(row)and a['fresh_compiled_replayed']==item['objects']and a['restored_objects']==previous.pin()['objects'],'endpoint scope/objects')
    require(a['compiler_binary_sha256']==previous.previous.pin()['compiler_binary_sha256']and a['checkpoint_sha256']==sha(previous.PIN_PATH)and a['exact_production_audit_names']==3260 and a['negative_actual_Wout_change']=='KERNEL_DECIDE_FALSE_EXIT_1','endpoint compiler/control/audit')
    require(data['compiled.jsonl']==data['replayed.jsonl']and[json.loads(s)for s in data['compiled.jsonl'].splitlines()]==item['objects'],'endpoint actual compile/replay')
    generation=load('generation.json');require(generation==a['generation']and generation['scope']==endpoint.scope(row)and generation['modules']==[prefix+'.'+s for s in endpoint.DECLARATIONS]and generation['declarations']==names,'endpoint generation inventory')
    require(generation['outputs']=={r['module'].replace('.','/')+'.lean':r['source_sha256']for r in item['objects']},'endpoint source identities')
    require(load('restored-union.json')['objects']==previous.pin()['objects']and load('restored-union.json')['selected_names']==previous.pin()['selected_names'],'endpoint301 prefix')
    verify_candidate(a['candidate'],item['candidate'])
    for label,names in item['audits'].items():require(load(label+'.expected.json')==names and check_correspondence_axioms(data[label+'.out'],names)==len(names),'endpoint strict audit')
    steps=[json.loads(s)for s in data['steps.jsonl'].splitlines()];require(steps==item['steps']and len({s['name']for s in steps})==len(steps),'endpoint exact producers/exits')
    witness=generation['witness'];require(witness['field']=='Wout'and witness['coordinate']==[row,0]and type(witness['old'])is int and witness['new']==witness['old']+1 and witness['delta']==1 and witness['nonzero_U_coordinate']==[0,0]and witness['output']==[row,0],'endpoint actual perturbation')
    return item['objects']

def validate_identities(items):
    expected=identities();require(items==expected and len(items)==39 and len({i['artifact_id']for i in items})==39,'G exact39 producer identities/order')
    require([i['row']for i in pin()['endpoints']]==[0,511],'endpoint coverage/order')
    require(len(pin()['objects'])==311 and len({r['module']for r in pin()['objects']})==311 and len(pin()['selected_names'])==len(set(pin()['selected_names']))==3274,'G311 object/name union')

def validate_archives(zs):
    validate_identities(identities());require(len(zs)==39,'G archive count')
    full=previous.previous;earlier=full.previous;base=earlier.base
    # Retain the exact older36 envelope/canonical seam, plus complete metadata validators.
    full.validate_projected_union(zs[:36],identities()[:36],full.pin()['objects'])
    a,b,c,d=zs[:4];packed,source,_=base.old.validate_metadata(base.old.read_metadata(a,full.base_locks()[0]),full.base_locks()[0]);base.verify_sources(source)
    records=packed+base.validate_ci(base.read_ci(b))+earlier.boundary.validate_row0(earlier.boundary.read_row0(c))+earlier.validate_row127(earlier.read_row127(d))
    for z,item in zip(zs[4:36],full.range_lock()):records+=full.validate_range(full.read_range(z,item),item)
    require(records==full.pin()['objects'],'G294 earlier union')
    records+=previous.validate_cu(previous.read_cu(zs[36]))
    for z,item in zip(zs[37:],pin()['endpoints']):records+=validate_endpoint(read_endpoint(z,item),item)
    require(records==pin()['objects'],'G311 exact union')
    base.verify_union_sources(zs,records)
    canonical=dict(full.pin()['earlier_checkpoint_sha256']);canonical.update({'RawCUFull-checkpoint.json':sha(full.PIN_PATH),'RawGPilot-checkpoint.json':sha(previous.PIN_PATH)})
    for r in records:
        stem=r['module'].replace('.','/');canonical[stem+'.lean']=r['source_sha256'];canonical['.lake/build/lib/lean/'+stem+'.olean']=r['olean_sha256']
    for name,value in canonical.items():
        found=[z for z in zs if name in z.namelist()]
        if name.endswith('.olean'):require(found,'missing G canonical object')
        for z in found:require(digest(z.read(name))==value,'G canonical overlap/hash: '+name)
    return records

def preflight(folder):
    folder=Path(folder);items=identities();validate_identities(items)
    require({p.name for p in folder.glob('*.zip')}=={str(i['artifact_id'])+'.zip'for i in items},'missing/extra archive ZIPs')
    for item in items:
        aid=str(item['artifact_id']);require(stream_sha(folder/(aid+'.zip'))==item['zip_sha256'],'G archive ZIP digest')
        api=json.loads((folder/(aid+'.json')).read_text());previous.previous.previous.base.api_identity(api,{**item,'source_run':item.get('source_run',item.get('run'))})
        if 'artifact_name'in item:require(api['name']==item['artifact_name']and api['size_in_bytes']==item['size_in_bytes']and api['digest']=='sha256:'+item['zip_sha256'],'G endpoint API bytes/name')
    with ExitStack()as stack:return validate_archives([stack.enter_context(zipfile.ZipFile(folder/(str(i['artifact_id'])+'.zip')))for i in items])

def restore(folder,binaries):
    cloud_only();require(sha(previous.PIN_PATH)==pin()['previous_checkpoint_sha256'],'G immutable endpoint lock')
    records=preflight(folder) # Authenticate complete39 union BEFORE any source/object write.
    result=previous.restore(folder,binaries)
    base=previous.previous.previous.base
    for item in pin()['endpoints']:
        with zipfile.ZipFile(Path(folder)/(str(item['identity']['artifact_id'])+'.zip'))as z:
            for r in item['objects']:
                stem=r['module'].replace('.','/');rel=stem+'.lean';base.old.write_exact(HERE/rel,z.read(rel));obj='.lake/build/lib/lean/'+stem+'.olean';base.restore_object(z,obj,HERE/obj,r['olean_sha256'])
    require(result['objects']+[r for i in pin()['endpoints']for r in i['objects']]==records,'G311 restored union')
    return {'objects':records,'selected_names':pin()['selected_names'],'archive_sha256':[i['zip_sha256']for i in identities()]}

if __name__=='__main__':
    import argparse
    p=argparse.ArgumentParser();p.add_argument('--artifact-ids',action='store_true');a=p.parse_args()
    if a.artifact_ids:
        for i in identities():print(i['artifact_id'])
