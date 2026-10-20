"""Exact40 archive /362 object continuation, preserving the strict old39 directory view."""
from contextlib import ExitStack
import json,zipfile
from pathlib import Path
import rawvoboundary_restore as previous
from rawpilot_data import HERE,ROOT,sha
from rawpilot_generate import cloud_only
from rawcorrespondence_runner import check_correspondence_axioms
base=previous.base;require=previous.require;digest=previous.digest;stream_sha=previous.stream_sha
PIN_PATH=HERE/'RawVORange-checkpoint.json'
def pin():return json.loads(PIN_PATH.read_text())
def inverse_workflow(text):
    rule=pin()['workflow_projection'];require(digest(text.encode())==rule['current_sha256'],'unknown range workflow drift')
    for fragment in rule['insertions']:
        require(text.count(fragment)==1,'range inverse count');text=text.replace(fragment,'',1)
    require(text.count(rule['exclusion'])==3,'range exclusions');text=text.replace(rule['exclusion'],'')
    require(digest(text.encode())==rule['accepted_sha256'],'range workflow accepted identity');return text

def project_current(path,data):
    rule=pin()['nonproof_projections'].get(path)
    if rule is None:return data
    require(digest(data)==rule['current_sha256'],'unknown range source drift: '+path)
    for edit in rule['edits']:
        a,b=edit['current'].encode(),edit['accepted'].encode();require(data.count(a)==1,'range inverse occurrence');data=data.replace(a,b,1)
    require(digest(data)==rule['accepted_sha256'],'range source inverse identity');return data

def identities():return previous.identities()+[pin()['continuation']['identity']]
def archive_path(folder,i,item):return Path(folder)/('previous/prior'if i<37 else'previous/pilots'if i<39 else'boundary')/(str(item['artifact_id'])+'.zip')
def verify_candidate(candidate):
    require(candidate==pin()['continuation']['candidate'],'boundary exact candidate map')
    for rel,expected in candidate.items():
        p=(HERE/rel).resolve();raw=p.read_bytes();raw=inverse_workflow(raw.decode()).encode()if p==ROOT/'.github/workflows/transformer.yml'else project_current(str(p.relative_to(ROOT)),raw)
        require(digest(raw)==expected,'boundary original producer source drift: '+rel)

def read_boundary(z):
    item=pin()['continuation'];paths=base.old.archive_index(z)
    require({n for n in paths if not n.endswith('/')}==set(item['files']),'boundary exact physical member inventory')
    for name,expected in item['files'].items():require(digest(z.read(name))==expected,'boundary pinned file drift: '+name)
    modules={r['module']for r in pin()['objects']}
    for r in item['objects']:
        stem=r['module'].replace('.','/');src=stem+'.lean';obj='.lake/build/lib/lean/'+stem+'.olean'
        require(item['files'][src]==r['source_sha256']and item['files'][obj]==r['olean_sha256'],'boundary source/object pin binding');base.check_imports(z.read(src),modules)
    return {p[len(item['out'])+1:]:z.read(p).decode()for p in item['files']if p.startswith(item['out']+'/')and p.endswith(('.json','.jsonl','.out','.lean'))}

def validate_boundary(data):
    item=pin()['continuation'];load=lambda n:json.loads(data[n]);a=load('VO_BOUNDARY_ACCEPTED.json');g=load('generation.json');fresh=item['objects']
    require(a['kernel_verdict']=='KERNEL_ACCEPTED'and a['scope']==item['scope'],'boundary exact scope')
    require(a['fresh_compiled_replayed']==fresh and a['restored_objects']==previous.pin()['objects'],'boundary source/object identities')
    require(a['compiler_binary_sha256']==pin()['compiler_binary_sha256']and a['checkpoint_sha256']==sha(previous.PIN_PATH)==item['checkpoint_sha256'],'boundary compiler/immutable lock')
    require(a['generation']==g and g['declarations']==item['names']and g['modules']==item['modules'],'boundary complete generation inventory')
    require([json.loads(s)for s in data['compiled.jsonl'].splitlines()]==fresh and data['compiled.jsonl']==data['replayed.jsonl'],'boundary ordinary compile/replay')
    require(load('restored-union.json')['objects']==previous.pin()['objects'],'boundary previous333')
    require(a['exact_production_audit_names']==3956 and a['negative_actual_U_change']=='KERNEL_DECIDE_FALSE_EXIT_1','boundary full audits/real U control')
    steps=[json.loads(s)for s in data['steps.jsonl'].splitlines()];require(steps==item['steps']and len({s['name']for s in steps})==len(steps),'boundary exact producers/exits')
    for label,names in item['audits'].items():require(load(label+'.expected.json')==names and check_correspondence_axioms(data[label+'.out'],names)==len(names),'boundary strict audit')
    verify_candidate(a['candidate']);return fresh

def boundary_preflight(folder):
    folder=Path(folder);item=pin()['continuation'];i=item['identity'];stem=folder/str(i['artifact_id']);path=stem.with_suffix('.zip')
    require({p.name for p in folder.glob('*.zip')}=={path.name},'exact one boundary ZIP')
    api=json.loads(stem.with_suffix('.json').read_text());require(stream_sha(path)==i['zip_sha256'],'boundary whole ZIP digest');base.api_identity(api,i)
    require(api['name']==i['artifact_name']and api['size_in_bytes']==i['size_in_bytes']==path.stat().st_size and api['digest']=='sha256:'+i['zip_sha256'],'boundary API identity/size/digest')
    with zipfile.ZipFile(path)as z:return validate_boundary(read_boundary(z))

def preflight(folder):
    folder=Path(folder);expected={archive_path(folder,n,i)for n,i in enumerate(identities())}
    require(set(folder.rglob('*.zip'))==expected and len(expected)==40,'range exact40 archive views')
    require(sha(previous.PIN_PATH)==pin()['previous_checkpoint_sha256'],'range immutable previous lock')
    fresh=boundary_preflight(folder/'boundary');old=previous.preflight(folder/'previous')
    require(old+fresh==pin()['objects']and len({r['module']for r in old+fresh})==362,'range exact362 object union')
    with ExitStack()as stack:
        zs=[stack.enter_context(zipfile.ZipFile(archive_path(folder,n,i)))for n,i in enumerate(identities())]
        previous.verify_canonical_storage(zs,pin()['objects'])
        checkpoints={p for p in pin()['continuation']['files']if p.endswith('checkpoint.json')}
        for p in checkpoints:
            expected=sha(HERE/p)
            for z in zs:
                if p in z.namelist():require(digest(z.read(p))==expected,'range canonical checkpoint overlap')
    return pin()['objects']

def restore(folder,binaries):
    cloud_only();folder=Path(folder);preflight(folder)
    require({k:sha(p)for k,p in binaries.items()}==pin()['compiler_binary_sha256'],'range current compiler drift')
    for r in pin()['objects']:require(not(HERE/'.lake/build/lib/lean'/(r['module'].replace('.','/')+'.olean')).exists(),'range preexisting proof object')
    previous.restore(folder/'previous',binaries)
    i=pin()['continuation']['identity']
    with zipfile.ZipFile(folder/'boundary'/(str(i['artifact_id'])+'.zip'))as z:
        for r in pin()['continuation']['objects']:
            stem=r['module'].replace('.','/');base.old.write_exact(HERE/(stem+'.lean'),z.read(stem+'.lean'))
            obj='.lake/build/lib/lean/'+stem+'.olean';base.restore_object(z,obj,HERE/obj,r['olean_sha256'])
    for r in pin()['objects']:
        stem=r['module'].replace('.','/');require(sha(HERE/(stem+'.lean'))==r['source_sha256']and stream_sha(HERE/'.lake/build/lib/lean'/(stem+'.olean'))==r['olean_sha256'],'range final source/object identity')
    return {'objects':pin()['objects'],'selected_names':pin()['selected_names'],'archive_sha256':[i['zip_sha256']for i in identities()]}

if __name__=='__main__':
    import argparse
    p=argparse.ArgumentParser();p.add_argument('--artifact-ids',action='store_true');p.add_argument('--group',choices=('prior','pilots','boundary'),default='prior');a=p.parse_args()
    items=previous.previous.identities()if a.group=='prior'else[i['identity']for i in previous.pin()['continuations']]if a.group=='pilots'else[pin()['continuation']['identity']]
    if a.artifact_ids:
        for i in items:print(i['artifact_id'])
