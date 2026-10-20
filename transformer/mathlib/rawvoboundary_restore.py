"""Closed39 archive /333 object union. Envelopes remain artifact-scoped, never restored."""
from contextlib import ExitStack
import json,zipfile
from pathlib import Path
import rawvobasis_restore as previous
import rawgpilot_restore as cu
import rawcu_restore as base
from rawpilot_data import HERE,ROOT,sha
from rawpilot_generate import cloud_only
from rawcorrespondence_runner import check_correspondence_axioms
require=base.require;digest=base.digest;stream_sha=previous.stream_sha
PIN_PATH=HERE/'RawVOBoundary-checkpoint.json'
def pin():return json.loads(PIN_PATH.read_text())
def inverse_workflow(text):
    rule=pin()['workflow_projection'];require(digest(text.encode())==rule['current_sha256'],'unknown boundary workflow drift')
    for fragment in rule['insertions']:
        require(text.count(fragment)==1,'boundary inverse count');text=text.replace(fragment,'',1)
    require(text.count(rule['exclusion'])==3,'boundary exclusions');text=text.replace(rule['exclusion'],'')
    require(digest(text.encode())==rule['accepted_sha256'],'boundary workflow inverse identity');return text

def project_current(path,data):
    rule=pin()['nonproof_projections'].get(path)
    if rule is None:return data
    require(digest(data)==rule['current_sha256'],'unknown boundary source drift: '+path)
    for edit in rule['edits']:
        a,b=edit['current'].encode(),edit['accepted'].encode();require(data.count(a)==1,'boundary inverse occurrence');data=data.replace(a,b,1)
    require(digest(data)==rule['accepted_sha256'],'boundary accepted source identity');return data

def identities():return previous.identities()+[i['identity']for i in pin()['continuations']]
def verify_candidate(candidate,item):
    require(candidate==item['candidate'],'pilot exact candidate map')
    for rel,expected in candidate.items():
        path=(HERE/rel).resolve();raw=path.read_bytes();workflow=path==ROOT/'.github/workflows/transformer.yml';relroot=str(path.relative_to(ROOT))
        if item['kind']=='VO':raw=inverse_workflow(raw.decode()).encode()if workflow else project_current(relroot,raw)
        else:raw=previous.inverse_workflow(raw.decode()).encode()if workflow else previous.project_current(relroot,raw)
        require(digest(raw)==expected,'accepted pilot candidate drift: '+rel)

def read_continuation(z,item):
    paths=base.old.archive_index(z);require({p for p in paths if not p.endswith('/')}==set(item['files']),'pilot exact physical inventory')
    for name,expected in item['files'].items():require(digest(z.read(name))==expected,'pilot pinned file drift: '+name)
    modules={r['module']for r in pin()['objects']}
    for record in item['objects']:
        stem=record['module'].replace('.','/');src=stem+'.lean';obj='.lake/build/lib/lean/'+stem+'.olean'
        require(item['files'].get(src)==record['source_sha256']and item['files'].get(obj)==record['olean_sha256'],'pilot source/object pin association')
        base.check_imports(z.read(src),modules)
    return {p[len(item['out'])+1:]:z.read(p).decode()for p in item['files']if p.startswith(item['out']+'/')and p.endswith(('.json','.jsonl','.out','.lean'))}

def validate_continuation(data,item):
    load=lambda n:json.loads(data[n]);a=load(item['acceptance']);fresh=item['objects'];g=load('generation.json')
    require(a['kernel_verdict']=='KERNEL_ACCEPTED'and a['scope']==item['scope'],'pilot exact scope')
    require(a['fresh_compiled_replayed']==fresh and a['restored_objects']==cu.pin()['objects'],'pilot source/object identity')
    require(a['compiler_binary_sha256']==pin()['compiler_binary_sha256']and a['checkpoint_sha256']==item['checkpoint_sha256'],'pilot compiler/checkpoint')
    checkpoint='RawVOBasis-checkpoint.json'if item['kind']=='VO'else'RawTUPilot-checkpoint.json'
    require(sha(HERE/checkpoint)==item['checkpoint_sha256'],'pilot immutable checkpoint bytes')
    require(a['generation']==g and g['declarations']==item['names']and g['modules']==item['modules'],'pilot complete generated inventory')
    require([json.loads(s)for s in data['compiled.jsonl'].splitlines()]==fresh and data['compiled.jsonl']==data['replayed.jsonl'],'pilot compile/replay records')
    require(load('restored-union.json')['objects']==cu.pin()['objects'],'pilot restored301')
    require(a['exact_production_audit_names']==3246+len(item['names'])and a[item['negative_key']]=='KERNEL_DECIDE_FALSE_EXIT_1','pilot exact audits and actual negative')
    steps=[json.loads(s)for s in data['steps.jsonl'].splitlines()];require(steps==item['steps']and len({s['name']for s in steps})==len(steps),'pilot exact producers/exits')
    for label,names in item['audits'].items():require(load(label+'.expected.json')==names and check_correspondence_axioms(data[label+'.out'],names)==len(names),'pilot strict complete audit')
    verify_candidate(a['candidate'],item);return fresh

def continuation_preflight(folder):
    folder=Path(folder);items=pin()['continuations'];require({p.name for p in folder.glob('*.zip')}=={str(i['identity']['artifact_id'])+'.zip'for i in items},'boundary exact two continuation ZIPs')
    records=[]
    with ExitStack()as stack:
        archives=[]
        for item in items:
            identity=item['identity'];stem=folder/str(identity['artifact_id']);path=stem.with_suffix('.zip');api=json.loads(stem.with_suffix('.json').read_text())
            require(stream_sha(path)==identity['zip_sha256'],'pilot whole ZIP digest');base.api_identity(api,identity)
            require(api['name']==identity['artifact_name']and api['size_in_bytes']==identity['size_in_bytes']==path.stat().st_size and api['digest']=='sha256:'+identity['zip_sha256'],'pilot API size/name/digest')
            z=stack.enter_context(zipfile.ZipFile(path));archives.append(z);records+=validate_continuation(read_continuation(z,item),item)
        require(len({r['module']for r in records})==32,'pilot duplicate object union')
        # Shared canonical checkpoints/sources/objects must agree; envelopes never share a destination.
        canonical={n for item in items for n in item['files']if not n.startswith(item['out']+'/')and not n.endswith(('.time','.out'))}
        for name in canonical:
            values=[digest(z.read(name))for z in archives if name in z.namelist()];require(len(set(values))<=1,'pilot canonical overlap: '+name)
    return records

def verify_canonical_storage(archives,records):
    # Existing source contract: every repo/archive copy is hash-pinned, imports closed.
    base.verify_union_sources(archives,records)
    for record in records:
        stem=record['module'].replace('.','/')
        for name,expected in ((stem+'.lean',record['source_sha256']),('.lake/build/lib/lean/'+stem+'.olean',record['olean_sha256'])):
            found=[z for z in archives if name in z.namelist()]
            if name.endswith('.olean'):
                require(found,'missing union object')
            else:
                # Archive omission is legitimate only with the exact pinned repository source.
                require(found or ((HERE/name).is_file()and sha(HERE/name)==expected),'missing pinned union source')
            for z in found:require(digest(z.read(name))==expected,'boundary physical canonical overlap')

def preflight(folder):
    folder=Path(folder);require(not list(folder.glob('*.zip')),'boundary archives must use exact separate prior/pilots views')
    require(sha(previous.PIN_PATH)==pin()['previous_checkpoint_sha256'],'immutable VO checkpoint')
    records=continuation_preflight(folder/'pilots');old=previous.preflight(folder/'prior');require(old+records==pin()['objects'],'boundary exact333 union')
    with ExitStack()as stack:
        archives=[stack.enter_context(zipfile.ZipFile(folder/('prior'if i<37 else'pilots')/(str(item['artifact_id'])+'.zip')))for i,item in enumerate(identities())]
        verify_canonical_storage(archives,pin()['objects'])
    return pin()['objects']

def restore(folder,binaries):
    cloud_only();folder=Path(folder);preflight(folder)
    require({k:sha(v)for k,v in binaries.items()}==pin()['compiler_binary_sha256'],'boundary compiler drift')
    for record in pin()['objects']:
        require(not(HERE/'.lake/build/lib/lean'/(record['module'].replace('.','/')+'.olean')).exists(),'preexisting boundary proof object')
    previous.restore(folder/'prior',binaries)
    for item in pin()['continuations']:
        with zipfile.ZipFile(folder/'pilots'/(str(item['identity']['artifact_id'])+'.zip'))as z:
            for record in item['objects']:
                stem=record['module'].replace('.','/');base.old.write_exact(HERE/(stem+'.lean'),z.read(stem+'.lean'))
                obj='.lake/build/lib/lean/'+stem+'.olean';base.restore_object(z,obj,HERE/obj,record['olean_sha256'])
    for record in pin()['objects']:
        stem=record['module'].replace('.','/');require(sha(HERE/(stem+'.lean'))==record['source_sha256']and stream_sha(HERE/'.lake/build/lib/lean'/(stem+'.olean'))==record['olean_sha256'],'boundary final identity')
    return {'objects':pin()['objects'],'selected_names':pin()['selected_names'],'archive_sha256':[i['zip_sha256']for i in identities()]}

if __name__=='__main__':
    import argparse
    p=argparse.ArgumentParser();p.add_argument('--artifact-ids',action='store_true');p.add_argument('--group',choices=('prior','pilots'),default='prior');a=p.parse_args()
    if a.artifact_ids:
        for i in (previous.identities()if a.group=='prior'else[item['identity']for item in pin()['continuations']]):print(i['artifact_id'])
