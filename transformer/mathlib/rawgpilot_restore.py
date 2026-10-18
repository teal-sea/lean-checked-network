"""Exact37-archive continuation of accepted CU; never rebuild accepted objects."""
from contextlib import ExitStack
import json
from pathlib import Path
import zipfile
import rawcufull_restore as previous
from rawpilot_data import HERE,ROOT,sha
from rawpilot_generate import cloud_only
from rawcorrespondence_runner import check_correspondence_axioms
require=previous.require
digest=previous.digest
stream_sha=previous.stream_sha
PIN_PATH=HERE/'RawGPilot-checkpoint.json'
def pin():return json.loads(PIN_PATH.read_text())
def inverse_workflow(text):
    from rawgrange_restore import inverse_workflow as range_inverse
    text=range_inverse(text)
    rule=pin()['workflow_projection'];require(digest(text.encode())==rule['current_sha256'],'unknown G workflow drift')
    for fragment in rule['insertions']:
        require(text.count(fragment)==1,'G workflow inverse occurrence');text=text.replace(fragment,'',1)
    require(text.count(rule['exclusion'])==3,'G workflow exclusion count');text=text.replace(rule['exclusion'],'')
    require(digest(text.encode())==rule['accepted_sha256'],'G workflow inverse identity');return text

def project_current(path,data):
    from rawgrange_restore import project_current as range_project
    data=range_project(path,data)
    rule=pin()['nonproof_projections'].get(path)
    if rule is None:return data
    require(digest(data)==rule['current_sha256'],'unknown G source drift: '+path)
    for edit in rule['edits']:
        a,b=edit['current'].encode(),edit['accepted'].encode();require(data.count(a)==1,'G inverse occurrence');data=data.replace(a,b,1)
    require(digest(data)==rule['accepted_sha256'],'G inverse identity');return data

def verify_candidate(candidate):
    require(candidate==pin()['cu_candidate'],'CU candidate inventory')
    for rel,value in candidate.items():
        path=(HERE/rel).resolve();raw=path.read_bytes()
        raw=inverse_workflow(raw.decode()).encode() if path==ROOT/'.github/workflows/transformer.yml' else project_current(str(path.relative_to(ROOT)),raw)
        require(digest(raw)==value,'CU candidate source drift: '+rel)

def identities():return previous.base_locks()+previous.range_lock()+[pin()['cu']]

def read_cu(z):
    paths=previous.previous.base.old.archive_index(z);expected=pin()['cu_files']
    require({n for n in paths if not n.endswith('/')}==set(expected),'CU exact physical inventory')
    for name,value in expected.items():require(digest(z.read(name))==value,'CU file/source/object/envelope drift: '+name)
    return {Path(n).name:z.read(n).decode() for n in expected if n.startswith('rawcufull-out/') and n.endswith(('.json','.jsonl','.out','.lean'))}

def validate_cu(data):
    load=lambda n:json.loads(data[n]);a=load('CU113_ACCEPTED.json');fresh=pin()['cu_objects']
    require(a['kernel_verdict']=='KERNEL_ACCEPTED' and a['CU_field']is True and a['U_matrix_finite_index_assembly']is True and a['full_hT']is False and a['full_raw_model_theorem']is False,'CU acceptance scope')
    require(a['fresh_compiled_replayed']==fresh and a['restored_objects']==previous.pin()['objects'] and a['compiler_binary_sha256']==previous.pin()['compiler_binary_sha256'] and a['checkpoint_sha256']==sha(previous.PIN_PATH),'CU accepted identities')
    require([json.loads(s)for s in data['compiled.jsonl'].splitlines()]==fresh and data['compiled.jsonl']==data['replayed.jsonl'],'CU compile/replay identity')
    require(load('restored-union.json')['objects']==previous.pin()['objects'] and a['generation']==load('generation.json'),'CU prefix/generation')
    require(a['negative_actual_bout_change']=='KERNEL_DECIDE_FALSE_EXIT_1' and a['exact_production_audit_names']==3246,'CU full audit/control receipt')
    verify_candidate(a['candidate'])
    for label,names in pin()['cu_audits'].items():
        require(load(label+'.expected.json')==names and check_correspondence_axioms(data[label+'.out'],names)==len(names),'CU strict audit')
    steps=[json.loads(s)for s in data['steps.jsonl'].splitlines()];require(len({s['name']for s in steps})==len(steps),'CU duplicate producer')
    require(steps==pin()['cu_steps'],'CU exact producer commands/exits')
    return fresh

def restore(folder,binaries):
    cloud_only();folder=Path(folder);lock=pin();cu=lock['cu'];aid=str(cu['artifact_id'])
    require(sha(HERE/'RawCUFull-checkpoint.json')==lock['previous_checkpoint_sha256'],'CU immutable lock')
    require(stream_sha(folder/(aid+'.zip'))==cu['zip_sha256'],'CU ZIP drift')
    api=json.loads((folder/(aid+'.json')).read_text());previous.previous.base.api_identity(api,cu)
    require(api['name']==cu['artifact_name'] and api['size_in_bytes']==cu['size_in_bytes'] and api['digest']=='sha256:'+cu['zip_sha256'],'CU API bytes/name')
    with ExitStack()as stack:
        zs=[stack.enter_context(zipfile.ZipFile(folder/(str(i['artifact_id'])+'.zip')))for i in identities()]
        validate_cu(read_cu(zs[-1]))
        previous.validate_projected_union(zs[:-1],identities()[:-1],previous.pin()['objects'])
        previous.previous.base.verify_union_sources(zs,lock['objects'])
        # Every physical canonical overlap, including checkpoints, remains byte-identical.
        canonical=set(previous.pin()['earlier_checkpoint_sha256'])|{'RawCUFull-checkpoint.json'}
        for r in lock['objects']:
            stem=r['module'].replace('.','/');canonical.update((stem+'.lean','.lake/build/lib/lean/'+stem+'.olean'))
        for name in canonical:
            values=[digest(z.read(name)) for z in zs if name in z.namelist()]
            require(len(set(values))<=1,'G canonical overlap mismatch: '+name)
    result=previous.restore(folder,binaries)
    with zipfile.ZipFile(folder/(aid+'.zip'))as z:
        for r in lock['cu_objects']:
            stem=r['module'].replace('.','/');rel=stem+'.lean'
            previous.previous.base.old.write_exact(HERE/rel,z.read(rel))
            obj='.lake/build/lib/lean/'+stem+'.olean';previous.previous.base.restore_object(z,obj,HERE/obj,r['olean_sha256'])
    require(result['objects']+lock['cu_objects']==lock['objects'],'G301 union')
    return {'objects':lock['objects'],'selected_names':lock['selected_names'],'archive_sha256':[i['zip_sha256']for i in identities()]}

if __name__=='__main__':
    import argparse
    p=argparse.ArgumentParser();p.add_argument('--artifact-ids',action='store_true');args=p.parse_args()
    if args.artifact_ids:
        for item in identities():print(item['artifact_id'])
