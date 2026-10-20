"""Minimal authenticated37-archive/301-object TU closure, through all later inverses."""
from contextlib import ExitStack
import json,zipfile
from pathlib import Path
import rawgpilot_restore as previous
from rawpilot_data import HERE,ROOT,sha
from rawpilot_generate import cloud_only
require=previous.require
digest=previous.digest
stream_sha=previous.stream_sha
PIN_PATH=HERE/'RawTUPilot-checkpoint.json'
def pin():return json.loads(PIN_PATH.read_text())
def inverse_workflow(text):
    rule=pin()['workflow_projection'];require(digest(text.encode())==rule['current_sha256'],'unknown TU workflow drift')
    for fragment in rule['insertions']:
        require(text.count(fragment)==1,'TU workflow inverse occurrence');text=text.replace(fragment,'',1)
    require(text.count(rule['exclusion'])==3,'TU workflow exclusion count');text=text.replace(rule['exclusion'],'')
    require(digest(text.encode())==rule['accepted_sha256'],'TU accepted workflow identity');return text

def project_current(path,data):
    rule=pin()['nonproof_projections'].get(path)
    if rule is None:return data
    require(digest(data)==rule['current_sha256'],'unknown TU nonproof source drift: '+path)
    for edit in rule['edits']:
        a,b=edit['current'].encode(),edit['accepted'].encode();require(data.count(a)==1,'TU source inverse occurrence');data=data.replace(a,b,1)
    require(digest(data)==rule['accepted_sha256'],'TU source inverse identity');return data

def identities():return previous.identities()
def preflight(folder):
    folder=Path(folder);items=identities();lock=pin();require(len(items)==37 and len({i['artifact_id']for i in items})==37,'TU exact37 identities')
    require({p.name for p in folder.glob('*.zip')}=={str(i['artifact_id'])+'.zip'for i in items},'TU missing/extra ZIPs')
    full=previous.previous;earlier=full.previous;base=earlier.base
    for item in items:
        stem=folder/str(item['artifact_id']);require(stream_sha(stem.with_suffix('.zip'))==item['zip_sha256'],'TU ZIP hash')
        api=json.loads(stem.with_suffix('.json').read_text());base.api_identity(api,{**item,'source_run':item.get('source_run',item.get('run'))})
        if 'artifact_name'in item:require(api['name']==item['artifact_name']and api['size_in_bytes']==stem.with_suffix('.zip').stat().st_size and api['digest']=='sha256:'+item['zip_sha256'],'TU API bytes/name')
    with ExitStack()as stack:
        zs=[stack.enter_context(zipfile.ZipFile(folder/(str(i['artifact_id'])+'.zip')))for i in items]
        full.validate_projected_union(zs[:36],items[:36],full.pin()['objects'])
        a,b,c,d=zs[:4];packed,source,_=base.old.validate_metadata(base.old.read_metadata(a,items[0]),items[0]);base.verify_sources(source)
        records=packed+base.validate_ci(base.read_ci(b))+earlier.boundary.validate_row0(earlier.boundary.read_row0(c))+earlier.validate_row127(earlier.read_row127(d))
        for z,item in zip(zs[4:36],full.range_lock()):records+=full.validate_range(full.read_range(z,item),item)
        records+=previous.validate_cu(previous.read_cu(zs[36]));require(records==lock['objects']and len({r['module']for r in records})==301,'TU exact301 union')
        base.verify_union_sources(zs,records)
        canonical=dict(full.pin()['earlier_checkpoint_sha256']);canonical['RawCUFull-checkpoint.json']=sha(full.PIN_PATH)
        for record in records:
            stem=record['module'].replace('.','/');canonical[stem+'.lean']=record['source_sha256'];canonical['.lake/build/lib/lean/'+stem+'.olean']=record['olean_sha256']
        indexes=[set(z.namelist())for z in zs]
        for name,value in canonical.items():
            found=[z for z,index in zip(zs,indexes)if name in index]
            if name.endswith('.olean'):require(found,'TU missing canonical object')
            for z in found:require(digest(z.read(name))==value,'TU canonical overlap/source/object: '+name)
    return records

def restore(folder,binaries):
    cloud_only();require(sha(previous.PIN_PATH)==pin()['previous_checkpoint_sha256'],'TU immutable CU continuation lock')
    preflight(folder)
    result=previous.restore(folder,binaries)
    require(result['objects']==pin()['objects']and result['selected_names']==pin()['selected_names'],'TU authenticated301/3246 closure')
    return result

if __name__=='__main__':
    import argparse
    p=argparse.ArgumentParser();p.add_argument('--artifact-ids',action='store_true');a=p.parse_args()
    if a.artifact_ids:
        for item in identities():print(item['artifact_id'])
