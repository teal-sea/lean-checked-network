"""Reuse exact37-archive/301-object CU closure; no accepted TU/G objects rebuilt."""
import json
from pathlib import Path
import rawtupilot_restore as previous
from rawpilot_data import HERE,ROOT,sha
from rawpilot_generate import cloud_only
require=previous.require
digest=previous.digest
stream_sha=previous.stream_sha
PIN_PATH=HERE/'RawVOBasis-checkpoint.json'
def pin():return json.loads(PIN_PATH.read_text())
def inverse_workflow(text):
    from rawvoboundary_restore import inverse_workflow as boundary_inverse
    text=boundary_inverse(text)
    rule=pin()['workflow_projection'];require(digest(text.encode())==rule['current_sha256'],'unknown VO workflow drift')
    for fragment in rule['insertions']:
        require(text.count(fragment)==1,'VO inverse count');text=text.replace(fragment,'',1)
    require(text.count(rule['exclusion'])==3,'VO workflow exclusions');text=text.replace(rule['exclusion'],'')
    require(digest(text.encode())==rule['accepted_sha256'],'VO accepted workflow identity');return text

def project_current(path,data):
    from rawvoboundary_restore import project_current as boundary_project
    data=boundary_project(path,data)
    rule=pin()['nonproof_projections'].get(path)
    if rule is None:return data
    require(digest(data)==rule['current_sha256'],'unknown VO source drift: '+path)
    for edit in rule['edits']:
        a,b=edit['current'].encode(),edit['accepted'].encode();require(data.count(a)==1,'VO source inverse count');data=data.replace(a,b,1)
    require(digest(data)==rule['accepted_sha256'],'VO accepted source identity');return data

def identities():return previous.identities()
def preflight(folder):
    require(sha(previous.PIN_PATH)==pin()['previous_checkpoint_sha256'],'VO immutable TU lock')
    records=previous.preflight(folder);require(records==pin()['objects'],'VO301 source/object union');return records

def restore(folder,binaries):
    cloud_only();require(sha(previous.PIN_PATH)==pin()['previous_checkpoint_sha256'],'VO immutable TU lock')
    result=previous.restore(folder,binaries)
    require(result['objects']==pin()['objects']and result['selected_names']==pin()['selected_names'],'VO301/3246 restored union')
    return result

if __name__=='__main__':
    import argparse
    p=argparse.ArgumentParser();p.add_argument('--artifact-ids',action='store_true');a=p.parse_args()
    if a.artifact_ids:
        for i in identities():print(i['artifact_id'])
