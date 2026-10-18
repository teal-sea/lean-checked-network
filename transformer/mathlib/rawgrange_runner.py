#!/usr/bin/env python3
"""At most four G rows in one production module, with actual independent kernel false control."""
import argparse,json,os,re
from pathlib import Path
from rawpilot_data import HERE,sha
from rawpilot_generate import cloud_only
from rawurange_runner import snapshot
import rawgrange_generate as gen
import rawgrange_restore as cache
import rawcorrespondence_runner as common
OUT=HERE/'rawgrange-out'

def main(archives,start=1,count=4):
    gen.rows_for(start,count);module_prefix,namespace=gen.identities(start,count);cloud_only()
    cache.require(os.environ.get('GITHUB_REPOSITORY')=='teal-sea/lean-checked-network' and os.environ.get('LEAN_NUM_THREADS')in('1','2'),'G public repository/threads')
    cache.require(not OUT.exists() and not(HERE/gen.PREFIX.replace('.','/')).exists(),'preexisting G output')
    OUT.mkdir();common.OUT=OUT;common.runner.OUT=OUT;common.runner.STEPS.clear();candidate=snapshot()
    version=common.runner.run('compiler-version',['lake','env','lean','--version'],60)
    cache.require('version 4.35.0' in version and 'commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc' in version,'G compiler version')
    prefix=Path(common.runner.run('compiler-prefix',['lake','env','lean','--print-prefix'],60).strip());binaries={t:(prefix/'bin'/t).resolve()for t in ('lean','lake','leanchecker')}
    restored=cache.restore(archives,binaries);(OUT/'restored-union.json').write_text(json.dumps(restored,indent=2,sort_keys=True)+'\n')
    record=gen.emit(OUT,start,count);modules,row_names,control_names=gen.inventory(start,count);fresh=[]
    for module,expected,label in zip(modules,(row_names,control_names),('batch','control')):
        gen.check_declarations(module,expected)
        common.runner.run(label+'-scan',['../lean/scan_sources.sh',module.replace('.','/')+'.lean'],60)
        fresh.append(common.fresh_compile(module));common.audit(label,[module],expected)
    names=row_names+control_names
    common.runner.run('negative-scan',['../lean/scan_sources.sh',str(OUT/'changed-Wout-range.lean')],60)
    imports=['TransformerBridge.RawPacked.Generated.Site','TransformerBridge.RawCorrespondence.Generated.Control',
        'TransformerBridge.RawCorrespondenceFixture','TransformerBridge.RawCorrespondenceLinear',
        cache.previous.previous.previous.boundary.row0.MODULES[-1],cache.previous.previous.previous.row127.MODULES[-1]]
    imports += [cache.previous.previous.batches.inventory(i['U_rows'][0],len(i['U_rows']))[0][-1] for i in cache.previous.previous.range_lock()]
    imports += [gen.CU+'.Control']+[i['objects'][-1]['module']for i in cache.pin()['endpoints']]+[modules[-1]]
    audit_count=common.audit('complete-G-range',imports,restored['selected_names']+names)
    common.runner.run('negative-actual-Wout-range-change',['lake','env','lean',str(OUT/'changed-Wout-range.lean')],900,negative=True)
    gen.emit(OUT,start,count,check=True)
    actual={str(p.relative_to(HERE))for p in (HERE/gen.PREFIX.replace('.','/')).rglob('*.lean')}
    cache.require(actual==set(record['outputs']),'G closed emitted source inventory')
    cache.require(snapshot()==candidate,'G source policy drift')
    cache.require({t:sha(p)for t,p in binaries.items()}==cache.previous.previous.pin()['compiler_binary_sha256'],'G compiler changed')
    cache.require((OUT/'compiled.jsonl').read_bytes()==(OUT/'replayed.jsonl').read_bytes(),'G compile/replay mismatch')
    for r in restored['objects']+fresh:
        stem=r['module'].replace('.','/');cache.require(sha(HERE/(stem+'.lean'))==r['source_sha256'] and cache.stream_sha(HERE/'.lake/build/lib/lean'/(stem+'.olean'))==r['olean_sha256'],'G final source/object drift')
    throughput={}
    for r in fresh:
        stats={}
        for phase in ('fresh_compile_','fresh_replay_'):
            label=phase+r['module'];rss=re.findall(r'Maximum resident set size \(kbytes\): (\d+)',(OUT/(label+'.time')).read_text());cache.require(len(rss)==1,'G missing RSS')
            stats[phase]={'seconds':common.runner.STEPS[label]['seconds'],'peak_rss_kib':int(rss[0])}
        throughput[r['module']]=stats
    (OUT/'throughput.json').write_text(json.dumps(throughput,indent=2,sort_keys=True)+'\n')
    (OUT/'G_RANGE_ACCEPTED.json').write_text(json.dumps({'kernel_verdict':'KERNEL_ACCEPTED','scope':gen.scope(start,count),'fresh_compiled_replayed':fresh,'restored_objects':restored['objects'],'exact_production_audit_names':audit_count,'negative_actual_Wout_range_change':'KERNEL_DECIDE_FALSE_EXIT_1','generation':record,'candidate':candidate,'compiler_binary_sha256':cache.previous.previous.pin()['compiler_binary_sha256'],'checkpoint_sha256':sha(cache.PIN_PATH),'fanout':'NOT_AUTHORIZED'},indent=2,sort_keys=True)+'\n')

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--archives',type=Path,required=True);p.add_argument('--start',type=int,default=1);p.add_argument('--count',type=int,default=4);a=p.parse_args()
    try:main(a.archives,a.start,a.count)
    except Exception as error:
        if OUT.exists():(OUT/'FAILURE.json').write_text(json.dumps({'kernel_verdict':'NOT_ACCEPTED','scope':gen.scope(a.start,a.count),'error':str(error),'completed_steps':list(common.runner.STEPS)},indent=2)+'\n')
        raise
