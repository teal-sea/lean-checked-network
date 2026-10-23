#!/usr/bin/env python3
"""Bounded split V/O basis range, with actual independent kernel false control."""
import argparse,json,os,re
from pathlib import Path
from rawpilot_data import HERE,sha
from rawpilot_generate import cloud_only
from rawurange_runner import snapshot
import rawvorange_generate as gen
import rawvorange_restore as cache
import rawcorrespondence_runner as common
OUT=HERE/'rawvorange-out'

def main(archives,sel):
    gen.scope(sel);cloud_only()
    cache.require(os.environ.get('GITHUB_REPOSITORY')=='teal-sea/lean-checked-network' and os.environ.get('LEAN_NUM_THREADS')in('1','2'),'G public repository/threads')
    cache.require(not OUT.exists() and not(HERE/gen.prefix(sel).replace('.','/')).exists(),'preexisting G output')
    OUT.mkdir();common.OUT=OUT;common.runner.OUT=OUT;common.runner.STEPS.clear();candidate=snapshot()
    version=common.runner.run('compiler-version',['lake','env','lean','--version'],60)
    cache.require('version 4.35.0' in version and 'commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc' in version,'G compiler version')
    prefix=Path(common.runner.run('compiler-prefix',['lake','env','lean','--print-prefix'],60).strip());binaries={t:(prefix/'bin'/t).resolve()for t in ('lean','lake','leanchecker')}
    restored=cache.restore(archives,binaries);(OUT/'restored-union.json').write_text(json.dumps(restored,indent=2,sort_keys=True)+'\n')
    fresh=[];names=[]
    # Both generic helper objects are authenticated in the restored333 closure.
    witness=gen.production_witness(sel);sources,negative=gen.sources(sel,witness['values'],witness['l'])
    modules,inventory=gen.inventory(sel)
    for module in modules:
        label=module.removeprefix(gen.prefix(sel)+'.').replace('.','_');expected=inventory[module]
        gen.write_sources(OUT,{module:sources[module]})
        common.check_declarations(module,gen.module_namespace(sel,module),expected)
        common.runner.run(label+'-scan',['../lean/scan_sources.sh',module.replace('.','/')+'.lean'],60)
        fresh.append(common.fresh_compile(module));common.audit(label,[module],expected);names+=expected
    record={'scope':gen.scope(sel),'witness':witness,'modules':list(sources),'declarations':names,
        'outputs':{m.replace('.','/')+'.lean':cache.digest(s.encode())for m,s in sources.items()},'negative_sha256':cache.digest(negative.encode()),'kernel_verdict':'KERNEL_NOT_RUN'}
    gen.write_sources(OUT,{},negative,record)
    common.runner.run('negative-scan',['../lean/scan_sources.sh',str(OUT/'changed-WO.lean')],60)
    imports=[r['module']for r in restored['objects']]+[r['module']for r in fresh]
    count=common.audit('complete-VO-range',imports,restored['selected_names']+names)
    common.runner.run('negative-actual-WO-change',['lake','env','lean',str(OUT/'changed-WO.lean')],900,negative=True)
    gen.write_sources(OUT,sources,negative,record,check=True)
    actual={str(p.relative_to(HERE))for p in (HERE/gen.prefix(sel).replace('.','/')).rglob('*.lean')}
    cache.require(actual==set(record['outputs']),'G closed emitted source inventory')
    cache.require(snapshot()==candidate,'G source policy drift')
    cache.require({t:sha(p)for t,p in binaries.items()}==cache.pin()['compiler_binary_sha256'],'G compiler changed')
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
    (OUT/'VO_RANGE_ACCEPTED.json').write_text(json.dumps({'kernel_verdict':'KERNEL_ACCEPTED','scope':{**gen.scope(sel),'covered_basis_groups':sel['count']},'fresh_compiled_replayed':fresh,'restored_objects':restored['objects'],'exact_production_audit_names':count,'negative_actual_WO_change':'KERNEL_DECIDE_FALSE_EXIT_1','generation':record,'candidate':candidate,'compiler_binary_sha256':cache.pin()['compiler_binary_sha256'],'checkpoint_sha256':sha(cache.PIN_PATH),'fanout':'NOT_AUTHORIZED'},indent=2,sort_keys=True)+'\n')

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--archives',type=Path,required=True);p.add_argument('--head',type=gen.uint,default=0);p.add_argument('--kind',choices=('token','position'),default='token');p.add_argument('--start',type=gen.uint,default=1);p.add_argument('--count',type=gen.uint,default=4);a=p.parse_args()
    sel=gen.selection(a.head,a.kind,a.start,a.count)
    try:main(a.archives,sel)
    except Exception as error:
        if OUT.exists():(OUT/'FAILURE.json').write_text(json.dumps({'kernel_verdict':'NOT_ACCEPTED','scope':gen.scope(sel),'error':str(error),'completed_steps':list(common.runner.STEPS)},indent=2)+'\n')
        raise
