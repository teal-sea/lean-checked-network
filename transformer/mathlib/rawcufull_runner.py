#!/usr/bin/env python3
"""U128 assembly then representative/bounded packed CU113, one public field gate."""
import argparse
import json
import os
from pathlib import Path
import re
from rawpilot_data import HERE,sha
from rawpilot_generate import cloud_only
import rawcufull_generate as gen
import rawcufull_restore as cache
import rawcorrespondence_runner as common
from rawurange_runner import snapshot

OUT=HERE/'rawcufull-out'


def main(archives):
    cloud_only();cache.require(os.environ.get('GITHUB_REPOSITORY')=='teal-sea/lean-checked-network' and os.environ.get('LEAN_NUM_THREADS')in('1','2'),'CU public repository/threads')
    cache.require(not OUT.exists() and not(HERE/gen.PREFIX.replace('.','/')).exists(),'preexisting full CU output')
    OUT.mkdir();common.OUT=OUT;common.runner.OUT=OUT;common.runner.STEPS.clear();candidate=snapshot()
    version=common.runner.run('compiler-version',['lake','env','lean','--version'],60)
    cache.require('version 4.35.0' in version and 'commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc' in version,'CU compiler version')
    prefix=Path(common.runner.run('compiler-prefix',['lake','env','lean','--print-prefix'],60).strip());binaries={t:(prefix/'bin'/t).resolve() for t in ('lean','lake','leanchecker')}
    restored=cache.restore(archives,binaries);(OUT/'restored-union.json').write_text(json.dumps(restored,indent=2,sort_keys=True)+'\n')
    fresh=[];names=[];modules=[]
    def compile_audit(module,namespace,expected,label):
        common.check_declarations(module,namespace,expected)
        common.runner.run(label+'-scan',['../lean/scan_sources.sh',module.replace('.','/')+'.lean'],60)
        fresh.append(common.fresh_compile(module));common.audit(label,[module],expected);names.extend(expected);modules.append(module)
    # New generic support is actually compiled/replayed/audited BEFORE any production witness emission.
    compile_audit(gen.HELPER,gen.HELPER,gen.HELPER_NAMES,'update-support')
    items=cache.range_lock();assembly=gen.assembly(items)
    gen.write_sources(OUT,{gen.PREFIX+'.UAll':assembly})
    compile_audit(gen.PREFIX+'.UAll',gen.NS,[gen.NS+'.'+n for n in gen.DECLARATIONS['UAll']],'U128-assembly')
    (OUT/'U128_ASSEMBLED.json').write_text(json.dumps({'kernel_verdict':'KERNEL_ACCEPTED','U_rows':list(range(128)),'U_matrix_finite_index_assembly':True,'CU_field':False,'full_hT':False,'compiled_replayed':fresh[-1]},indent=2)+'\n')
    witness=gen.production_witness();sources,negative=gen.numeric_sources(witness['Kinput'],witness['d'],witness['k'])
    record={'scope':{'U_matrix_finite_index_assembly':True,'CU_components':113,'CU_field':False,'full_hT':False},'witness':witness,
      'modules':list(sources),'declarations':[gen.NS+'.'+n for m in gen.DECLARATIONS if m!='UAll' for n in gen.DECLARATIONS[m]],
      'outputs':{m.replace('.','/')+'.lean':cache.digest(s.encode()) for m,s in {gen.PREFIX+'.UAll':assembly,**sources}.items()},
      'negative_sha256':cache.digest(negative.encode()),'kernel_verdict':'KERNEL_NOT_RUN'}
    gen.write_sources(OUT,sources,negative,record)
    for stage in ('Parameters','Representative','PackedCU','CU','Control'):
        compile_audit(gen.PREFIX+'.'+stage,gen.NS,[gen.NS+'.'+n for n in gen.DECLARATIONS[stage]],stage)
    common.runner.run('negative-scan',['../lean/scan_sources.sh',str(OUT/'changed-bout.lean')],60)
    imports=['TransformerBridge.RawPacked.Generated.Site','TransformerBridge.RawCorrespondence.Generated.Control',
        'TransformerBridge.RawCorrespondenceFixture','TransformerBridge.RawCorrespondenceLinear',cache.previous.boundary.row0.MODULES[-1],cache.previous.row127.MODULES[-1]]
    imports += [cache.batches.inventory(i['U_rows'][0],len(i['U_rows']))[0][-1] for i in items]+[gen.PREFIX+'.Control']
    expected=restored['selected_names']+names
    count=common.audit('complete-CU113',imports,expected)
    common.runner.run('negative-actual-bout-change',['lake','env','lean',str(OUT/'changed-bout.lean')],900,negative=True)
    gen.write_sources(OUT,{gen.PREFIX+'.UAll':assembly,**sources},negative,record,check=True)
    cache.require(snapshot()==candidate,'CU current source drift')
    cache.require({t:sha(p) for t,p in binaries.items()}==cache.pin()['compiler_binary_sha256'],'CU compiler changed')
    cache.require((OUT/'compiled.jsonl').read_bytes()==(OUT/'replayed.jsonl').read_bytes(),'CU compiled/replayed mismatch')
    for r in restored['objects']+fresh:
        stem=r['module'].replace('.','/');cache.require(sha(HERE/(stem+'.lean'))==r['source_sha256'] and cache.stream_sha(HERE/'.lake/build/lib/lean'/(stem+'.olean'))==r['olean_sha256'],'CU final source/object drift')
    throughput={}
    for item in fresh:
        stats={}
        for phase in ('fresh_compile_','fresh_replay_'):
            label=phase+item['module'];rss=re.findall(r'Maximum resident set size \(kbytes\): (\d+)',(OUT/(label+'.time')).read_text());cache.require(len(rss)==1,'CU missing RSS')
            stats[phase]={'seconds':common.runner.STEPS[label]['seconds'],'peak_rss_kib':int(rss[0])}
        throughput[item['module']]=stats
    (OUT/'throughput.json').write_text(json.dumps(throughput,indent=2,sort_keys=True)+'\n')
    (OUT/'CU113_ACCEPTED.json').write_text(json.dumps({'kernel_verdict':'KERNEL_ACCEPTED','U_matrix_finite_index_assembly':True,'CU_field':True,'CU_components':113,'full_hT':False,'full_raw_model_theorem':False,
      'fresh_compiled_replayed':fresh,'restored_objects':restored['objects'],'exact_production_audit_names':count,'negative_actual_bout_change':'KERNEL_DECIDE_FALSE_EXIT_1',
      'generation':record,'candidate':candidate,'compiler_binary_sha256':cache.pin()['compiler_binary_sha256'],'checkpoint_sha256':sha(cache.PIN_PATH),'fanout':'NOT_AUTHORIZED'},indent=2,sort_keys=True)+'\n')


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--archives',type=Path,required=True);args=p.parse_args()
    try:main(args.archives)
    except Exception as error:
        if OUT.exists():(OUT/'FAILURE.json').write_text(json.dumps({'kernel_verdict':'NOT_ACCEPTED','CU_field':False,'full_hT':False,'error':str(error),'completed_steps':list(common.runner.STEPS)},indent=2)+'\n')
        raise
