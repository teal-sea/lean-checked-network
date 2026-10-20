"""Pure symbolic Fin512 G assembly; no coefficient parsing or row reproving."""
import json
from rawpilot_data import HERE
from rawpilot_generate import cloud_only
from rawcu_restore import require,digest
import rawgrange_generate as ranges
PREFIX='TransformerBridge.RawCorrespondence.GFullGenerated'
NS='TransformerBridge.RawCorrespondence.GFullCanonical'
ENDPOINT='TransformerBridge.RawCorrespondence.GPilotCanonical.Row000'
MODULES=[PREFIX+'.Assembly',PREFIX+'.Control']
NAMES=[NS+'.G_field',NS+'.changed_wout',NS+'.changed_G',NS+'.changed_G_ne']
SCOPE={'G_rows':list(range(512)),'G_components':113,'G_field':False,'full_hT':False,'finalraw':False}

def row_inventory(items):
    result=[{'row':0,'module':'TransformerBridge.RawCorrespondence.GPilotGenerated.Row000.Row','proof':ENDPOINT+'.G_row'}]
    for item in items:
        selected=item['G_rows'];require(selected and all(type(r)is int for r in selected)and selected==ranges.rows_for(selected[0],len(selected)),'G assembly range coverage')
        modules,_,_=ranges.inventory(selected[0],len(selected));require([r['module']for r in item['objects']]==modules,'G assembly range modules')
        _,namespace=ranges.identities(selected[0],len(selected))
        result += [{'row':r,'module':modules[0],'proof':namespace+f'.Row{r:03d}.G_row'}for r in selected]
    result.append({'row':511,'module':'TransformerBridge.RawCorrespondence.GPilotGenerated.Row511.Row','proof':'TransformerBridge.RawCorrespondence.GPilotCanonical.Row511.G_row'})
    require([r['row']for r in result]==list(range(512))and len({r['proof']for r in result})==512,'G exact512 rows/no duplicates')
    return result

def source(imports,body):
    # Use normal compiler defaults; no recursion/heartbeat overrides.
    return ''.join('import '+m+'\n'for m in imports)+'\nnamespace '+NS+'\n\n'+body+'\nend '+NS+'\n'

def sources(items):
    rows=row_inventory(items)
    body='theorem G_field : (TransformerBridge.toTables TransformerCore.Net.tab).G =\n    (TransformerBridge.RawPackedPilot.weights.rawTables 256).G := by\n  funext i\n  fin_cases i\n'
    body+=''.join('  · exact '+r['proof']+'\n'for r in rows)
    assembly=source(['Mathlib','Transformer.Raw','TransformerBridge.Bridge']+list(dict.fromkeys(r['module']for r in rows)),body)
    pre='open TransformerBridge.RawPackedPilot\n\n'
    control=source([MODULES[0],'TransformerBridge.RawCorrespondence.GPilotGenerated.Row000.Control'],pre+
      f'theorem changed_wout : {ENDPOINT}.changedWeights.Wout 0 0 = weights.Wout 0 0 + 1 := {ENDPOINT}.changed_wout\n\n'
      f'theorem changed_G : ({ENDPOINT}.changedWeights.rawTables 256).G 0 0 = (weights.rawTables 256).G 0 0 + weights.U 0 0 := {ENDPOINT}.changed_G\n\n'
      f'theorem changed_G_ne : ({ENDPOINT}.changedWeights.rawTables 256).G 0 0 ≠ (TransformerBridge.toTables TransformerCore.Net.tab).G 0 0 := {ENDPOINT}.changed_G_ne\n')
    negative=source([MODULES[1]],pre+f'example : ({ENDPOINT}.changedWeights.rawTables 256).G 0 0 = (TransformerBridge.toTables TransformerCore.Net.tab).G 0 0 := by\n  rw [TransformerBridge.RawCorrespondence.G_of_contract]\n  decide +kernel\n')
    return dict(zip(MODULES,[assembly,control])),negative

def emit(out,items,check=False):
    cloud_only();texts,negative=sources(items)
    record={'scope':SCOPE,'modules':MODULES,'declarations':NAMES,'row_inventory':row_inventory(items),'outputs':{m.replace('.','/')+'.lean':digest(s.encode())for m,s in texts.items()},'negative_sha256':digest(negative.encode()),'negative':{'field':'Wout','coordinate':[0,0],'delta':1,'accepted_endpoint':ENDPOINT,'frozen_target':'(TransformerBridge.toTables TransformerCore.Net.tab).G 0 0'},'kernel_verdict':'KERNEL_NOT_RUN'}
    for module,text in texts.items():
        path=HERE/(module.replace('.','/')+'.lean')
        if not check:require(not path.exists(),'preexisting full G source');path.parent.mkdir(parents=True,exist_ok=True);path.write_text(text)
        require(path.read_text()==text,'G symbolic assembly source drift')
    if not check:(out/'changed-Wout.lean').write_text(negative);(out/'generation.json').write_text(json.dumps(record,indent=2,sort_keys=True)+'\n')
    require((out/'changed-Wout.lean').read_text()==negative and json.loads((out/'generation.json').read_text())==record,'G full control/receipt drift')
    require({str(p.relative_to(HERE))for p in (HERE/PREFIX.replace('.','/')).rglob('*.lean')}==set(record['outputs']),'G full source inventory')
    return record
