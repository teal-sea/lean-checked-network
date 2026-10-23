"""At most four raw G rows in one production module. Cloud-only canonical witnesses."""
import json,re,sys
from rawpilot_data import HERE,sha
from rawpilot_generate import cloud_only,source
from rawcufull_generate import literal_vector
from rawpacked_data import expected_coefficients
from rawcu_restore import require,digest
PREFIX='TransformerBridge.RawCorrespondence.GRangeGenerated'
NS='TransformerBridge.RawCorrespondence.GRangeCanonical'
CU='TransformerBridge.RawCorrespondence.CUFullGenerated'
CUNS='TransformerBridge.RawCorrespondence.CUFullCanonical'
PRE='open TransformerBridge.RawPilot TransformerBridge.RawPacked TransformerBridge.RawCorrespondence TransformerBridge.RawPackedPilot '+CUNS+'\n\n'
ROW_NAMES=['gInput','frozenG','Ko','input_bound','representative_G_zero','target_bound','carry_bound','packed_cert','g_eq','G_row']
CONTROL_NAMES=['changedWeights','changed_wout','changed_G','changed_G_ne']
def rows_for(start,count):
    require(type(start)is int and type(count)is int and 1<=start<=510 and 1<=count<=4 and start+count<=511,'G range requires rows1..510,count1..4')
    return list(range(start,start+count))
def scope(start,count):return {'G_rows':rows_for(start,count),'G_components':113,'full_G_field':False,'full_hT':False,'finalraw':False}
def identities(start,count):
    rows=rows_for(start,count);tag=f'.Rows{rows[0]:03d}_{rows[-1]:03d}';return PREFIX+tag,NS+tag
def inventory(start,count):
    rows=rows_for(start,count);prefix,namespace=identities(start,count)
    return [prefix+'.Batch',prefix+'.Control'],[namespace+f'.Row{r:03d}.'+n for r in rows for n in ROW_NAMES],[namespace+'.'+n for n in CONTROL_NAMES]
def _row_bodies(row,Ko):
    bodies={
    'Parameters':(
      f'def gInput (d : Fin 128) : Int := weights.Wout {row} d\n\n'
      f'def frozenG (k : Fin 113) : Int := (TransformerBridge.toTables TransformerCore.Net.tab).G {row} k\n\n'
      f'def Ko : Nat := {Ko}\n\n'
      'theorem input_bound (d : Fin 128) : -(Ko : Int) ≤ gInput d ∧ gInput d ≤ Ko := by\n  revert d\n  decide +kernel\n'),
    'Representative':(
      f'theorem representative_G_zero : (weights.rawTables 256).G {row} 0 = frozenG 0 := by\n'
      '  rw [G_of_contract]\n  exact contract_eq_of_packed gInput\n'
      '    (fun d : Fin 128 => fun _ : Fin 1 => weights.U d 0)\n'
      '    (fun d => pack (fun _ : Fin 1 => weights.U d 0)) (fun _ : Fin 1 => frozenG 0)\n'
      '    Ko KU (fun _ => rfl) input_bound (fun d _ => urows_bound d 0)\n'
      '    (by decide +kernel) (by decide +kernel) (by decide +kernel) 0\n'),
    'PackedG':(
      'theorem target_bound (k : Fin 113) : -((128 * Ko * KU : Nat) : Int) ≤ frozenG k ∧ frozenG k ≤ (128 * Ko * KU : Nat) := by\n  revert k\n  decide +kernel\n\n'
      'theorem carry_bound : 2 * (128 * Ko * KU) < TransformerCore.B := by decide +kernel\n\n'
      'theorem packed_cert : contract gInput packedURows = pack frozenG := by decide +kernel\n'),
    'Row':(
      f'theorem g_eq (k : Fin 113) : (weights.rawTables 256).G {row} k = frozenG k := by\n'
      '  rw [G_of_contract]\n  exact contract_eq_of_packed gInput weights.U packedURows frozenG\n'
      '    Ko KU urows_eq input_bound urows_bound target_bound carry_bound packed_cert k\n\n'
      f'theorem G_row : (TransformerBridge.toTables TransformerCore.Net.tab).G {row} = (weights.rawTables 256).G {row} := by\n'
      '  funext k\n  exact (g_eq k).symm\n'),
    'Control':(
      f'def changedWeights : Transformer.Weights := {{ weights with Wout := fun i d => weights.Wout i d + if i = {row} ∧ d = 0 then 1 else 0 }}\n\n'
      f'theorem changed_wout : changedWeights.Wout {row} 0 = weights.Wout {row} 0 + 1 := by rfl\n\n'
      f'theorem changed_G : (changedWeights.rawTables 256).G {row} 0 = (weights.rawTables 256).G {row} 0 + weights.U 0 0 := by\n'
      f'  have hi : changedWeights.Wout {row} = (fun d : Fin 128 => weights.Wout {row} d + if d = 0 then 1 else 0) := by\n'
      '    funext d\n    simp [changedWeights]\n'
      '  have hU : changedWeights.U = weights.U := rfl\n'
      f'  have hc := G_of_contract changedWeights 256 {row} 0\n  rw [hi, hU] at hc\n'
      '  calc\n'
      f'    (changedWeights.rawTables 256).G {row} 0 = contract (fun d => weights.Wout {row} d + if d = 0 then 1 else 0) (fun d => weights.U d 0) := hc\n'
      f'    _ = contract (weights.Wout {row}) (fun d => weights.U d 0) + weights.U 0 0 := TransformerBridge.RawCUUpdate.contract_update _ _ 0\n'
      f'    _ = (weights.rawTables 256).G {row} 0 + weights.U 0 0 := congrArg (fun value : Int => value + weights.U 0 0) (G_of_contract weights 256 {row} 0).symm\n\n'
      f'theorem changed_G_ne : (changedWeights.rawTables 256).G {row} 0 ≠ frozenG 0 := by\n'
      '  rw [changed_G, g_eq]\n  intro h\n  apply '+CUNS+'.u_nonzero\n  omega\n')}
    return bodies

def batch_sources(start,count,bounds):
    rows=rows_for(start,count)
    require(type(bounds)is dict and all(type(r)is int for r in bounds) and list(bounds)==rows and all(type(v)is int and v>=0 for v in bounds.values()),'G exact ordered row/bound inventory')
    modules,_,_=inventory(start,count);_,namespace=identities(start,count);body=PRE
    for row in rows:
        pieces=_row_bodies(row,bounds[row]);body+=f'namespace Row{row:03d}\n\n'
        body+='\n'.join(pieces[stage]for stage in ('Parameters','Representative','PackedG','Row'))
        body+=f'\nend Row{row:03d}\n\n'
    control=PRE+f'open {namespace}.Row{start:03d}\n\n'+_row_bodies(start,bounds[start])['Control']
    negative=PRE+f'open {namespace}.Row{start:03d}\n\n'+f'example : (changedWeights.rawTables 256).G {start} 0 = frozenG 0 := by\n  rw [G_of_contract]\n  decide +kernel\n'
    return dict(zip(modules,[source([CU+'.Control','TransformerCore.Net.Weights'],namespace,body),source([modules[0],'TransformerBridge.RawCUUpdate'],namespace,control)])),source([modules[1]],namespace,negative)

def production_witness(start,count):
    rows=rows_for(start,count);cloud_only();sys.set_int_max_str_digits(0)
    import rawgrange_restore as cache
    expected={r['module']:r['source_sha256']for r in cache.pin()['objects']};hashes={};vectors=[]
    for chunk in range(8):
        module=f'TransformerBridge.RawPacked.Generated.Wout{chunk:03d}';path=HERE/(module.replace('.','/')+'.lean')
        require(sha(path)==expected[module],'G canonical Wout source drift');hashes[str(path.relative_to(HERE))]=sha(path);text=path.read_text()
        require(re.findall(r'^def Wout_(\d+) :',text,re.M)==[str(i)for i in range(chunk*64,(chunk+1)*64)],'G Wout closed chunk')
        vectors += [literal_vector(text,'Wout_'+str(i),128)for i in range(chunk*64,(chunk+1)*64)]
    require(digest(json.dumps([v for row in vectors for v in row],separators=(',',':')).encode())==expected_coefficients()['Wout']['canonical_flat_integer_json_sha256'],'G canonical Wout layout/hash')
    return {'bounds':{str(r):max(abs(v)for v in vectors[r])for r in rows},'source_hashes':hashes,'negative':{'field':'Wout','coordinate':[start,0],'old':vectors[start][0],'new':vectors[start][0]+1,'delta':1,'nonzero_U_coordinate':[0,0],'output':[start,0]}}

def check_declarations(module,expected):
    text=(HERE/(module.replace('.','/')+'.lean')).read_text();stack=[];found=[]
    for line in text.splitlines():
        match=re.fullmatch(r'namespace ([A-Za-z0-9_.]+)',line)
        if match:stack.append(match[1]);continue
        match=re.fullmatch(r'end ([A-Za-z0-9_.]+)',line)
        if match:require(stack and stack.pop()==match[1],'G namespace closure');continue
        match=re.match(r'^(?:def|theorem) (\w+)\b',line)
        if match:require(stack,'G declaration outside namespace');found.append('.'.join(stack)+'.'+match[1])
    require(not stack and found==expected and len(set(found))==len(found),'G exact qualified declaration inventory')

def emit(out,start,count,check=False):
    rows=rows_for(start,count);cloud_only();witness=production_witness(start,count)
    texts,negative=batch_sources(start,count,{r:witness['bounds'][str(r)]for r in rows});modules,names,controls=inventory(start,count)
    record={'scope':scope(start,count),'witness':witness,'modules':modules,'declarations':names+controls,'outputs':{m.replace('.','/')+'.lean':digest(s.encode())for m,s in texts.items()},'negative_sha256':digest(negative.encode()),'kernel_verdict':'KERNEL_NOT_RUN'}
    for module,text in texts.items():
        path=HERE/(module.replace('.','/')+'.lean')
        if not check:require(not path.exists(),'preexisting G batch source');path.parent.mkdir(parents=True,exist_ok=True);path.write_text(text)
        require(path.read_text()==text,'G batch source drift')
    if not check:(out/'changed-Wout-range.lean').write_text(negative);(out/'generation.json').write_text(json.dumps(record,indent=2,sort_keys=True)+'\n')
    require((out/'changed-Wout-range.lean').read_text()==negative and json.loads((out/'generation.json').read_text())==record,'G batch generation/control drift')
    actual={str(p.relative_to(HERE))for p in (HERE/PREFIX.replace('.','/')).rglob('*.lean')};require(actual==set(record['outputs']),'G batch closed source inventory')
    return record
