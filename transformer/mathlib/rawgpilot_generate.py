"""One closed endpoint G row; production canonical parsing is public Actions only."""
import json
import sys
from rawpilot_data import HERE, sha
from rawpilot_generate import cloud_only, source
from rawcufull_generate import literal_vector
from rawpacked_data import expected_coefficients
from rawcu_restore import require, digest

PREFIX='TransformerBridge.RawCorrespondence.GPilotGenerated'
NS='TransformerBridge.RawCorrespondence.GPilotCanonical'
CU='TransformerBridge.RawCorrespondence.CUFullGenerated'
CUNS='TransformerBridge.RawCorrespondence.CUFullCanonical'
DECLARATIONS={'Parameters':['gInput','frozenG','Ko','input_bound'],
 'Representative':['representative_G_zero'],'PackedG':['target_bound','carry_bound','packed_cert'],
 'Row':['g_eq','G_row'],'Control':['changedWeights','changed_wout','changed_G','changed_G_ne']}
PRE='open TransformerBridge.RawPilot TransformerBridge.RawPacked TransformerBridge.RawCorrespondence TransformerBridge.RawPackedPilot '+CUNS+'\n\n'

def endpoint(row):
    require(type(row)is int and row in (0,511),'only G endpoint0 or511');return row

def identities(row):
    suffix=f'.Row{endpoint(row):03d}'
    return PREFIX+suffix,NS+suffix

def scope(row):
    return {'G_rows':[endpoint(row)],'G_components':113,'full_G_field':False,'full_hT':False,'finalraw':False}

def sources(row,Ko):
    endpoint(row);require(type(Ko)is int and Ko>=0,'independent Wout bound')
    prefix,namespace=identities(row)
    bodies={
    'Parameters':([CU+'.Control','TransformerCore.Net.Weights'],
      f'def gInput (d : Fin 128) : Int := weights.Wout {row} d\n\n'
      f'def frozenG (k : Fin 113) : Int := (TransformerBridge.toTables TransformerCore.Net.tab).G {row} k\n\n'
      f'def Ko : Nat := {Ko}\n\n'
      'theorem input_bound (d : Fin 128) : -(Ko : Int) ≤ gInput d ∧ gInput d ≤ Ko := by\n  revert d\n  decide +kernel\n'),
    'Representative':([prefix+'.Parameters'],
      f'theorem representative_G_zero : (weights.rawTables 256).G {row} 0 = frozenG 0 := by\n'
      '  rw [G_of_contract]\n  exact contract_eq_of_packed gInput\n'
      '    (fun d : Fin 128 => fun _ : Fin 1 => weights.U d 0)\n'
      '    (fun d => pack (fun _ : Fin 1 => weights.U d 0)) (fun _ : Fin 1 => frozenG 0)\n'
      '    Ko KU (fun _ => rfl) input_bound (fun d _ => urows_bound d 0)\n'
      '    (by decide +kernel) (by decide +kernel) (by decide +kernel) 0\n'),
    'PackedG':([prefix+'.Representative'],
      'theorem target_bound (k : Fin 113) : -((128 * Ko * KU : Nat) : Int) ≤ frozenG k ∧ frozenG k ≤ (128 * Ko * KU : Nat) := by\n  revert k\n  decide +kernel\n\n'
      'theorem carry_bound : 2 * (128 * Ko * KU) < TransformerCore.B := by decide +kernel\n\n'
      'theorem packed_cert : contract gInput packedURows = pack frozenG := by decide +kernel\n'),
    'Row':([prefix+'.PackedG'],
      f'theorem g_eq (k : Fin 113) : (weights.rawTables 256).G {row} k = frozenG k := by\n'
      '  rw [G_of_contract]\n  exact contract_eq_of_packed gInput weights.U packedURows frozenG\n'
      '    Ko KU urows_eq input_bound urows_bound target_bound carry_bound packed_cert k\n\n'
      f'theorem G_row : (TransformerBridge.toTables TransformerCore.Net.tab).G {row} = (weights.rawTables 256).G {row} := by\n'
      '  funext k\n  exact (g_eq k).symm\n'),
    'Control':([prefix+'.Row','TransformerBridge.RawCUUpdate'],
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
    result={prefix+'.'+stage:source(imports,namespace,PRE+body) for stage,(imports,body) in bodies.items()}
    negative=source([prefix+'.Control'],namespace,PRE+f'example : (changedWeights.rawTables 256).G {row} 0 = frozenG 0 := by\n  rw [G_of_contract]\n  decide +kernel\n')
    return result,negative

def production_witness(row):
    endpoint(row);cloud_only();sys.set_int_max_str_digits(0)
    import rawgpilot_restore as cache
    expected={r['module']:r['source_sha256'] for r in cache.pin()['objects']};hashes={};vectors=[]
    # Validate the complete original Wout layout/hash, then select a single row.
    for chunk in range(8):
        module=f'TransformerBridge.RawPacked.Generated.Wout{chunk:03d}';p=HERE/(module.replace('.','/')+'.lean')
        require(sha(p)==expected[module],'canonical Wout source drift');hashes[str(p.relative_to(HERE))]=sha(p)
        text=p.read_text()
        import re
        require(re.findall(r'^def Wout_(\d+) :',text,re.M)==[str(i) for i in range(chunk*64,(chunk+1)*64)],'Wout exact chunk inventory')
        vectors += [literal_vector(text,'Wout_'+str(i),128) for i in range(chunk*64,(chunk+1)*64)]
    require(digest(json.dumps([v for line in vectors for v in line],separators=(',',':')).encode())==expected_coefficients()['Wout']['canonical_flat_integer_json_sha256'],'canonical Wout layout/hash')
    values=vectors[row]
    return {'Ko':max(abs(v) for v in values),'field':'Wout','coordinate':[row,0],'old':values[0],'new':values[0]+1,'delta':1,'nonzero_U_coordinate':[0,0],'output':[row,0],'source_hashes':hashes}

def emit(out,texts,negative=None,record=None,check=False):
    cloud_only()
    for module,text in texts.items():
        p=HERE/(module.replace('.','/')+'.lean')
        if not check:require(not p.exists(),'preexisting G source');p.parent.mkdir(parents=True,exist_ok=True);p.write_text(text)
        require(p.read_text()==text,'G emitted source drift')
    if negative is not None:
        if not check:(out/'changed-Wout.lean').write_text(negative);(out/'generation.json').write_text(json.dumps(record,indent=2,sort_keys=True)+'\n')
        require((out/'changed-Wout.lean').read_text()==negative and json.loads((out/'generation.json').read_text())==record,'G receipt/control drift')
