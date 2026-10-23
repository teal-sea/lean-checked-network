"""Fixed h0/j0/tk0 TU113 pilot. Only cloud reads authenticated O/U integer sources."""
import json,re
from rawpilot_data import HERE,sha
from rawpilot_generate import cloud_only,source
from rawcufull_generate import literal_vector
from rawpacked_data import expected_coefficients
from rawcu_restore import require,digest
PREFIX='TransformerBridge.RawCorrespondence.TUPilotGenerated'
NS='TransformerBridge.RawCorrespondence.TUPilotCanonical'
HELPER='TransformerBridge.RawTUUpdate'
HELPER_NAMES=[HELPER+'.contract_update_right',HELPER+'.TU_U_update']
SCOPE={'TU_sites':[{'h':0,'j':0,'tk':0}],'TU_components':113,'full_TU_field':False,'full_hT':False,'finalraw':False}
DECLARATIONS={'Parameters':['frozenTU','input_bound'],'Representative':['representative_TU_zero'],
 'PackedTU':['target_bound','carry_bound','packed_cert'],'Site':['tu_eq','TU_site'],
 'Control':['changedWeights','o_nonzero','changed_u','changed_TU','changed_TU_ne']}
PRE='open TransformerBridge.RawPilot TransformerBridge.RawPacked TransformerBridge.RawCorrespondence TransformerBridge.RawPackedPilot TransformerBridge.RawCorrespondence.CUFullCanonical\n\n'

def sources(d):
    require(type(d)is int and 0<=d<128,'TU sensitivity coordinate')
    bodies={
    'Parameters':(['TransformerBridge.RawCorrespondence.CUFullGenerated.Control','TransformerBridge.RawPacked.Generated.PackedTI','TransformerBridge.RawPacked.Generated.OAll','TransformerCore.Net.Weights'],
      'def frozenTU (k : Fin 113) : Int := (TransformerBridge.toTables TransformerCore.Net.tab).TU 0 0 0 k\n\n'
      'theorem input_bound (e : Fin 128) : -(Ko : Int) ≤ proposedO e ∧ proposedO e ≤ Ko := o_bound e\n'),
    'Representative':([PREFIX+'.Parameters'],
      'theorem representative_TU_zero : (weights.rawTables 256).TU 0 0 0 0 = frozenTU 0 := by\n'
      '  calc\n    (weights.rawTables 256).TU 0 0 0 0 = contract proposedO (fun e => weights.U e 0) :=\n'
      '      TU_of_ovec weights 256 0 0 0 proposedO o_eq (by decide) 0\n'
      '    _ = frozenTU 0 := contract_eq_of_packed proposedO\n'
      '      (fun e : Fin 128 => fun _ : Fin 1 => weights.U e 0)\n'
      '      (fun e => pack (fun _ : Fin 1 => weights.U e 0)) (fun _ : Fin 1 => frozenTU 0)\n'
      '      Ko KU (fun _ => rfl) input_bound (fun e _ => urows_bound e 0)\n'
      '      (by decide +kernel) (by decide +kernel) (by decide +kernel) 0\n'),
    'PackedTU':([PREFIX+'.Representative'],
      'theorem target_bound (k : Fin 113) : -((128 * Ko * KU : Nat) : Int) ≤ frozenTU k ∧ frozenTU k ≤ (128 * Ko * KU : Nat) := by\n  revert k\n  decide +kernel\n\n'
      'theorem carry_bound : 2 * (128 * Ko * KU) < TransformerCore.B := by decide +kernel\n\n'
      'theorem packed_cert : contract proposedO packedURows = pack frozenTU := by decide +kernel\n'),
    'Site':([PREFIX+'.PackedTU'],
      'theorem tu_eq (k : Fin 113) : (weights.rawTables 256).TU 0 0 0 k = frozenTU k := by\n'
      '  exact (TU_of_ovec weights 256 0 0 0 proposedO o_eq (by decide) k).trans\n'
      '    (contract_eq_of_packed proposedO weights.U packedURows frozenTU\n'
      '      Ko KU urows_eq input_bound urows_bound target_bound carry_bound packed_cert k)\n\n'
      'theorem TU_site : (TransformerBridge.toTables TransformerCore.Net.tab).TU 0 0 0 = (weights.rawTables 256).TU 0 0 0 := by\n'
      '  funext k\n  exact (tu_eq k).symm\n'),
    'Control':([PREFIX+'.Site',HELPER],
      f'def changedWeights : Transformer.Weights := {{ weights with U := fun e k => weights.U e k + if e = {d} ∧ k = 0 then 1 else 0 }}\n\n'
      f'theorem o_nonzero : proposedO {d} ≠ 0 := by decide +kernel\n\n'
      f'theorem changed_u : changedWeights.U {d} 0 = weights.U {d} 0 + 1 := by rfl\n\n'
      f'theorem changed_TU : (changedWeights.rawTables 256).TU 0 0 0 0 = (weights.rawTables 256).TU 0 0 0 0 + proposedO {d} := by\n'
      f'  have ht := {HELPER}.TU_U_update weights 256 0 0 0 {d} 0 (by decide)\n'
      '  rw [o_eq] at ht\n  exact ht\n\n'
      'theorem changed_TU_ne : (changedWeights.rawTables 256).TU 0 0 0 0 ≠ frozenTU 0 := by\n'
      '  rw [changed_TU, tu_eq]\n  intro h\n  apply o_nonzero\n  omega\n')}
    texts={PREFIX+'.'+stage:source(imports,NS,PRE+body)for stage,(imports,body)in bodies.items()}
    negative=source([PREFIX+'.Control'],NS,PRE+
      'example : (changedWeights.rawTables 256).TU 0 0 0 0 = frozenTU 0 := by\n'
      '  rw [TU_of_ovec changedWeights 256 0 0 0 proposedO (fun e => o_eq e) (by decide) 0]\n'
      '  decide +kernel\n')
    return texts,negative

def parse_o(text):
    matches=re.findall(r'^def proposedO \(d : Fin 128\) : Int := TransformerCore.nth 0 (\[.*\]) d.val$',text,re.M)
    require(len(matches)==1 and re.findall(r'^def (\w+) ',text,re.M)==['proposedV','proposedO'],'accepted O closed layout')
    return literal_vector('def witness : List Int := '+matches[0]+'\n','witness',128)

def choose_nonzero(values):
    require(type(values)is list and len(values)==128 and all(type(v)is int for v in values),'O128 shape')
    found=next((d for d,v in enumerate(values)if v!=0),None);require(found is not None,'missing nonzero accepted O sensitivity witness');return found

def production_witness():
    cloud_only()
    import rawtupilot_restore as cache
    import rawcu_generate as parser
    expected={r['module']:r['source_sha256']for r in cache.pin()['objects']};hashes={}
    def read(module):
        path=HERE/(module.replace('.','/')+'.lean');require(sha(path)==expected[module],'TU accepted source drift: '+module);hashes[str(path.relative_to(HERE))]=sha(path);return path.read_text()
    values=parse_o(read('TransformerBridge.RawPacked.Generated.Vectors'));d=choose_nonzero(values);columns=[]
    for first,size in ((0,64),(64,49)):columns+=parser.parse_columns(read('TransformerBridge.RawPacked.Generated.U'+str(first//64).zfill(3)),first,size)
    canonical=[columns[k][e]for e in range(128)for k in range(113)]
    require(digest(json.dumps(canonical,separators=(',',':')).encode())==expected_coefficients()['U']['canonical_flat_integer_json_sha256'],'TU original U layout/hash')
    old=columns[0][d]
    return {'d':d,'nonzero_O_value':values[d],'accepted_O_source_sha256':expected['TransformerBridge.RawPacked.Generated.Vectors'],'source_hashes':hashes,
      'negative':{'field':'U','coordinate':[d,0],'old':old,'new':old+1,'delta':1,'output':[0,0,0,0]}}

def write_sources(out,texts,negative=None,record=None,check=False):
    cloud_only()
    for module,text in texts.items():
        path=HERE/(module.replace('.','/')+'.lean')
        if not check:require(not path.exists(),'preexisting TU source');path.parent.mkdir(parents=True,exist_ok=True);path.write_text(text)
        require(path.read_text()==text,'TU emitted source drift')
    if negative is not None:
        if not check:(out/'changed-U.lean').write_text(negative);(out/'generation.json').write_text(json.dumps(record,indent=2,sort_keys=True)+'\n')
        require((out/'changed-U.lean').read_text()==negative and json.loads((out/'generation.json').read_text())==record,'TU negative/record drift')
