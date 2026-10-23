"""Extreme h3/token113/position2 V/O and TU113, scalar chunk16 certificates. Cloud-only canonical reads."""
import json,re
from rawpilot_data import HERE,sha,layout,SHAPES
from rawpilot_generate import cloud_only,source,vector
from rawvobasis_generate import parse_vectors,canonical_flat
from rawpacked_data import expected_coefficients
from rawcu_restore import require,digest
PREFIX='TransformerBridge.RawCorrespondence.VOBoundaryGenerated.H003Tk113J002'
NS='TransformerBridge.RawCorrespondence.VOBoundaryCanonical.H003Tk113J002'
HELPER='TransformerBridge.RawVOBasis'
TU_HELPER='TransformerBridge.RawTUUpdate'
SCOPE={'head':3,'token_basis':113,'position_basis':2,'TU_sites':[{'h':3,'j':2,'tk':113}],'V_components':32,'O_components':128,'TU_components':113,'full_basis':False,'fullTU':False,'fullTI':False,'sc':False,'hT':False,'finalraw':False}
PRE='open TransformerBridge.RawPilot TransformerBridge.RawPacked TransformerBridge.RawCorrespondence TransformerBridge.RawPackedPilot TransformerBridge.RawCorrespondence.CUFullCanonical\n\n'
KINDS=[('TokenV','token_v',32),('PositionV','position_v',32),('TokenO','token_o',128),('PositionO','position_o',128)]

TU_DECLARATIONS={'TUParameters':['Kboundary','frozenTU','input_bound'],'Representative':['representative_TU_zero'],'PackedTU':['target_bound','carry_bound','packed_cert'],'Site':['tu_eq','TU_site'],'Control':['changedWeights','o_nonzero','changed_u','changed_TU','changed_TU_ne']}
def inventory():
    modules=[PREFIX+'.Parameters',PREFIX+'.First'];names={modules[0]:['tokenV','positionV','tokenO','positionO'],modules[1]:['first_token_v','first_position_v','first_token_o','first_position_o']}
    for kind,prefix,width in KINDS:
        if kind=='TokenO':modules.append(PREFIX+'.VAll');names[modules[-1]]=['token_v_eq','position_v_eq','v_split_eq']
        for start in range(0,width,16):
            module=PREFIX+'.'+kind+f'{start//16:03d}';modules.append(module);names[module]=[f'{prefix}_cert_{i:03d}'for i in range(start,start+16)]
    modules.append(PREFIX+'.OAll');names[modules[-1]]=['token_o_eq','position_o_eq','boundaryO','boundary_o_eq']
    for stage,decls in TU_DECLARATIONS.items():modules.append(PREFIX+'.'+stage);names[modules[-1]]=decls
    return modules,{m:[NS+'.'+n for n in names[m]]for m in modules}

def sources(values,d,ko):
    require(type(values)is dict and list(values)==['tokenV','positionV','tokenO','positionO'],'closed basis proposal inventory')
    for name,width in (('tokenV',32),('positionV',32),('tokenO',128),('positionO',128)):
        require(type(values[name])is list and len(values[name])==width and all(type(v)is int for v in values[name]),'basis proposal shape')
    require(type(d)is int and 0<=d<128 and type(ko)is int and ko>=0,'boundary sensitivity/bound shape')
    actual=[x+y for x,y in zip(values['tokenO'],values['positionO'])]
    require(actual[d]!=0 and all(abs(v)<=ko for v in actual),'nonzero new O and independent proposed O bound required')
    modules,names=inventory();texts={}
    def put(stage,imports,body):texts[PREFIX+'.'+stage]=source(imports,NS,PRE+body)
    put('Parameters',['TransformerBridge.RawCorrespondence.CUFullGenerated.Control','TransformerCore.Net.Weights'],
        ''.join(f'def {name} (i : Fin {len(v)}) : Int := TransformerCore.nth 0 {vector(v)} i.val\n\n'for name,v in values.items()))
    def equation(kind,i):
        if kind=='TokenV':return f'contract (weights.tok 113) (fun e => weights.WV 3 e {i}) = tokenV {i}'
        if kind=='PositionV':return f'contract (weights.pos 2) (fun e => weights.WV 3 e {i}) = positionV {i}'
        if kind=='TokenO':return f'contract tokenV (fun l => weights.WO 3 l {i}) = tokenO {i}'
        return f'contract positionV (fun l => weights.WO 3 l {i}) = positionO {i}'
    put('First',[PREFIX+'.Parameters'],''.join(f'theorem first_{p} : {equation(k,0)} := by decide +kernel\n\n'for k,p,_ in KINDS))
    for kind,prefix,width in KINDS:
        if kind=='TokenO':
            imports=[PREFIX+'.'+k+f'{chunk:03d}'for k in ('TokenV','PositionV')for chunk in range(2)]
            body=''
            for k,p,base in (('TokenV','token_v','tokenV'),('PositionV','position_v','positionV')):
                raw='tok'if k=='TokenV'else'pos';index=113 if k=='TokenV'else 2
                body+=f'theorem {p}_eq (l : Fin 32) : contract (weights.{raw} {index}) (fun e => weights.WV 3 e l) = {base} l := by\n  fin_cases l\n'
                body+=''.join(f'  · exact {p}_cert_{i:03d}\n'for i in range(32))+'\n'
            body+=f'theorem v_split_eq (l : Fin 32) : weights.vvec 3 113 2 l = tokenV l + positionV l :=\n  {HELPER}.vvec_of_basis weights 3 113 2 tokenV positionV token_v_eq position_v_eq l\n\n'
            put('VAll',imports+[HELPER],body)
        for start in range(0,width,16):
            put(kind+str(start//16).zfill(3),[PREFIX+('.Parameters'if width==32 else'.VAll')],''.join(f'theorem {prefix}_cert_{i:03d} : {equation(kind,i)} := by decide +kernel\n\n'for i in range(start,start+16)))
    body=''
    for prefix,base,vin in (('token_o','tokenO','tokenV'),('position_o','positionO','positionV')):
        body+=f'theorem {prefix}_eq (d : Fin 128) : contract {vin} (fun l => weights.WO 3 l d) = {base} d := by\n  fin_cases d\n'
        body+=''.join(f'  · exact {prefix}_cert_{i:03d}\n'for i in range(128))+'\n'
    body+='def boundaryO (d : Fin 128) : Int := tokenO d + positionO d\n\n'
    body+=f'theorem boundary_o_eq (d : Fin 128) : weights.ovec 3 113 2 d = boundaryO d :=\n  {HELPER}.ovec_of_basis weights 3 113 2 tokenV positionV tokenO positionO token_v_eq position_v_eq token_o_eq position_o_eq d\n'
    put('OAll',[PREFIX+'.'+k+f'{chunk:03d}'for k in ('TokenO','PositionO')for chunk in range(8)],body)
    more,negative=tu_sources(d,ko);texts.update(more)
    require(list(texts)==modules,'boundary ordered complete module inventory')
    return texts,negative

def tu_sources(d,ko):
    require(type(d)is int and 0<=d<128,'TU sensitivity coordinate')
    bodies={
    'TUParameters':([PREFIX+'.OAll'],
      f'def Kboundary : Nat := {ko}\n\n'
      'def frozenTU (k : Fin 113) : Int := (TransformerBridge.toTables TransformerCore.Net.tab).TU 3 2 113 k\n\n'
      'theorem input_bound (e : Fin 128) : -(Kboundary : Int) ≤ boundaryO e ∧ boundaryO e ≤ Kboundary := by\n  revert e\n  decide +kernel\n'),
    'Representative':([PREFIX+'.TUParameters'],
      'theorem representative_TU_zero : (weights.rawTables 256).TU 3 2 113 0 = frozenTU 0 := by\n'
      '  calc\n    (weights.rawTables 256).TU 3 2 113 0 = contract boundaryO (fun e => weights.U e 0) :=\n'
      '      TU_of_ovec weights 256 3 113 2 boundaryO boundary_o_eq (by decide) 0\n'
      '    _ = frozenTU 0 := contract_eq_of_packed boundaryO\n'
      '      (fun e : Fin 128 => fun _ : Fin 1 => weights.U e 0)\n'
      '      (fun e => pack (fun _ : Fin 1 => weights.U e 0)) (fun _ : Fin 1 => frozenTU 0)\n'
      '      Kboundary KU (fun _ => rfl) input_bound (fun e _ => urows_bound e 0)\n'
      '      (by decide +kernel) (by decide +kernel) (by decide +kernel) 0\n'),
    'PackedTU':([PREFIX+'.Representative'],
      'theorem target_bound (k : Fin 113) : -((128 * Kboundary * KU : Nat) : Int) ≤ frozenTU k ∧ frozenTU k ≤ (128 * Kboundary * KU : Nat) := by\n  revert k\n  decide +kernel\n\n'
      'theorem carry_bound : 2 * (128 * Kboundary * KU) < TransformerCore.B := by decide +kernel\n\n'
      'theorem packed_cert : contract boundaryO packedURows = pack frozenTU := by decide +kernel\n'),
    'Site':([PREFIX+'.PackedTU'],
      'theorem tu_eq (k : Fin 113) : (weights.rawTables 256).TU 3 2 113 k = frozenTU k := by\n'
      '  exact (TU_of_ovec weights 256 3 113 2 boundaryO boundary_o_eq (by decide) k).trans\n'
      '    (contract_eq_of_packed boundaryO weights.U packedURows frozenTU\n'
      '      Kboundary KU urows_eq input_bound urows_bound target_bound carry_bound packed_cert k)\n\n'
      'theorem TU_site : (TransformerBridge.toTables TransformerCore.Net.tab).TU 3 2 113 = (weights.rawTables 256).TU 3 2 113 := by\n'
      '  funext k\n  exact (tu_eq k).symm\n'),
    'Control':([PREFIX+'.Site',TU_HELPER],
      f'def changedWeights : Transformer.Weights := {{ weights with U := fun e k => weights.U e k + if e = {d} ∧ k = 0 then 1 else 0 }}\n\n'
      f'theorem o_nonzero : boundaryO {d} ≠ 0 := by decide +kernel\n\n'
      f'theorem changed_u : changedWeights.U {d} 0 = weights.U {d} 0 + 1 := by rfl\n\n'
      f'theorem changed_TU : (changedWeights.rawTables 256).TU 3 2 113 0 = (weights.rawTables 256).TU 3 2 113 0 + boundaryO {d} := by\n'
      f'  have ht := {TU_HELPER}.TU_U_update weights 256 3 113 2 {d} 0 (by decide)\n'
      '  rw [boundary_o_eq] at ht\n  exact ht\n\n'
      'theorem changed_TU_ne : (changedWeights.rawTables 256).TU 3 2 113 0 ≠ frozenTU 0 := by\n'
      '  rw [changed_TU, tu_eq]\n  intro h\n  apply o_nonzero\n  omega\n')}
    texts={PREFIX+'.'+stage:source(imports,NS,PRE+body)for stage,(imports,body)in bodies.items()}
    negative=source([PREFIX+'.Control'],NS,PRE+
      'example : (changedWeights.rawTables 256).TU 3 2 113 0 = frozenTU 0 := by\n'
      '  rw [TU_of_ovec changedWeights 256 3 113 2 boundaryO (fun e => boundary_o_eq e) (by decide) 0]\n'
      '  decide +kernel\n')
    return texts,negative

def production_witness():
    cloud_only()
    import rawvoboundary_restore as cache
    expected={r['module']:r['source_sha256']for r in cache.pin()['objects']};hashes={};fields={};coeff=expected_coefficients()
    require(set(coeff)==set(SHAPES),'original eleven-field coefficient inventory')
    for key in ('tok','pos','WV','WO'):
        axes,rows,width=layout(key);values=[]
        require(coeff[key]['shape']==list(SHAPES[key])and coeff[key]['serialized_axes']==list(axes)and coeff[key]['vectors']==rows and coeff[key]['width']==width,'VO canonical field axes/dimensions')
        for first in range(0,rows,64):
            module='TransformerBridge.RawPacked.Generated.'+key+str(first//64).zfill(3);path=HERE/(module.replace('.','/')+'.lean')
            require(sha(path)==expected[module],'VO actual source drift: '+module);hashes[str(path.relative_to(HERE))]=sha(path)
            values+=parse_vectors(path.read_text(),key,first,min(64,rows-first),width)
        require(digest(json.dumps(canonical_flat(key,values),separators=(',',':')).encode())==coeff[key]['canonical_flat_integer_json_sha256'],'VO canonical field hash/layout')
        fields[key]=values
    tv=[sum(fields['tok'][113][e]*fields['WV'][3*32+l][e]for e in range(128))for l in range(32)]
    pv=[sum(fields['pos'][2][e]*fields['WV'][3*32+l][e]for e in range(128))for l in range(32)]
    to=[sum(tv[l]*fields['WO'][3*128+d][l]for l in range(32))for d in range(128)]
    po=[sum(pv[l]*fields['WO'][3*128+d][l]for l in range(32))for d in range(128)]
    combined=[a+b for a,b in zip(to,po)]
    from rawtupilot_generate import choose_nonzero
    import rawcu_generate as parser
    d=choose_nonzero(combined);ko=max(abs(v)for v in combined);columns=[]
    for first,count in ((0,64),(64,49)):
        module='TransformerBridge.RawPacked.Generated.U'+f'{first//64:03d}';path=HERE/(module.replace('.','/')+'.lean')
        require(sha(path)==expected[module],'boundary U source drift');hashes[str(path.relative_to(HERE))]=sha(path)
        columns+=parser.parse_columns(path.read_text(),first,count)
    require(digest(json.dumps([columns[k][e]for e in range(128)for k in range(113)],separators=(',',':')).encode())==coeff['U']['canonical_flat_integer_json_sha256'],'boundary U canonical hash')
    old=columns[0][d]
    return {'values':{'tokenV':tv,'positionV':pv,'tokenO':to,'positionO':po},'d':d,'ko':ko,'source_hashes':hashes,'canonical_fields':{k:coeff[k]for k in (*fields,'U')},'negative':{'field':'U','coordinate':[d,0],'old':old,'new':old+1,'delta':1,'nonzero_O_coordinate':d,'nonzero_O_value':combined[d],'output':[3,2,113,0]}}

def write_sources(out,texts,negative=None,record=None,check=False):
    cloud_only()
    for module,text in texts.items():
        path=HERE/(module.replace('.','/')+'.lean')
        if not check:require(not path.exists(),'preexisting VO source');path.parent.mkdir(parents=True,exist_ok=True);path.write_text(text)
        require(path.read_text()==text,'VO source drift')
    if negative is not None:
        if not check:(out/'changed-U.lean').write_text(negative);(out/'generation.json').write_text(json.dumps(record,indent=2,sort_keys=True)+'\n')
        require((out/'changed-U.lean').read_text()==negative and json.loads((out/'generation.json').read_text())==record,'VO control/receipt drift')
