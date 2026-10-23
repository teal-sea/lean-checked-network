"""One token0+position0 V/O split, scalar chunk16 certificates. Cloud-only canonical reads."""
import json,re
from rawpilot_data import HERE,sha,layout,SHAPES
from rawpilot_generate import cloud_only,source,vector
from rawcufull_generate import literal_vector
from rawpacked_data import expected_coefficients
from rawcu_restore import require,digest
PREFIX='TransformerBridge.RawCorrespondence.VOBasisGenerated'
NS='TransformerBridge.RawCorrespondence.VOBasisCanonical'
HELPER='TransformerBridge.RawVOBasis'
HELPER_NAMES=[HELPER+'.'+n for n in ('vvec_of_basis','ovec_of_basis','contract_update_right','ovec_WO_update')]
SCOPE={'head':0,'token_basis':0,'position_basis':0,'V_components':32,'O_components':128,'full_basis':False,'fullTU':False,'fullTI':False,'sc':False,'hT':False,'finalraw':False}
PRE='open TransformerBridge.RawPilot TransformerBridge.RawCorrespondence TransformerBridge.RawPackedPilot\n\n'
KINDS=[('TokenV','token_v',32),('PositionV','position_v',32),('TokenO','token_o',128),('PositionO','position_o',128)]

def inventory():
    modules=[PREFIX+'.Parameters',PREFIX+'.First'];names={modules[0]:['tokenV','positionV','tokenO','positionO'],modules[1]:['first_token_v','first_position_v','first_token_o','first_position_o']}
    for kind,prefix,width in KINDS:
        if kind=='TokenO':modules.append(PREFIX+'.VAll');names[modules[-1]]=['token_v_eq','position_v_eq','v_split_eq','v_basis_consistency']
        for start in range(0,width,16):
            module=PREFIX+'.'+kind+str(start//16).zfill(3);modules.append(module);names[module]=[f'{prefix}_cert_{i:03d}'for i in range(start,start+16)]
    modules += [PREFIX+'.OAll',PREFIX+'.Control'];names[modules[-2]]=['token_o_eq','position_o_eq','ovec_split_eq','basis_consistency'];names[modules[-1]]=['changedWeights','v_nonzero','basis_nonzero','changed_WO','changed_ovec','changed_ovec_ne']
    return modules,{m:[NS+'.'+n for n in names[m]]for m in modules}

def select_witness(tv,pv):
    require(len(tv)==len(pv)==32 and all(type(x)is int for x in tv+pv),'V32 witness dimensions')
    l=next((i for i in range(32)if tv[i]+pv[i]!=0),None);require(l is not None,'no nonzero actual combined V sensitivity witness')
    return l,'token'if tv[l]!=0 else 'position'

def sources(values,l,basis):
    require(type(values)is dict and list(values)==['tokenV','positionV','tokenO','positionO'],'closed basis proposal inventory')
    for name,width in (('tokenV',32),('positionV',32),('tokenO',128),('positionO',128)):
        require(type(values[name])is list and len(values[name])==width and all(type(v)is int for v in values[name]),'basis proposal shape')
    require(type(l)is int and 0<=l<32 and basis in ('token','position'),'WO sensitivity witness shape')
    require(values['tokenV'][l]+values['positionV'][l]!=0 and values['tokenV'if basis=='token'else'positionV'][l]!=0,'nonzero actual and basis V sensitivity witness required')
    modules,names=inventory();texts={}
    def put(stage,imports,body):texts[PREFIX+'.'+stage]=source(imports,NS,PRE+body)
    put('Parameters',['TransformerBridge.RawPacked.Generated.OAll','TransformerBridge.RawCorrespondence.CUFullGenerated.Control'],
        ''.join(f'def {name} (i : Fin {len(v)}) : Int := TransformerCore.nth 0 {vector(v)} i.val\n\n'for name,v in values.items()))
    def equation(kind,i):
        if kind=='TokenV':return f'contract (weights.tok 0) (fun e => weights.WV 0 e {i}) = tokenV {i}'
        if kind=='PositionV':return f'contract (weights.pos 0) (fun e => weights.WV 0 e {i}) = positionV {i}'
        if kind=='TokenO':return f'contract tokenV (fun l => weights.WO 0 l {i}) = tokenO {i}'
        return f'contract positionV (fun l => weights.WO 0 l {i}) = positionO {i}'
    put('First',[PREFIX+'.Parameters'],''.join(f'theorem first_{p} : {equation(k,0)} := by decide +kernel\n\n'for k,p,_ in KINDS))
    for kind,prefix,width in KINDS:
        if kind=='TokenO':
            imports=[PREFIX+'.'+k+f'{chunk:03d}'for k in ('TokenV','PositionV')for chunk in range(2)]
            body=''
            for k,p,base in (('TokenV','token_v','tokenV'),('PositionV','position_v','positionV')):
                raw='tok'if k=='TokenV'else'pos'
                body+=f'theorem {p}_eq (l : Fin 32) : contract (weights.{raw} 0) (fun e => weights.WV 0 e l) = {base} l := by\n  fin_cases l\n'
                body+=''.join(f'  · exact {p}_cert_{i:03d}\n'for i in range(32))+'\n'
            body+=f'theorem v_split_eq (l : Fin 32) : weights.vvec 0 0 0 l = tokenV l + positionV l :=\n  {HELPER}.vvec_of_basis weights 0 0 0 tokenV positionV token_v_eq position_v_eq l\n\n'
            body+='theorem v_basis_consistency (l : Fin 32) : tokenV l + positionV l = proposedV l := (v_split_eq l).symm.trans (v_eq l)\n'
            put('VAll',imports+[HELPER],body)
        for start in range(0,width,16):
            put(kind+str(start//16).zfill(3),[PREFIX+('.Parameters'if width==32 else'.VAll')],''.join(f'theorem {prefix}_cert_{i:03d} : {equation(kind,i)} := by decide +kernel\n\n'for i in range(start,start+16)))
    body=''
    for prefix,base,vin in (('token_o','tokenO','tokenV'),('position_o','positionO','positionV')):
        body+=f'theorem {prefix}_eq (d : Fin 128) : contract {vin} (fun l => weights.WO 0 l d) = {base} d := by\n  fin_cases d\n'
        body+=''.join(f'  · exact {prefix}_cert_{i:03d}\n'for i in range(128))+'\n'
    body+=f'theorem ovec_split_eq (d : Fin 128) : weights.ovec 0 0 0 d = tokenO d + positionO d :=\n  {HELPER}.ovec_of_basis weights 0 0 0 tokenV positionV tokenO positionO token_v_eq position_v_eq token_o_eq position_o_eq d\n\n'
    body+='theorem basis_consistency (d : Fin 128) : tokenO d + positionO d = proposedO d := (ovec_split_eq d).symm.trans (o_eq d)\n'
    put('OAll',[PREFIX+'.'+k+f'{chunk:03d}'for k in ('TokenO','PositionO')for chunk in range(8)],body)
    base='tokenV'if basis=='token'else'positionV'
    put('Control',[PREFIX+'.OAll',HELPER],
      f'def changedWeights : Transformer.Weights := {{ weights with WO := fun h i d => weights.WO h i d + if h = 0 ∧ i = {l} ∧ d = 0 then 1 else 0 }}\n\n'
      f'theorem v_nonzero : proposedV {l} ≠ 0 := by decide +kernel\n\n'
      f'theorem basis_nonzero : {base} {l} ≠ 0 := by decide +kernel\n\n'
      f'theorem changed_WO : changedWeights.WO 0 {l} 0 = weights.WO 0 {l} 0 + 1 := by rfl\n\n'
      f'theorem changed_ovec : changedWeights.ovec 0 0 0 0 = weights.ovec 0 0 0 0 + proposedV {l} := by\n'
      f'  have h := {HELPER}.ovec_WO_update weights 0 0 0 {l} 0\n  rw [v_eq] at h\n  exact h\n\n'
      'theorem changed_ovec_ne : changedWeights.ovec 0 0 0 0 ≠ proposedO 0 := by\n  rw [changed_ovec, o_eq]\n  intro h\n  apply v_nonzero\n  omega\n')
    negative=source([PREFIX+'.Control'],NS,PRE+
      'example : changedWeights.ovec 0 0 0 0 = proposedO 0 := by\n'
      '  rw [ovec_of_vvec changedWeights 0 0 0 proposedV (fun l => v_eq l) 0]\n  decide +kernel\n')
    require(list(texts)==modules,'VO ordered module inventory')
    return texts,negative

def parse_vectors(text,key,start,count,width):
    require(re.findall(r'^def '+re.escape(key)+r'_(\d+) :',text,re.M)==[str(i)for i in range(start,start+count)],'VO exact canonical chunk declarations')
    return [literal_vector(text,key+'_'+str(i),width)for i in range(start,start+count)]

def canonical_flat(key,rows):
    if key in ('tok','pos'):return [v for row in rows for v in row]
    if key=='WV':return [rows[h*32+l][e]for h in range(4)for e in range(128)for l in range(32)]
    require(key=='WO','VO allowed field');return [rows[h*128+d][l]for h in range(4)for l in range(32)for d in range(128)]

def production_witness():
    cloud_only()
    import rawvobasis_restore as cache
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
    tv=[sum(fields['tok'][0][e]*fields['WV'][l][e]for e in range(128))for l in range(32)]
    pv=[sum(fields['pos'][0][e]*fields['WV'][l][e]for e in range(128))for l in range(32)]
    to=[sum(tv[l]*fields['WO'][d][l]for l in range(32))for d in range(128)]
    po=[sum(pv[l]*fields['WO'][d][l]for l in range(32))for d in range(128)]
    l,basis=select_witness(tv,pv);old=fields['WO'][0][l]
    return {'values':{'tokenV':tv,'positionV':pv,'tokenO':to,'positionO':po},'l':l,'basis':basis,'source_hashes':hashes,'canonical_fields':{k:coeff[k]for k in fields},
      'negative':{'field':'WO','coordinate':[0,l,0],'old':old,'new':old+1,'delta':1,'nonzero_V_coordinate':l,'nonzero_V_value':tv[l]+pv[l],'basis':basis,'basis_value':(tv if basis=='token'else pv)[l],'actual_O_output':[0,0,0,0]}}

def write_sources(out,texts,negative=None,record=None,check=False):
    cloud_only()
    for module,text in texts.items():
        path=HERE/(module.replace('.','/')+'.lean')
        if not check:require(not path.exists(),'preexisting VO source');path.parent.mkdir(parents=True,exist_ok=True);path.write_text(text)
        require(path.read_text()==text,'VO source drift')
    if negative is not None:
        if not check:(out/'changed-WO.lean').write_text(negative);(out/'generation.json').write_text(json.dumps(record,indent=2,sort_keys=True)+'\n')
        require((out/'changed-WO.lean').read_text()==negative and json.loads((out/'generation.json').read_text())==record,'VO control/receipt drift')
