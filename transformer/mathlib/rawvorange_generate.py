"""Bounded scalar split-basis ranges. Imports and toy source emission never read coefficients."""
import json,re
from rawpilot_data import HERE,sha,layout,SHAPES
from rawpilot_generate import cloud_only,source,vector
from rawvobasis_generate import parse_vectors,canonical_flat
from rawpacked_data import expected_coefficients
from rawcu_restore import require,digest
PREFIX='TransformerBridge.RawCorrespondence.VORangeGenerated'
NS='TransformerBridge.RawCorrespondence.VORangeCanonical'
HELPER='TransformerBridge.RawVOBasis'
OLD='TransformerBridge.RawCorrespondence.VOBasisCanonical'
EXTREME='TransformerBridge.RawCorrespondence.VOBoundaryCanonical.H003Tk113J002'
PRE='open TransformerBridge.RawPilot TransformerBridge.RawCorrespondence TransformerBridge.RawPackedPilot\n\n'
ACCEPTED={(0,'token',0),(0,'position',0),(3,'token',113),(3,'position',2)}

def uint(text):
    require(type(text)is str and re.fullmatch(r'0|[1-9][0-9]*',text)is not None,'closed decimal selector')
    return int(text)

def selection(head=0,kind='token',start=1,count=4):
    require(all(type(v)is int for v in (head,start,count))and 0<=head<4 and kind in ('token','position'),'basis finite head/kind')
    limit=114 if kind=='token'else 3
    require(0<=start<limit and 1<=count<=4 and start+count<=limit,'basis bounded start/count')
    rows=list(range(start,start+count));require(not any((head,kind,i)in ACCEPTED for i in rows),'accepted basis group cannot be reproved')
    return {'head':head,'kind':kind,'start':start,'count':count,'indices':rows}

def scope(sel):
    require(sel==selection(sel['head'],sel['kind'],sel['start'],sel['count']),'exact selector schema')
    return {**sel,'basis_groups':[{'h':sel['head'],'kind':sel['kind'],'index':i}for i in sel['indices']],'V_components_per_group':32,'O_components_per_group':128,'full_basis':False,'fullTI':False,'fullTU':False,'sc':False,'hT':False,'finalraw':False}

def batch(sel):
    scope(sel);return f"Head{sel['head']:03d}{sel['kind'].title()}{sel['start']:03d}_{sel['indices'][-1]:03d}"

def prefix(sel):return PREFIX+'.'+batch(sel)
def namespace(sel):return NS+'.'+batch(sel)
def group(sel,i):return sel['kind'].title()+f'{i:03d}'
def module_namespace(sel,module):
    relative=module.removeprefix(prefix(sel)+'.').split('.')
    return namespace(sel)if relative==['Control']else namespace(sel)+'.'+relative[0]

def site(sel,i):
    return (i,2 if sel['head']==3 else 0)if sel['kind']=='token'else(113 if sel['head']==3 else 0,i)

def inventory(sel):
    modules=[];names={}
    def add(m,decls,ns):modules.append(m);names[m]=[ns+'.'+n for n in decls]
    for i in sel['indices']:
        p=prefix(sel)+'.'+group(sel,i);ns=namespace(sel)+'.'+group(sel,i)
        add(p+'.Parameters',['basisV','basisO'],ns);add(p+'.First',['first_v','first_o'],ns)
        for k in range(2):add(p+f'.V{k:03d}',[f'v_cert_{j:03d}'for j in range(k*16,k*16+16)],ns)
        add(p+'.VAll',['v_eq'],ns)
        for k in range(8):add(p+f'.O{k:03d}',[f'o_cert_{j:03d}'for j in range(k*16,k*16+16)],ns)
        add(p+'.OAll',['o_eq'],ns)
        add(p+'.Assembly',['companionV','companionO','actualV','actualO','actual_v_eq','actual_o_eq'],ns)
    add(prefix(sel)+'.Control',['changedWeights','actual_v_nonzero','changed_WO','changed_ovec','changed_ovec_ne'],namespace(sel))
    return modules,names

def companion(sel):
    # Accepted first/extreme opposite bases; other heads use symbolic ordinary contractions.
    if sel['head']in(0,3):
        ns=OLD if sel['head']==0 else EXTREME
        name='position'if sel['kind']=='token'else'token'
        return ns+'.'+name+'V',ns+'.'+name+'O',ns+'.'+name+'_v_eq',ns+'.'+name+'_o_eq'
    h=sel['head'];field='pos'if sel['kind']=='token'else'tok'
    return f'(fun l => contract (weights.{field} 0) (fun e => weights.WV {h} e l))',f'(fun d => contract companionV (fun l => weights.WO {h} l d))','(fun _ => rfl)','(fun _ => rfl)'

def sources(sel,values,l):
    scope(sel);require(type(values)is list and len(values)==sel['count'],'exact ordered group proposals')
    require(type(l)is int and 0<=l<32,'actual V sensitivity coordinate')
    for i,value in zip(sel['indices'],values):
        require(type(value)is dict and list(value)==['index','V','O']and type(value['index'])is int and value['index']==i,'gap/duplicate/wrong group proposal')
        for k,n in (('V',32),('O',128)):require(type(value[k])is list and len(value[k])==n and all(type(v)is int for v in value[k]),'basis vector shape')
    modules,names=inventory(sel);texts={};h=sel['head'];kind=sel['kind'];field='tok'if kind=='token'else'pos'
    def put(m,ns,imports,body):texts[m]=source(imports,ns,PRE+body)
    for value in values:
        i=value['index'];p=prefix(sel)+'.'+group(sel,i);ns=namespace(sel)+'.'+group(sel,i)
        put(p+'.Parameters',ns,['TransformerBridge.RawCorrespondence.VOBoundaryGenerated.H003Tk113J002.Control','TransformerBridge.RawCorrespondence.VOBasisGenerated.Control'],
            ''.join(f'def basis{k} (i : Fin {n}) : Int := TransformerCore.nth 0 {vector(value[k])} i.val\n\n'for k,n in (('V',32),('O',128))))
        def eq(k,j):return f'contract (weights.{field} {i}) (fun e => weights.WV {h} e {j}) = basisV {j}'if k=='v'else f'contract basisV (fun l => weights.WO {h} l {j}) = basisO {j}'
        put(p+'.First',ns,[p+'.Parameters'],''.join(f'theorem first_{k} : {eq(k,0)} := by decide +kernel\n\n'for k in ('v','o')))
        for block in range(2):put(p+f'.V{block:03d}',ns,[p+'.Parameters'],''.join(f'theorem v_cert_{j:03d} : {eq("v",j)} := by decide +kernel\n\n'for j in range(block*16,block*16+16)))
        put(p+'.VAll',ns,[p+f'.V{k:03d}'for k in range(2)],f'theorem v_eq (l : Fin 32) : contract (weights.{field} {i}) (fun e => weights.WV {h} e l) = basisV l := by\n  fin_cases l\n'+''.join(f'  · exact v_cert_{j:03d}\n'for j in range(32)))
        for block in range(8):put(p+f'.O{block:03d}',ns,[p+'.VAll'],''.join(f'theorem o_cert_{j:03d} : {eq("o",j)} := by decide +kernel\n\n'for j in range(block*16,block*16+16)))
        put(p+'.OAll',ns,[p+f'.O{k:03d}'for k in range(8)],f'theorem o_eq (d : Fin 128) : contract basisV (fun l => weights.WO {h} l d) = basisO d := by\n  fin_cases d\n'+''.join(f'  · exact o_cert_{j:03d}\n'for j in range(128)))
        cv,co,hv,ho=companion(sel);tk,j=site(sel,i)
        vt,vp,ot,op,ht,hp,hot,hop=('basisV','companionV','basisO','companionO','v_eq',hv,'o_eq',ho)if kind=='token'else('companionV','basisV','companionO','basisO',hv,'v_eq',ho,'o_eq')
        body=f'def companionV : Fin 32 → Int := {cv}\n\ndef companionO : Fin 128 → Int := {co}\n\ndef actualV (l : Fin 32) : Int := {vt} l + {vp} l\n\ndef actualO (d : Fin 128) : Int := {ot} d + {op} d\n\n'
        body+=f'theorem actual_v_eq (l : Fin 32) : weights.vvec {h} {tk} {j} l = actualV l :=\n  {HELPER}.vvec_of_basis weights {h} {tk} {j} {vt} {vp} {ht} {hp} l\n\n'
        body+=f'theorem actual_o_eq (d : Fin 128) : weights.ovec {h} {tk} {j} d = actualO d :=\n  {HELPER}.ovec_of_basis weights {h} {tk} {j} {vt} {vp} {ot} {op} {ht} {hp} {hot} {hop} d\n'
        put(p+'.Assembly',ns,[p+'.OAll',HELPER],body)
    i=sel['start'];tk,j=site(sel,i);firstns=namespace(sel)+'.'+group(sel,i);use='open '+firstns+'\n\n'
    body=use+f'def changedWeights : Transformer.Weights := {{ weights with WO := fun a e d => weights.WO a e d + if a = {h} ∧ e = {l} ∧ d = 0 then 1 else 0 }}\n\n'
    body+=f'theorem actual_v_nonzero : actualV {l} ≠ 0 := by decide +kernel\n\ntheorem changed_WO : changedWeights.WO {h} {l} 0 = weights.WO {h} {l} 0 + 1 := by rfl\n\n'
    body+=f'theorem changed_ovec : changedWeights.ovec {h} {tk} {j} 0 = weights.ovec {h} {tk} {j} 0 + actualV {l} := by\n  have ht := {HELPER}.ovec_WO_update weights {h} {tk} {j} {l} 0\n  rw [actual_v_eq] at ht\n  exact ht\n\n'
    body+=f'theorem changed_ovec_ne : changedWeights.ovec {h} {tk} {j} 0 ≠ actualO 0 := by\n  rw [changed_ovec, actual_o_eq]\n  intro h\n  apply actual_v_nonzero\n  omega\n'
    put(prefix(sel)+'.Control',namespace(sel),[prefix(sel)+'.'+group(sel,i)+'.Assembly',HELPER],body)
    negative=source([prefix(sel)+'.Control'],namespace(sel),PRE+use+f'example : changedWeights.ovec {h} {tk} {j} 0 = actualO 0 := by\n  rw [ovec_of_vvec changedWeights {h} {tk} {j} actualV (fun l => actual_v_eq l) 0]\n  decide +kernel\n')
    require(list(texts)==modules,'ordered range module inventory');return texts,negative

def production_witness(sel):
    scope(sel);cloud_only()
    import rawvorange_restore as cache
    expected={o['module']:o['source_sha256']for o in cache.pin()['objects']};hashes={};fields={};coeff=expected_coefficients()
    require(set(coeff)==set(SHAPES),'exact eleven-field coefficient metadata')
    for key in ('tok','pos','WV','WO'):
        axes,rows,width=layout(key);vectors=[]
        require(coeff[key]['shape']==list(SHAPES[key])and coeff[key]['serialized_axes']==list(axes)and coeff[key]['vectors']==rows and coeff[key]['width']==width,'canonical basis layout')
        for start in range(0,rows,64):
            module='TransformerBridge.RawPacked.Generated.'+key+f'{start//64:03d}';path=HERE/(module.replace('.','/')+'.lean')
            require(sha(path)==expected[module],'range canonical source drift');hashes[str(path.relative_to(HERE))]=sha(path)
            vectors+=parse_vectors(path.read_text(),key,start,min(64,rows-start),width)
        require(digest(json.dumps(canonical_flat(key,vectors),separators=(',',':')).encode())==coeff[key]['canonical_flat_integer_json_sha256'],'canonical basis coefficient hash')
        fields[key]=vectors
    h=sel['head'];kind=sel['kind'];values=[]
    for index in sel['indices']:
        v=[sum(fields['tok'if kind=='token'else'pos'][index][e]*fields['WV'][h*32+l][e]for e in range(128))for l in range(32)]
        o=[sum(v[l]*fields['WO'][h*128+d][l]for l in range(32))for d in range(128)]
        values.append({'index':index,'V':v,'O':o})
    tk,j=site(sel,sel['start']);actual=[sum((fields['tok'][tk][e]+fields['pos'][j][e])*fields['WV'][h*32+l][e]for e in range(128))for l in range(32)]
    l=next((i for i,v in enumerate(actual)if v!=0),None);require(l is not None,'no nonzero actual V sensitivity witness');old=fields['WO'][h*128][l]
    return {'selection':sel,'values':values,'l':l,'source_hashes':hashes,'canonical_fields':{k:coeff[k]for k in fields},'negative':{'field':'WO','coordinate':[h,l,0],'old':old,'new':old+1,'delta':1,'actual_V_nonzero_value':actual[l],'actual_output':[h,tk,j,0]}}

def write_sources(out,texts,negative=None,record=None,check=False):
    cloud_only()
    for module,text in texts.items():
        path=HERE/(module.replace('.','/')+'.lean')
        if not check:require(not path.exists(),'preexisting range source');path.parent.mkdir(parents=True,exist_ok=True);path.write_text(text)
        require(path.read_text()==text,'range emitted source drift')
    if negative is not None:
        if not check:(out/'changed-WO.lean').write_text(negative);(out/'generation.json').write_text(json.dumps(record,indent=2,sort_keys=True)+'\n')
        require((out/'changed-WO.lean').read_text()==negative and json.loads((out/'generation.json').read_text())==record,'range control/receipt drift')
