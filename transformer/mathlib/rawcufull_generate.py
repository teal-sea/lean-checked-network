"""U128 symbolic assembly then CU113 certificates. Production witnesses are cloud-only."""
import json
import re
from rawpilot_data import HERE, sha
from rawpilot_generate import cloud_only, source
from rawpacked_data import expected_coefficients
import rawcu_generate as literal_parser
from rawcu_restore import require, digest

PREFIX = 'TransformerBridge.RawCorrespondence.CUFullGenerated'
NS = 'TransformerBridge.RawCorrespondence.CUFullCanonical'
HELPER = 'TransformerBridge.RawCUUpdate'
HELPER_NAMES = [HELPER + '.contract_update', HELPER + '.CU_bout_update']
DECLARATIONS = {'UAll': ['packedURows', 'KU'] + [f'KU_le_{d:03d}' for d in range(128)] + ['urows_eq', 'urows_bound'],
 'Parameters': ['cuInput', 'frozenCU', 'Kinput', 'input_bound'], 'Representative': ['representative_CU_zero'],
 'PackedCU': ['target_bound', 'carry_bound', 'packed_cert'], 'CU': ['cu_eq', 'CU_field'],
 'Control': ['changedWeights', 'u_nonzero', 'changed_bout', 'changed_CU', 'changed_CU_ne']}


def row_inventory(ranges):
    import rawurange_generate as batches
    rows = [{'row': 0, 'module': 'TransformerBridge.RawCorrespondence.CUGenerated.URow000',
             'ns': 'TransformerBridge.RawCorrespondence.CUCanonical', 'pack': 'packedURow_000', 'bound': 'KU0', 'cert': 'urow_cert_000'}]
    for item in ranges:
        selected = item['U_rows']; batches.rows_for(selected[0], len(selected))
        require(selected == batches.rows_for(selected[0], len(selected)), 'nonconsecutive U range')
        module = batches.inventory(selected[0], len(selected))[0][0]
        rows += [{'row': r, 'module': module, 'ns': batches.NS, 'pack': f'packedURow_{r:03d}', 'bound': f'KU_{r:03d}', 'cert': f'urow_cert_{r:03d}'} for r in selected]
    rows.append({'row':127,'module':'TransformerBridge.RawCorrespondence.UBoundaryGenerated.URow127',
        'ns':'TransformerBridge.RawCorrespondence.UBoundaryCanonical','pack':'packedURow_127','bound':'KU127','cert':'urow_cert_127'})
    require([r['row'] for r in rows] == list(range(128)), 'U128 exact coverage gaps/duplicates/order')
    return rows


def assembly(ranges):
    rows = row_inventory(ranges); imports = list(dict.fromkeys(r['module'] for r in rows))
    q = lambda r, key: r['ns'] + '.' + r[key]
    body = 'open TransformerBridge.RawPacked TransformerBridge.RawPackedPilot\n\n'
    body += 'def packedURows (d : Fin 128) : Int := TransformerCore.nth 0 [' + ', '.join(q(r,'pack') for r in rows) + '] d.val\n\n'
    bound = '0'
    for r in reversed(rows): bound = 'max ' + q(r,'bound') + ' (' + bound + ')'
    body += 'def KU : Nat := ' + bound + '\n\n'
    for r in rows:
        body += f"theorem KU_le_{r['row']:03d} : {q(r,'bound')} ≤ KU := by decide +kernel\n\n"
    body += 'theorem urows_eq (d : Fin 128) : pack (weights.U d) = packedURows d := by\n  fin_cases d\n'
    body += ''.join('  · exact ' + q(r,'cert') + '.1\n' for r in rows)
    body += '\ntheorem urows_bound (d : Fin 128) (k : Fin 113) : -(KU : Int) ≤ weights.U d k ∧ weights.U d k ≤ KU := by\n  fin_cases d\n'
    for r in rows:
        body += f"  · have hb : ({q(r,'bound')} : Int) ≤ (KU : Int) := by exact_mod_cast KU_le_{r['row']:03d}\n"
        body += '    exact ⟨le_trans (neg_le_neg hb) (' + q(r,'cert') + '.2 k).1, le_trans (' + q(r,'cert') + '.2 k).2 hb⟩\n'
    return source(imports, NS, body)


def numeric_sources(Kinput, d, k):
    require(type(Kinput) is int and Kinput >= 0 and type(d) is int and 0 <= d < 128 and type(k) is int and 0 <= k < 113, 'CU witness shape')
    pre='open TransformerBridge.RawPilot TransformerBridge.RawPacked TransformerBridge.RawCorrespondence TransformerBridge.RawPackedPilot\n\n'
    bodies={
    'Parameters': ([PREFIX+'.UAll', 'TransformerBridge.RawCorrespondenceLinear', 'TransformerCore.Net.W.Misc'],
      'def cuInput (d : Fin 128) : Int := (256 : Int)^4 * weights.xhat 113 2 d + weights.bout d\n\n'
      'def frozenCU (k : Fin 113) : Int := TransformerCore.nth 0 TransformerCore.Net.CU k\n\n'
      f'def Kinput : Nat := {Kinput}\n\n'
      'theorem input_bound (d : Fin 128) : -(Kinput : Int) ≤ cuInput d ∧ cuInput d ≤ Kinput := by\n  revert d\n  decide +kernel\n'),
    'Representative': ([PREFIX+'.Parameters'],
      'theorem representative_CU_zero : (weights.rawTables 256).CU 0 = frozenCU 0 := by\n'
      '  rw [CU_of_contract]\n'
      '  exact contract_eq_of_packed cuInput\n'
      '    (fun d : Fin 128 => fun _ : Fin 1 => weights.U d 0)\n'
      '    (fun d => pack (fun _ : Fin 1 => weights.U d 0)) (fun _ : Fin 1 => frozenCU 0)\n'
      '    Kinput KU (fun _ => rfl) input_bound (fun d _ => urows_bound d 0)\n'
      '    (by decide +kernel) (by decide +kernel) (by decide +kernel) 0\n'),
    'PackedCU': ([PREFIX+'.Representative'],
      'theorem target_bound (k : Fin 113) : -((128 * Kinput * KU : Nat) : Int) ≤ frozenCU k ∧ frozenCU k ≤ (128 * Kinput * KU : Nat) := by\n  revert k\n  decide +kernel\n\n'
      'theorem carry_bound : 2 * (128 * Kinput * KU) < TransformerCore.B := by decide +kernel\n\n'
      'theorem packed_cert : contract cuInput packedURows = pack frozenCU := by decide +kernel\n'),
    'CU': ([PREFIX+'.PackedCU','TransformerCore.Net.Weights'],
      'theorem cu_eq (k : Fin 113) : (weights.rawTables 256).CU k = frozenCU k := by\n'
      '  rw [CU_of_contract]\n  exact contract_eq_of_packed cuInput weights.U packedURows frozenCU\n'
      '    Kinput KU urows_eq input_bound urows_bound target_bound carry_bound packed_cert k\n\n'
      'theorem CU_field : (TransformerBridge.toTables TransformerCore.Net.tab).CU = (weights.rawTables 256).CU := by\n'
      '  funext k\n  exact (cu_eq k).symm\n'),
    'Control': ([PREFIX+'.CU',HELPER],
      f'def changedWeights : Transformer.Weights := {{ weights with bout := fun i => weights.bout i + if i = {d} then 1 else 0 }}\n\n'
      f'theorem u_nonzero : weights.U {d} {k} ≠ 0 := by decide +kernel\n\n'
      f'theorem changed_bout : changedWeights.bout {d} = weights.bout {d} + 1 := by rfl\n\n'
      f'theorem changed_CU : (changedWeights.rawTables 256).CU {k} = (weights.rawTables 256).CU {k} + weights.U {d} {k} := by\n'
      f'  exact TransformerBridge.RawCUUpdate.CU_bout_update weights 256 {d} {k}\n\n'
      f'theorem changed_CU_ne : (changedWeights.rawTables 256).CU {k} ≠ frozenCU {k} := by\n'
      '  rw [changed_CU, cu_eq]\n  intro h\n  apply u_nonzero\n  omega\n')}
    sources={PREFIX+'.'+m:source(imports,NS,pre+text) for m,(imports,text) in bodies.items()}
    negative=source([PREFIX+'.Control'],NS,pre+f'example : (changedWeights.rawTables 256).CU {k} = frozenCU {k} := by\n  rw [CU_of_contract]\n  decide +kernel\n')
    return sources,negative


def literal_vector(text,name,width):
    matches=re.findall(r'^def '+re.escape(name)+r' : List Int := (\[.*\])$',text,re.M)
    require(len(matches)==1,'missing/duplicate canonical vector '+name)
    values=[]
    for token in matches[0][1:-1].split(', '):
        m=re.fullmatch(r'\(\.(ofNat|negSucc) (0|[1-9][0-9]*)\)',token)
        require(m is not None,'nonliteral canonical coefficient')
        v=int(m[2]);values.append(v if m[1]=='ofNat' else -v-1)
    require(len(values)==width,'canonical vector dimension');return values


def production_witness():
    cloud_only()
    import rawcu_restore as cache
    expected={r['module']:r['source_sha256'] for r in cache.pin()['packed_objects']}; hashes={}
    def read(module):
        path=HERE/(module.replace('.','/')+'.lean');require(sha(path)==expected[module],'canonical source drift: '+module)
        hashes[str(path.relative_to(HERE))]=sha(path);return path.read_text()
    tok=literal_vector(read('TransformerBridge.RawPacked.Generated.tok001'),'tok_113',128)
    pos=literal_vector(read('TransformerBridge.RawPacked.Generated.pos000'),'pos_2',128)
    bout=literal_vector(read('TransformerBridge.RawPacked.Generated.bout000'),'bout_0',128)
    columns=[]
    for first,size in [(0,64),(64,49)]:
        columns+=literal_parser.parse_columns(read('TransformerBridge.RawPacked.Generated.U'+str(first//64).zfill(3)),first,size)
    flat=[columns[k][d] for d in range(128) for k in range(113)]
    require(digest(json.dumps(flat,separators=(',',':')).encode())==expected_coefficients()['U']['canonical_flat_integer_json_sha256'],'canonical U layout/hash')
    found=next(((d,k) for k in range(113) for d in range(128) if columns[k][d]!=0),None)
    require(found is not None,'no nonzero U sensitivity witness')
    d,k=found;y=[256**4*(tok[i]+pos[i])+bout[i] for i in range(128)]
    return {'Kinput':max(abs(x) for x in y),'d':d,'k':k,'old_bout':bout[d],'new_bout':bout[d]+1,'delta':1,'U_value':columns[k][d],'source_hashes':hashes}


def write_sources(out,sources,negative=None,record=None,check=False):
    cloud_only()
    for module,text in sources.items():
        path=HERE/(module.replace('.','/')+'.lean')
        if not check:
            require(not path.exists(),'preexisting full CU source');path.parent.mkdir(parents=True,exist_ok=True);path.write_text(text)
        require(path.read_text()==text,'full CU source drift')
    if negative is not None:
        if not check:
            (out/'changed-bout.lean').write_text(negative);(out/'generation.json').write_text(json.dumps(record,indent=2,sort_keys=True)+'\n')
        require((out/'changed-bout.lean').read_text()==negative and json.loads((out/'generation.json').read_text())==record,'full CU generation/control drift')
