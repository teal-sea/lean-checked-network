"""Canonical indexed row theorem and selected declarations, shared by runner/controls."""
from pathlib import Path

HERE = Path(__file__).resolve().parent


def checks_source():
    text = '\n'.join(f'import TransformerCore.Net.CachedPair0_{b}' for b in range(113))
    text += '\nimport TransformerBridge.Row0Compat\n\nnamespace TransformerBridge\n\n'
    text += 'set_option maxRecDepth 100000\nset_option maxHeartbeats 4000000\n\n'
    text += ('theorem row0_fastCheck (b : Fin 113) :\n'
             '    TransformerCore.fastCheck TransformerCore.Net.cfg TransformerCore.Net.tab\n'
             '      TransformerCore.Net.bnd TransformerCore.Net.E2 0 b = true := by\n'
             '  fin_cases b\n')
    text += ''.join(f'  · exact TransformerCore.Net.Cached.cached_pilot_0_{b}\n' for b in range(113))
    return text + '\nend TransformerBridge\n'


def check_branches(path):
    if path.read_text() != checks_source():
        raise ValueError('ROW0 explicit indexed import/branch coverage differs')


BASE_AXIOMS = [
    'TransformerCore.fastCheck_correct',
    'TransformerCore.cachedHeadPk_map', 'TransformerCore.cachedFastCheck_pack',
    'TransformerCore.cachedFastCheck_eq', 'TransformerCore.PackedTab.eq_of_fields',
    'TransformerCore.packed_cons_of', 'TransformerCore.nth_pkI_map', 'TransformerCore.nth_pkI_map₂',
    *('TransformerCore.CachedFixture.' + n for n in
      ('empty', 'negative', 'signed', 'default_inner', 'default_outer', 'empty_vector', 'arbitrary_indices')),
    'TransformerCore.Net.tables_ok', 'TransformerCore.Net.G_length', 'TransformerCore.Net.colSums_ok',
    'TransformerBridge.expFix_eq', 'TransformerBridge.logits_nth_eq', 'TransformerBridge.hA_of_fastCheck',
    'TransformerBridge.cfg_eq_of_fields', 'TransformerBridge.row0_cfg', 'TransformerBridge.row0_E2',
    'TransformerBridge.row0_fastCheck', 'TransformerBridge.row0_integer_margin',
    'Transformer.real_model_adds_mod_113_pointwise',
    'Transformer.clamp_chosen', 'Transformer.deltaBound_chosen', 'Transformer.Ebound_chosen',
]
ANALYTIC = ['Transformer.ExpFix', 'Transformer.Program', 'Transformer.Logits', 'Transformer.Compose']


def selected(receipt, real=False):
    names = [*BASE_AXIOMS, *(n.replace('Transformer.', 'TransformerCore.', 1) for n in receipt['axioms'])]
    if real:
        from check_bounds_audit import EXPECTED
        names.extend(n for n in EXPECTED if n not in names)
        names.append('TransformerBridge.row0_mq_argmax')
    if len(names) != len(set(names)):
        raise ValueError('duplicate selected axiom name')
    return names
