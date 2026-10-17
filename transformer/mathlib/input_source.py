"""Source-only extension of the frozen cached evaluator; no packing or evaluation."""
from pathlib import Path

N = 113
CHUNK = 16
NS = 'TransformerCore.Net.Cached'


def require(ok, message):
    if not ok:
        raise ValueError(message)


def coverage(pairs, row=None):
    expected = [[a, b] for a in (range(N) if row is None else [row]) for b in range(N)]
    require(row is None or type(row) is int and 0 <= row < N, 'invalid row')
    require(type(pairs) is list and all(type(p) is list and len(p) == 2 and
            all(type(x) is int for x in p) for p in pairs) and pairs == expected,
            'missing/duplicate/wrong-row/out-of-order input coverage')
    return expected


def chunks(a):
    require(type(a) is int and 1 <= a < N, 'fresh rows must be 1..112')
    return [(f'TransformerCore.Net.InputRows.R{a}C{i // CHUNK}', list(range(i, min(i + CHUNK, N))))
            for i in range(0, N, CHUNK)]


def literal(a, b, wrong_answer=False):
    # Negative control changes the ACTUAL expected Bool literal, retaining all inputs.
    truth = 'false' if wrong_answer else 'true'
    return (f'theorem cached_value_{a}_{b} : cachedFastCheck cfg tab frozenCache bnd E2 {a} {b} = {truth} := by\n'
            '  decide +kernel\n\n' + ('' if wrong_answer else
            f'theorem cached_pilot_{a}_{b} : fastCheck cfg tab bnd E2 {a} {b} = true := by\n'
            f'  rw [← cachedFastCheck_eq cfg tab frozenCache cache_eq bnd E2 {a} {b}]\n'
            f'  exact cached_value_{a}_{b}\n\n'))


def chunk_source(a, bs):
    return ('import TransformerCore.Net.Cached\n\nnamespace ' + NS + '\nopen TransformerCore.Net\n\n'
            'set_option maxRecDepth 100000\nset_option maxHeartbeats 4000000\n\n' +
            ''.join(literal(a, b) for b in bs) + 'end ' + NS + '\n')


def row_sources(a, here):
    result = {m: chunk_source(a, bs) for m, bs in chunks(a)}
    text = ''.join('import ' + m + '\n' for m, _ in chunks(a))
    text += 'import TransformerBridge.Row0Compat\n\nnamespace TransformerBridge\n\n'
    text += 'set_option maxRecDepth 100000\nset_option maxHeartbeats 4000000\n\n'
    text += (f'theorem row{a}_fastCheck (b : Fin 113) :\n'
             '    TransformerCore.fastCheck TransformerCore.Net.cfg TransformerCore.Net.tab\n'
             f'      TransformerCore.Net.bnd TransformerCore.Net.E2 {a} b = true := by\n  fin_cases b\n')
    text += ''.join(f'  · exact {NS}.cached_pilot_{a}_{b}\n' for b in range(N))
    result[f'TransformerBridge.InputRows.Row{a}Checks'] = text + '\nend TransformerBridge\n'
    for suffix in ('', 'Real'):
        text = (here / f'TransformerBridge/Row0{suffix}.lean').read_text()
        text = text.replace('import TransformerBridge.Row0Checks', f'import TransformerBridge.InputRows.Row{a}Checks')
        text = text.replace('import TransformerBridge.Row0\n', f'import TransformerBridge.InputRows.Row{a}\n')
        text = text.replace('row0_', f'row{a}_').replace(f'row{a}_cfg', 'row0_cfg').replace(f'row{a}_E2', 'row0_E2')
        text = text.replace(' 0 b', f' {a} b').replace('first row', f'row {a}').replace('ROW0', f'ROW{a}')
        result[f'TransformerBridge.InputRows.Row{a}{suffix}'] = text
    return result


def all_sources(here):
    text = 'import TransformerBridge.Row0Real\n'
    text += ''.join(f'import TransformerBridge.InputRows.Row{a}Real\n' for a in range(1, N))
    text += '\nnamespace TransformerBridge\n\nset_option maxRecDepth 100000\nset_option maxHeartbeats 4000000\n\n'
    text += ('theorem all_fastCheck (a b : Fin 113) :\n'
             '    TransformerCore.fastCheck TransformerCore.Net.cfg TransformerCore.Net.tab\n'
             '      TransformerCore.Net.bnd TransformerCore.Net.E2 a b = true := by\n  fin_cases a\n')
    text += ''.join(f'  · exact row{a}_fastCheck b\n' for a in range(N))
    text += '\nend TransformerBridge\n'
    result = {'TransformerBridge.InputAllChecks': text}
    for suffix in ('', 'Real'):
        text = (here / f'TransformerBridge/Row0{suffix}.lean').read_text()
        text = text.replace('import TransformerBridge.Row0Checks', 'import TransformerBridge.InputAllChecks')
        text = text.replace('import TransformerBridge.Row0\n', 'import TransformerBridge.InputAll\n')
        text = text.replace('row0_', 'all_').replace('all_cfg', 'row0_cfg').replace('all_E2', 'row0_E2')
        text = text.replace('(b : Fin 113)', '(a b : Fin 113)').replace(' 0 b', ' a b')
        text = text.replace('all_fastCheck b', 'all_fastCheck a b').replace('all_integer_margin b', 'all_integer_margin a b')
        text = text.replace('exactly the first row', 'all input pairs').replace('ROW0 only', 'all input pairs')
        result[f'TransformerBridge.InputAll{suffix}'] = text
    return result


def pair_names(a):
    return [f'{NS}.cached_{kind}_{a}_{b}' for b in range(N) for kind in ('value', 'pilot')]
