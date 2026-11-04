"""Generate lean/FloatCert.lean: weight tables of the forward cell, backward cell and head (from the
pinned weight file), plus the three input boxes of the range certificate."""
import argparse, pathlib, sys
ROOT = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT))
from exact import Model, WEIGHTS
ap = argparse.ArgumentParser(); ap.add_argument('--weights', default=str(WEIGHTS)); ap.add_argument('--out', default=str(ROOT / 'lean/FloatTables.lean'))
a = ap.parse_args()
m = Model(a.weights)
def I(n):
    assert int(n) == n
    return str(int(n)) if n >= 0 else f'({int(n)})'
def cell(layers):
    out = []
    for l in layers:
        rows = []
        for row, b, hi in zip(l['W'], l['b'], l['hi']):
            terms = ', '.join(f'({i}, {I(w)})' for i, w in enumerate(row) if w)
            h = 'none' if hi == float('inf') else f'some {I(hi)}'
            rows.append(f'⟨{I(b)}, [{terms}], {h}⟩')
        out.append('⟨[' + ',\n    '.join(rows) + '], [' + ', '.join(map(str, l['skip'])) + ']⟩')
    return '[' + ',\n  '.join(out) + ']'
L = ['import lean.Cell', 'namespace Lexnet', 'open Cell', 'set_option maxRecDepth 100000', 'set_option maxHeartbeats 0']
L.append('def fwdCell : List Layer := ' + cell(m.fwd))
L.append('def bwdCell : List Layer := ' + cell(m.bwd))
rows = []
for row, b in zip(m.head2, m.hb2):
    terms = ', '.join(f'({i}, {I(w)})' for i, w in enumerate(row) if w)
    rows.append(f'⟨{I(b)}, [{terms}], none⟩')
L.append('def headRows : List Row := [' + ',\n  '.join(rows) + ']')
L.append('def fsIdx : List Nat := [' + ', '.join(map(str, m.fs)) + ']')
L.append('def foIdx : List Nat := [' + ', '.join(map(str, m.fo)) + ']')
L.append('def bsIdx : List Nat := [' + ', '.join(map(str, m.bs)) + ']')
L.append('end Lexnet')
pathlib.Path(a.out).write_text('\n'.join(L) + '\n')
print('forward layers', len(m.fwd), 'rows', sum(len(l['W']) for l in m.fwd), 'backward rows', sum(len(l['W']) for l in m.bwd))
