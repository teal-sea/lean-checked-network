"""Independent sparse evaluator, read directly from LEXNET01, with exact dyadics.

The fast path uses integers when a layer's affine output is integral. Half-integer
threshold biases are handled by doubling the entire affine expression before
clipping; division must be exact or falls back to Fraction. No C/kernel parsing.
"""
from fractions import Fraction
from pathlib import Path
import math, struct

ROOT = Path(__file__).resolve().parent
WEIGHTS = ROOT / 'upstream/lexnet/lexnet_weights.bin'

class Model:
    def __init__(self, path=WEIGHTS):
        blob = Path(path).read_bytes(); pos = 8
        assert blob[:8] == b'LEXNET01'
        def ints(n=1):
            nonlocal pos
            v = struct.unpack_from('<' + 'q'*n, blob, pos); pos += 8*n
            return list(v) if n != 1 else v[0]
        def nums(n):
            nonlocal pos
            v = struct.unpack_from('<' + 'd'*n, blob, pos); pos += 8*n
            return [x if math.isinf(x) else (int(x) if x.is_integer() else Fraction(x)) for x in v]
        self.nf, self.nfs, self.nfo, self.nbs, self.nc, self.hc = ints(6)
        self.emb = [nums(self.nf) for _ in range(128)]
        def cell():
            layers = []
            for _ in range(ints()):
                r, c, s = ints(3)
                W = [nums(c) for _ in range(r)]
                b, hi = nums(r), nums(r)
                skip = [ints() for _ in range(s)]
                layers.append(dict(W=W, b=b, hi=hi, skip=skip, cols=c))
            return layers
        self.fwd, self.bwd = cell(), cell()
        self.fs = [ints() for _ in range(self.nfs)]
        self.fo = [ints() for _ in range(self.nfo)]
        self.bs = [ints() for _ in range(self.nbs)]
        self.h0 = nums(self.nfs)
        self.head = [nums(self.hc) for _ in range(self.nc)]
        self.hb = nums(self.nc)
        self.head2 = [[int(2*w) for w in row] for row in self.head]
        self.hb2 = [int(2*b) for b in self.hb]
        assert pos == len(blob)
        self.forward = self.compile_cell(self.fwd)
        self.backward = self.compile_cell(self.bwd)

    @staticmethod
    def compile_cell(layers):
        # Generate Python straight from sparse weight rows, retaining all operations.
        # At most /2 is needed in any affine expression; half is exact for odd ints.
        lines = ['def cell(v):']
        for l in layers:
            lines.append('    v = [')
            for row, b, hi in zip(l['W'], l['b'], l['hi']):
                den = max(Fraction(x).denominator for x in row + [b])
                assert den in (1, 2)
                expr = str(int(b * den))
                for i, x in enumerate(row):
                    if x: expr += f' + ({int(x*den)}) * v[{i}]'
                if den == 2: expr = f'half({expr})'
                upper = '' if math.isinf(hi) else f', {int(hi)}'
                expr = f'max(0, {expr})'
                if upper: expr = f'min({int(hi)}, {expr})'
                lines.append('        ' + expr + ',')
            lines += [f'        v[{i}],' for i in l['skip']]
            lines.append('    ]')
        lines.append('    return v')
        scope = {'half': lambda x: x//2 if isinstance(x, int) and x%2 == 0 else Fraction(x, 2)}
        exec('\n'.join(lines), scope)
        return scope['cell']

    def features(self, data):
        h = self.h0[:]; result = []
        for c in data:
            v = self.forward(self.emb[min(c,127)] + h)
            h = [v[i] for i in self.fs]
            result.append([v[i] for i in self.fo])
        return result

    def classes(self, data):
        feats = self.features(data); r = [0]*self.nbs; out = []
        for f in reversed(feats):
            v = self.backward(f + r)
            r = [v[i] for i in self.bs]
            logits = [b + sum(w*x for w,x in zip(row,v) if w)
                      for row,b in zip(self.head2,self.hb2)]
            out.append(max(range(self.nc), key=logits.__getitem__))
        return bytes(reversed(out))

if __name__ == '__main__':
    import sys
    m = Model()
    if len(sys.argv) > 1:
        print(''.join('0123456789A'[c] for c in m.classes(Path(sys.argv[1]).read_bytes())))
    else:
        print('h0', m.h0, 'fs',m.fs,'fo',m.fo,'bs',m.bs)
        for cell in ('fwd','bwd'):
            for li,l in enumerate(getattr(m,cell)):
                print(cell,li,'half weights',[(r,c,w) for r,row in enumerate(l['W']) for c,w in enumerate(row) if isinstance(w,Fraction)],'half biases',[(r,b) for r,b in enumerate(l['b']) if isinstance(b,Fraction)])
        print('embedding rows:',m.emb)
