"""Regression for the emission of Net/Weights.lean (CI run 38994002308 failed on it): the file must import
Transformer.Fast (where Bnd lives), and in a multi-line structure instance every continuation line must start
at the column of the first field (Lean's sepByIndent), so the first field goes on its own line.
Cheap: no weights, no Lean. Run: python3 -I transformer/test_gen_emission.py"""
import re, sys, tempfile
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import gen_lean_transformer as g


def emit():
    vecs = [[1, -2]] * g.HEADS
    tb = {"sc0": vecs, "sc1": vecs, "sc2": [0], "TI0": [[[1]]] * g.HEADS, "TI1": [[[1]]] * g.HEADS,
          "TU0": [[[1]]] * g.HEADS, "TU1": [[[1]]] * g.HEADS, "TI2": vecs, "TU2": vecs,
          "CI": [1], "CU": [1], "G": [[1]], "kTI": 1, "kCI": 1, "kTU": 1, "kCU": 1, "kG": 1}
    K = {"S": 256, "S2": 1, "f2": 1, "lo": 1, "pw": 1, "cs": [1], "Fpow": 1, "E": 1, "E2": 1}
    root = Path(tempfile.mkdtemp())
    g.write_weights(root, "Net", tb, K, "test")
    return (root / "Weights.lean").read_text()


def problems(text):
    bad = []
    if "import Transformer.Fast" not in text.splitlines():
        bad.append("Weights.lean does not import Transformer.Fast")
    lines = text.splitlines()
    for i, l in enumerate(lines):
        m = re.match(r"def (\w+) : \w+ := \{(.*)$", l)
        if m and not m.group(2).rstrip().endswith("}"):  # multi-line structure instance
            first = m.group(2).strip()
            if first:  # fields start on the brace line: continuation must align with them
                col = l.index("{") + 1 + (len(m.group(2)) - len(m.group(2).lstrip()))
            else:
                nxt = lines[i + 1]
                col = len(nxt) - len(nxt.lstrip())
            j = i + 1
            while j < len(lines) and not lines[j - 1].rstrip().endswith("}"):
                if j > i + 1 or first:
                    ind = len(lines[j]) - len(lines[j].lstrip())
                    if ind < col:
                        bad.append(f"line {j + 1} of `{m.group(1)}` is indented {ind} < first field column {col}")
                j += 1
    return bad


GOOD = emit()
OLD = "import Transformer.Model\ndef tab : Tab := { sc0 := sc0,\n  TU0 := TU0 }\n"
assert problems(GOOD) == [], problems(GOOD)
assert problems(OLD), "the checker must flag the shape that failed in CI"
print("ok: emitted Weights.lean imports Fast and aligns structure fields; the old shape is flagged")
