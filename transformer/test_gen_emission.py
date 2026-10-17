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


# ---- the bounds layer: tables_ok as one kernel check per vector plus an assembly proof -------------------------
# Cheap and Lean-free: the emitted B/*.lean, Table.lean and Cols.lean must be mutually consistent (every theorem the
# assembly uses is emitted exactly once, with the right numeral and size), and the committed ones must be what the
# generator emits from the committed data (so the generator, not a hand edit, is the source).

def emit_bounds(heads=4, ntok=3, nG=5, ncol=2):
    tb = {"TI0": [[[1]] * ntok] * heads, "G": [[1] * ncol] * nG, "kTI": 11, "kCI": 12, "kTU": 13, "kCU": 14, "kG": 15}
    root = Path(tempfile.mkdtemp())
    mods = g.write_bounds(root, "Net", tb)
    g.write_table(root, "Net", tb)
    return root, mods


def bounds_problems(root, mods, ks, ntok, nG, ncol, heads=4):
    bad = []
    files = {m: (root / (m.replace(".", "/") + ".lean")).read_text() for m in mods}
    table = (root / "Table.lean").read_text()
    cols = (root / "Cols.lean").read_text()
    defined = {}
    for m, text in files.items():
        for name in re.findall(r"^theorem (ok_\w+) :", text, re.M):
            if name in defined:
                bad.append(f"{name} defined in {defined[name]} and {m}")
            defined[name] = m
    # every theorem Table.lean mentions is emitted, and every module Table.lean imports is one of the B modules
    used = set(re.findall(r"\b(ok_\w+)\b", table))
    for u in sorted(used - set(defined)):
        bad.append(f"Table.lean uses {u}, which no B module defines")
    imported = set(re.findall(r"^import Transformer\.Net\.(B\.\w+)$", table, re.M))
    if imported != set(mods):
        bad.append(f"Table.lean imports {sorted(imported)}, B modules are {sorted(mods)}")
    # per-vector theorems: right size numeral, one per vector, each decided by the kernel
    sizes = {"TI0": (512, ks["kTI"]), "TI1": (512, ks["kTI"]), "TU0": (113, ks["kTU"]), "TU1": (113, ks["kTU"])}
    for key, (n, k) in sizes.items():
        for h in range(heads):
            for t in range(ntok):
                want = f"theorem ok_{key}_{h}_{t} : vecOk {n} {k} {key}_{h}_{t} = true := by decide +kernel"
                if not any(want in files[m] for m in mods):
                    bad.append(f"missing: {want}")
    for i in range(nG):
        want = f"theorem ok_G_{i} : vecOk 113 {ks['kG']} G_{i} = true := by decide +kernel"
        if want not in files["B.G"]:
            bad.append(f"missing: {want}")
    for want in (f"theorem ok_CI : vecOk 512 {ks['kCI']} CI", f"theorem ok_CU : vecOk 113 {ks['kCU']} CU"):
        if want not in files["B.Misc"]:
            bad.append(f"missing: {want}")
    # no monolithic evaluation, no forbidden construct anywhere
    if re.search(r"tablesOk tab bnd = true := by", table):
        bad.append("Table.lean evaluates tablesOk directly")
    for text in list(files.values()) + [table, cols]:
        if re.search(r"sorry|native_decide|^\s*axiom |opaque |implemented_by|extern|skipKernelTC|decide \+native", text, re.M):
            bad.append("forbidden construct emitted")
    nchain = len(re.findall(r"refine all_cons_of \(vecOk 113 %d\) G_\d+ _ ok_G_\d+ \?_" % ks["kG"], files["B.G"]))
    if nchain != nG:
        bad.append(f"G chain has {nchain} steps, expected {nG}")
    if len(re.findall(r"theorem ok_col_\d+ :", cols)) != ncol:
        bad.append("wrong number of column certificates")
    if f"≤ {g.G_COL_BOUND}" not in cols or g.G_COL_BOUND != 17767350:
        bad.append("G column bound is not 8774 * 2025 = 17767350")
    return bad


KS = {"kTI": 11, "kCI": 12, "kTU": 13, "kCU": 14, "kG": 15}
ROOT, MODS = emit_bounds()
assert bounds_problems(ROOT, MODS, KS, 3, 5, 2) == [], bounds_problems(ROOT, MODS, KS, 3, 5, 2)
# red: a table the assembly forgot (one vector theorem deleted) and a bound that disagrees with `bnd` must be flagged
victim = ROOT / "B" / "TI1_2.lean"
victim.write_text(victim.read_text().replace("theorem ok_TI1_2_1 : vecOk 512 11 TI1_2_1 = true := by decide +kernel", ""))
assert any("ok_TI1_2_1" in p for p in bounds_problems(ROOT, MODS, KS, 3, 5, 2)), "a missing vector theorem must be flagged"
assert any("kTI" in p or "vecOk 512 99" in p or "missing" in p for p in bounds_problems(ROOT, MODS, {**KS, "kTI": 99}, 3, 5, 2))
# the committed sources are what the generator emits from them (regeneration is a no-op)
import shutil  # noqa: E402
lean_net = Path(__file__).resolve().parent / "lean" / "Transformer" / "Net"
if (lean_net / "Weights.lean").exists():
    ks, shape = g.sources_shape(lean_net, "Net")
    work = Path(tempfile.mkdtemp())
    shutil.copytree(lean_net, work / "Transformer" / "Net")
    g.write_bounds(work / "Transformer" / "Net", "Net", dict(ks), shape)
    g.write_table(work / "Transformer" / "Net", "Net", shape=shape)
    for f in ["Table.lean", "Cols.lean"] + [f"B/{p.name}" for p in sorted((lean_net / "B").glob("*.lean"))]:
        assert (work / "Transformer" / "Net" / f).read_text() == (lean_net / f).read_text(), f"{f} is not what the generator emits"
    assert bounds_problems(lean_net, ["B." + p.stem for p in sorted((lean_net / "B").glob("*.lean"))], ks,
                           shape["ntok"], shape["nG"], shape["ncol"]) == []
    import hashlib
    for line in (lean_net / "W.sha256").read_text().splitlines():
        digest, rel = line.split("  ")
        assert hashlib.sha256((lean_net / rel).read_bytes()).hexdigest() == digest, f"{rel} differs from W.sha256"
    print(f"ok: committed bounds layer = generator output ({shape}); W data matches W.sha256")
print("ok: bounds layer emission is consistent; a missing vector theorem and a wrong bound are flagged")
