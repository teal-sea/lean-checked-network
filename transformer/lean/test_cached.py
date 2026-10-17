"""Small emission/provenance regression only. No Lean evidence or model simulation."""
import importlib.util
from pathlib import Path
import re
import tempfile

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("gen_cached", HERE / "gen_cached.py")
g = importlib.util.module_from_spec(spec)
spec.loader.exec_module(g)


def check_literals(root, metadata, vectors):
    found = {}
    for rel in metadata["generated"]:
        text = (root / rel).read_text()
        for name, kind, digits in re.findall(
                r"^def p_(\w+) : Int := \(\.(ofNat|negSucc) (\d+)\)$", text, re.M):
            value = int(digits) if kind == "ofNat" else -int(digits) - 1
            assert name not in found
            assert value == g.pack(vectors[name]), name
            assert f"theorem eq_{name} : p_{name} = pkI {name} := by decide +kernel" in text
            found[name] = value
    assert set(found) == set(vectors)


def must_reject(fn):
    try:
        fn()
    except (AssertionError, ValueError, FileNotFoundError):
        return
    raise AssertionError("red control accepted")


with tempfile.TemporaryDirectory() as tmp:
    root = Path(tmp)
    # One entry beyond the unit bound exercises chunk boundaries without large vectors.
    tokens = g.CHUNK + 1
    names = [n for ns in g.groups(heads=1, tokens=tokens, grows=3).values() for n in ns] + ["CI", "CU"]
    examples = [[], [-7], [3, -2, 1], [0, 0], [-1, -1], [2, -3]]
    vectors = {name: examples[i % len(examples)] for i, name in enumerate(names)}
    origins = {name: "W.Fixture" for name in names}
    first = g.emit(root / "one", vectors, origins, heads=1, tokens=tokens, grows=3)
    second = g.emit(root / "two", vectors, origins, heads=1, tokens=tokens, grows=3)
    assert first == second
    assert g.emit(root / "one", vectors, origins, heads=1, tokens=tokens, grows=3, check=True) == first
    for rel in first["generated"]:
        assert (root / "one" / rel).read_bytes() == (root / "two" / rel).read_bytes()
    check_literals(root / "one", first, vectors)
    assert first["vector_count"] == len(vectors)
    assert "Transformer.Net.CachedUnits.TI0_0_001" in first["modules"]
    assert first["modules"].index("Transformer.Net.CachedUnits.TI0_0_001") < first["modules"].index("Transformer.Net.CachedUnits.TI0_0")
    assert first["modules"][-1] == "Transformer.Net.Cached"
    theorem_names = []
    for rel in first["generated"]:
        text = (root / "one" / rel).read_text()
        theorem_names.extend("Transformer.Net.Cached." + name
                             for name in re.findall(r"^theorem (\w+) :", text, re.M))
    assert len(theorem_names) == len(set(theorem_names))
    assert set(theorem_names) == set(first["axioms"])
    pair_modules = [f"Transformer.Net.CachedPair{a}_{b}" for a, b in g.PAIRS]
    all_modules = first["modules"] + pair_modules
    assert {m.replace(".", "/") + ".lean" for m in all_modules} == set(first["generated"])
    for index, module in enumerate(all_modules):
        text = (root / "one" / (module.replace(".", "/") + ".lean")).read_text()
        for imported in re.findall(r"^import (Transformer.Net.Cached\S*)$", text, re.M):
            assert imported in all_modules[:index], (module, imported)
    assert len([a for a in first["axioms"] if a.rsplit(".", 1)[-1] in {"eq_" + n for n in names}]) == len(names)
    for rel in first["generated"]:
        assert (root / "one" / rel).read_text().count("by decide +kernel") <= g.CHUNK
    for a, b in g.PAIRS:
        text = (root / "one/Transformer/Net" / f"CachedPair{a}_{b}.lean").read_text()
        assert f"cached_pilot_{a}_{b} : fastCheck cfg tab bnd E2 {a} {b} = true" in text
        assert "cachedFastCheck_eq cfg tab frozenCache cache_eq" in text
    # Alter one generated constructor literal, retaining its certificate statement.
    victim = root / "one/Transformer/Net/CachedUnits/TI0_0_000.lean"
    victim.write_text(victim.read_text().replace("def p_TI0_0_0 : Int := (.ofNat 0)",
                                                "def p_TI0_0_0 : Int := (.ofNat 1)"))
    must_reject(lambda: check_literals(root / "one", first, vectors))
    must_reject(lambda: g.emit(root / "one", vectors, origins, heads=1,
                              tokens=tokens, grows=3, check=True))

    # Integer arithmetic and default-zero fixtures, with independent low-degree formulas.
    assert g.pack([]) == 0 and g.pack([-7]) == -7
    assert g.pack([3, -2, 1]) == 3 - 2 * g.BASE + g.BASE**2
    nth = lambda xs, i, default: xs[i] if i < len(xs) else default
    nested = [[], [[], [-7], [3, -2, 1]]]
    cached = [[g.pack(v) for v in head] for head in nested]
    for h in (0, 1, 2, 9):
        for i in (0, 1, 2, 3, 9):
            assert nth(nth(cached, h, []), i, 0) == g.pack(nth(nth(nested, h, []), i, []))

    # Real input byte verification is read-only; no full frozen-table packing is run here.
    records = g.verify_inputs(HERE, HERE / "cached-inputs.sha256")
    assert len(records) == 16
    fixture = root / "provenance"
    for rel in records:
        dest = fixture / rel
        dest.parent.mkdir(parents=True, exist_ok=True)
        dest.write_bytes((HERE / rel).read_bytes())
    manifest = HERE / "cached-inputs.sha256"
    assert g.verify_inputs(fixture, manifest) == records
    changed = fixture / "Transformer/Net/W/Misc.lean"
    changed.write_bytes(changed.read_bytes() + b"\n")
    must_reject(lambda: g.verify_inputs(fixture, manifest))

# Cached code must remain a mechanical copy of the frozen evaluator's arithmetic.
fast = (HERE / "Transformer/Fast.lean").read_text()
expected = fast[fast.index("def fastCheck "):fast.index("\nend Transformer")]
expected = expected.replace("def fastCheck (K : Cfg) (T : Tab)",
                            "def cachedFastCheck (K : Cfg) (T : Tab) (C : PackedTab)")
expected = expected.replace("(pkI T.CI)", "C.CI").replace("(pkI T.CU)", "C.CU")
expected = expected.replace("(T.G.map pkI)", "C.G").replace("headPk ", "cachedHeadPk ")
for key in ("TI0", "TI1", "TU0", "TU1"):
    expected = expected.replace(f"(nth [] (nth [] T.{key}", f"(nth 0 (nth [] C.{key}")
for key in ("TI2", "TU2"):
    expected = expected.replace(f"(nth [] T.{key}", f"(nth 0 C.{key}")
actual = (HERE / "Transformer/Cached.lean").read_text()
assert expected in actual
assert "pkI" not in expected and "packTab" not in expected
assert "unsafe" not in actual
print("ok: small cached emission/determinism, signed/empty/default fixtures, altered literal and changed-byte red controls; no Lean evidence")
