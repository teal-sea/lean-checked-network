"""Emit kernel certificates for frozen signed vector packings; never evaluate a network.

Run from any directory: python3 gen_cached.py --out LEAN_PACKAGE
The committed input manifest pins the exact baseline sources and table bytes. All large
generated files are CI artifacts. No numpy, weights checkpoint, or numerical model is used.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import sys

sys.set_int_max_str_digits(0)
HERE = Path(__file__).resolve().parent
BASE = 2**208
PAIRS = ((0, 0), (0, 112), (96, 73))
CHUNK = 16
FIELDS = ("TI0", "TI1", "TI2", "TU0", "TU1", "TU2", "CI", "CU", "G")


def digest(data):
    return hashlib.sha256(data).hexdigest()


def verify_inputs(root, manifest):
    """Fail closed on absent, extra or changed frozen sources, before emission."""
    records = {}
    for line in manifest.read_text().splitlines():
        sha, rel = line.split("  ")
        if not re.fullmatch(r"[0-9a-f]{64}", sha) or rel in records:
            raise ValueError("invalid/duplicate input manifest entry")
        path = Path(rel)
        if path.is_absolute() or ".." in path.parts:
            raise ValueError("input manifest path escapes package")
        if digest((root / path).read_bytes()) != sha:
            raise ValueError(f"frozen input changed: {rel}")
        records[rel] = sha
    required = {"Transformer/Model.lean", "Transformer/Fast.lean", "Transformer/Equiv.lean",
                "Transformer/Net/Weights.lean", "Transformer/Net/W.sha256"}
    required.update(str(p.relative_to(root)) for p in (root / "Transformer/Net/W").glob("*.lean"))
    if set(records) != required:
        raise ValueError("input manifest does not cover the exact frozen source set")
    w_records = {}
    for line in (root / "Transformer/Net/W.sha256").read_text().splitlines():
        sha, rel = line.split("  ")
        key = "Transformer/Net/" + rel
        if key in w_records or records.get(key) != sha:
            raise ValueError("W.sha256 does not match the pinned input manifest")
        w_records[key] = sha
    if set(w_records) != required - {"Transformer/Model.lean", "Transformer/Fast.lean",
                                    "Transformer/Equiv.lean", "Transformer/Net/Weights.lean",
                                    "Transformer/Net/W.sha256"}:
        raise ValueError("W.sha256 file set mismatch")
    fast = (root / "Transformer/Fast.lean").read_text()
    if not re.search(rf"^def B : Nat := {BASE}$", fast, re.M):
        raise ValueError("fixed base changed")
    return records


def pack(values):
    acc = 0
    for value in reversed(values):
        acc = value + BASE * acc
    return acc


def literal(value):
    return f"(.ofNat {value})" if value >= 0 else f"(.negSucc {-value - 1})"


def groups(heads=4, tokens=114, grows=512):
    result = {}
    for key in ("TI0", "TI1", "TU0", "TU1"):
        for h in range(heads):
            result[f"{key}_{h}"] = [f"{key}_{h}_{t}" for t in range(tokens)]
    for key in ("TI2", "TU2"):
        result[key] = [f"{key}_{h}" for h in range(heads)]
    result["G"] = [f"G_{i}" for i in range(grows)]
    return result


def read_vectors(root):
    wanted = {n for names in groups().values() for n in names} | {"CI", "CU"}
    vectors, origins = {}, {}
    for path in sorted((root / "Transformer/Net/W").glob("*.lean")):
        for name, body in re.findall(r"^def (\w+) : List Int := \[(.*)\]$", path.read_text(), re.M):
            if name not in wanted:
                continue
            if name in vectors:
                raise ValueError(f"duplicate vector: {name}")
            parts = body.split(", ") if body else []
            values = []
            for part in parts:
                m = re.fullmatch(r"\(\.(ofNat|negSucc) (\d+)\)", part)
                if not m:
                    raise ValueError(f"nonliteral frozen vector: {name}")
                n = int(m[2])
                values.append(n if m[1] == "ofNat" else -n - 1)
            vectors[name] = values
            origins[name] = "W." + path.stem
    if set(vectors) != wanted:
        raise ValueError("missing frozen vectors")
    for name, values in vectors.items():
        length = 512 if name.startswith("TI") or name == "CI" else 113
        if len(values) != length:
            raise ValueError(f"unexpected vector length: {name}")
    return vectors, origins


def header(imports):
    return "\n".join(f"import {m}" for m in dict.fromkeys(["Transformer.Cached", *imports])) + """

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Transformer.Net.Cached
open Transformer.Net

"""


def chain(function, names):
    return "\n".join([
        f"  refine packed_cons_of ({function}) p_{n} {n} _ _ eq_{n} ?_"
        for n in names] + ["  rfl"])


def emit(out, vectors, origins, heads=4, tokens=114, grows=512, check=False):
    """Deterministic emission. At most CHUNK independently decided vectors per unit."""
    net = out / "Transformer/Net"
    unit_dir = net / "CachedUnits"
    if not check:
        unit_dir.mkdir(parents=True, exist_ok=True)
    modules, axioms, generated, vector_units = [], [], [], {}

    def write(relative, text):
        path = out / relative
        if check:
            if path.read_bytes() != text.encode():
                raise ValueError(f"nondeterministic/altered generated source: {relative}")
        else:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text)
        generated.append(relative)

    group_map = groups(heads, tokens, grows)
    units = [(key, names) for key, names in group_map.items()]
    units.append(("Bias", ["CI", "CU"]))
    for key, names in units:
        imports = []
        for index, start in enumerate(range(0, len(names), CHUNK)):
            selected = names[start:start + CHUNK]
            module = f"Transformer.Net.CachedUnits.{key}_{index:03d}"
            imports.append(module)
            text = header(["Transformer.Net." + origins[n] for n in selected])
            for name in selected:
                text += f"def p_{name} : Int := {literal(pack(vectors[name]))}\n"
                text += f"theorem eq_{name} : p_{name} = pkI {name} := by decide +kernel\n\n"
                axioms.append(f"Transformer.Net.Cached.eq_{name}")
                vector_units[name] = module
            write(module.replace(".", "/") + ".lean", text + "end Transformer.Net.Cached\n")
            modules.append(module)
        if key == "Bias":
            continue
        text = header(imports)
        text += f"def p_{key} : List Int := [" + ", ".join("p_" + n for n in names) + "]\n\n"
        text += f"theorem eq_{key} : p_{key} = {key}.map pkI := by\n{chain('pkI', names)}\n\n"
        text += "end Transformer.Net.Cached\n"
        module = f"Transformer.Net.CachedUnits.{key}"
        write(module.replace(".", "/") + ".lean", text)
        modules.append(module)
        axioms.append(f"Transformer.Net.Cached.eq_{key}")

    assembly = header(["Transformer.Net.Weights", *[
        f"Transformer.Net.CachedUnits.{key}" for key in group_map], vector_units["CI"]])
    for key in ("TI0", "TI1", "TU0", "TU1"):
        names = [f"{key}_{h}" for h in range(heads)]
        assembly += f"def p_{key} : List (List Int) := [" + ", ".join("p_" + n for n in names) + "]\n\n"
        assembly += f"theorem eq_{key} : p_{key} = {key}.map (List.map pkI) := by\n"
        assembly += chain("List.map pkI", names) + "\n\n"
        axioms.append(f"Transformer.Net.Cached.eq_{key}")
    assembly += "def frozenCache : PackedTab where\n"
    assembly += "\n".join(f"  {key} := p_{key}" for key in FIELDS) + "\n\n"
    assembly += "theorem cache_eq : frozenCache = packTab tab :=\n"
    assembly += "  PackedTab.eq_of_fields _ _\n    " + " ".join("eq_" + key for key in FIELDS) + "\n\n"
    assembly += "end Transformer.Net.Cached\n"
    write("Transformer/Net/Cached.lean", assembly)
    modules.append("Transformer.Net.Cached")
    axioms.append("Transformer.Net.Cached.cache_eq")

    for a, b in PAIRS:
        text = header(["Transformer.Net.Cached"])
        text += f"theorem cached_value_{a}_{b} : cachedFastCheck cfg tab frozenCache bnd E2 {a} {b} = true := by\n  decide +kernel\n\n"
        text += f"theorem cached_pilot_{a}_{b} : fastCheck cfg tab bnd E2 {a} {b} = true := by\n"
        text += f"  rw [← cachedFastCheck_eq cfg tab frozenCache cache_eq bnd E2 {a} {b}]\n"
        text += f"  exact cached_value_{a}_{b}\n\nend Transformer.Net.Cached\n"
        write(f"Transformer/Net/CachedPair{a}_{b}.lean", text)
        axioms.extend([f"Transformer.Net.Cached.cached_value_{a}_{b}",
                       f"Transformer.Net.Cached.cached_pilot_{a}_{b}"])

    return {"modules": modules, "axioms": axioms, "generated": generated,
            "vector_count": len(vectors), "certificate_units": len(set(vector_units.values())),
            "max_vectors_per_unit": CHUNK, "pairs": PAIRS}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--source", type=Path, default=HERE)
    parser.add_argument("--manifest", type=Path, default=HERE / "cached-inputs.sha256")
    parser.add_argument("--check", action="store_true",
                        help="regenerate in memory and compare every source byte and manifest, without writing")
    args = parser.parse_args()
    records = verify_inputs(args.source, args.manifest)
    vectors, origins = read_vectors(args.source)
    result = emit(args.out, vectors, origins, check=args.check)
    result.update({"base": str(BASE), "inputs": records,
                   "generator_sha256": digest(Path(__file__).read_bytes()),
                   "input_manifest_sha256": digest(args.manifest.read_bytes()),
                   "generic_sha256": digest((args.source / "Transformer/Cached.lean").read_bytes()),
                   "baseline_source": "9a7f6d6a5ce7c5be37012c45144ddd8548e5b9a8"})
    evidence = args.out / "ci-out/cache-codegen"
    if not args.check:
        evidence.mkdir(parents=True, exist_ok=True)
    # Sorted hashes include every generated source. No timestamps or host paths.
    result["outputs"] = {rel: digest((args.out / rel).read_bytes()) for rel in sorted(result["generated"])}
    artifacts = {"manifest.json": json.dumps(result, indent=2, sort_keys=True) + "\n",
                 "modules.txt": "\n".join(result["modules"]) + "\n",
                 "sources.txt": "\n".join(result["generated"]) + "\n",
                 "axioms.txt": "\n".join(result["axioms"]) + "\n"}
    for name, contents in artifacts.items():
        if args.check:
            if (evidence / name).read_bytes() != contents.encode():
                raise ValueError(f"altered generated manifest: {name}")
        else:
            (evidence / name).write_text(contents)
    verb = "verified deterministic bytes for" if args.check else "emitted"
    print(f"{verb} {result['vector_count']} kernel equalities in {result['certificate_units']} bounded units; three cached pilots only")


if __name__ == "__main__":
    main()
