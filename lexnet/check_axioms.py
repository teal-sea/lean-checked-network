#!/usr/bin/env python3
"""Fail closed unless the captured log of lean/Axioms.lean is exactly the expected inventory.
Every nonblank line must be a `#print axioms` record; the 17 theorem names printed by lean/Axioms.lean must each
appear exactly once and nothing else may appear; helpers use only the standard axioms and `lexnet_correct` uses
exactly the three standard ones.  usage: check_axioms.py LOGFILE"""
import re, sys
STANDARD = {"propext", "Classical.choice", "Quot.sound"}
EXPECTED = ["lexnet_correct", "Lexnet.num_step", "Lexnet.fwd_step", "Lexnet.fwd_all", "Lexnet.bwd_all",
            "Lexnet.backward_ok", "Lexnet.kw_flag", "Lexnet.ty_flag", "Lexnet.co_flag", "Lexnet.kw_char",
            "Hash.wordHash_inj", "Lexnet.core_mem", "Lexnet.hash_first", "Lexnet.hash_second",
            "Lexnet.hash_full", "Lexnet.hash_idle", "Lexnet.automaton_correct"]
LINE = re.compile(r"^'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)$")

def check(text):
    seen = {}
    for n, raw in enumerate(text.splitlines(), 1):
        line = raw.rstrip("\r")
        if not line.strip():
            continue
        m = LINE.match(line)
        if not m:
            return False, f"line {n} is not an axiom record: {line[:80]!r}"
        name = m.group(1)
        if name in seen:
            return False, f"duplicate record for {name}"
        seen[name] = {x.strip() for x in (m.group(2) or "").split(",") if x.strip()}
    missing = [e for e in EXPECTED if e not in seen]
    extra = [k for k in seen if k not in EXPECTED]
    if missing:
        return False, f"missing records: {missing}"
    if extra:
        return False, f"unexpected records: {extra}"
    for name, axs in seen.items():
        if not axs <= STANDARD:
            return False, f"{name} uses {sorted(axs - STANDARD)}"
    if seen["lexnet_correct"] != STANDARD:
        return False, f"lexnet_correct uses {sorted(seen['lexnet_correct'])}, expected exactly {sorted(STANDARD)}"
    return True, f"{len(seen)} records, exact inventory; lexnet_correct uses exactly {sorted(STANDARD)}"

if __name__ == "__main__":
    ok, msg = check(open(sys.argv[1], encoding="utf-8").read())
    print(("axiom allowlist OK: " if ok else "axiom allowlist FAIL: ") + msg)
    sys.exit(0 if ok else 1)
