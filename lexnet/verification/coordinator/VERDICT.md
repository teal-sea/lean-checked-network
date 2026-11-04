Coordinator re-check, 2026-11-04, from a fresh clone of commit c632f97 + receipts.
- gen_lean.py and gen_extra.py regenerate Pilot.lean and NetExtra.lean byte-identical.
- Clean compile of all 18 main-chain modules: exit 0 each; lexnet_correct axioms [propext, Classical.choice, Quot.sound].
- leanchecker --fresh lean.Full (scrubbed env): exit 0, 773 s.
- Head mutant (weights sha256 d90c578c...): unchanged Bwd.lean rejected, "Tactic `decide` proved that the proposition ... is false".
  (First attempt exited 1 for a harness reason: compiled outside the Lean root dir. Rerun inside the mutant root: Reference 0, Pilot 0, Bwd 1 with the semantic error.)
- Ref.referenceClasses on upstream lexnet.c (12,350 bytes) == shipped C binary --classes output, byte for byte.
  (First cmp failed only because a Lean deprecation warning was printed into the same file; filtered to the class line it matches.)
