"""Planted fault for the p = 7 instance: swap the read-out rows of answers 0 and 1 (as the first
repository's fault does), so every weight stays in range but pairs whose answer is 0 or 1 are wrong.
Writes PhaseGridInstances/P7Fault/{Weights,Table}.lean and expected_fail/FaultRow.lean; the latter
must be REJECTED by the kernel."""
from pathlib import Path
import numpy as np

here = Path(__file__).resolve().parent
src = here / "phasegrid-instances" / "PhaseGridInstances" / "P7Full" / "P7Full.npz"
net = np.load(src)
p, H, M = int(net["p"]), int(net["H"]), int(net["M"])
E1, E2, W2 = net["E1q"], net["E2q"], net["W2q"].copy()
W2[[0, 1]] = W2[[1, 0]]
U = (E1*E1) @ W2.T; V = (E2*E2) @ W2.T
wrong = 0; wrong_row0 = 0
for a in range(p):
    I = U[a][None, :] + V + 2*((E1[a]*E2) @ W2.T)
    w = int((I.argmax(1) != (a + np.arange(p)) % p).sum()); wrong += w
    if a == 0: wrong_row0 = w
print(f"P7Fault: rows 0 and 1 of W2 swapped: {wrong} of {p*p} pairs wrong, {wrong_row0} of them in row 0")
assert wrong > 0 and wrong_row0 > 0
root = here / "phasegrid-instances" / "PhaseGridInstances" / "P7Fault"; root.mkdir(exist_ok=True)
def lit(v):
    v = int(v); return f"(.ofNat {v})" if v >= 0 else f"(.negSucc {-v - 1})"
def table(m):
    return "[\n" + ",\n".join("  [" + ", ".join(lit(v) for v in row) + "]" for row in m) + "]"
(root / "Weights.lean").write_text(f"""import PhaseGridInstances.Network

/-! # Planted fault: the p = 7 network with the read-out rows of answers 0 and 1 swapped ({wrong} pairs wrong). -/

set_option maxRecDepth 100000

namespace PhaseGridInstances.P7Fault

def E1 : List (List Int) := {table(E1)}

def E2 : List (List Int) := {table(E2)}

def W2 : List (List Int) := {table(W2)}

def answer (a b : Nat) : Nat := LeanCheckedNetwork.answer E1 E2 W2 a b

end PhaseGridInstances.P7Fault
""")
(root / "Table.lean").write_text(f"""import PhaseGridInstances.Fast
import PhaseGridInstances.P7Fault.Weights

namespace PhaseGridInstances.P7Fault

open LeanCheckedNetwork

theorem table_ok : tableOk W2 {H} = true := by decide +kernel

end PhaseGridInstances.P7Fault
""")
(here / "phasegrid-instances" / "expected_fail").mkdir(exist_ok=True)
(here / "phasegrid-instances" / "expected_fail" / "FaultRow.lean").write_text(f"""import PhaseGridInstances.P7Fault.Table

/-!
# Planted fault: this file must FAIL

`P7Fault` is the p = 7 phase-grid network with the read-out rows of answers 0 and 1 swapped
({wrong} of 49 pairs wrong, {wrong_row0} of them in row 0). The same proof that succeeds for the real
network must be rejected here, by the kernel. If this file ever builds, the check is broken.
-/

namespace PhaseGridInstances.P7Fault

open LeanCheckedNetwork

theorem fast_0 : ∀ b, b < {p} →
    (fastOk E1 E2 {H} 0 b && fastAnswer E1 E2 W2 {H} 0 b == (0 + b) % {p}) = true := by
  decide +kernel

end PhaseGridInstances.P7Fault
""")
print("wrote P7Fault/Weights.lean, P7Fault/Table.lean, expected_fail/FaultRow.lean")
