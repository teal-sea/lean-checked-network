"""Build a 'fast route' submission for one task: the repo's Fast.lean (its proof that the packed
big-number evaluator equals the network), then one `decide +kernel` per row, as gen_lean.py does,
all in ONE file in namespace LeanCheckedNetwork.Net. Usage: make_fast_submission.py TASK_DIR OUT.md"""
import json, sys
from pathlib import Path
task = Path(sys.argv[1]); meta = json.loads((task / "meta.json").read_text())
p, H = meta["p"], meta["H"]
fast = (Path(__file__).resolve().parents[2] / "lean" / "LeanCheckedNetwork" / "Fast.lean").read_text()   # the repo's Fast.lean
fast_body = fast.replace("import LeanCheckedNetwork.Network\n", "", 1)
rows = []
for a in range(p):
    rows.append(f"""theorem fast_{a} : ∀ b, b < {p} →
    (fastOk E1 E2 {H} {a} b && fastAnswer E1 E2 W2 {H} {a} b == ({a} + b) % {p}) = true := by
  decide +kernel

theorem row_{a} : ∀ b, b < {p} → answer {a} b = ({a} + b) % {p} := by
  intro b hb
  have h := fast_{a} b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 {a} b = _
  rw [answer_eq_fastAnswer E1 E2 W2 {H} {a} b table_ok h.1, h.2]
""")
cases = "\n".join(f"  | {a}, _ => exact row_{a}" for a in range(p))
src = f"""import LeanCheckedNetwork.Weights

set_option maxRecDepth 100000
set_option Elab.async false

{fast_body.rstrip()}

namespace LeanCheckedNetwork.Net

open LeanCheckedNetwork

theorem table_ok : tableOk W2 {H} = true := by decide +kernel

{chr(10).join(rows)}
theorem adds_mod_{p} : ∀ a, a < {p} → ∀ b, b < {p} → answer a b = (a + b) % {p} := by
  intro a ha
  match a, ha with
{cases}
  | n + {p}, h => exact absurd h (by omega)

end LeanCheckedNetwork.Net
"""
Path(sys.argv[2]).write_text("The fast route from the repository, packed big numbers, one row at a time.\n\n```lean\n" + src + "```\n")
print(f"wrote {sys.argv[2]}: p={p} H={H}, {len(src)} chars")
