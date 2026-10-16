import Lean
import PhaseGridInstances.P7LastFault.Table
import PhaseGridInstances.P7Full.Table
import PhaseGridInstances.P113LastFault.Table
import PhaseGridInstances.P113Full.Table

set_option Elab.async false  -- so that `addDecl` returns only after the kernel has checked the declaration

/-!
The last-pair faults (`gen_last_fault.py`), submitted to the kernel directly as `kernel_reject.lean`
does: the proof term `of_decide_eq_true _ _ (Eq.refl true)` is handed to `addDecl` with no tactic in
between. Six verdicts, all the kernel's own: for each fault, the range that stops before the bad pair
is ACCEPTED, the range that includes it is REJECTED, and the real network's same range is ACCEPTED.
-/
open Lean Elab Command Meta in
elab "#kernel_check " nm:ident " : " t:term : command => do
  liftTermElabM do
    let ty ← Term.elabType t
    Term.synthesizeSyntheticMVarsNoPostponing
    let ty ← instantiateMVars ty
    let inst ← synthInstance (mkApp (mkConst ``Decidable) ty)
    let pf := mkApp3 (mkConst ``of_decide_eq_true) ty inst
      (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``true))
    let decl := Declaration.thmDecl { name := nm.getId, levelParams := [], type := ty, value := pf }
    try
      addDecl decl
      logInfo m!"kernel ACCEPTED {nm.getId}"
    catch ex =>
      logInfo m!"kernel REJECTED {nm.getId}: {ex.toMessageData}"

-- p = 7, faulty network, last row, b < 6 only (all right): must be ACCEPTED
open LeanCheckedNetwork in
#kernel_check fault7_row6_first6 : ∀ b, b < 6 →
    (fastOk PhaseGridInstances.P7LastFault.E1 PhaseGridInstances.P7LastFault.E2 24 6 b &&
      fastAnswer PhaseGridInstances.P7LastFault.E1 PhaseGridInstances.P7LastFault.E2 PhaseGridInstances.P7LastFault.W2 24 6 b == (6 + b) % 7) = true
-- p = 7, faulty network, last row, all 7 pairs (the pair (6, 6) is wrong): must be REJECTED
open LeanCheckedNetwork in
#kernel_check fault7_row6_all : ∀ b, b < 7 →
    (fastOk PhaseGridInstances.P7LastFault.E1 PhaseGridInstances.P7LastFault.E2 24 6 b &&
      fastAnswer PhaseGridInstances.P7LastFault.E1 PhaseGridInstances.P7LastFault.E2 PhaseGridInstances.P7LastFault.W2 24 6 b == (6 + b) % 7) = true
-- p = 7, real network, last row: must be ACCEPTED
open LeanCheckedNetwork in
#kernel_check real7_row6 : ∀ b, b < 7 →
    (fastOk PhaseGridInstances.P7Full.E1 PhaseGridInstances.P7Full.E2 24 6 b &&
      fastAnswer PhaseGridInstances.P7Full.E1 PhaseGridInstances.P7Full.E2 PhaseGridInstances.P7Full.W2 24 6 b == (6 + b) % 7) = true

-- p = 113, faulty network (column 112 wrong), last row, last chunk without its last pair, b = 90 to 111: must be ACCEPTED
open LeanCheckedNetwork in
#kernel_check fault113_row112_b90_111 : ∀ b, b < 22 →
    (fastOk PhaseGridInstances.P113LastFault.E1 PhaseGridInstances.P113LastFault.E2 448 112 (90 + b) &&
      fastAnswer PhaseGridInstances.P113LastFault.E1 PhaseGridInstances.P113LastFault.E2 PhaseGridInstances.P113LastFault.W2 448 112 (90 + b) == (112 + (90 + b)) % 113) = true
-- p = 113, faulty network, the whole last chunk, b = 90 to 112 (the statement of P113Full.fast_112_4): must be REJECTED
open LeanCheckedNetwork in
#kernel_check fault113_row112_b90_112 : ∀ b, b < 23 →
    (fastOk PhaseGridInstances.P113LastFault.E1 PhaseGridInstances.P113LastFault.E2 448 112 (90 + b) &&
      fastAnswer PhaseGridInstances.P113LastFault.E1 PhaseGridInstances.P113LastFault.E2 PhaseGridInstances.P113LastFault.W2 448 112 (90 + b) == (112 + (90 + b)) % 113) = true
-- p = 113, real network, the same chunk: must be ACCEPTED
open LeanCheckedNetwork in
#kernel_check real113_row112_b90_112 : ∀ b, b < 23 →
    (fastOk PhaseGridInstances.P113Full.E1 PhaseGridInstances.P113Full.E2 448 112 (90 + b) &&
      fastAnswer PhaseGridInstances.P113Full.E1 PhaseGridInstances.P113Full.E2 PhaseGridInstances.P113Full.W2 448 112 (90 + b) == (112 + (90 + b)) % 113) = true
