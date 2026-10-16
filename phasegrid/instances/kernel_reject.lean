import Lean
import PhaseGridInstances.P7Fault.Table
import PhaseGridInstances.P7Full.Table

set_option Elab.async false  -- so that `addDecl` returns only after the kernel has checked the declaration

/-!
The planted fault, submitted to the kernel directly: the proof term that `decide +kernel` would send
(`of_decide_eq_true _ _ (Eq.refl true)`) is handed to `addDecl`, which is the kernel's type checker,
with no tactic in between. For the faulty tables the kernel must throw; for the real tables it must
accept. The messages printed are the kernel's own.
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

open LeanCheckedNetwork in
#kernel_check fault_row0 : ∀ b, b < 7 →
    (fastOk PhaseGridInstances.P7Fault.E1 PhaseGridInstances.P7Fault.E2 24 0 b &&
      fastAnswer PhaseGridInstances.P7Fault.E1 PhaseGridInstances.P7Fault.E2 PhaseGridInstances.P7Fault.W2 24 0 b == (0 + b) % 7) = true

open LeanCheckedNetwork in
#kernel_check real_row0 : ∀ b, b < 7 →
    (fastOk PhaseGridInstances.P7Full.E1 PhaseGridInstances.P7Full.E2 24 0 b &&
      fastAnswer PhaseGridInstances.P7Full.E1 PhaseGridInstances.P7Full.E2 PhaseGridInstances.P7Full.W2 24 0 b == (0 + b) % 7) = true
