import TransformerBridge.RawCUUpdate

namespace TransformerBridge.RawVOBasis
open TransformerBridge.RawPilot (contract contract_eq ovec_of_vvec)
open TransformerBridge.RawCorrespondence (contract_add_left vvec_split)

/-- Certified token and position projections combine without evaluating new input sites. -/
theorem vvec_of_basis (W : Transformer.Weights) (h : Fin 4) (tk : Fin 114) (j : Fin 3)
    (vt vp : Fin 32 → Int)
    (ht : ∀ l, contract (W.tok tk) (fun e => W.WV h e l) = vt l)
    (hp : ∀ l, contract (W.pos j) (fun e => W.WV h e l) = vp l) (l : Fin 32) :
    W.vvec h tk j l = vt l + vp l := by
  rw [vvec_split, ht, hp]

/-- The same ordinary linear split transports both certified V bases into O. -/
theorem ovec_of_basis (W : Transformer.Weights) (h : Fin 4) (tk : Fin 114) (j : Fin 3)
    (vt vp : Fin 32 → Int) (ot op : Fin 128 → Int)
    (ht : ∀ l, contract (W.tok tk) (fun e => W.WV h e l) = vt l)
    (hp : ∀ l, contract (W.pos j) (fun e => W.WV h e l) = vp l)
    (hot : ∀ d, contract vt (fun l => W.WO h l d) = ot d)
    (hop : ∀ d, contract vp (fun l => W.WO h l d) = op d) (d : Fin 128) :
    W.ovec h tk j d = ot d + op d := by
  calc
    W.ovec h tk j d = contract (fun l => vt l + vp l) (fun l => W.WO h l d) :=
      ovec_of_vvec W h tk j _ (vvec_of_basis W h tk j vt vp ht hp) d
    _ = contract vt (fun l => W.WO h l d) + contract vp (fun l => W.WO h l d) :=
      contract_add_left vt vp (fun l => W.WO h l d)
    _ = ot d + op d := by rw [hot, hop]

/-- A real right-hand learned coefficient change has an exact scalar sensitivity. -/
theorem contract_update_right {m : Nat} (x w : Fin m → Int) (i : Fin m) :
    contract x (fun l => w l + if l = i then 1 else 0) = contract x w + x i := by
  have comm (a b : Fin m → Int) : contract a b = contract b a := by
    simp only [contract_eq, mul_comm]
  calc
    contract x (fun l => w l + if l = i then 1 else 0) =
        contract (fun l => w l + if l = i then 1 else 0) x := comm _ _
    _ = contract w x + x i := TransformerBridge.RawCUUpdate.contract_update w x i
    _ = contract x w + x i := congrArg (fun value : Int => value + x i) (comm w x)

/-- Changing only WO leaves V unchanged and changes an actual O output by that V input. -/
theorem ovec_WO_update (W : Transformer.Weights) (h : Fin 4) (tk : Fin 114) (j : Fin 3)
    (i : Fin 32) (d : Fin 128) :
    ({ W with WO := fun a l e => W.WO a l e + if a = h ∧ l = i ∧ e = d then 1 else 0 } : Transformer.Weights).ovec h tk j d =
      W.ovec h tk j d + W.vvec h tk j i := by
  let changed : Transformer.Weights :=
    { W with WO := fun a l e => W.WO a l e + if a = h ∧ l = i ∧ e = d then 1 else 0 }
  have hv (l : Fin 32) : changed.vvec h tk j l = W.vvec h tk j l := rfl
  have hw : (fun l : Fin 32 => changed.WO h l d) =
      (fun l : Fin 32 => W.WO h l d + if l = i then 1 else 0) := by
    funext l
    simp [changed]
  have ho := ovec_of_vvec changed h tk j (W.vvec h tk j) hv d
  rw [hw] at ho
  calc
    changed.ovec h tk j d = contract (W.vvec h tk j) (fun l => W.WO h l d + if l = i then 1 else 0) := ho
    _ = contract (W.vvec h tk j) (fun l => W.WO h l d) + W.vvec h tk j i :=
      contract_update_right (W.vvec h tk j) (fun l => W.WO h l d) i
    _ = W.ovec h tk j d + W.vvec h tk j i :=
      congrArg (fun value : Int => value + W.vvec h tk j i)
        (ovec_of_vvec W h tk j (W.vvec h tk j) (fun _ => rfl) d).symm

end TransformerBridge.RawVOBasis
