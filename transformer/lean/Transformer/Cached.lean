import Transformer.Equiv

/-! Reuse only input-invariant signed packings. Scores, bounds, shifts, digit extraction,
answer and margin are exactly those of Fast. The correspondence has no shape assumptions. -/

namespace Transformer

structure PackedTab where
  TI0 : List (List Int)
  TI1 : List (List Int)
  TI2 : List Int
  TU0 : List (List Int)
  TU1 : List (List Int)
  TU2 : List Int
  CI : Int
  CU : Int
  G : List Int

/-- Specification only: the cached evaluator never calls this packing function. -/
def packTab (T : Tab) : PackedTab where
  TI0 := T.TI0.map (List.map pkI)
  TI1 := T.TI1.map (List.map pkI)
  TI2 := T.TI2.map pkI
  TU0 := T.TU0.map (List.map pkI)
  TU1 := T.TU1.map (List.map pkI)
  TU2 := T.TU2.map pkI
  CI := pkI T.CI
  CU := pkI T.CU
  G := T.G.map pkI

def cachedHeadPk (e : Nat × Nat × Nat) (v0 v1 v2 : Int) : Int :=
  Int.add (nmul e.1 v0) (Int.add (nmul e.2.1 v1) (nmul e.2.2 v2))

def cachedFastCheck (K : Cfg) (T : Tab) (C : PackedTab) (bd : Bnd) (E2 : Nat) (a b : Nat) : Bool :=
  let E0 := headE K T a b 0
  let E1 := headE K T a b 1
  let E2' := headE K T a b 2
  let E3 := headE K T a b 3
  let dc := dens E0 E1 E2' E3
  let D := dc.1
  let c0 := dc.2.1
  let c1 := dc.2.2.1
  let c2 := dc.2.2.2.1
  let c3 := dc.2.2.2.2
  let preP : Int := Int.add (nmul D C.CI)
    (Int.add (nmul c0 (cachedHeadPk E0 (nth 0 (nth [] C.TI0 0) a) (nth 0 (nth [] C.TI1 0) b) (nth 0 C.TI2 0)))
      (Int.add (nmul c1 (cachedHeadPk E1 (nth 0 (nth [] C.TI0 1) a) (nth 0 (nth [] C.TI1 1) b) (nth 0 C.TI2 1)))
        (Int.add (nmul c2 (cachedHeadPk E2' (nth 0 (nth [] C.TI0 2) a) (nth 0 (nth [] C.TI1 2) b) (nth 0 C.TI2 2)))
          (nmul c3 (cachedHeadPk E3 (nth 0 (nth [] C.TI0 3) a) (nth 0 (nth [] C.TI1 3) b) (nth 0 C.TI2 3))))))
  let Kp : Nat := D * bd.kCI + (c0 * headK E0 bd.kTI + (c1 * headK E1 bd.kTI + (c2 * headK E2' bd.kTI + c3 * headK E3 bd.kTI)))
  let m : List Nat := unpkSub 512 (Int.toNat (Int.add preP (nmul Kp (Int.ofNat (ones 512))))) Kp
  let LP : Int := Int.add (nmul D C.CU)
    (Int.add (nmul K.S2
        (Int.add (nmul c0 (cachedHeadPk E0 (nth 0 (nth [] C.TU0 0) a) (nth 0 (nth [] C.TU1 0) b) (nth 0 C.TU2 0)))
          (Int.add (nmul c1 (cachedHeadPk E1 (nth 0 (nth [] C.TU0 1) a) (nth 0 (nth [] C.TU1 1) b) (nth 0 C.TU2 1)))
            (Int.add (nmul c2 (cachedHeadPk E2' (nth 0 (nth [] C.TU0 2) a) (nth 0 (nth [] C.TU1 2) b) (nth 0 C.TU2 2)))
              (nmul c3 (cachedHeadPk E3 (nth 0 (nth [] C.TU0 3) a) (nth 0 (nth [] C.TU1 3) b) (nth 0 C.TU2 3)))))))
      (dotNI m C.G))
  let KL : Nat := D * bd.kCU + (K.S2 * (c0 * headK E0 bd.kTU + (c1 * headK E1 bd.kTU + (c2 * headK E2' bd.kTU + c3 * headK E3 bd.kTU))) + 512 * Kp * bd.kG)
  let d : List Nat := unpk 113 (Int.toNat (Int.add LP (nmul KL (Int.ofNat (ones 113)))))
  let right := (a + b) % 113
  decide (2 * Kp < B) && decide (2 * KL < B) && (argmaxN d == right) && decide (maxExceptN d right + E2 < nth 0 d right)


/-- Mapping pkI respects the original empty-vector default, also out of range. -/
theorem nth_pkI_map (vs : List (List Int)) (i : Nat) :
    nth 0 (vs.map pkI) i = pkI (nth [] vs i) :=
  nth_map pkI [] vs i

theorem nth_pkI_map₂ (vs : List (List (List Int))) (h i : Nat) :
    nth 0 (nth [] (vs.map (List.map pkI)) h) i =
      pkI (nth [] (nth [] vs h) i) := by
  have hh : nth [] (vs.map (List.map pkI)) h = (nth [] vs h).map pkI :=
    nth_map (List.map pkI) [] vs h
  rw [hh]
  exact nth_pkI_map _ _

/-- Purely symbolic correspondence: no bounds, token range, or nonempty-list premises. -/
theorem cachedFastCheck_pack (K : Cfg) (T : Tab) (bd : Bnd) (E2 a b : Nat) :
    cachedFastCheck K T (packTab T) bd E2 a b = fastCheck K T bd E2 a b := by
  simp only [cachedFastCheck, packTab, nth_pkI_map₂, nth_pkI_map,
    cachedHeadPk, headPk]

/-- Every cache is accepted only through an equality to the original signed packing. -/
theorem cachedFastCheck_eq (K : Cfg) (T : Tab) (C : PackedTab)
    (h : C = packTab T) (bd : Bnd) (E2 a b : Nat) :
    cachedFastCheck K T C bd E2 a b = fastCheck K T bd E2 a b := by
  rw [h]
  exact cachedFastCheck_pack K T bd E2 a b

/-- Assemble certified list entries without evaluating any original vector. -/
theorem packed_cons_of {α β : Type} (f : α → β) (x : β) (v : α)
    (xs : List β) (vs : List α) (hx : x = f v) (hxs : xs = vs.map f) :
    x :: xs = (v :: vs).map f := by
  rw [List.map_cons, hx, hxs]

/-- Structure assembly uses field equalities, never a decision over the full tables. -/
theorem PackedTab.eq_of_fields (C D : PackedTab)
    (hTI0 : C.TI0 = D.TI0) (hTI1 : C.TI1 = D.TI1) (hTI2 : C.TI2 = D.TI2)
    (hTU0 : C.TU0 = D.TU0) (hTU1 : C.TU1 = D.TU1) (hTU2 : C.TU2 = D.TU2)
    (hCI : C.CI = D.CI) (hCU : C.CU = D.CU) (hG : C.G = D.G) : C = D := by
  cases C
  cases D
  cases hTI0
  cases hTI1
  cases hTI2
  cases hTU0
  cases hTU1
  cases hTU2
  cases hCI
  cases hCU
  cases hG
  rfl

end Transformer
