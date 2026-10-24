import Lean
set_option autoImplicit false

namespace RouteA



noncomputable section

/-! ## `Int` level: packed signed values -/

/-- Entrywise sum of two lists, padding the shorter one with zeros. -/
def addV (xs ys : List Int) : List Int :=
  @List.rec Int (fun _ => List Int → List Int) (fun ys => ys)
    (fun x _ ih ys => @List.casesOn Int (fun _ => List Int) ys (x :: ih [])
      (fun y ys => Int.add x y :: ih ys)) xs ys

/-- Scalar multiple `c · xs`. -/
def scale (c : Int) (xs : List Int) : List Int :=
  @List.rec Int (fun _ => List Int) [] (fun x _ ih => Int.mul c x :: ih) xs

/-- Coefficient-weighted sum of rows: entry `e` is `Σ_l Ps_l · rows_l[e]`, reading missing
coefficients and coordinates as zero; coordinates outside the later contraction are ignored. -/
def vecmat (Ps : List Int) (rows : List (List Int)) : List Int :=
  @List.rec Int (fun _ => List (List Int) → List Int) (fun _ => [])
    (fun p _ ih rows => @List.casesOn (List Int) (fun _ => List Int) rows []
      (fun r rs => addV (scale p r) (ih rs))) Ps rows

/-- Dot product `Σ_e Cs_e · Ps_e`, over the shorter of the two lists. -/
def dot (Cs Ps : List Int) : Int :=
  @List.rec Int (fun _ => List Int → Int) (fun _ => 0)
    (fun c _ ih Ps => @List.casesOn Int (fun _ => Int) Ps 0
      (fun p ps => Int.add (Int.mul c p) (ih ps))) Cs Ps

/-- Integer equality, decided as `a - b = 0`. -/
def eqB (a b : Int) : Bool :=
  @Int.casesOn (fun _ => Bool) (Int.sub a b) (fun n => Nat.beq n 0) (fun _ => false)

/-! ## `Nat` level: one GMP operation per data entry -/

/-- The offset digit `x + c` as a natural number (exact when `-c ≤ x`). -/
def dig (c : Nat) (x : Int) : Nat :=
  @Int.casesOn (fun _ => Nat) x (fun n => Nat.add n c) (fun n => Nat.sub c (Nat.succ n))

/-- The bound test `|x| ≤ K`. -/
def inK (K : Nat) (x : Int) : Bool :=
  @Int.casesOn (fun _ => Bool) x (fun n => Nat.ble n K) (fun n => Nat.blt n K)

/-- Offset packing of one list, `Σ_i (L_i + c) Bⁱ`, by Horner's rule. -/
def pkN (B c : Nat) (L : List Int) : Nat :=
  @List.rec Int (fun _ => Nat) 0 (fun x _ acc => Nat.add (dig c x) (Nat.mul B acc)) L

/-- Every entry of the list satisfies `|x| ≤ K`. -/
def inBN (K : Nat) (L : List Int) : Bool :=
  @List.rec Int (fun _ => Bool) true (fun x _ acc => and (inK K x) acc) L

/-- List length, as a direct recursor term. -/
def lenN {α : Type} (L : List α) : Nat :=
  @List.rec α (fun _ => Nat) 0 (fun _ _ n => Nat.succ n) L

/-- One Horner step over a row: entry `d` becomes `(r_d + c) + B · acc_d`. -/
def hrow (B c : Nat) (r : List Int) (acc : List Nat) : List Nat :=
  @List.rec Int (fun _ => List Nat → List Nat) (fun _ => [])
    (fun x _ ih acc => @List.casesOn Nat (fun _ => List Nat) acc (dig c x :: ih [])
      (fun a as => Nat.add (dig c x) (Nat.mul B a) :: ih as)) r acc

/-- Offset column packing: entry `d` is `Σ_i (rows_i[d] + c) Bⁱ`. -/
def colpkN (B c : Nat) (rows : List (List Int)) : List Nat :=
  @List.rec (List Int) (fun _ => List Nat) [] (fun r _ acc => hrow B c r acc) rows

/-- Subtract the total offset `cr` from every packed value, returning to signed integers. -/
def unoff (cr : Nat) (xs : List Nat) : List Int :=
  @List.rec Nat (fun _ => List Int) [] (fun x _ ih => Int.sub (Int.ofNat x) (Int.ofNat cr) :: ih) xs

/-- Every row satisfies the Boolean predicate `p`. -/
def allB (p : List Int → Bool) (rows : List (List Int)) : Bool :=
  @List.rec (List Int) (fun _ => Bool) true (fun r _ acc => and (p r) acc) rows

/-- The repunit `Σ_{i<n} Bⁱ` (for `2 ≤ B`). -/
def rep (B n : Nat) : Nat := Nat.div (Nat.sub (Nat.pow B n) 1) (Nat.sub B 1)

/-- Rows `a, …, a + n - 1` of a list of rows. -/
def slice (a n : Nat) (L : List (List Int)) : List (List Int) := (L.drop a).take n


end
end RouteA
