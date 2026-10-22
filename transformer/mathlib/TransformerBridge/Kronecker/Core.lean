import TransformerCore.Model

/-!
# Whole-head Kronecker check: the Boolean checker

This file defines `headCheck`, a Boolean function that the Lean kernel evaluates directly on the
list-encoded raw weights (`tok`, `pos`, `WV`, `WO` and `Win` or `U`) and on the frozen table rows
of one attention head. It contains definitions only; their meaning is proved once in
`TransformerBridge.Kronecker.Spec`.

## What the check computes

For a head `h`, an output matrix `Mout` with `n` columns (`Win`, `n = 512`, for the `TI` table;
`U`, `n = 113`, for `TU`) and a base `B`, signed base-`B` packing `Σ_i x_i Bⁱ` turns each
`n`-wide row into one integer. Packing is linear, so the head's matrix chain is evaluated on
packed integers:

* `colpkN`, `unoff`: the packed columns `PW_d = Σ_i Mout_{d,i} Bⁱ` (one per input coordinate `d`);
* `vecmat` twice: `PM_l = Σ_d WO_{h,l,d} PW_d`, then `R_e = Σ_l WV_{h,e,l} PM_l`;
* `dot`: the packed value of site `(j, tk)` is `Σ_e (tok_{tk,e} + pos_{j,e}) R_e`, with the
  position part computed once per position;
* `pkN`, `eqB`: the frozen row, packed with offset `K`, must equal that value plus the offset.

`paramsOk` and `inputsOk` check, inside the same evaluation, the token, position and output-matrix
shapes, the lengths of the selected `WV`/`WO` slices and of the frozen rows, the entry bounds
`Kt, Kp, Kv, Ko, Kw` and the inequalities `128·Kw·32·Ko·128·(Kt+Kp)·Kv ≤ K`, `2K < B`, `2 ≤ B`
that make base-`B` digits unique. The inner widths of the `WV`/`WO` rows are not checked: like the
raw model, the check reads them with zero-default list access, and only the contracted coordinates
contribute.

## Kernel-cost design

* Every list function is written as a direct `List.rec`/`List.casesOn` term and is
  `noncomputable`: only the kernel reduces it, and nothing is compiled or run outside the kernel.
* Passes that touch every data entry (column packing, frozen-row packing, bound tests) work on
  `Nat` with offset digits `x + c`, so each entry costs one GMP-backed operation.
* `Int` is used only for the comparatively few operations on packed signed values
  (`vecmat`, `dot`).
-/

set_option autoImplicit false

namespace TransformerBridge.Kronecker

open TransformerCore (nth)

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

/-! ## The check -/

/-- The packed head product `R_e = Σ_l WV_{h,e,l} Σ_d WO_{h,l,d} Σ_i Mout_{d,i} Bⁱ`
(128 entries, one per input coordinate `e`). -/
def headR (B cw n h : Nat) (WV WO Mout : List (List Int)) : List Int :=
  vecmat (vecmat (unoff (Nat.mul cw (rep B n)) (colpkN B cw Mout)) (slice (h * 128) 128 WO))
    (slice (h * 32) 32 WV)

/-- One frozen row `f` against token row `t`: `f` has length `n`, entries in `[-K, K]`, and its
offset packing equals `dot t R + p + KR`, where `p` is the position part and `KR = K · rep B n`. -/
def rowOk (B K n KR : Nat) (R : List Int) (p : Int) (t f : List Int) : Bool :=
  and (Nat.beq (lenN f) n) (and (inBN K f)
    (eqB (Int.ofNat (pkN B K f)) (Int.add (Int.add (dot t R) p) (Int.ofNat KR))))

/-- `rowOk` for every token row against the frozen row of the same index; the two lists must
have equal length. -/
def siteRows (B K n KR : Nat) (R : List Int) (p : Int) (ts fs : List (List Int)) : Bool :=
  @List.rec (List Int) (fun _ => List (List Int) → Bool)
    (fun fs => @List.casesOn (List Int) (fun _ => Bool) fs true (fun _ _ => false))
    (fun t _ ih fs => @List.casesOn (List Int) (fun _ => Bool) fs false
      (fun f fs => and (rowOk B K n KR R p t f) (ih fs))) ts fs

/-- All sites of one head and field: positions 0 and 1 for every token, and position 2 at
token 113 (the only position-2 slot that the tables use). -/
def sitesOk (B K n KR : Nat) (tok pos F0 F1 : List (List Int)) (F2 : List Int) (R : List Int) :
    Bool :=
  and (siteRows B K n KR R (dot (nth [] pos 0) R) tok F0)
    (and (siteRows B K n KR R (dot (nth [] pos 1) R) tok F1)
      (rowOk B K n KR R (dot (nth [] pos 2) R) (nth [] tok 113) F2))

/-- The parameter inequalities: the crude output bound is at most `K`, `2K < B` and `2 ≤ B`. -/
def paramsOk (B K Kt Kp Kv Ko Kw : Nat) : Bool :=
  and (Nat.ble (Nat.mul 128 (Nat.mul Kw (Nat.mul 32 (Nat.mul Ko (Nat.mul 128
    (Nat.mul (Nat.add Kt Kp) Kv)))))) K)
    (and (Nat.blt (Nat.mul 2 K) B) (Nat.ble 2 B))

/-- Shapes and entry bounds of the inputs; only the head-`h` slices of `WV` and `WO` are read. -/
def inputsOk (Kt Kp Kv Ko Kw n h : Nat) (tok pos WV WO Mout : List (List Int)) : Bool :=
  and (Nat.beq (lenN tok) 114) (and (allB (fun r => Nat.beq (lenN r) 128) tok) (and (allB (inBN Kt) tok)
  (and (Nat.beq (lenN pos) 3) (and (allB (fun r => Nat.beq (lenN r) 128) pos) (and (allB (inBN Kp) pos)
  (and (Nat.beq (lenN (slice (h * 32) 32 WV)) 32) (and (allB (inBN Kv) (slice (h * 32) 32 WV))
  (and (Nat.beq (lenN (slice (h * 128) 128 WO)) 128) (and (allB (inBN Ko) (slice (h * 128) 128 WO))
  (and (Nat.beq (lenN Mout) n) (and (allB (fun r => Nat.beq (lenN r) 128) Mout)
    (allB (inBN Kw) Mout))))))))))))

/-- **The whole-head check** for one field: `Mout = Win`, `n = 512` against the frozen rows
`TI0`, `TI1`, `TI2` of head `h`, or `Mout = U`, `n = 113` against `TU0`, `TU1`, `TU2`. -/
def headCheck (B K Kt Kp Kv Ko Kw n h : Nat) (tok pos WV WO Mout F0 F1 : List (List Int))
    (F2 : List Int) : Bool :=
  and (paramsOk B K Kt Kp Kv Ko Kw) (and (inputsOk Kt Kp Kv Ko Kw n h tok pos WV WO Mout)
    (sitesOk B K n (Nat.mul K (rep B n)) tok pos F0 F1 F2 (headR B Kw n h WV WO Mout)))

end

end TransformerBridge.Kronecker
