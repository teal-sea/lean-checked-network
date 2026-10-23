import TransformerBridge.Kronecker.Core
import Transformer.Raw
import TransformerBridge.Bridge

/-!
# Whole-head Kronecker check: what a passing check proves

`field_of_check` is the meaning of `headCheck`, proved once for all heads and both fields: if
`headCheck … = true` for head `h` with output matrix `Mout`, then every entry of the three frozen
slots of that head equals the raw-model value `Σ_d ovec h tk j d · Mout d i`.
`TI_head_of_check` and `TU_head_of_check` restate this as
`(toTables T).TI h j tk = (W.rawTables S).TI h j tk` (and the same for `TU`) for every position
`j` and token `tk`; the unused slots `j = 2, tk ≠ 113` are `0` on both sides by definition.
The conclusion assumes that the supplied lists read back to the chosen raw weight functions, via
the five explicit bridge equalities (`htok`, `hpos`, `hWV`, `hWO`, `hM`); for the frozen network
these are `rfl`.

The proof has four ingredients.

1. **List semantics.** Each list program agrees with its `nth`-indexed meaning (`nth_vecmat`,
   `dot_eq`, `nth_colpkN`, `pkN_spec`, …); offset digits are exact under the checked bounds
   (`dig_spec`).
2. **Linearity.** Signed packing is linear, so three sum exchanges
   (`sum_input_through_value`, `sum_value_through_output`, `sum_output_through_pack`) show that
   the packed site value is `Σ_i (Σ_d ovec · Mout_{d,i}) Bⁱ`. This is an identity of integers
   and needs no carry argument.
3. **Bounds.** The checked input bounds give `|Σ_d ovec · Mout_{d,i}| ≤ K` (`ovec_mul_bound`), and
   the frozen entries are checked to lie in `[-K, K]`.
4. **Uniqueness of balanced digits.** With `2K < B`, two digit vectors in `[-K, K]` with the same
   base-`B` value are equal entrywise (`packed_inj`).
-/

set_option autoImplicit false

namespace TransformerBridge.Kronecker

open TransformerCore (nth)
open Finset

/-! ## `nth` -/

/-- Reading any index of the empty list gives the default. -/
theorem nth_nil {α : Type} (x : α) (i : Nat) : nth x [] i = x := by cases i <;> rfl

/-- Index `0` of a cons is its head. -/
theorem nth_cons_zero {α : Type} (x a : α) (l : List α) : nth x (a :: l) 0 = a := rfl

/-- Index `i + 1` of a cons is index `i` of its tail. -/
theorem nth_cons_succ {α : Type} (x a : α) (l : List α) (i : Nat) :
    nth x (a :: l) (i + 1) = nth x l i := rfl

/-- Reading after `List.drop a` shifts the index by `a`. -/
theorem nth_drop {α : Type} (x : α) : ∀ (a : Nat) (L : List α) (d : Nat),
    nth x (L.drop a) d = nth x L (a + d)
  | 0, L, d => by simp
  | a + 1, [], d => by simp [nth_nil]
  | a + 1, y :: ys, d => by
    rw [List.drop_succ_cons, nth_drop x a ys d, show a + 1 + d = (a + d) + 1 by omega, nth_cons_succ]

/-- Reading below `n` is unchanged by `List.take n`. -/
theorem nth_take {α : Type} (x : α) : ∀ (n : Nat) (L : List α) (d : Nat), d < n →
    nth x (L.take n) d = nth x L d
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | _ + 1, [], d, _ => by simp
  | _ + 1, _ :: _, 0, _ => rfl
  | n + 1, y :: ys, d + 1, h => by
    rw [List.take_succ_cons, nth_cons_succ, nth_cons_succ]
    exact nth_take x n ys d (by omega)

/-- Row `d < n` of `slice a n L` is row `a + d` of `L`. -/
theorem nth_slice (a n : Nat) (L : List (List Int)) (d : Nat) (hd : d < n) :
    nth [] (slice a n L) d = nth [] L (a + d) := by
  rw [slice, nth_take _ n _ d hd, nth_drop]

/-! ## Defining equations of the `List.rec` programs (all `rfl`) -/

section eqns
variable (B c K n KR : Nat) (R : List Int) (p : Int)

/-- Defining equation of `addV` (empty left list). -/
theorem addV_nil (ys : List Int) : addV [] ys = ys := rfl
/-- Defining equation of `addV` (empty right list). -/
theorem addV_cons_nil (x : Int) (xs : List Int) : addV (x :: xs) [] = x :: addV xs [] := rfl
/-- Defining equation of `addV` (two non-empty lists). -/
theorem addV_cons_cons (x y : Int) (xs ys : List Int) :
    addV (x :: xs) (y :: ys) = (x + y) :: addV xs ys := rfl
/-- Defining equation of `scale` (empty list). -/
theorem scale_nil (a : Int) : scale a [] = [] := rfl
/-- Defining equation of `scale` (cons). -/
theorem scale_cons (a x : Int) (xs : List Int) : scale a (x :: xs) = a * x :: scale a xs := rfl
/-- Defining equation of `vecmat` (no coefficients). -/
theorem vecmat_nil (rows : List (List Int)) : vecmat [] rows = [] := rfl
/-- Defining equation of `vecmat` (no rows). -/
theorem vecmat_cons_nil (q : Int) (ps : List Int) : vecmat (q :: ps) [] = [] := rfl
/-- Defining equation of `vecmat` (coefficient and row). -/
theorem vecmat_cons_cons (q : Int) (ps : List Int) (r : List Int) (rs : List (List Int)) :
    vecmat (q :: ps) (r :: rs) = addV (scale q r) (vecmat ps rs) := rfl
/-- Defining equation of `dot` (empty left list). -/
theorem dot_nil (Ps : List Int) : dot [] Ps = 0 := rfl
/-- Defining equation of `dot` (empty right list). -/
theorem dot_cons_nil (a : Int) (cs : List Int) : dot (a :: cs) [] = 0 := rfl
/-- Defining equation of `dot` (two non-empty lists). -/
theorem dot_cons_cons (a q : Int) (cs ps : List Int) : dot (a :: cs) (q :: ps) = a * q + dot cs ps := rfl
/-- Defining equation of `pkN` (empty list). -/
theorem pkN_nil : pkN B c [] = 0 := rfl
/-- Defining equation of `pkN` (cons): one Horner step. -/
theorem pkN_cons (x : Int) (xs : List Int) : pkN B c (x :: xs) = dig c x + B * pkN B c xs := rfl
/-- Defining equation of `inBN` (empty list). -/
theorem inBN_nil : inBN K [] = true := rfl
/-- Defining equation of `inBN` (cons). -/
theorem inBN_cons (x : Int) (xs : List Int) : inBN K (x :: xs) = (inK K x && inBN K xs) := rfl
/-- Defining equation of `hrow` (empty row). -/
theorem hrow_nil (acc : List Nat) : hrow B c [] acc = [] := rfl
/-- Defining equation of `hrow` (empty accumulator). -/
theorem hrow_cons_nil (x : Int) (xs : List Int) : hrow B c (x :: xs) [] = dig c x :: hrow B c xs [] := rfl
/-- Defining equation of `hrow` (row entry and accumulator entry). -/
theorem hrow_cons_cons (x : Int) (xs : List Int) (a : Nat) (as : List Nat) :
    hrow B c (x :: xs) (a :: as) = (dig c x + B * a) :: hrow B c xs as := rfl
/-- Defining equation of `colpkN` (no rows). -/
theorem colpkN_nil : colpkN B c [] = [] := rfl
/-- Defining equation of `colpkN` (cons): one Horner step per column. -/
theorem colpkN_cons (r : List Int) (rs : List (List Int)) :
    colpkN B c (r :: rs) = hrow B c r (colpkN B c rs) := rfl
/-- Defining equation of `unoff` (empty list). -/
theorem unoff_nil : unoff c [] = [] := rfl
/-- Defining equation of `unoff` (cons). -/
theorem unoff_cons (x : Nat) (xs : List Nat) : unoff c (x :: xs) = ((x : Int) - c) :: unoff c xs := rfl
/-- Defining equation of `allB` (no rows). -/
theorem allB_nil (q : List Int → Bool) : allB q [] = true := rfl
/-- Defining equation of `allB` (cons). -/
theorem allB_cons (q : List Int → Bool) (r : List Int) (rs : List (List Int)) :
    allB q (r :: rs) = (q r && allB q rs) := rfl
/-- Defining equation of `siteRows`: two empty lists pass. -/
theorem siteRows_nil_nil : siteRows B K n KR R p [] [] = true := rfl
/-- Defining equation of `siteRows`: a surplus frozen row fails. -/
theorem siteRows_nil_cons (f : List Int) (fs : List (List Int)) :
    siteRows B K n KR R p [] (f :: fs) = false := rfl
/-- Defining equation of `siteRows`: a missing frozen row fails. -/
theorem siteRows_cons_nil (t : List Int) (ts : List (List Int)) :
    siteRows B K n KR R p (t :: ts) [] = false := rfl
/-- Defining equation of `siteRows` (one token row and one frozen row). -/
theorem siteRows_cons_cons (t f : List Int) (ts fs : List (List Int)) :
    siteRows B K n KR R p (t :: ts) (f :: fs) = (rowOk B K n KR R p t f && siteRows B K n KR R p ts fs) :=
  rfl

end eqns

/-- `lenN` is `List.length`. -/
theorem lenN_eq {α : Type} : ∀ L : List α, lenN L = L.length
  | [] => rfl
  | _ :: xs => by rw [List.length_cons, ← lenN_eq xs]; rfl

/-! ## Semantics of the list programs -/

/-- `addV` adds entrywise. -/
theorem nth_addV : ∀ (xs ys : List Int) (i : Nat), nth 0 (addV xs ys) i = nth 0 xs i + nth 0 ys i
  | [], ys, i => by rw [addV_nil, nth_nil, zero_add]
  | x :: xs, [], 0 => by rw [addV_cons_nil, nth_cons_zero, nth_cons_zero, nth_nil, add_zero]
  | x :: xs, [], i + 1 => by
    rw [addV_cons_nil, nth_cons_succ, nth_cons_succ, nth_addV xs [] i, nth_nil, nth_nil]
  | x :: xs, y :: ys, 0 => by rw [addV_cons_cons, nth_cons_zero, nth_cons_zero, nth_cons_zero]
  | x :: xs, y :: ys, i + 1 => by
    rw [addV_cons_cons, nth_cons_succ, nth_cons_succ, nth_cons_succ, nth_addV xs ys i]

/-- `scale` multiplies entrywise. -/
theorem nth_scale (a : Int) : ∀ (xs : List Int) (i : Nat), nth 0 (scale a xs) i = a * nth 0 xs i
  | [], i => by rw [scale_nil, nth_nil, mul_zero]
  | x :: xs, 0 => by rw [scale_cons, nth_cons_zero, nth_cons_zero]
  | x :: xs, i + 1 => by rw [scale_cons, nth_cons_succ, nth_cons_succ, nth_scale a xs i]

/-- Entry `e` of `vecmat Ps rows` is the contraction `Σ_l Ps_l · rows_l[e]`. -/
theorem nth_vecmat : ∀ (Ps : List Int) (rows : List (List Int)) (e : Nat),
    nth 0 (vecmat Ps rows) e = ∑ l ∈ range rows.length, nth 0 Ps l * nth 0 (nth [] rows l) e
  | [], rows, e => by simp [vecmat_nil, nth_nil]
  | _ :: _, [], e => by simp [vecmat_cons_nil, nth_nil]
  | q :: ps, r :: rs, e => by
    rw [vecmat_cons_cons, nth_addV, nth_scale, nth_vecmat ps rs e, List.length_cons, sum_range_succ']
    simp only [nth_cons_succ, nth_cons_zero]
    ring

/-- `dot` is the finite sum `Σ_e Cs_e · Ps_e` over the length of `Cs`. -/
theorem dot_eq : ∀ (Cs Ps : List Int), dot Cs Ps = ∑ e ∈ range Cs.length, nth 0 Cs e * nth 0 Ps e
  | [], Ps => by simp [dot_nil]
  | _ :: _, [] => by simp [dot_cons_nil, nth_nil]
  | a :: cs, q :: ps => by
    rw [dot_cons_cons, dot_eq cs ps, List.length_cons, sum_range_succ']
    simp only [nth_cons_succ, nth_cons_zero]
    ring

/-- `inK K x` decides `|x| ≤ K`. -/
theorem inK_iff (K : Nat) (x : Int) : inK K x = true ↔ |x| ≤ (K : Int) := by
  rcases x with m | m
  · show Nat.ble m K = true ↔ _
    rw [Nat.ble_eq, Int.ofNat_eq_natCast, abs_of_nonneg (by positivity)]
    exact_mod_cast Iff.rfl
  · show Nat.blt m K = true ↔ _
    rw [Nat.blt_eq, Int.negSucc_eq, abs_neg, abs_of_nonneg (by positivity)]
    omega

/-- Under `|x| ≤ c`, the offset digit is exactly `x + c`. -/
theorem dig_spec (c : Nat) (x : Int) (h : |x| ≤ (c : Int)) : ((dig c x : Nat) : Int) = x + c := by
  rcases x with m | m
  · show ((Nat.add m c : Nat) : Int) = _
    push_cast [Nat.add_eq]; rfl
  · show ((Nat.sub c (Nat.succ m) : Nat) : Int) = _
    rw [Int.negSucc_eq, abs_neg, abs_of_nonneg (by positivity)] at h
    rw [Int.negSucc_eq]
    have : m + 1 ≤ c := by omega
    rw [Nat.sub_eq, Nat.cast_sub this]
    push_cast
    ring

/-- A list passing `inBN K` has every entry (and the default) in `[-K, K]`. -/
theorem inBN_spec (K : Nat) : ∀ (L : List Int), inBN K L = true → ∀ i, |nth 0 L i| ≤ (K : Int)
  | [], _, i => by rw [nth_nil, abs_zero]; positivity
  | x :: xs, h, i => by
    rw [inBN_cons, Bool.and_eq_true, inK_iff] at h
    cases i with
    | zero => rw [nth_cons_zero]; exact h.1
    | succ i => rw [nth_cons_succ]; exact inBN_spec K xs h.2 i

/-- Under the digit bound, `pkN` is the offset base-`B` value `Σ_i (L_i + c) Bⁱ`. -/
theorem pkN_spec (B c : Nat) : ∀ (L : List Int), inBN c L = true →
    ((pkN B c L : Nat) : Int) = ∑ i ∈ range L.length, (nth 0 L i + c) * (B : Int) ^ i
  | [], _ => by simp [pkN_nil]
  | x :: xs, h => by
    have h' := h
    rw [inBN_cons, Bool.and_eq_true, inK_iff] at h'
    rw [pkN_cons, Nat.cast_add, Nat.cast_mul, dig_spec c x h'.1, pkN_spec B c xs h'.2,
      List.length_cons, sum_range_succ', mul_sum]
    simp only [nth_cons_succ, nth_cons_zero, pow_zero, mul_one, pow_succ]
    rw [add_comm]
    congr 1
    refine sum_congr rfl fun i _ => ?_
    ring

/-- `hrow` has the length of its row. -/
theorem hrow_length (B c : Nat) : ∀ (r : List Int) (acc : List Nat), (hrow B c r acc).length = r.length
  | [], acc => by rw [hrow_nil]; rfl
  | x :: xs, [] => by rw [hrow_cons_nil, List.length_cons, List.length_cons, hrow_length B c xs []]
  | x :: xs, a :: as => by
    rw [hrow_cons_cons, List.length_cons, List.length_cons, hrow_length B c xs as]

/-- Entry `d` of `hrow` is one Horner step `(r_d + c) + B · acc_d`. -/
theorem nth_hrow (B c : Nat) : ∀ (r : List Int) (acc : List Nat) (d : Nat), d < r.length →
    nth 0 (hrow B c r acc) d = dig c (nth 0 r d) + B * nth 0 acc d
  | [], _, d, hd => absurd hd (Nat.not_lt_zero _)
  | x :: xs, [], 0, _ => by rw [hrow_cons_nil, nth_cons_zero, nth_cons_zero, nth_nil, mul_zero, add_zero]
  | x :: xs, [], d + 1, hd => by
    rw [hrow_cons_nil, nth_cons_succ, nth_cons_succ, nth_hrow B c xs [] d (by simp at hd; omega),
      nth_nil, nth_nil]
  | x :: xs, a :: as, 0, _ => by rw [hrow_cons_cons, nth_cons_zero, nth_cons_zero, nth_cons_zero]
  | x :: xs, a :: as, d + 1, hd => by
    rw [hrow_cons_cons, nth_cons_succ, nth_cons_succ, nth_cons_succ,
      nth_hrow B c xs as d (by simp at hd; omega)]

/-- Every row of a list passing `allB q` satisfies `q`. -/
theorem allB_spec (q : List Int → Bool) : ∀ (rows : List (List Int)), allB q rows = true →
    ∀ i, i < rows.length → q (nth [] rows i) = true
  | [], _, i, hi => absurd hi (Nat.not_lt_zero _)
  | r :: rs, h, i, hi => by
    rw [allB_cons, Bool.and_eq_true] at h
    cases i with
    | zero => rw [nth_cons_zero]; exact h.1
    | succ i => rw [nth_cons_succ]; exact allB_spec q rs h.2 i (by simp at hi; omega)

/-- Every entry of every row (including default reads) of a list passing `allB (inBN K)` lies in `[-K, K]`. -/
theorem allInB_spec (K : Nat) (rows : List (List Int)) (h : allB (inBN K) rows = true) (i e : Nat) :
    |nth 0 (nth [] rows i) e| ≤ (K : Int) := by
  by_cases hi : i < rows.length
  · exact inBN_spec K _ (allB_spec _ rows h i hi) e
  · have : nth [] rows i = [] := by
      clear h
      induction rows generalizing i with
      | nil => exact nth_nil _ _
      | cons r rs ih =>
        cases i with
        | zero => simp at hi
        | succ i => rw [nth_cons_succ]; exact ih i (by simp at hi; omega)
    rw [this, nth_nil, abs_zero]; positivity

/-- Every row of a list passing the length test has length `m`. -/
theorem allLen_spec (m : Nat) (rows : List (List Int))
    (h : allB (fun r => Nat.beq (lenN r) m) rows = true) (i : Nat) (hi : i < rows.length) :
    (nth [] rows i).length = m := by
  have := allB_spec _ rows h i hi
  rwa [Nat.beq_eq, lenN_eq] at this

/-- Entry `d` of `colpkN` is the offset column packing `Σ_i (rows_i[d] + c) Bⁱ`. -/
theorem nth_colpkN (B c m : Nat) : ∀ (rows : List (List Int)),
    allB (fun r => Nat.beq (lenN r) m) rows = true → ∀ d, d < m →
    nth 0 (colpkN B c rows) d = ∑ i ∈ range rows.length, dig c (nth 0 (nth [] rows i) d) * B ^ i
  | [], _, d, _ => by rw [colpkN_nil, nth_nil]; rfl
  | r :: rs, h, d, hd => by
    have hr := allLen_spec m (r :: rs) h 0 (by simp)
    rw [nth_cons_zero] at hr
    rw [allB_cons, Bool.and_eq_true] at h
    rw [colpkN_cons, nth_hrow B c r _ d (by rw [hr]; exact hd), nth_colpkN B c m rs h.2 d hd,
      List.length_cons, sum_range_succ', mul_sum]
    simp only [nth_cons_succ, nth_cons_zero, pow_zero, mul_one, pow_succ]
    rw [add_comm]
    congr 1
    refine sum_congr rfl fun i _ => ?_
    ring

/-- The column packing of a non-empty list has the width of its first row. -/
theorem colpkN_length (B c : Nat) (r : List Int) (rs : List (List Int)) :
    (colpkN B c (r :: rs)).length = r.length := by
  rw [colpkN_cons, hrow_length]

/-- `unoff` subtracts the offset from each entry. -/
theorem nth_unoff (cr : Nat) : ∀ (xs : List Nat) (d : Nat), d < xs.length →
    nth 0 (unoff cr xs) d = ((nth 0 xs d : Nat) : Int) - cr
  | [], d, hd => absurd hd (Nat.not_lt_zero _)
  | x :: xs, 0, _ => by rw [unoff_cons, nth_cons_zero, nth_cons_zero]
  | x :: xs, d + 1, hd => by
    rw [unoff_cons, nth_cons_succ, nth_cons_succ, nth_unoff cr xs d (by simp at hd; omega)]

/-- For `2 ≤ B`, `rep B n` is the geometric sum `Σ_{i<n} Bⁱ`. -/
theorem rep_eq (B n : Nat) (hB : 2 ≤ B) : ((rep B n : Nat) : Int) = ∑ i ∈ range n, (B : Int) ^ i := by
  have h : rep B n = ∑ i ∈ range n, B ^ i := (Nat.geomSum_eq hB n).symm
  rw [h]; push_cast; rfl

/-- The signed packed columns `PW_d = Σ_i Mout_{i,d} Bⁱ`, from the offset packing. -/
theorem nth_PW (B cw m : Nat) (hB : 2 ≤ B) (rows : List (List Int))
    (hl : allB (fun r => Nat.beq (lenN r) m) rows = true) (hb : allB (inBN cw) rows = true)
    (d : Nat) (hd : d < m) :
    nth 0 (unoff (Nat.mul cw (rep B rows.length)) (colpkN B cw rows)) d =
      ∑ i ∈ range rows.length, nth 0 (nth [] rows i) d * (B : Int) ^ i := by
  cases rows with
  | nil => simp [colpkN_nil, unoff_nil, nth_nil]
  | cons r rs =>
    have hr := allLen_spec m (r :: rs) hl 0 (by simp)
    rw [nth_cons_zero] at hr
    rw [nth_unoff _ _ _ (by rw [colpkN_length, hr]; exact hd), nth_colpkN B cw m _ hl d hd]
    push_cast
    rw [show ((Nat.mul cw (rep B (r :: rs).length) : Nat) : Int) = cw * (rep B (r :: rs).length : Int)
      from by push_cast [Nat.mul_eq]; rfl, rep_eq B _ hB, mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun i _ => ?_
    rw [dig_spec cw _ (allInB_spec cw _ hb i d)]
    ring

/-- A passing `siteRows` gives `rowOk` for every token index. -/
theorem siteRows_spec (B K n KR : Nat) (R : List Int) (p : Int) :
    ∀ (ts fs : List (List Int)), siteRows B K n KR R p ts fs = true →
      ∀ tk, tk < ts.length → rowOk B K n KR R p (nth [] ts tk) (nth [] fs tk) = true
  | [], _, _, tk, h => absurd h (Nat.not_lt_zero _)
  | _ :: _, [], h, _, _ => by rw [siteRows_cons_nil] at h; exact absurd h Bool.false_ne_true
  | t :: ts, f :: fs, h, tk, htk => by
    rw [siteRows_cons_cons, Bool.and_eq_true] at h
    cases tk with
    | zero => exact h.1
    | succ tk =>
      rw [nth_cons_succ, nth_cons_succ]
      exact siteRows_spec B K n KR R p ts fs h.2 tk (by simp at htk; omega)

/-- A passing `rowOk` gives the row length, the entry bound and the packed equality over `ℤ`. -/
theorem rowOk_spec {B K n KR : Nat} {R : List Int} {p : Int} {t f : List Int}
    (h : rowOk B K n KR R p t f = true) :
    f.length = n ∧ inBN K f = true ∧ ((pkN B K f : Nat) : Int) = dot t R + p + KR := by
  have h' : (Nat.beq (lenN f) n && (inBN K f && eqB (Int.ofNat (pkN B K f))
      (Int.add (Int.add (dot t R) p) (Int.ofNat KR)))) = true := h
  rw [Bool.and_eq_true, Bool.and_eq_true, Nat.beq_eq, lenN_eq] at h'
  refine ⟨h'.1, h'.2.1, ?_⟩
  have he := h'.2.2
  unfold eqB at he
  have hs : Int.sub (Int.ofNat (pkN B K f)) (Int.add (Int.add (dot t R) p) (Int.ofNat KR)) =
      (pkN B K f : Int) - (dot t R + p + KR) := rfl
  rw [hs] at he
  rcases hc : (pkN B K f : Int) - (dot t R + p + KR) with m | m
  · rw [hc] at he
    have : m = 0 := by simpa using he
    subst this
    simp only [Int.ofNat_eq_natCast, Nat.cast_zero] at hc
    linarith
  · rw [hc] at he; exact absurd he Bool.false_ne_true

/-! ## Sum exchanges (linearity of the packing) -/

/-- First sum exchange: pushes the input vector through the packed `WV` stage. -/
theorem sum_input_through_value {p q : Nat} (x : Fin p → Int) (P : Fin q → Int)
    (V : Fin p → Fin q → Int) :
    ∑ e, x e * ∑ l, P l * V e l = ∑ l, P l * ∑ e, x e * V e l := by
  simp only [mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring

/-- Second sum exchange: pushes the value vector through the packed `WO` stage. -/
theorem sum_value_through_output {p q : Nat} (Pw : Fin p → Int) (O : Fin q → Fin p → Int)
    (v : Fin q → Int) :
    ∑ l, (∑ d, Pw d * O l d) * v l = ∑ d, Pw d * ∑ l, v l * O l d := by
  simp only [mul_sum, sum_mul]
  rw [sum_comm]
  exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring

/-- Third sum exchange: moves the output contraction inside the base-`B` packing. -/
theorem sum_output_through_pack {p n : Nat} (B : Int) (M : Fin p → Fin n → Int)
    (o : Fin p → Int) :
    ∑ d, (∑ i, M d i * B ^ (i : Nat)) * o d = ∑ i, (∑ d, o d * M d i) * B ^ (i : Nat) := by
  simp only [sum_mul]
  rw [sum_comm]
  exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring

/-! ## Uniqueness of balanced digits -/

/-- Uniqueness of balanced base-`B` digits: if `2K < B` and both digit vectors lie in `[-K, K]`, equal packed values force equal digits. -/
theorem packed_inj (B K : Int) (hB : 2 * K < B) : ∀ (n : Nat) (a b : Fin n → Int),
    (∀ i, |a i| ≤ K) → (∀ i, |b i| ≤ K) →
    ∑ i, a i * B ^ (i : Nat) = ∑ i, b i * B ^ (i : Nat) → ∀ i, a i = b i
  | 0, _, _, _, _, _, i => i.elim0
  | n + 1, a, b, ha, hb, hs, i => by
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ] at hs
    simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ] at hs
    have hfac : ∀ c : Fin (n + 1) → Int,
        ∑ i : Fin n, c i.succ * (B ^ (i : Nat) * B) = B * ∑ i : Fin n, c i.succ * B ^ (i : Nat) := by
      intro c; rw [mul_sum]; exact sum_congr rfl fun _ _ => by ring
    rw [hfac a, hfac b] at hs
    have hK0 : 0 ≤ K := (abs_nonneg _).trans (ha 0)
    have hB0 : B ≠ 0 := by omega
    have h0 : a 0 = b 0 := by
      have hdvd : B ∣ a 0 - b 0 :=
        ⟨(∑ i : Fin n, b i.succ * B ^ (i : Nat)) - ∑ i : Fin n, a i.succ * B ^ (i : Nat), by
          rw [mul_sub]; linarith⟩
      have hlt : |a 0 - b 0| < B := by
        have h1 := ha 0; have h2 := hb 0
        rw [abs_le] at h1 h2; rw [abs_lt]; constructor <;> linarith
      have := Int.eq_zero_of_abs_lt_dvd hdvd hlt
      linarith
    have hrest : ∑ i : Fin n, a i.succ * B ^ (i : Nat) = ∑ i : Fin n, b i.succ * B ^ (i : Nat) :=
      mul_left_cancel₀ hB0 (by linarith)
    have ih := packed_inj B K hB n (fun i => a i.succ) (fun i => b i.succ) (fun _ => ha _)
      (fun _ => hb _) hrest
    exact Fin.cases h0 (fun i => ih i) i

/-! ## Crude entry bounds -/

/-- Crude bound for a finite sum of `n` terms each bounded by `c`. -/
theorem abs_sum_fin_le {n : Nat} (f : Fin n → Int) (c : Int) (h : ∀ i, |f i| ≤ c) :
    |∑ i, f i| ≤ n * c := by
  calc |∑ i, f i| ≤ ∑ i, |f i| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin n, c := sum_le_sum fun i _ => h i
    _ = n * c := by simp

/-- Crude bound for a product of two bounded integers. -/
theorem abs_mul_le' {a b A C : Int} (ha : |a| ≤ A) (hb : |b| ≤ C) : |a * b| ≤ A * C := by
  rw [abs_mul]
  exact mul_le_mul ha hb (abs_nonneg _) ((abs_nonneg _).trans ha)

/-- The crude output bound `128·Kw·32·Ko·128·(Kt+Kp)·Kv` from the input bounds alone. -/
theorem ovec_mul_bound {n : Nat} (W : Transformer.Weights) (h : Fin 4) (tk : Fin 114) (j : Fin 3)
    (Mf : Fin 128 → Fin n → Int) (Kt Kp Kv Ko Kw : Int)
    (ht : ∀ d, |W.tok tk d| ≤ Kt) (hp : ∀ d, |W.pos j d| ≤ Kp) (hv : ∀ d l, |W.WV h d l| ≤ Kv)
    (ho : ∀ l d, |W.WO h l d| ≤ Ko) (hm : ∀ d i, |Mf d i| ≤ Kw) (i : Fin n) :
    |∑ d, W.ovec h tk j d * Mf d i| ≤ 128 * (Kw * (32 * (Ko * (128 * ((Kt + Kp) * Kv))))) := by
  have hx : ∀ d, |W.xhat tk j d| ≤ Kt + Kp := fun d =>
    (abs_add_le _ _).trans (add_le_add (ht d) (hp d))
  have hvv : ∀ l, |W.vvec h tk j l| ≤ 128 * ((Kt + Kp) * Kv) := fun l => by
    have := abs_sum_fin_le (fun d => W.xhat tk j d * W.WV h d l) _ fun d => abs_mul_le' (hx d) (hv d l)
    simpa [Transformer.Weights.vvec] using this
  have hov : ∀ d, |W.ovec h tk j d| ≤ 32 * (128 * ((Kt + Kp) * Kv) * Ko) := fun d => by
    have := abs_sum_fin_le (fun l => W.vvec h tk j l * W.WO h l d) _ fun l => abs_mul_le' (hvv l) (ho l d)
    simpa [Transformer.Weights.ovec] using this
  have := abs_sum_fin_le (fun d => W.ovec h tk j d * Mf d i) _ fun d => abs_mul_le' (hov d) (hm d i)
  calc _ ≤ ((128 : Nat) : Int) * (32 * (128 * ((Kt + Kp) * Kv) * Ko) * Kw) := this
    _ = 128 * (Kw * (32 * (Ko * (128 * ((Kt + Kp) * Kv))))) := by push_cast; ring

/-! ## The generic head theorem -/

section head

variable (W : Transformer.Weights) (h : Fin 4) {n : Nat} (B K Kt Kp Kv Ko Kw : Nat)
  (tok pos WV WO Mrows F0 F1 : List (List Int)) (F2 : List Int) (Mf : Fin 128 → Fin n → Int)

/-- The packed head product, entrywise. -/
theorem headR_spec (hB : 2 ≤ B)
    (hWV : ∀ d l, W.WV h d l = nth 0 (nth [] WV (h.val * 32 + l.val)) d.val)
    (hWO : ∀ l d, W.WO h l d = nth 0 (nth [] WO (h.val * 128 + d.val)) l.val)
    (hM : ∀ d i, Mf d i = nth 0 (nth [] Mrows i.val) d.val)
    (hlv : (slice (h.val * 32) 32 WV).length = 32) (hlo : (slice (h.val * 128) 128 WO).length = 128)
    (hlm : Mrows.length = n) (hal : allB (fun r => Nat.beq (lenN r) 128) Mrows = true)
    (hbm : allB (inBN Kw) Mrows = true) (e : Fin 128) :
    nth 0 (headR B Kw n h.val WV WO Mrows) e.val =
      ∑ l : Fin 32, (∑ d : Fin 128, (∑ i : Fin n, Mf d i * (B : Int) ^ (i : Nat)) * W.WO h l d) *
        W.WV h e l := by
  subst hlm
  unfold headR
  rw [nth_vecmat, hlv, ← Fin.sum_univ_eq_sum_range]
  refine sum_congr rfl fun l _ => ?_
  rw [nth_slice _ _ _ _ l.isLt, ← hWV, nth_vecmat, hlo, ← Fin.sum_univ_eq_sum_range]
  congr 1
  refine sum_congr rfl fun d _ => ?_
  rw [nth_slice _ _ _ _ d.isLt, ← hWO, nth_PW B Kw 128 hB Mrows hal hbm d.val d.isLt,
    ← Fin.sum_univ_eq_sum_range]
  congr 1
  refine sum_congr rfl fun i _ => ?_
  rw [hM]

/-- One site: a checked frozen row equals the raw `Σ_d ovec_d · Mout_{d,i}`. -/
theorem site_of_row (tk : Fin 114) (j : Fin 3) (R f : List Int)
    (htok : ∀ tk d, W.tok tk d = nth 0 (nth [] tok tk.val) d.val)
    (hpos : ∀ j d, W.pos j d = nth 0 (nth [] pos j.val) d.val)
    (hR : ∀ e : Fin 128, nth 0 R e.val =
      ∑ l : Fin 32, (∑ d : Fin 128, (∑ i : Fin n, Mf d i * (B : Int) ^ (i : Nat)) * W.WO h l d) *
        W.WV h e l)
    (htl : (nth [] tok tk.val).length = 128) (hpl : (nth [] pos j.val).length = 128)
    (hB : 2 * (K : Int) < B) (hB2 : 2 ≤ B) (hT : ∀ i, |∑ d, W.ovec h tk j d * Mf d i| ≤ (K : Int))
    (hrow : rowOk B K n (Nat.mul K (rep B n)) R (dot (nth [] pos j.val) R) (nth [] tok tk.val) f = true)
    (i : Fin n) :
    nth 0 f i.val = ∑ d, W.ovec h tk j d * Mf d i := by
  obtain ⟨hlf, hinf, hpk⟩ := rowOk_spec hrow
  -- the packed true row
  have htrue : dot (nth [] tok tk.val) R + dot (nth [] pos j.val) R =
      ∑ i : Fin n, (∑ d, W.ovec h tk j d * Mf d i) * (B : Int) ^ (i : Nat) := by
    rw [dot_eq, dot_eq, htl, hpl, ← Fin.sum_univ_eq_sum_range, ← Fin.sum_univ_eq_sum_range,
      ← sum_add_distrib]
    have hx : ∀ e : Fin 128, nth 0 (nth [] tok tk.val) e.val * nth 0 R e.val +
        nth 0 (nth [] pos j.val) e.val * nth 0 R e.val = W.xhat tk j e * nth 0 R e.val := by
      intro e
      rw [Transformer.Weights.xhat, htok, hpos]
      ring
    rw [sum_congr rfl fun e _ => hx e]
    simp only [hR]
    rw [sum_input_through_value, sum_value_through_output, sum_output_through_pack]
    rfl
  -- the packed frozen row, offset removed
  have hfro : ∑ i : Fin n, nth 0 f i.val * (B : Int) ^ (i : Nat) =
      dot (nth [] tok tk.val) R + dot (nth [] pos j.val) R := by
    have h1 := pkN_spec B K f hinf
    rw [hpk, hlf] at h1
    have h2 : (((Nat.mul K (rep B n)) : Nat) : Int) = (K : Int) * ∑ i ∈ range n, (B : Int) ^ i := by
      rw [← rep_eq B n hB2]; push_cast [Nat.mul_eq]; rfl
    rw [h2] at h1
    have h3 : ∑ i ∈ range n, (nth 0 f i + K) * (B : Int) ^ i =
        ∑ i ∈ range n, nth 0 f i * (B : Int) ^ i + (K : Int) * ∑ i ∈ range n, (B : Int) ^ i := by
      rw [mul_sum, ← sum_add_distrib]; exact sum_congr rfl fun _ _ => by ring
    rw [h3] at h1
    rw [Fin.sum_univ_eq_sum_range (fun i => nth 0 f i * (B : Int) ^ i) n]
    linarith
  exact packed_inj B K hB n (fun i => nth 0 f i.val) _ (fun i => inBN_spec K f hinf i.val) hT
    (hfro.trans htrue) i

/-- **Generic head theorem.** A passing `headCheck` identifies the three frozen slots of the head
with the raw model, entrywise. -/
theorem field_of_check
    (htok : ∀ tk d, W.tok tk d = nth 0 (nth [] tok tk.val) d.val)
    (hpos : ∀ j d, W.pos j d = nth 0 (nth [] pos j.val) d.val)
    (hWV : ∀ d l, W.WV h d l = nth 0 (nth [] WV (h.val * 32 + l.val)) d.val)
    (hWO : ∀ l d, W.WO h l d = nth 0 (nth [] WO (h.val * 128 + d.val)) l.val)
    (hM : ∀ d i, Mf d i = nth 0 (nth [] Mrows i.val) d.val)
    (hc : headCheck B K Kt Kp Kv Ko Kw n h.val tok pos WV WO Mrows F0 F1 F2 = true) :
    (∀ (tk : Fin 114) (i : Fin n), nth 0 (nth [] F0 tk.val) i.val = ∑ d, W.ovec h tk 0 d * Mf d i) ∧
    (∀ (tk : Fin 114) (i : Fin n), nth 0 (nth [] F1 tk.val) i.val = ∑ d, W.ovec h tk 1 d * Mf d i) ∧
    (∀ i : Fin n, nth 0 F2 i.val = ∑ d, W.ovec h 113 2 d * Mf d i) := by
  simp only [headCheck, paramsOk, inputsOk, sitesOk, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq,
    Nat.beq_eq] at hc
  obtain ⟨⟨hKK, hBK, hB2⟩, ⟨hlt, hat, hbt, hlp, hap, hbp, hlv, hbv, hlo, hbo, hlm, hal, hbm⟩,
    hs0, hs1, hs2⟩ := hc
  rw [lenN_eq] at hlt hlp hlv hlo hlm
  have hB : 2 * (K : Int) < B := by
    have : 2 * K < B := hBK
    exact_mod_cast this
  have hKK' : (128 * (Kw * (32 * (Ko * (128 * ((Kt + Kp) * Kv))))) : Int) ≤ K := by
    have : 128 * (Kw * (32 * (Ko * (128 * ((Kt + Kp) * Kv))))) ≤ K := hKK
    exact_mod_cast this
  -- entry bounds of the inputs
  have bt : ∀ tk d, |W.tok tk d| ≤ (Kt : Int) := fun tk d => by
    rw [htok]; exact allInB_spec Kt tok hbt _ _
  have bp : ∀ j d, |W.pos j d| ≤ (Kp : Int) := fun j d => by
    rw [hpos]; exact allInB_spec Kp pos hbp _ _
  have bv : ∀ d l, |W.WV h d l| ≤ (Kv : Int) := fun d l => by
    rw [hWV, ← nth_slice (h.val * 32) 32 WV l.val l.isLt]; exact allInB_spec Kv _ hbv _ _
  have bo : ∀ l d, |W.WO h l d| ≤ (Ko : Int) := fun l d => by
    rw [hWO, ← nth_slice (h.val * 128) 128 WO d.val d.isLt]; exact allInB_spec Ko _ hbo _ _
  have bm : ∀ d i, |Mf d i| ≤ (Kw : Int) := fun d i => by
    rw [hM]; exact allInB_spec Kw _ hbm _ _
  have hT : ∀ tk j i, |∑ d, W.ovec h tk j d * Mf d i| ≤ (K : Int) := fun tk j i =>
    (ovec_mul_bound W h tk j Mf Kt Kp Kv Ko Kw (bt tk) (bp j) bv bo bm i).trans hKK'
  have hR := headR_spec W h B Kw WV WO Mrows Mf hB2 hWV hWO hM hlv hlo hlm hal hbm
  have tl : ∀ tk : Fin 114, (nth [] tok tk.val).length = 128 := fun tk =>
    allLen_spec 128 tok hat tk.val (by rw [hlt]; exact tk.isLt)
  have pl : ∀ j : Fin 3, (nth [] pos j.val).length = 128 := fun j =>
    allLen_spec 128 pos hap j.val (by rw [hlp]; exact j.isLt)
  refine ⟨fun tk i => ?_, fun tk i => ?_, fun i => ?_⟩
  · exact site_of_row W h B K tok pos Mf tk 0 _ _ htok hpos hR (tl tk) (pl 0) hB hB2 (hT tk 0)
      (siteRows_spec B K n _ _ _ tok F0 hs0 tk.val (by rw [hlt]; exact tk.isLt)) i
  · exact site_of_row W h B K tok pos Mf tk 1 _ _ htok hpos hR (tl tk) (pl 1) hB hB2 (hT tk 1)
      (siteRows_spec B K n _ _ _ tok F1 hs1 tk.val (by rw [hlt]; exact tk.isLt)) i
  · exact site_of_row W h B K tok pos Mf 113 2 _ _ htok hpos hR (tl 113) (pl 2) hB hB2 (hT 113 2)
      hs2 i

end head

/-! ## Statements against `toTables` and `rawTables` -/

/-- **TI of one head**, every position and token, from one passing `headCheck` over `Win`. -/
theorem TI_head_of_check (W : Transformer.Weights) (S : Nat) (T : TransformerCore.Tab) (h : Fin 4)
    (tok pos WV WO Win : List (List Int)) {B K Kt Kp Kv Ko Kw : Nat}
    (htok : ∀ tk d, W.tok tk d = nth 0 (nth [] tok tk.val) d.val)
    (hpos : ∀ j d, W.pos j d = nth 0 (nth [] pos j.val) d.val)
    (hWV : ∀ d l, W.WV h d l = nth 0 (nth [] WV (h.val * 32 + l.val)) d.val)
    (hWO : ∀ l d, W.WO h l d = nth 0 (nth [] WO (h.val * 128 + d.val)) l.val)
    (hWin : ∀ d i, W.Win d i = nth 0 (nth [] Win i.val) d.val)
    (hc : headCheck B K Kt Kp Kv Ko Kw 512 h.val tok pos WV WO Win
      (nth [] T.TI0 h.val) (nth [] T.TI1 h.val) (nth [] T.TI2 h.val) = true)
    (j : Fin 3) (tk : Fin 114) :
    (TransformerBridge.toTables T).TI h j tk = (W.rawTables S).TI h j tk := by
  obtain ⟨h0, h1, h2⟩ := field_of_check W h B K Kt Kp Kv Ko Kw tok pos WV WO Win _ _ _ W.Win
    htok hpos hWV hWO hWin hc
  funext i
  change _ = (if j = 2 ∧ tk ≠ 113 then 0 else ∑ d, W.ovec h tk j d * W.Win d i)
  fin_cases j
  · exact h0 tk i
  · exact h1 tk i
  · change (if tk = 113 then nth 0 (nth [] T.TI2 h.val) i.val else 0) = _
    by_cases ht : tk = 113
    · subst ht; simpa using h2 i
    · simp [ht]

/-- **TU of one head**, every position and token, from one passing `headCheck` over `U`. -/
theorem TU_head_of_check (W : Transformer.Weights) (S : Nat) (T : TransformerCore.Tab) (h : Fin 4)
    (tok pos WV WO U : List (List Int)) {B K Kt Kp Kv Ko Kw : Nat}
    (htok : ∀ tk d, W.tok tk d = nth 0 (nth [] tok tk.val) d.val)
    (hpos : ∀ j d, W.pos j d = nth 0 (nth [] pos j.val) d.val)
    (hWV : ∀ d l, W.WV h d l = nth 0 (nth [] WV (h.val * 32 + l.val)) d.val)
    (hWO : ∀ l d, W.WO h l d = nth 0 (nth [] WO (h.val * 128 + d.val)) l.val)
    (hU : ∀ d k, W.U d k = nth 0 (nth [] U k.val) d.val)
    (hc : headCheck B K Kt Kp Kv Ko Kw 113 h.val tok pos WV WO U
      (nth [] T.TU0 h.val) (nth [] T.TU1 h.val) (nth [] T.TU2 h.val) = true)
    (j : Fin 3) (tk : Fin 114) :
    (TransformerBridge.toTables T).TU h j tk = (W.rawTables S).TU h j tk := by
  obtain ⟨h0, h1, h2⟩ := field_of_check W h B K Kt Kp Kv Ko Kw tok pos WV WO U _ _ _ W.U
    htok hpos hWV hWO hU hc
  funext k
  change _ = (if j = 2 ∧ tk ≠ 113 then 0 else ∑ d, W.ovec h tk j d * W.U d k)
  fin_cases j
  · exact h0 tk k
  · exact h1 tk k
  · change (if tk = 113 then nth 0 (nth [] T.TU2 h.val) k.val else 0) = _
    by_cases ht : tk = 113
    · subst ht; simpa using h2 k
    · simp [ht]

end TransformerBridge.Kronecker
