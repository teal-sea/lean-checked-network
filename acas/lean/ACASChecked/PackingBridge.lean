import ACASChecked.MatrixSound
import ACASChecked.SameSpec
set_option maxRecDepth 4096
namespace RouteA
open Finset

@[simp] theorem lenN_eq {α : Type} (xs : List α) : lenN xs = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simpa [lenN] using congrArg Nat.succ ih

@[simp] theorem inK_spec (K : Nat) (x : Int) : inK K x = true ↔ |x| ≤ (K : Int) := by
  cases x with
  | ofNat n => simp [inK]
  | negSucc n =>
    rw [abs_of_nonpos (by omega : Int.negSucc n ≤ 0)]
    simp only [inK, Nat.blt_eq, decide_eq_true_eq, Int.negSucc_eq]
    omega

@[simp] theorem inBN_spec (K : Nat) (xs : List Int) :
    inBN K xs = true ↔ ∀ x ∈ xs, |x| ≤ (K : Int) := by
  induction xs with
  | nil => simp [inBN]
  | cons x xs ih =>
    change (inK K x && inBN K xs = true) ↔ _
    simp [ih]

@[simp] theorem allB_spec (p : List Int → Bool) (xs : List (List Int)) :
    allB p xs = true ↔ ∀ x ∈ xs, p x = true := by
  induction xs with
  | nil => simp [allB]
  | cons x xs ih =>
    change (p x && allB p xs = true) ↔ _
    simp [ih]

@[simp] theorem shape_spec (n : Nat) (xs : List Int) :
    shape n xs = true ↔ xs.length = n := by simp [shape]

/-- Offset digits retain the original integer whenever the checked bound holds. -/
theorem dig_cast (c : Nat) (x : Int) (h : |x| ≤ (c : Int)) :
    (dig c x : Int) = x + c := by
  cases x with
  | ofNat n => simp [dig]
  | negSucc n =>
    have hn : n + 1 ≤ c := by
      simp only [Int.negSucc_eq, abs_neg, Nat.cast_add, Nat.cast_one,
        abs_of_nonneg (by positivity : (0 : Int) ≤ (n : Int) + 1)] at h
      omega
    change ((c - (n+1) : Nat) : Int) = Int.negSucc n + c
    rw [Int.ofNat_sub hn]
    simp only [Int.negSucc_eq, Nat.cast_add, Nat.cast_one]
    omega

/-- Signed Horner packing used as the mathematical interpretation of the executable pack. -/
def packZ (B : Int) : List Int → Int
  | [] => 0
  | x :: xs => x + B * packZ B xs

def repZ (B : Int) : Nat → Int
  | 0 => 0
  | n+1 => 1 + B * repZ B n

theorem pkN_cast (B c : Nat) (xs : List Int) (h : inBN c xs = true) :
    (pkN B c xs : Int) = packZ B xs + c * repZ B xs.length := by
  induction xs with
  | nil => simp [pkN, packZ, repZ]
  | cons x xs ih =>
    have hh := inBN_spec c (x::xs) |>.mp h
    have hx := hh x (by simp)
    have ht : inBN c xs = true := (inBN_spec _ _).mpr (fun z hz => hh z (by simp [hz]))
    change ((dig c x + B * pkN B c xs : Nat) : Int) = _
    simp only [Nat.cast_add, Nat.cast_mul, dig_cast c x hx, ih ht,
      packZ, List.length_cons, repZ]
    ring

theorem repZ_eq_sum (B : Int) (n : Nat) : repZ B n = ∑ i : Fin n, B^(i : Nat) := by
  induction n with
  | zero => simp [repZ]
  | succ n ih =>
    rw [repZ, Fin.sum_univ_succ, ih, mul_sum]
    simp only [Fin.val_zero, pow_zero, Fin.val_succ, pow_succ]
    congr 1
    apply sum_congr rfl
    intro i _
    ring

theorem rep_cast (B n : Nat) (hB : 1 < B) : (rep B n : Int) = repZ B n := by
  have he := geom_sum_mul_of_one_le (R := Nat) (show 1 ≤ B by omega) n
  have hd : B - 1 ≠ 0 := by omega
  have hr : rep B n = ∑ i ∈ range n, B^i := by
    change (B^n-1)/(B-1) = _
    rw [← he, Nat.mul_div_cancel _ (Nat.sub_pos_of_lt hB)]
  rw [hr, repZ_eq_sum]
  simp only [Nat.cast_sum, Nat.cast_pow, Fin.sum_univ_eq_sum_range]

theorem unoff_pack (B c t : Nat) (hB : 1 < B) (v : List (List Int))
    (hs : ∀ r ∈ v, r.length = t) (hb : allB (inBN c) v = true) :
    unoff (c * rep B t) (v.map (pkN B c)) = v.map (packZ B) := by
  induction v with
  | nil => rfl
  | cons r rs ih =>
    have hr := hs r (by simp)
    have hbr : inBN c r = true := (allB_spec _ _).mp hb r (by simp)
    have hbs : allB (inBN c) rs = true := (allB_spec _ _).mpr
      (fun a ha => (allB_spec _ _).mp hb a (by simp [ha]))
    change ((pkN B c r : Int) - ↑(c * rep B t)) ::
      unoff (c * rep B t) (rs.map (pkN B c)) = _
    rw [pkN_cast B c r hbr, Nat.cast_mul, rep_cast B t hB, hr,
      ih (fun a ha => hs a (by simp [ha])) hbs]
    simp

theorem packZ_ofFn (B : Int) {t : Nat} (v : Fin t → Int) :
    packZ B (List.ofFn v) = ∑ j, v j * B^(j : Nat) := by
  induction t with
  | zero => simp [packZ]
  | succ t ih =>
    rw [List.ofFn_succ, packZ, Fin.sum_univ_succ, ih, mul_sum]
    simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ]
    congr 1
    apply sum_congr rfl
    intro i _
    ring

theorem dot_ofFn {n : Nat} (a b : Fin n → Int) :
    dot (List.ofFn a) (List.ofFn b) = ∑ i, a i * b i := by
  induction n with
  | zero => simp [dot]
  | succ n ih =>
    rw [List.ofFn_succ, List.ofFn_succ, Fin.sum_univ_succ]
    change a 0 * b 0 + dot (List.ofFn (fun i => a i.succ))
      (List.ofFn (fun i => b i.succ)) = _
    rw [ih]

theorem rowChecks_spec (w c : List (List Int)) (p : List Int) (B K KR : Nat)
    (h : rowChecks w p c B K KR = true) :
    List.Forall₂ (fun r cr => (pkN B K cr : Int) = dot r p + KR) w c := by
  induction w generalizing c with
  | nil =>
    cases c with
    | nil => exact .nil
    | cons x xs => simp [rowChecks] at h
  | cons r rs ih =>
    cases c with
    | nil => simp [rowChecks] at h
    | cons cr cs =>
      change (eqB _ _ && rowChecks rs p cs B K KR) = true at h
      have hh : eqB (pkN B K cr) (dot r p + KR) = true ∧ rowChecks rs p cs B K KR = true := by
        simpa only [Bool.and_eq_true, Int.add_def, Int.ofNat_eq_natCast] using h
      exact .cons (eqB_spec _ _ hh.1) (ih cs hh.2)

theorem block_sound_fin {m n t : Nat} (hn : 0 < n)
    (w : Fin m → Fin n → Int) (v : Fin n → Fin t → Int)
    (c : Fin m → Fin t → Int)
    (h : block (List.ofFn (fun i => List.ofFn (w i)))
      (List.ofFn (fun i => List.ofFn (v i)))
      (List.ofFn (fun i => List.ofFn (c i))) = true) :
    ∀ i j, c i j = ∑ k, w i k * v k j := by
  let B : Nat := 2^160
  let G : Nat := 2^60
  let H : Nat := 2^60
  let K : Nat := 2^127
  have ht : lenN ((List.ofFn (fun i => List.ofFn (v i))).headD []) = t := by
    cases n with
    | zero => omega
    | succ n => simp [List.ofFn_succ]
  unfold block at h
  rw [ht] at h
  dsimp only at h
  simp only [Bool.and_eq_true] at h
  rcases h with ⟨hsize, hbase, hws, hvs, hcs, hlen, hw, hv, hc, he⟩
  have hvb := hv
  simp only [allB_spec, List.forall_mem_ofFn_iff, inBN_spec,
    List.forall_mem_ofFn_iff] at hw hv hc
  have hup : unoff (H * rep B t)
      ((List.ofFn (fun i => List.ofFn (v i))).map (pkN B H)) =
      List.ofFn (fun i => packZ B (List.ofFn (v i))) := by
    rw [unoff_pack B H t (by norm_num [B]) _
      (by simp only [List.forall_mem_ofFn_iff, List.length_ofFn]; simp) hvb,
      List.map_ofFn]
    rfl
  change rowChecks (List.ofFn (fun i => List.ofFn (w i)))
    (unoff (H * rep B t) ((List.ofFn (fun i => List.ofFn (v i))).map (pkN B H)))
    (List.ofFn (fun i => List.ofFn (c i))) B K (K * rep B t) = true at he
  rw [hup] at he
  have heq := rowChecks_spec _ _ _ B K (K * rep B t) he
  intro i
  have hi := heq.get (i := i.val) (by simpa using i.isLt) (by simpa using i.isLt)
  simp only [List.get_eq_getElem, List.getElem_ofFn] at hi
  have hcb : inBN K (List.ofFn (c i)) = true := by
    simp only [inBN_spec, List.forall_mem_ofFn_iff]
    exact hc i
  rw [pkN_cast B K _ hcb, List.length_ofFn, Nat.cast_mul,
    rep_cast B t (by norm_num [B])] at hi
  have hpack : ∑ j, c i j * (B : Int)^(j : Nat) =
      ∑ k, w i k * ∑ j, v k j * (B : Int)^(j : Nat) := by
    rw [← packZ_ofFn, ← dot_ofFn]
    simp_rw [← packZ_ofFn]
    linarith [hi]
  apply packed_product_sound (B : Int) (K : Int) (G : Int) (H : Int)
    (w i) v (c i) (by norm_num [B, K]) (by positivity) (by positivity)
    (hw i) hv (hc i) _ hpack
  have hs := Nat.le_of_ble_eq_true hsize
  rw [lenN_eq, List.length_ofFn] at hs
  change n * (G * H) ≤ K at hs
  have hsI := Int.ofNat_le.mpr hs
  simpa only [Nat.cast_mul, mul_assoc] using hsI

theorem ofFn_getD {α : Type} (xs : List α) (d : α) (n : Nat) (h : xs.length = n) :
    List.ofFn (fun i : Fin n => xs.getD i.val d) = xs := by
  subst n
  simpa only [List.getD_eq_get] using List.ofFn_get xs

def matrix (xs : List (List Int)) (i j : Nat) : Int := (xs.getD i []).getD j 0

theorem ofFn_matrix (xs : List (List Int)) (m n : Nat) (hm : xs.length = m)
    (hn : ∀ r ∈ xs, r.length = n) :
    List.ofFn (fun i : Fin m => List.ofFn (fun j : Fin n => matrix xs i j)) = xs := by
  calc
    _ = List.ofFn (fun i : Fin m => xs.getD i []) := by
      apply congrArg List.ofFn
      funext i
      apply ofFn_getD
      have hi : i.val < xs.length := by omega
      rw [List.getD_eq_getElem xs [] hi]
      exact hn _ (List.getElem_mem hi)
    _ = xs := ofFn_getD xs [] m hm

/-- The executable receipt implies integer entrywise matrix equality.
The row and column indices are the dimensions extracted from the receipt itself. -/
theorem block_sound_list (w v c : List (List Int)) (hn : 0 < v.length)
    (h : block w v c = true) :
    ∀ (i : Fin w.length) (j : Fin (v.headD []).length),
      matrix c i j = ∑ k : Fin v.length, matrix w i k * matrix v k j := by
  have hh := h
  unfold block at hh
  dsimp only at hh
  simp only [Bool.and_eq_true] at hh
  rcases hh with ⟨_, _, hw, hv, hc, hm, _⟩
  have hw' : ∀ r ∈ w, r.length = v.length := by
    simpa only [allB_spec, shape_spec, lenN_eq] using hw
  have hv' : ∀ r ∈ v, r.length = (v.headD []).length := by
    simpa only [allB_spec, shape_spec, lenN_eq] using hv
  have hc' : ∀ r ∈ c, r.length = (v.headD []).length := by
    simpa only [allB_spec, shape_spec, lenN_eq] using hc
  have hm' : c.length = w.length := by
    simpa only [lenN_eq] using Nat.eq_of_beq_eq_true hm
  have hf := block_sound_fin hn
    (fun i : Fin w.length => fun k : Fin v.length => matrix w i k)
    (fun k : Fin v.length => fun j : Fin (v.headD []).length => matrix v k j)
    (fun i : Fin w.length => fun j : Fin (v.headD []).length => matrix c i j)
    (by simpa only [ofFn_matrix w _ _ rfl hw', ofFn_matrix v _ _ rfl hv',
      ofFn_matrix c _ _ hm' hc'] using h)
  exact hf

#print axioms block_sound_list
#print axioms block_sound_fin
#print axioms dig_cast
#print axioms pkN_cast
end RouteA
