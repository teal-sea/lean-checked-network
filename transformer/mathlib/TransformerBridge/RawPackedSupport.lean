import TransformerBridge.RawPilotSupport

/-! Signed packing support, independent of concrete weights and frozen numeric data. -/
namespace TransformerBridge.RawPacked

open TransformerCore (B pkI AbsBnd)
open TransformerBridge.RawPilot (sumN contract)

/-- Little-endian signed packing of exactly n coordinates. -/
def pack {n : Nat} (f : Fin n → Int) : Int := pkI (List.ofFn f)

theorem pack_zero (f : Fin 0 → Int) : pack f = 0 := by
  simp [pack, pkI]

theorem pack_succ {n : Nat} (f : Fin (n + 1) → Int) :
    pack f = f 0 + (B : Int) * pack (fun i => f i.succ) := by
  simp only [pack, List.ofFn_succ, pkI, Int.add_def, Int.mul_def, Int.ofNat_eq_natCast]

theorem pack_add {n : Nat} (f g : Fin n → Int) :
    pack (fun i => f i + g i) = pack f + pack g := by
  induction n with
  | zero => exact (zero_add 0).symm
  | succ n ih =>
    rw [pack_succ, pack_succ f, pack_succ g, ih]
    ring

theorem pack_mul {n : Nat} (c : Int) (f : Fin n → Int) :
    pack (fun i => c * f i) = c * pack f := by
  induction n with
  | zero =>
    change (0 : Int) = c * 0
    exact (mul_zero c).symm
  | succ n ih =>
    rw [pack_succ, pack_succ f, ih]
    ring

theorem pack_const_zero (n : Nat) : pack (fun _ : Fin n => (0 : Int)) = 0 := by
  have h := pack_mul (n := n) 0 (fun _ => (0 : Int))
  simpa only [zero_mul] using h

theorem pack_sumN {n : Nat} (m : Nat) (f : Nat → Fin n → Int) :
    pack (fun i => sumN m (fun d => f d i)) = sumN m (fun d => pack (f d)) := by
  induction m with
  | zero => exact pack_const_zero n
  | succ m ih =>
    change pack (fun i => sumN m (fun d => f d i) + f m i) =
      sumN m (fun d => pack (f d)) + pack (f m)
    rw [pack_add, ih]

/-- One signed packed contraction replaces all n scalar contractions. -/
theorem pack_contract {m n : Nat} (o : Fin m → Int) (W : Fin m → Fin n → Int) :
    pack (fun i => contract o (fun d => W d i)) = contract o (fun d => pack (W d)) := by
  unfold contract
  rw [pack_sumN]
  congr 1
  funext k
  by_cases hk : k < m
  · simp only [dite_eq_left hk]
    exact pack_mul (o ⟨k, hk⟩) (W ⟨k, hk⟩)
  · simp only [dite_eq_right hk]
    exact pack_const_zero n

/-- The existing exact digit decoder supplies signed injectivity after a bounded shift. -/
theorem pkI_injective_bounded (u v : List Int) (K : Nat)
    (hl : u.length = v.length) (hu : AbsBnd K u) (hv : AbsBnd K v)
    (hB : 2 * K < B) (hp : pkI u = pkI v) : u = v := by
  have h := congrArg
    (fun z : Int => TransformerCore.unpk u.length
      (z + (K : Int) * pkI (List.replicate u.length 1)).toNat) hp
  rw [TransformerCore.digits_eq u K hu hB] at h
  rw [hl, TransformerCore.digits_eq v K hv hB] at h
  have recover (w : List Int) (hw : AbsBnd K w) :
      (w.map (fun x : Int => (x + (K : Int)).toNat)).map
        (fun d : Nat => (d : Int) - K) = w := by
    rw [List.map_map]
    calc
      w.map ((fun d : Nat => (d : Int) - K) ∘ (fun x : Int => (x + (K : Int)).toNat)) =
          w.map (fun x => x) := by
        apply List.map_congr_left
        intro x hx
        have hx' := hw x hx
        simp only [Function.comp_def]
        omega
      _ = w := List.map_id w
  have h' := congrArg (List.map (fun d : Nat => (d : Int) - K)) h
  rw [recover u hu, recover v hv] at h'
  exact h'

theorem pack_injective_bounded {n : Nat} (f g : Fin n → Int) (K : Nat)
    (hf : ∀ i, -(K : Int) ≤ f i ∧ f i ≤ K)
    (hg : ∀ i, -(K : Int) ≤ g i ∧ g i ≤ K)
    (hB : 2 * K < B) (hp : pack f = pack g) : ∀ i, f i = g i := by
  have bf : AbsBnd K (List.ofFn f) := by
    intro x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    exact hf i
  have bg : AbsBnd K (List.ofFn g) := by
    intro x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    exact hg i
  have he := pkI_injective_bounded (List.ofFn f) (List.ofFn g) K
    (by simp only [List.length_ofFn]) bf bg hB hp
  intro i
  have hi := congrArg (fun l : List Int => l[i.val]?) he
  simpa only [List.getElem?_ofFn, dite_eq_left i.isLt, Option.some.injEq] using hi

theorem sumN_bounded (n : Nat) (f : Nat → Int) (k : Int)
    (hf : ∀ d, d < n → -k ≤ f d ∧ f d ≤ k) :
    -((n : Int) * k) ≤ sumN n f ∧ sumN n f ≤ (n : Int) * k := by
  induction n with
  | zero => simp [sumN]
  | succ n ih =>
    have hb := hf n (by omega)
    have hs := ih (fun d hd => hf d (by omega))
    simp only [sumN, Int.add_def, Nat.cast_succ]
    constructor <;> nlinarith [hb.1, hb.2, hs.1, hs.2]

/-- Bounds come from o and the actual raw matrix, independently of the desired identity. -/
theorem contract_bounded {m n : Nat} (o : Fin m → Int) (W : Fin m → Fin n → Int)
    (Ko Kw : Nat) (ho : ∀ d, -(Ko : Int) ≤ o d ∧ o d ≤ Ko)
    (hw : ∀ d i, -(Kw : Int) ≤ W d i ∧ W d i ≤ Kw) (i : Fin n) :
    -((m * Ko * Kw : Nat) : Int) ≤ contract o (fun d => W d i) ∧
      contract o (fun d => W d i) ≤ (m * Ko * Kw : Nat) := by
  have hb := sumN_bounded m
    (fun k => if hk : k < m then Int.mul (o ⟨k, hk⟩) (W ⟨k, hk⟩ i) else 0)
    ((Ko : Int) * Kw) (by
      intro d hd
      rw [dite_eq_left hd]
      have ho' := abs_le.mpr (ho ⟨d, hd⟩)
      have hw' := abs_le.mpr (hw ⟨d, hd⟩ i)
      apply abs_le.mp
      change |o ⟨d, hd⟩ * W ⟨d, hd⟩ i| ≤ (Ko : Int) * Kw
      rw [abs_mul]
      exact mul_le_mul ho' hw' (abs_nonneg _) (by positivity))
  simpa only [contract, Nat.cast_mul, mul_assoc] using hb

/-- Complete finite linear algebra transport with independently discharged carry bounds. -/
theorem contract_eq_of_packed {m n : Nat} (o : Fin m → Int)
    (W : Fin m → Fin n → Int) (r : Fin m → Int) (t : Fin n → Int)
    (Ko Kw : Nat) (hr : ∀ d, pack (W d) = r d)
    (ho : ∀ d, -(Ko : Int) ≤ o d ∧ o d ≤ Ko)
    (hw : ∀ d i, -(Kw : Int) ≤ W d i ∧ W d i ≤ Kw)
    (ht : ∀ i, -((m * Ko * Kw : Nat) : Int) ≤ t i ∧ t i ≤ (m * Ko * Kw : Nat))
    (hB : 2 * (m * Ko * Kw) < B) (hp : contract o r = pack t) :
    ∀ i, contract o (fun d => W d i) = t i := by
  apply pack_injective_bounded _ t (m * Ko * Kw)
    (contract_bounded o W Ko Kw ho hw) ht hB
  rw [pack_contract]
  have he : (fun d => pack (W d)) = r := funext hr
  rw [he]
  exact hp

end TransformerBridge.RawPacked
