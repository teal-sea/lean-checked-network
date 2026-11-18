/- Generic sparse-affine cells with an interval evaluator and its soundness.
   No weights appear in this file.  Used only for the optional float64-range certificate. -/
namespace Cell

structure Row where
  b : Int
  terms : List (Nat × Int)      -- (input index, weight), in evaluation order
  hi : Option Int               -- upper clip (none = unbounded)

structure Layer where
  rows : List Row
  skip : List Nat

abbrev Iv := Int × Int

def absI (x : Int) : Int := max x (-x)

def clipV (hi : Option Int) (x : Int) : Int :=
  match hi with
  | none => max 0 x
  | some c => min c (max 0 x)

/-- Exact value of a row. -/
def Row.eval (r : Row) (v : List Int) : Int :=
  clipV r.hi (r.terms.foldl (fun acc t => acc + t.2 * v.getD t.1 0) r.b)

/-- Raw (unclipped) value of a row, as used by the head logits. -/
def Row.raw (r : Row) (v : List Int) : Int :=
  r.terms.foldl (fun acc t => acc + t.2 * v.getD t.1 0) r.b

/-- Every product and every ordered partial sum of the row (bias first). -/
def Row.trace (r : Row) (v : List Int) : List Int :=
  (r.terms.foldl (fun (st : Int × List Int) t =>
      let p := t.2 * v.getD t.1 0
      let a := st.1 + p
      (a, st.2 ++ [p, a])) (r.b, [r.b])).2

def Layer.eval (L : Layer) (v : List Int) : List Int :=
  L.rows.map (fun r => r.eval v) ++ L.skip.map (fun i => v.getD i 0)

def Layer.trace (L : Layer) (v : List Int) : List Int :=
  L.rows.flatMap (fun r => r.trace v)

def evalCell : List Layer → List Int → List Int
  | [], v => v
  | L :: ls, v => evalCell ls (L.eval v)

def traceCell : List Layer → List Int → List Int
  | [], _ => []
  | L :: ls, v => L.trace v ++ traceCell ls (L.eval v)

/-! ### Interval evaluation -/
structure RIv where
  lo : Int
  hi : Int
  m : Int

def stepIv (r : RIv) (iv : Iv) (w : Int) : RIv :=
  let p1 := w * iv.1
  let p2 := w * iv.2
  let pl := min p1 p2
  let ph := max p1 p2
  let lo := r.lo + pl
  let hi := r.hi + ph
  ⟨lo, hi, max r.m (max (max (absI pl) (absI ph)) (max (absI lo) (absI hi)))⟩

def Row.iv (r : Row) (ivs : List Iv) : Iv × Int :=
  let s := r.terms.foldl (fun st t => stepIv st (ivs.getD t.1 (0, 0)) t.2) ⟨r.b, r.b, absI r.b⟩
  ((clipV r.hi s.lo, clipV r.hi s.hi), s.m)

def Layer.iv (L : Layer) (ivs : List Iv) : List Iv × Int :=
  (L.rows.map (fun r => (r.iv ivs).1) ++ L.skip.map (fun i => ivs.getD i (0, 0)),
   (L.rows.map (fun r => (r.iv ivs).2)).foldl max 0)

def cellIv : List Layer → List Iv → List Iv × Int
  | [], ivs => (ivs, 0)
  | L :: ls, ivs => let a := L.iv ivs; let b := cellIv ls a.1; (b.1, max a.2 b.2)

def Within (v : List Int) (ivs : List Iv) : Prop :=
  ∀ i, (ivs.getD i (0, 0)).1 ≤ v.getD i 0 ∧ v.getD i 0 ≤ (ivs.getD i (0, 0)).2

theorem mul_bounds (w a z v : Int) (h1 : a ≤ v) (h2 : v ≤ z) :
    min (w * a) (w * z) ≤ w * v ∧ w * v ≤ max (w * a) (w * z) := by
  rcases Int.le_total 0 w with hw | hw
  · have := Int.mul_le_mul_of_nonneg_left h1 hw
    have := Int.mul_le_mul_of_nonneg_left h2 hw
    omega
  · have := Int.mul_le_mul_of_nonpos_left hw h1
    have := Int.mul_le_mul_of_nonpos_left hw h2
    omega

theorem fold_sound (ts : List (Nat × Int)) (ivs : List Iv) (v : List Int) (hW : Within v ivs) :
    ∀ (acc : Int) (tr : List Int) (s : RIv),
      s.lo ≤ acc → acc ≤ s.hi → -s.m ≤ s.lo → s.hi ≤ s.m → (∀ t ∈ tr, -s.m ≤ t ∧ t ≤ s.m) →
      let s' := ts.foldl (fun st t => stepIv st (ivs.getD t.1 (0, 0)) t.2) s
      let r := ts.foldl (fun (st : Int × List Int) t =>
          let p := t.2 * v.getD t.1 0
          let a := st.1 + p
          (a, st.2 ++ [p, a])) (acc, tr)
      s'.lo ≤ r.1 ∧ r.1 ≤ s'.hi ∧ -s'.m ≤ s'.lo ∧ s'.hi ≤ s'.m ∧ (∀ t ∈ r.2, -s'.m ≤ t ∧ t ≤ s'.m) := by
  induction ts with
  | nil => intro acc tr s h1 h2 h3 h4 h5; exact ⟨h1, h2, h3, h4, h5⟩
  | cons t ts ih =>
    intro acc tr s h1 h2 h3 h4 h5
    simp only [List.foldl_cons]
    have hv := hW t.1
    have mb := mul_bounds t.2 (ivs.getD t.1 (0, 0)).1 (ivs.getD t.1 (0, 0)).2 (v.getD t.1 0) hv.1 hv.2
    apply ih
    · simp only [stepIv, absI]; omega
    · simp only [stepIv, absI]; omega
    · simp only [stepIv, absI]; omega
    · simp only [stepIv, absI]; omega
    · intro x hx
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
      simp only [stepIv, absI]
      rcases hx with hx | hx | hx
      · have := h5 x hx; omega
      · subst hx; omega
      · subst hx; omega

theorem fold_fst (ts : List (Nat × Int)) (v : List Int) : ∀ (acc : Int) (tr : List Int),
    (ts.foldl (fun (st : Int × List Int) t =>
      let p := t.2 * v.getD t.1 0
      let a := st.1 + p
      (a, st.2 ++ [p, a])) (acc, tr)).1 = ts.foldl (fun acc t => acc + t.2 * v.getD t.1 0) acc := by
  induction ts with
  | nil => intro acc tr; rfl
  | cons t ts ih => intro acc tr; simp only [List.foldl_cons]; exact ih _ _

theorem row_sound (r : Row) (ivs : List Iv) (v : List Int) (hW : Within v ivs) :
    (r.iv ivs).1.1 ≤ r.eval v ∧ r.eval v ≤ (r.iv ivs).1.2 ∧ ∀ t ∈ r.trace v, -(r.iv ivs).2 ≤ t ∧ t ≤ (r.iv ivs).2 := by
  have h := fold_sound r.terms ivs v hW r.b [r.b] ⟨r.b, r.b, absI r.b⟩
    (by simp) (by simp) (by simp only [absI]; omega) (by simp only [absI]; omega)
    (by intro t ht; simp at ht; subst ht; simp only [absI]; omega)
  obtain ⟨h1, h2, _, _, h5⟩ := h
  rw [fold_fst] at h1 h2
  simp only [Row.iv, Row.eval, Row.trace]
  refine ⟨?_, ?_, h5⟩
  · cases hh : r.hi <;> simp only [hh, clipV] at * <;> omega
  · cases hh : r.hi <;> simp only [hh, clipV] at * <;> omega

theorem within_append (a b : List Int) (ia ib : List Iv) (hl : a.length = ia.length)
    (ha : Within a ia) (hb : Within b ib) : Within (a ++ b) (ia ++ ib) := by
  intro i
  by_cases h : i < a.length
  · have e1 : (a ++ b).getD i 0 = a.getD i 0 := by simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
    have e2 : (ia ++ ib).getD i (0, 0) = ia.getD i (0, 0) := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : i < ia.length)]
    rw [e1, e2]; exact ha i
  · have e1 : (a ++ b).getD i 0 = b.getD (i - a.length) 0 := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega : a.length ≤ i)]
    have e2 : (ia ++ ib).getD i (0, 0) = ib.getD (i - ia.length) (0, 0) := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega : ia.length ≤ i)]
    rw [e1, e2, ← hl]; exact hb _

theorem within_map (xs : List α) (f : α → Int) (g : α → Iv) (h : ∀ x ∈ xs, (g x).1 ≤ f x ∧ f x ≤ (g x).2) :
    Within (xs.map f) (xs.map g) := by
  intro i
  by_cases hi : i < xs.length
  · have e1 : (xs.map f).getD i 0 = f (xs[i]) := by simp [List.getD_eq_getElem?_getD, hi]
    have e2 : (xs.map g).getD i (0, 0) = g (xs[i]) := by simp [List.getD_eq_getElem?_getD, hi]
    rw [e1, e2]; exact h _ (List.getElem_mem hi)
  · have e1 : (xs.map f).getD i 0 = 0 := by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]; rfl
    have e2 : (xs.map g).getD i (0, 0) = (0, 0) := by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]; rfl
    rw [e1, e2]; omega

theorem foldl_max_ge (xs : List Int) : ∀ a : Int, a ≤ xs.foldl max a := by
  induction xs with
  | nil => intro a; simp
  | cons y ys ih => intro a; simp only [List.foldl_cons]; have := ih (max a y); omega

theorem layer_sound (L : Layer) (ivs : List Iv) (v : List Int) (hW : Within v ivs) :
    Within (L.eval v) (L.iv ivs).1 ∧ (∀ t ∈ L.trace v, -(L.iv ivs).2 ≤ t ∧ t ≤ (L.iv ivs).2) := by
  constructor
  · unfold Layer.eval Layer.iv
    apply within_append
    · simp
    · exact within_map L.rows (fun r => r.eval v) (fun r => (r.iv ivs).1)
        (fun r _ => ⟨(row_sound r ivs v hW).1, (row_sound r ivs v hW).2.1⟩)
    · exact within_map L.skip (fun i => v.getD i 0) (fun i => ivs.getD i (0, 0))
        (fun i _ => hW i)
  · intro t ht
    unfold Layer.trace at ht
    obtain ⟨r, hr, ht⟩ := List.mem_flatMap.mp ht
    have hs := (row_sound r ivs v hW).2.2 t ht
    have : (r.iv ivs).2 ≤ (L.iv ivs).2 := by
      unfold Layer.iv
      simp only []
      have key : ∀ (xs : List Int) (a : Int) (x : Int), x ∈ xs → x ≤ xs.foldl max a := by
        intro xs
        induction xs with
        | nil => intro a x hx; simp at hx
        | cons y ys ih =>
          intro a x hx
          simp only [List.foldl_cons]
          rcases List.mem_cons.mp hx with h | h
          · subst h
            have := foldl_max_ge ys (max a x)
            omega
          · exact ih _ _ h
      exact key _ 0 _ (List.mem_map.mpr ⟨r, hr, rfl⟩)
    omega

theorem cell_sound (ls : List Layer) : ∀ (ivs : List Iv) (v : List Int), Within v ivs →
    Within (evalCell ls v) (cellIv ls ivs).1 ∧
    ∀ t ∈ traceCell ls v, -(cellIv ls ivs).2 ≤ t ∧ t ≤ (cellIv ls ivs).2 := by
  induction ls with
  | nil => intro ivs v h; exact ⟨h, by simp [traceCell]⟩
  | cons L ls ih =>
    intro ivs v h
    obtain ⟨w1, t1⟩ := layer_sound L ivs v h
    obtain ⟨w2, t2⟩ := ih _ _ w1
    refine ⟨w2, ?_⟩
    intro t ht
    simp only [traceCell, List.mem_append] at ht
    simp only [cellIv, evalCell]
    rcases ht with ht | ht
    · have := t1 t ht; omega
    · have := t2 t ht; omega
end Cell
