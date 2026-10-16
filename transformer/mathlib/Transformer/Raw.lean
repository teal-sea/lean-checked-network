import Transformer.Compose

/-!
# The quantised model from its raw matrices, and the tables it defines

`Compose.lean` states Theorem C about `mq`, the quantised model written through the tables. This
file defines the model from the raw integer matrices (`Weights`: the quantised `tok`, `pos`, `W_Q`
(with `1/√32` absorbed), `W_K`, `W_V`, `W_O`, `W_in`, `b_in`, `W_out`, `b_out`, `U` of DESIGN.md
section 2, all at scale `S` except the biases at `S⁴` and `S⁵`), as the ordinary real-valued
transformer whose weights are these integers divided by their scales (`model`): embeddings
`x_j = x̂_j / S`, scores `q · k`, a real softmax, head outputs through `W_V/S` and `W_O/S`, the
residual stream, the MLP with ReLU and the unembedding. `rawTables` builds the tables of
DESIGN.md section 6 from the same matrices exactly as `build_tables` in `int_transformer.py`
(position 2 filled at token 113 only). `model_eq_mq` proves `model = mq (rawTables)` when
`S⁴ = 2^t`, and `real_model_adds_mod_113_raw` restates Theorem C for `model`.
-/

namespace Transformer

/-- The integer matrices of the quantised model. -/
structure Weights where
  tok : Fin 114 → Fin 128 → ℤ
  pos : Fin 3 → Fin 128 → ℤ
  WQ : Fin 4 → Fin 128 → Fin 32 → ℤ
  WK : Fin 4 → Fin 128 → Fin 32 → ℤ
  WV : Fin 4 → Fin 128 → Fin 32 → ℤ
  WO : Fin 4 → Fin 32 → Fin 128 → ℤ
  Win : Fin 128 → Fin 512 → ℤ
  bin : Fin 512 → ℤ
  Wout : Fin 512 → Fin 128 → ℤ
  bout : Fin 128 → ℤ
  U : Fin 128 → Fin 113 → ℤ

namespace Weights
variable (W : Weights)

/-- `x̂_j = tok[tk] + pos[j]`. -/
def xhat (tk : Fin 114) (j : Fin 3) (d : Fin 128) : ℤ := W.tok tk d + W.pos j d
/-- `q^h = W_Q^h x̂_2` (the query at the last position, token `=`). -/
def qvec (h : Fin 4) (l : Fin 32) : ℤ := ∑ d, W.xhat 113 2 d * W.WQ h d l
/-- `k^h_j = W_K^h x̂_j`. -/
def kvec (h : Fin 4) (tk : Fin 114) (j : Fin 3) (l : Fin 32) : ℤ := ∑ d, W.xhat tk j d * W.WK h d l
/-- `v^h_j = W_V^h x̂_j`. -/
def vvec (h : Fin 4) (tk : Fin 114) (j : Fin 3) (l : Fin 32) : ℤ := ∑ d, W.xhat tk j d * W.WV h d l
/-- `Ô^h_j = W_O^h W_V^h x̂_j`. -/
def ovec (h : Fin 4) (tk : Fin 114) (j : Fin 3) (d : Fin 128) : ℤ := ∑ l, W.vvec h tk j l * W.WO h l d
/-- The integer score `q^h · k^h_j`. -/
def score (h : Fin 4) (j : Fin 3) (tk : Fin 114) : ℤ := ∑ l, W.qvec h l * W.kvec h tk j l

/-- The tables of DESIGN.md section 6, as `build_tables` computes them: `sc`, `TI`, `TU` at position
`2` are filled at token `113` only (zero elsewhere, never read). -/
def rawTables (S : ℕ) : Tables where
  sc := fun h j tk => if j = 2 ∧ tk ≠ 113 then 0 else W.score h j tk
  TI := fun h j tk i => if j = 2 ∧ tk ≠ 113 then 0 else ∑ d, W.ovec h tk j d * W.Win d i
  TU := fun h j tk k => if j = 2 ∧ tk ≠ 113 then 0 else ∑ d, W.ovec h tk j d * W.U d k
  CI := fun i => (S : ℤ) ^ 2 * ∑ d, W.xhat 113 2 d * W.Win d i + W.bin i
  CU := fun k => (S : ℤ) ^ 4 * ∑ d, W.xhat 113 2 d * W.U d k + ∑ d, W.bout d * W.U d k
  G := fun i k => ∑ d, W.Wout i d * W.U d k

/-! ### The real model `M_q` -/

/-- `x_j = x̂_j / S`. -/
noncomputable def rx (S : ℕ) (tk : Fin 114) (j : Fin 3) (d : Fin 128) : ℝ := (W.xhat tk j d : ℝ) / S
/-- `q^h = (W_Q^h / S) x_2`. -/
noncomputable def rq (S : ℕ) (h : Fin 4) (l : Fin 32) : ℝ := ∑ d, W.rx S 113 2 d * ((W.WQ h d l : ℝ) / S)
noncomputable def rk (S : ℕ) (h : Fin 4) (tk : Fin 114) (j : Fin 3) (l : Fin 32) : ℝ :=
  ∑ d, W.rx S tk j d * ((W.WK h d l : ℝ) / S)
noncomputable def rv (S : ℕ) (h : Fin 4) (tk : Fin 114) (j : Fin 3) (l : Fin 32) : ℝ :=
  ∑ d, W.rx S tk j d * ((W.WV h d l : ℝ) / S)
/-- The real score `q^h · k^h_j` (no further `1/√32`: `W_Q` carries it). -/
noncomputable def rscore (S : ℕ) (h : Fin 4) (tk : Fin 114) (j : Fin 3) : ℝ :=
  ∑ l, W.rq S h l * W.rk S h tk j l
/-- The softmax over the three positions. -/
noncomputable def rsoftmax (S : ℕ) (tok : Fin 3 → Fin 114) (h : Fin 4) (j : Fin 3) : ℝ :=
  Real.exp (W.rscore S h (tok j) j) / ∑ j', Real.exp (W.rscore S h (tok j') j')
/-- Head `h`'s output in the residual stream: `(W_O^h / S) Σ_j p_j v^h_j`. -/
noncomputable def rhead (S : ℕ) (tok : Fin 3 → Fin 114) (h : Fin 4) (d : Fin 128) : ℝ :=
  ∑ l, (∑ j, W.rsoftmax S tok h j * W.rv S h (tok j) j l) * ((W.WO h l d : ℝ) / S)
/-- The residual stream after attention: `x_2 + Σ_h head_h`. -/
noncomputable def rresid (S : ℕ) (tok : Fin 3 → Fin 114) (d : Fin 128) : ℝ :=
  W.rx S 113 2 d + ∑ h, W.rhead S tok h d
/-- The MLP pre-activation: `(W_in / S)ᵀ r + b_in / S⁴`. -/
noncomputable def rpre (S : ℕ) (tok : Fin 3 → Fin 114) (i : Fin 512) : ℝ :=
  ∑ d, W.rresid S tok d * ((W.Win d i : ℝ) / S) + (W.bin i : ℝ) / (S : ℝ) ^ 4
noncomputable def rhid (S : ℕ) (tok : Fin 3 → Fin 114) (i : Fin 512) : ℝ := max 0 (W.rpre S tok i)
/-- The MLP output: `(W_out / S)ᵀ m + b_out / S⁵`. -/
noncomputable def rout (S : ℕ) (tok : Fin 3 → Fin 114) (d : Fin 128) : ℝ :=
  ∑ i, W.rhid S tok i * ((W.Wout i d : ℝ) / S) + (W.bout d : ℝ) / (S : ℝ) ^ 5
/-- The logits: `(U / S)ᵀ (r + o)`. -/
noncomputable def rlogits (S : ℕ) (tok : Fin 3 → Fin 114) (k : Fin 113) : ℝ :=
  ∑ d, (W.rresid S tok d + W.rout S tok d) * ((W.U d k : ℝ) / S)
/-- The quantised model `M_q` on the pair `(a, b)`. -/
noncomputable def model (S : ℕ) (a b : Fin 113) : Fin 113 → ℝ := W.rlogits S (toks a b)

/-! ### `model = mq (rawTables)` -/

theorem sum_sum_mul {ι κ μ : Type*} [Fintype ι] [Fintype κ] [Fintype μ] (f : ι → κ → μ → ℝ)
    (g : μ → ℝ) : ∑ d, (∑ h, ∑ j, f h j d) * g d = ∑ h, ∑ j, ∑ d, f h j d * g d := by
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h _
  rw [Finset.sum_comm]

theorem sum_mul_sum {ι μ : Type*} [Fintype ι] [Fintype μ] (f : ι → μ → ℝ) (g : μ → ℝ) :
    ∑ d, (∑ i, f i d) * g d = ∑ i, ∑ d, f i d * g d := by
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]

variable (S : ℕ) (hS : 0 < S)
include hS

omit hS in
theorem rq_eq (h : Fin 4) (l : Fin 32) : W.rq S h l = (W.qvec h l : ℝ) / (S : ℝ) ^ 2 := by
  unfold rq qvec rx
  push_cast
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro d _
  ring

omit hS in
theorem rk_eq (h : Fin 4) (tk : Fin 114) (j : Fin 3) (l : Fin 32) :
    W.rk S h tk j l = (W.kvec h tk j l : ℝ) / (S : ℝ) ^ 2 := by
  unfold rk kvec rx
  push_cast
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro d _
  ring

omit hS in
theorem rv_eq (h : Fin 4) (tk : Fin 114) (j : Fin 3) (l : Fin 32) :
    W.rv S h tk j l = (W.vvec h tk j l : ℝ) / (S : ℝ) ^ 2 := by
  unfold rv vvec rx
  push_cast
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro d _
  ring

omit hS in
theorem rscore_eq (h : Fin 4) (tk : Fin 114) (j : Fin 3) :
    W.rscore S h tk j = (W.score h j tk : ℝ) / (S : ℝ) ^ 4 := by
  unfold rscore score
  simp only [rq_eq W S, rk_eq W S]
  push_cast
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro l _
  ring

omit hS in
theorem rhead_eq (tok : Fin 3 → Fin 114) (h : Fin 4) (d : Fin 128) :
    W.rhead S tok h d = ∑ j, W.rsoftmax S tok h j * ((W.ovec h (tok j) j d : ℝ) / (S : ℝ) ^ 3) := by
  unfold rhead ovec
  simp only [rv_eq W S, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  push_cast
  rw [Finset.sum_div, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  ring

omit hS in
theorem not_unused (tok : Fin 3 → Fin 114) (htok : tok 2 = 113) (j : Fin 3) :
    ¬ (j = 2 ∧ tok j ≠ 113) := by
  rintro ⟨hj, hne⟩
  exact hne (hj ▸ htok)

theorem rsoftmax_eq (t : ℕ) (hSt : (S : ℝ) ^ 4 = 2 ^ t) (tok : Fin 3 → Fin 114)
    (htok : tok 2 = 113) (h : Fin 4) (j : Fin 3) :
    W.rsoftmax S tok h j = softmaxW (W.rawTables S) t tok h j := by
  unfold rsoftmax softmaxW
  simp only [rscore_eq W S, rawTables, not_unused tok htok, ite_false, hSt]

/-- `Σ_d (x̂_2/S + Σ_h Σ_j p Ô/S³)_d · (M_d / S) = (Σ_d x̂_2 M_d) / S² + Σ_h Σ_j p (Σ_d Ô_d M_d) / S⁴`,
the pattern shared by the MLP input (`M = W_in`) and the unembedding (`M = U`). -/
theorem resid_dot (tok : Fin 3 → Fin 114) {ι : Type*} [Fintype ι] (M : Fin 128 → ι → ℤ) (c : ι) :
    ∑ d, W.rresid S tok d * ((M d c : ℝ) / S)
      = (∑ d, W.xhat 113 2 d * M d c : ℤ) / (S : ℝ) ^ 2
        + (∑ h, ∑ j, W.rsoftmax S tok h j * (∑ d, W.ovec h (tok j) j d * M d c : ℤ)) / (S : ℝ) ^ 4 := by
  unfold rresid
  simp only [rhead_eq W S, add_mul, Finset.sum_add_distrib, rx]
  congr 1
  · push_cast
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro d _
    ring
  · rw [sum_sum_mul, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro h _
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    push_cast
    simp only [Finset.mul_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro d _
    ring

theorem rpre_eq (t : ℕ) (hSt : (S : ℝ) ^ 4 = 2 ^ t) (tok : Fin 3 → Fin 114) (htok : tok 2 = 113)
    (i : Fin 512) : W.rpre S tok i = mqPre (W.rawTables S) S t tok i := by
  unfold rpre mqPre
  rw [resid_dot W S hS tok W.Win i]
  simp only [rsoftmax_eq W S hS t hSt tok htok, rawTables, not_unused tok htok, ite_false]
  have : (S : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

theorem rhid_eq (t : ℕ) (hSt : (S : ℝ) ^ 4 = 2 ^ t) (tok : Fin 3 → Fin 114) (htok : tok 2 = 113)
    (i : Fin 512) : W.rhid S tok i = mqHid (W.rawTables S) S t tok i := by
  unfold rhid mqHid
  rw [rpre_eq W S hS t hSt tok htok]

omit hS in
theorem rout_dot (tok : Fin 3 → Fin 114) (k : Fin 113) :
    ∑ d, W.rout S tok d * ((W.U d k : ℝ) / S)
      = (∑ i, W.rhid S tok i * (∑ d, W.Wout i d * W.U d k : ℤ)) / (S : ℝ) ^ 2
        + (∑ d, W.bout d * W.U d k : ℤ) / (S : ℝ) ^ 6 := by
  unfold rout
  simp only [add_mul, Finset.sum_add_distrib]
  congr 1
  · rw [sum_mul_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    push_cast
    rw [Finset.mul_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro d _
    ring
  · push_cast
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro d _
    ring

/-- The identity between the raw model and the table form: `M_q = mq (rawTables)` when `S⁴ = 2^t`. -/
theorem rlogits_eq (t : ℕ) (hSt : (S : ℝ) ^ 4 = 2 ^ t) (tok : Fin 3 → Fin 114) (htok : tok 2 = 113)
    (k : Fin 113) : W.rlogits S tok k = mqLogits (W.rawTables S) S t tok k := by
  unfold rlogits mqLogits
  simp only [add_mul, Finset.sum_add_distrib]
  rw [resid_dot W S hS tok W.U k, rout_dot W S tok k]
  simp only [rsoftmax_eq W S hS t hSt tok htok, rhid_eq W S hS t hSt tok htok, rawTables,
    not_unused tok htok, ite_false]
  have : (S : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

theorem model_eq_mq (t : ℕ) (hSt : (S : ℝ) ^ 4 = 2 ^ t) (a b : Fin 113) :
    W.model S a b = mq (W.rawTables S) S t a b := by
  funext k
  unfold model mq
  exact rlogits_eq W S hS t hSt (toks a b) rfl k

end Weights

/-- **Theorem C for the raw model.** With the tables equal to `rawTables W S` (one `decide` per
table for the core lane) and the brute-force facts `hA` on the integer program, the quantised
model `M_q` built from the raw matrices answers `(a + b) % 113` on every pair. -/
theorem real_model_adds_mod_113_raw (W : Weights)
    (p : ExpParams) (hn : 0 < p.n) (hm : 0 < p.m) (hR : p.R ≤ 2 ^ p.m)
    (hclamp : (2 : ℝ) ^ p.f ≤ Real.exp p.R)
    (δ : ℕ) (hδ : deltaBound p ≤ δ)
    (T : Tables) (B : Bounds) (hB : T.Bounded B) (S : ℕ) (hS : 0 < S)
    (hSt : (S : ℝ) ^ 4 = 2 ^ p.t) (hT : T = W.rawTables S)
    (hA : ∀ a b : Fin 113, ∀ k, k ≠ ans a b →
      intLogits p T S a b k + 2 * (Ebound S p.f δ B : ℤ) < intLogits p T S a b (ans a b)) :
    ∀ a b : Fin 113,
      (∀ k, k ≠ ans a b → W.model S a b k < W.model S a b (ans a b)) ∧
        argmaxFirst (W.model S a b) = ans a b := by
  intro a b
  rw [W.model_eq_mq S hS p.t hSt a b, ← hT]
  exact real_model_adds_mod_113 p hn hm hR hclamp δ hδ T B hB S hS hA a b

/-- The same at the chosen configuration (`S = 256`, `t = 32`, `δ = 2`, the design's `E`). -/
theorem real_model_adds_mod_113_raw_chosen (W : Weights) (T : Tables)
    (hT : T = W.rawTables 256) (hB : T.Bounded chosenBounds)
    (hA : ∀ a b : Fin 113, ∀ k, k ≠ ans a b →
      intLogits chosen T 256 a b k
        + 2 * 416063585574805997938804232439435952711840399411200
        < intLogits chosen T 256 a b (ans a b)) :
    ∀ a b : Fin 113,
      (∀ k, k ≠ ans a b → W.model 256 a b k < W.model 256 a b (ans a b)) ∧
        argmaxFirst (W.model 256 a b) = ans a b := by
  intro a b
  have hSt : ((256 : ℕ) : ℝ) ^ 4 = 2 ^ chosen.t := by
    show ((256 : ℕ) : ℝ) ^ 4 = 2 ^ 32
    norm_num
  rw [W.model_eq_mq 256 (by norm_num) chosen.t hSt a b, ← hT]
  exact real_model_adds_mod_113_chosen T hB hA a b

end Transformer
