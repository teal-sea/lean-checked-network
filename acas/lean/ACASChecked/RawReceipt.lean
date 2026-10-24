import ACASChecked.LeafSafety
import ACASChecked.MatrixLists
noncomputable section
namespace CertSound
open RouteA RouteNC Finset

def dim : Nat → Nat | 0 => 5 | _+1 => 50
def columns (k : Nat) : Nat := 100*(5-k)+1

structure RawReceipt where
  w : Nat → List (List Int)
  b : Nat → List Int
  l : Nat → List Int
  u : Nat → List Int
  v : Nat → List (List Int)
  c : Nat → List (List Int)
  s : Nat → List Int
  afinal : List (List Int)
  boxl : List Int
  boxu : List Int

def RawReceipt.a (r : RawReceipt) (k : Nat) : List (List Int) :=
  if k = 5 then r.afinal else appendRows (rowsSign (r.w (k+1))) (r.c (k+1))
def RawReceipt.cost (r : RawReceipt) (k : Nat) : List Int :=
  contrib (r.l k) (r.u k) (r.b k) (r.a k) (r.v k)
def RawReceipt.claims (r : RawReceipt) : List Int :=
  addV (r.s 0) (inputCost r.boxl r.boxu (r.c 0))

abbrev RawReceipt.net (r : RawReceipt) : GridNetwork where
  dim := dim
  w k j i := matrix (r.w k) i j
  b k j := (r.b k).getD j 0

abbrev RawReceipt.lower (r : RawReceipt) (k : Nat) (j : Fin (r.net.dim (k+1))) : Int :=
  (r.l k).getD j 0
abbrev RawReceipt.upper (r : RawReceipt) (k : Nat) (j : Fin (r.net.dim (k+1))) : Int :=
  (r.u k).getD j 0

structure RawReceipt.Valid (r : RawReceipt) : Prop where
  wlen : ∀ k < 6, (r.w k).length = dim k
  vlen : ∀ k < 6, (r.v k).length = 50
  tlen : ∀ k < 6, ((r.v k).headD []).length = CertSound.columns k
  blen : ∀ k < 6, (r.b k).length = 50
  llen : ∀ k < 6, (r.l k).length = 50
  ulen : ∀ k < 6, (r.u k).length = 50
  boxllen : r.boxl.length = 5
  boxulen : r.boxu.length = 5
  afinallen : r.afinal.length = 50
  afinalrows : ∀ row ∈ r.afinal, row.length = 1
  afinalvalue : ∀ i : Fin 50, matrix r.afinal i 0 = -Q*matrix (r.w 6) i 0
  blocks : ∀ k < 6, block (r.w k) (r.v k) (r.c k) = true
  tails : ∀ k < 5, r.s k = addV ((scale (Q*Q) (signs (r.b (k+1)))) ++ r.s (k+1)) (r.cost k)
  last : r.s 5 = addV (scale (-(Q*Q)) ((r.b 6).take 1)) (r.cost 5)
  endpoints : ∀ k < 6,
    checkEndpoints (r.l k) (r.u k) (transpose (r.w k)) (r.b k)
      (if k = 0 then r.boxl else nonneg (r.l (k-1)))
      (if k = 0 then r.boxu else nonneg (r.u (k-1)))
      ((r.claims.drop (100*(k-1))).take 100) (decide (k=0)) = true
  margin : 0 < r.claims.getD 500 0*1000000000000000 + 3991125645861615*(Q*Q*Q)

/-- Shapes are read from the accepted block checks, without rechecking any products. -/
theorem block_shape_facts (w v c : List (List Int)) (h : block w v c = true) :
    (∀ row ∈ w, row.length = v.length) ∧
    (∀ row ∈ v, row.length = (v.headD []).length) ∧
    (∀ row ∈ c, row.length = (v.headD []).length) ∧ c.length = w.length := by
  unfold block at h
  dsimp only at h
  simp only [Bool.and_eq_true] at h
  rcases h with ⟨_,_,hw,hv,hc,hlen,_⟩
  exact ⟨by simpa only [allB_spec, shape_spec, lenN_eq] using hw,
    by simpa only [allB_spec, shape_spec, lenN_eq] using hv,
    by simpa only [allB_spec, shape_spec, lenN_eq] using hc,
    by simpa only [lenN_eq] using Nat.eq_of_beq_eq_true hlen⟩

theorem RawReceipt.Valid.wrows {r : RawReceipt} (h : r.Valid) (k : Nat) (hk : k < 6) :
    ∀ row ∈ r.w k, row.length = 50 := by
  simpa only [h.vlen k hk] using (block_shape_facts _ _ _ (h.blocks k hk)).1

theorem RawReceipt.Valid.vrows {r : RawReceipt} (h : r.Valid) (k : Nat) (hk : k < 6) :
    ∀ row ∈ r.v k, row.length = columns k := by
  simpa only [h.tlen k hk] using (block_shape_facts _ _ _ (h.blocks k hk)).2.1

theorem RawReceipt.Valid.crows {r : RawReceipt} (h : r.Valid) (k : Nat) (hk : k < 6) :
    ∀ row ∈ r.c k, row.length = columns k := by
  simpa only [h.tlen k hk] using (block_shape_facts _ _ _ (h.blocks k hk)).2.2.1

theorem RawReceipt.Valid.clen {r : RawReceipt} (h : r.Valid) (k : Nat) (hk : k < 6) :
    (r.c k).length = dim k :=
  (block_shape_facts _ _ _ (h.blocks k hk)).2.2.2.trans (h.wlen k hk)

theorem RawReceipt.Valid.a_eq {r : RawReceipt} (h : r.Valid) (k : Nat) (hk : k < 5) :
    r.a k = List.ofFn (fun i : Fin 50 => signs (scale Q (List.ofFn (fun j : Fin 50 => matrix (r.w (k+1)) i j))) ++
      List.ofFn (fun j : Fin (columns (k+1)) => matrix (r.c (k+1)) i j)) := by
  unfold RawReceipt.a
  rw [if_neg (by omega)]
  have hw := ofFn_matrix (r.w (k+1)) 50 50 (h.wlen (k+1) (by omega)) (h.wrows (k+1) (by omega))
  have hc := ofFn_matrix (r.c (k+1)) 50 (columns (k+1)) (h.clen (k+1) (by omega)) (h.crows (k+1) (by omega))
  conv_lhs => rw [← hw, ← hc, rowsSign, List.map_ofFn, appendRows_ofFn]
  rfl

theorem RawReceipt.Valid.ashape {r : RawReceipt} (h : r.Valid) (k : Nat) (hk : k < 6) :
    (r.a k).length = 50 ∧ ∀ row ∈ r.a k, row.length = columns k := by
  by_cases he : k = 5
  · subst k
    change r.afinal.length = 50 ∧ ∀ row ∈ r.afinal, row.length = 1
    exact ⟨h.afinallen,h.afinalrows⟩
  · rw [h.a_eq k (by omega)]
    constructor
    · simp
    · simp only [List.forall_mem_ofFn_iff, List.length_append, signs_length, scale_length, List.length_ofFn]
      intro i
      dsimp [columns]
      omega

#print axioms RawReceipt.Valid.ashape
end CertSound
