import ACASChecked.LocalReceipt
namespace CertSound
open RouteA RouteNC Finset

@[simp] theorem addV_getD (xs ys : List Int) (j : Nat) :
    (addV xs ys).getD j 0 = xs.getD j 0 + ys.getD j 0 := by
  induction xs generalizing ys j with
  | nil => simp [addV]
  | cons x xs ih =>
    cases ys with
    | nil => cases j <;> simp_all [addV, List.getD_cons_succ, Int.add_def]
    | cons y ys =>
      cases j with
      | zero => rfl
      | succ j =>
        change (addV xs ys).getD j 0 = _
        exact ih ys j

@[simp] theorem scale_getD (p : Int) (xs : List Int) (j : Nat) :
    (scale p xs).getD j 0 = p * xs.getD j 0 := by
  induction xs generalizing j with
  | nil => simp [scale]
  | cons x xs ih =>
    cases j with
    | zero => rfl
    | succ j => exact ih j

@[simp] theorem scale_ofFn {n : Nat} (p : Int) (a : Fin n → Int) :
    scale p (List.ofFn a) = List.ofFn (fun i => p * a i) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.ofFn_succ, List.ofFn_succ]
    change p * a 0 :: scale p (List.ofFn (fun i => a i.succ)) = _
    rw [ih]

@[simp] theorem getD_ofFn {α : Type} {n : Nat} (a : Fin n → α) (j : Fin n) (d : α) :
    (List.ofFn a).getD j d = a j := by
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp

theorem contrib_col {n t : Nat} (l u b : Fin n → Int)
    (a v : Fin n → Fin t → Int) (j : Fin t) :
    (contrib (List.ofFn l) (List.ofFn u) (List.ofFn b)
      (List.ofFn (fun i => List.ofFn (a i)))
      (List.ofFn (fun i => List.ofFn (v i)))).getD j 0 =
    ∑ i, (minZ (l i) (u i) (a i j) (v i j) + b i * Q * v i j) := by
  induction n with
  | zero => simp [contrib]
  | succ n ih =>
    simp only [List.ofFn_succ]
    change (addV (zipI Int.add (minima (l 0) (u 0) (List.ofFn (a 0)) (List.ofFn (v 0)))
      (scale (Int.mul (b 0) Q) (List.ofFn (v 0))))
      (contrib (List.ofFn (fun i => l i.succ)) (List.ofFn (fun i => u i.succ))
      (List.ofFn (fun i => b i.succ))
      (List.ofFn (fun i => List.ofFn (a i.succ)))
      (List.ofFn (fun i => List.ofFn (v i.succ))))).getD j 0 = _
    rw [addV_getD, minima_ofFn, scale_ofFn, zipI_ofFn, getD_ofFn, ih, Fin.sum_univ_succ]
    rfl

theorem inputCost_col {n t : Nat} (l u : Fin n → Int)
    (c : Fin n → Fin t → Int) (j : Fin t) :
    (inputCost (List.ofFn l) (List.ofFn u) (List.ofFn (fun i => List.ofFn (c i)))).getD j 0 =
      ∑ i, min (c i j*l i) (c i j*u i) := by
  induction n with
  | zero => simp [inputCost]
  | succ n ih =>
    rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_succ]
    change (addV ((List.ofFn (c 0)).map _)
      (inputCost (List.ofFn (fun i => l i.succ)) (List.ofFn (fun i => u i.succ))
      (List.ofFn (fun i => List.ofFn (c i.succ))))).getD j 0 = _
    rw [addV_getD, List.map_ofFn, getD_ofFn, ih, Fin.sum_univ_succ]
    rfl

theorem contrib_col_list (n t : Nat) (l u b : List Int) (a v : List (List Int))
    (hl : l.length = n) (hu : u.length = n) (hb : b.length = n)
    (ha : a.length = n) (hv : v.length = n)
    (hat : ∀ r ∈ a, r.length = t) (hvt : ∀ r ∈ v, r.length = t) (j : Fin t) :
    (contrib l u b a v).getD j 0 = ∑ i : Fin n,
      (minZ (l.getD i 0) (u.getD i 0) (matrix a i j) (matrix v i j) +
        b.getD i 0 * Q * matrix v i j) := by
  have hh := contrib_col (fun i : Fin n => l.getD i 0) (fun i : Fin n => u.getD i 0)
    (fun i : Fin n => b.getD i 0) (fun i : Fin n => fun j : Fin t => matrix a i j)
    (fun i : Fin n => fun j : Fin t => matrix v i j) j
  simpa only [ofFn_getD l 0 n hl, ofFn_getD u 0 n hu, ofFn_getD b 0 n hb,
    ofFn_matrix a n t ha hat, ofFn_matrix v n t hv hvt] using hh

theorem inputCost_col_list (n t : Nat) (l u : List Int) (c : List (List Int))
    (hl : l.length = n) (hu : u.length = n) (hc : c.length = n)
    (hct : ∀ r ∈ c, r.length = t) (j : Fin t) :
    (inputCost l u c).getD j 0 = ∑ i : Fin n,
      min (matrix c i j * l.getD i 0) (matrix c i j * u.getD i 0) := by
  have hh := inputCost_col (fun i : Fin n => l.getD i 0) (fun i : Fin n => u.getD i 0)
    (fun i : Fin n => fun j : Fin t => matrix c i j) j
  simpa only [ofFn_getD l 0 n hl, ofFn_getD u 0 n hu, ofFn_matrix c n t hc hct] using hh

#print axioms contrib_col_list
#print axioms inputCost_col_list
#print axioms contrib_col
#print axioms inputCost_col
end CertSound
