/- Step 4: the backward cell and head agree with the reference right-to-left pass, for every
   Boolean forward-output pattern and every Boolean backward state (symbolic: by unit, not by
   enumerating the 2^22 combinations). -/
import lean.Pilot
import lean.Reference
namespace Lexnet
set_option maxRecDepth 100000
set_option maxHeartbeats 0

structure Pat where
  c0 : Bool
  c1 : Bool
  s : Bool
  q : Bool
  p : Bool
  w : Bool
  n : Bool
  k : Bool
  t : Bool
  v : Bool
  o : Bool
  sl : Bool
  bl : Bool
  nl : Bool
  lp : Bool

def fvec (P : Pat) : List Int :=
  [enc P.c0, enc P.c1, enc P.s, enc P.q, enc P.p, enc P.w, enc P.n, enc P.k, enc P.t, enc P.v,
   enc P.o, enc P.sl, enc P.bl, enc P.nl, enc P.lp]

def seenOf (P : Pat) : Ref.Seen :=
  { comment := P.c0 || P.c1, string := P.s, char := P.q, pp := P.p, word := P.w, number := P.n,
    isKeyword := P.k, isType := P.t, isConstant := P.v, opener := P.o, slash := P.sl,
    blank := P.bl, newline := P.nl, paren := P.lp }

def encR (R : Ref.Right) : List Int :=
  [enc R.nextWord, enc R.nextOpener, enc R.paren, enc R.keyword, enc R.type, enc R.constant,
   enc R.function]

def canonLogits (R' : Ref.Right) (P : Pat) (cm : Bool) : List Int :=
  [1, 14 * enc R'.keyword, 14 * enc R'.type, 14 * enc R'.function, 10 * enc P.w,
   12 * enc R'.constant + 12 * enc P.n, 20 * enc P.s, 20 * enc P.q, 18 * enc cm, 16 * enc P.p,
   2 - 2 * enc P.bl - 2 * enc P.nl]

theorem backward_canon (P : Pat) (R : Ref.Right) :
    backward (fvec P) (encR R) =
      (encR (Ref.label (seenOf P) R).1,
       canonLogits (Ref.label (seenOf P) R).1 P ((P.c0 || P.c1) || (P.sl && R.nextOpener))) := by
  rcases P with ⟨c0, c1, s, q, p, w, n, k, t, v, o, sl, bl, nl, lp⟩
  rcases R with ⟨nw, no, par, rk, rt, rc, rf⟩
  simp only [backward, fvec, encR, canonLogits, Ref.label, seenOf, List.getD_cons_succ,
    List.getD_cons_zero, List.getD_eq_getElem?_getD, List.getElem?_cons_succ, List.getElem?_cons_zero,
    Option.getD_some, Prod.mk.injEq, List.cons.injEq, and_true]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first
    | rfl
    | decide +revert

def ansOf (kc tc fc w cs n s q cm p sp nl : Bool) : Nat :=
  if s then 6 else if q then 7 else if cm then 8 else if p then 9 else if kc then 1
  else if tc then 2 else if fc then 3 else if cs || n then 5 else if w then 4
  else if sp || nl then 0 else 10

theorem argmax_atoms : ∀ kc tc fc w cs n s q cm p sp nl : Bool, (cs && n) = false →
    argmax [1, 14 * enc kc, 14 * enc tc, 14 * enc fc, 10 * enc w, 12 * enc cs + 12 * enc n,
            20 * enc s, 20 * enc q, 18 * enc cm, 16 * enc p, 2 - 2 * enc sp - 2 * enc nl] =
      ansOf kc tc fc w cs n s q cm p sp nl := by
  decide +kernel

/-- Step 4 theorem: one right-to-left step of the network equals one step of the reference. -/
theorem backward_ok (P : Pat) (R : Ref.Right) (hx : (P.w && P.n) = false) :
    (backward (fvec P) (encR R)).1 = encR (Ref.label (seenOf P) R).1 ∧
    argmax (backward (fvec P) (encR R)).2 = (Ref.label (seenOf P) R).2 := by
  rw [backward_canon]
  refine ⟨rfl, ?_⟩
  simp only [canonLogits]
  have hc : ((Ref.label (seenOf P) R).1.constant && P.n) = false := by
    have : (Ref.label (seenOf P) R).1.constant = (P.w && (if R.nextWord then R.constant else P.v)) := rfl
    rw [this]; revert hx; cases P.w <;> cases P.n <;> simp
  rw [argmax_atoms _ _ _ _ _ _ _ _ _ _ _ _ hc]
  rfl
end Lexnet
