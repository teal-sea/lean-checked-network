import ACASChecked.Pack
namespace RouteA
noncomputable section
def shape (n : Nat) (xs : List Int) : Bool := Nat.beq (lenN xs) n
def rowChecks (w : List (List Int)) (p : List Int) (c : List (List Int)) (B K KR : Nat) : Bool :=
 @List.rec (List Int) (fun _ => List (List Int) → Bool)
 (fun cs => cs.isEmpty)
 (fun row _ ih cs => @List.casesOn (List Int) (fun _ => Bool) cs false
 (fun cr rest => and (eqB (Int.ofNat (pkN B K cr)) (Int.add (dot row p) (Int.ofNat KR))) (ih rest))) w c

def block (w v c : List (List Int)) : Bool :=
 let B := 2^160; let G := 2^60; let H := 2^60; let K := 2^127
 let n := lenN w; let t := lenN (v.headD [])
 and (Nat.ble (Nat.mul (lenN v) (Nat.mul G H)) K)
 (and (Nat.blt (Nat.mul 2 K) B)
 (and (allB (shape (lenN v)) w)
 (and (allB (shape t) v)
 (and (allB (shape t) c)
 (and (Nat.beq (lenN c) n)
 (and (allB (inBN G) w)
 (and (allB (inBN H) v)
 (and (allB (inBN K) c)
 (rowChecks w (unoff (Nat.mul H (rep B t)) (v.map (pkN B H))) c B K (Nat.mul K (rep B t))))))))))

)
def dots (row : List Int) (v : List (List Int)) : List Int :=
 @List.rec Int (fun _ => List (List Int) → List Int) (fun _ => [])
 (fun a _ ih vs => @List.casesOn (List Int) (fun _ => List Int) vs []
 (fun r rs => addV (scale a r) (ih rs))) row v

def same (a b : List Int) : Bool :=
 @List.rec Int (fun _ => List Int → Bool) (fun bs => bs.isEmpty)
 (fun x _ ih bs => @List.casesOn Int (fun _ => Bool) bs false
 (fun y ys => and (eqB x y) (ih ys))) a b

def scalar (w v c : List (List Int)) : Bool :=
 @List.rec (List Int) (fun _ => List (List Int) → Bool) (fun cs => cs.isEmpty)
 (fun row _ ih cs => @List.casesOn (List Int) (fun _ => Bool) cs false
 (fun cr rest => and (same (dots row v) cr) (ih rest))) w c
end
end RouteA
