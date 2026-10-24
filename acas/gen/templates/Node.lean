import Block
namespace RouteA
noncomputable section
def zipI (f : Int → Int → Int) (xs ys : List Int) : List Int :=
 @List.rec Int (fun _ => List Int → List Int) (fun _ => [])
 (fun x _ ih ys => @List.casesOn Int (fun _ => List Int) ys [] (fun y ys => f x y :: ih ys)) xs ys

def Q : Int := Int.ofNat 1125899906842624

def minima (l u : Int) (a n : List Int) : List Int := zipI (fun aa nn =>
 let ml := Int.sub (Int.mul aa (max 0 l)) (Int.mul (Int.mul nn l) Q)
 let mu := Int.sub (Int.mul aa (max 0 u)) (Int.mul (Int.mul nn u) Q)
 if l ≤ 0 ∧ 0 ≤ u then min 0 (min ml mu) else min ml mu) a n

def contrib (ls us bs : List Int) (a v : List (List Int)) : List Int :=
 @List.rec Int (fun _ => List Int → List Int → List (List Int) → List (List Int) → List Int)
 (fun _ _ _ _ => [])
 (fun l _ ih us bs aa vv =>
  match us,bs,aa,vv with
  | u::ur,b::br,ar::ars,vr::vrs => addV (zipI Int.add (minima l u ar vr) (scale (Int.mul b Q) vr)) (ih ur br ars vrs)
  | _,_,_,_ => []) ls us bs a v

def signs (xs : List Int) : List Int :=
 @List.rec Int (fun _ => List Int) [] (fun x _ ih => x :: Int.neg x :: ih) xs

def rowsSign (w : List (List Int)) : List (List Int) := w.map (fun row => signs (scale Q row))
def appendRows (xs ys : List (List Int)) : List (List Int) :=
 @List.rec (List Int) (fun _ => List (List Int) → List (List Int)) (fun _ => [])
 (fun x _ ih ys => match ys with | [] => [x] | y::yr => (x++y) :: ih yr) xs ys

def consRow (r : List Int) (acc : List (List Int)) : List (List Int) :=
 @List.rec Int (fun _ => List (List Int) → List (List Int)) (fun _ => [])
 (fun x _ ih acc => match acc with | [] => [x] :: ih [] | a::rest => (x::a) :: ih rest) r acc

def transpose (rows : List (List Int)) : List (List Int) :=
 @List.rec (List Int) (fun _ => List (List Int)) [] (fun r _ acc => consRow r acc) rows

def inputCost (boxl boxu : List Int) (c : List (List Int)) : List Int :=
 @List.rec Int (fun _ => List Int → List (List Int) → List Int) (fun _ _ => [])
 (fun l _ ih us cs => match us,cs with
 | u::ur,cr::rest => addV (cr.map (fun x => min (Int.mul x l) (Int.mul x u))) (ih ur rest)
 | _,_ => []) boxl boxu c

def nonneg (xs : List Int) : List Int := xs.map (max 0)
def ibpRow (row : List Int) (l u : List Int) (b : Int) : Int × Int :=
 @List.rec Int (fun _ => List Int → List Int → Int × Int)
 (fun _ _ => (Int.mul b Q,Int.mul b Q))
 (fun w _ ih ls us => match ls,us with
 | l::lr,u::ur => let p := ih lr ur
                  (Int.add p.1 (min (Int.mul w l) (Int.mul w u)), Int.add p.2 (max (Int.mul w l) (Int.mul w u)))
 | _,_ => (0,0)) row l u

def checkEndpoints (ls us : List Int) (w : List (List Int)) (bs insl insu claims : List Int) (first : Bool) : Bool :=
 @List.rec (List Int) (fun _ => List Int → List Int → List Int → List Int → Bool)
 (fun _ _ _ _ => true)
 (fun row _ ih bs ls us cs => match bs,ls,us with
 | b::br,l::lr,u::ur =>
   let p := ibpRow row insl insu b
   let il := Int.ediv p.1 Q
   let iu := Int.neg (Int.ediv (Int.neg p.2) Q)
   if first then and (and (eqB l il) (eqB u iu)) (ih br lr ur cs)
   else match cs with
    | lo::negHi::rest =>
      and (and (eqB l (max il (Int.ediv lo (Int.mul Q Q))))
       (and (eqB u (min iu (Int.neg (Int.ediv negHi (Int.mul Q Q)))) ) (decide (l ≤ u))))
       (ih br lr ur rest)
    | _ => false
 | _,_,_ => false) w bs ls us claims
end
end RouteA
