import Lean
namespace TreePilot
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
abbrev Box := List (Int × Int)
inductive Kind where
 | leaf
 | split (d : Nat) (cut : Int) (left right : Nat)
 deriving Inhabited, Repr
structure Node where
 box : Box
 kind : Kind
 deriving Inhabited, Repr
def visit (nodes : Array Node) : Nat → Nat → Box → List Nat → Option (List Nat)
 | 0,_,_,_ => none
 | fuel+1,i,expected,seen => do
   if seen.contains i then none else do
   let node ← nodes[i]?
   if node.box != expected then none else do
   let seen := i::seen
   match node.kind with
   | .leaf => return seen
   | .split d c left right => do
     if !(d < expected.length && left != right) then none else do
     let (lo,hi) := expected[d]!
     if !(lo < c && c < hi) then none else do
     let seen ← visit nodes fuel left (expected.set d (lo,c)) seen
     visit nodes fuel right (expected.set d (c,hi)) seen
def rootOk (root : Box) : Bool :=
 root.length == 5 &&
 (root.zip [(3,5),( -1,2),(-1,2),(9,20),(-1,2)]).all (fun ((l,_),(n,d)) => l*d ≤ n*1125899906842624) &&
 (root.zip [(679857769,1000000000),(1,2),(1,2),(1,2),(-9,20)]).all (fun ((_,u),(n,d)) => n*1125899906842624 ≤ u*d) &&
 root.all (fun (l,u) => l ≤ u)
def check (root : Box) (nodes : Array Node) : Bool :=
 rootOk root && match visit nodes nodes.size 0 root [] with
 | none => false
 | some seen => seen.length == nodes.size
end TreePilot
