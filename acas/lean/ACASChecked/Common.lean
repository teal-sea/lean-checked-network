import ACASChecked.RawReceipt
import ACASChecked.Weights
import ACASChecked.N8.NodeDataNC
noncomputable section
namespace ACASCommon
open RouteA RouteNC SharedWeights

def outW : List (List Int) := Leaf8.afinal.map (fun row => [-(row.headD 0) / Q])
def weights (k : Nat) : List (List Int) := [w0,w1,w2,w3,w4,w5,outW].getD k []
def biases (k : Nat) : List Int := [Leaf8.b0,Leaf8.b1,Leaf8.b2,Leaf8.b3,Leaf8.b4,Leaf8.b5,Leaf8.b6].getD k []
def net : CertSound.GridNetwork where
  dim := CertSound.dim
  w k j i := matrix (weights k) i j
  b k j := (biases k).getD j 0
end ACASCommon
