import ACASChecked.RawLeafSound
import ACASChecked.Common
import ACASChecked.N63.AcceptNC
noncomputable section
namespace Instance63
open CertSound RouteA RouteNC SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def raw : RawReceipt where
  w := ACASCommon.weights
  b := ACASCommon.biases
  l k := [Leaf63.lo0,Leaf63.lo1,Leaf63.lo2,Leaf63.lo3,Leaf63.lo4,Leaf63.lo5].getD k []
  u k := [Leaf63.hi0,Leaf63.hi1,Leaf63.hi2,Leaf63.hi3,Leaf63.hi4,Leaf63.hi5].getD k []
  v k := [Leaf63.v0,Leaf63.v1,Leaf63.v2,Leaf63.v3,Leaf63.v4,Leaf63.v5].getD k []
  c k := [Leaf63.c0,Leaf63.c1,Leaf63.c2,Leaf63.c3,Leaf63.c4,Leaf63.c5].getD k []
  s k := [Leaf63.s0,Leaf63.s1,Leaf63.s2,Leaf63.s3,Leaf63.s4,Leaf63.s5].getD k []
  afinal := Leaf63.afinal
  boxl := Leaf63.boxl
  boxu := Leaf63.boxu

theorem biases_eq : [Leaf63.b0,Leaf63.b1,Leaf63.b2,Leaf63.b3,Leaf63.b4,Leaf63.b5,Leaf63.b6] = [Leaf8.b0,Leaf8.b1,Leaf8.b2,Leaf8.b3,Leaf8.b4,Leaf8.b5,Leaf8.b6] := by decide +kernel

theorem raw_b : raw.b = fun k => [Leaf63.b0,Leaf63.b1,Leaf63.b2,Leaf63.b3,Leaf63.b4,Leaf63.b5,Leaf63.b6].getD k [] := by
  funext k
  change [Leaf8.b0,Leaf8.b1,Leaf8.b2,Leaf8.b3,Leaf8.b4,Leaf8.b5,Leaf8.b6].getD k [] = [Leaf63.b0,Leaf63.b1,Leaf63.b2,Leaf63.b3,Leaf63.b4,Leaf63.b5,Leaf63.b6].getD k []
  rw [biases_eq]

theorem claims_eq : raw.claims = Leaf63.claims := rfl

theorem valid : raw.Valid := by
  constructor
  · intro k hk
    interval_cases k <;> decide +kernel
  · intro k hk
    interval_cases k <;> decide +kernel
  · intro k hk
    interval_cases k <;> decide +kernel
  · intro k hk
    interval_cases k <;> decide +kernel
  · intro k hk
    interval_cases k <;> decide +kernel
  · intro k hk
    interval_cases k <;> decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro k hk
    interval_cases k
    · exact Proof63.packedNC0
    · exact Proof63.packedNC1
    · exact Proof63.packedNC2
    · exact Proof63.packedNC3
    · exact Proof63.packedNC4
    · exact Proof63.packedNC5
  · intro k hk
    interval_cases k <;> (simp only [RawReceipt.cost,RawReceipt.a,raw_b]; rfl)
  · simp only [RawReceipt.cost,RawReceipt.a,raw_b]
    rfl
  · intro k hk
    rw [raw_b,claims_eq]
    interval_cases k
    · have hh := Proof63.endpointsNC0
      change Leaf63.endpoints0 = true at hh
      simp only [Leaf63.endpoints0, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof63.endpointsNC1
      change Leaf63.endpoints1 = true at hh
      simp only [Leaf63.endpoints1, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof63.endpointsNC2
      change Leaf63.endpoints2 = true at hh
      simp only [Leaf63.endpoints2, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof63.endpointsNC3
      change Leaf63.endpoints3 = true at hh
      simp only [Leaf63.endpoints3, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof63.endpointsNC4
      change Leaf63.endpoints4 = true at hh
      simp only [Leaf63.endpoints4, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof63.endpointsNC5
      change Leaf63.endpoints5 = true at hh
      simp only [Leaf63.endpoints5, List.take_take, Nat.min_self] at hh
      exact hh
  · have hh := Proof63.marginNC
    unfold Leaf63.marginCheck at hh
    have hn := of_decide_eq_true hh
    rw [slice_head] at hn
    rw [claims_eq]
    exact hn

#print axioms valid
end Instance63
