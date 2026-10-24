import ACASChecked.RawLeafSound
import ACASChecked.Common
import ACASChecked.N58.AcceptNC
noncomputable section
namespace Instance58
open CertSound RouteA RouteNC SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def raw : RawReceipt where
  w := ACASCommon.weights
  b := ACASCommon.biases
  l k := [Leaf58.lo0,Leaf58.lo1,Leaf58.lo2,Leaf58.lo3,Leaf58.lo4,Leaf58.lo5].getD k []
  u k := [Leaf58.hi0,Leaf58.hi1,Leaf58.hi2,Leaf58.hi3,Leaf58.hi4,Leaf58.hi5].getD k []
  v k := [Leaf58.v0,Leaf58.v1,Leaf58.v2,Leaf58.v3,Leaf58.v4,Leaf58.v5].getD k []
  c k := [Leaf58.c0,Leaf58.c1,Leaf58.c2,Leaf58.c3,Leaf58.c4,Leaf58.c5].getD k []
  s k := [Leaf58.s0,Leaf58.s1,Leaf58.s2,Leaf58.s3,Leaf58.s4,Leaf58.s5].getD k []
  afinal := Leaf58.afinal
  boxl := Leaf58.boxl
  boxu := Leaf58.boxu

theorem biases_eq : [Leaf58.b0,Leaf58.b1,Leaf58.b2,Leaf58.b3,Leaf58.b4,Leaf58.b5,Leaf58.b6] = [Leaf8.b0,Leaf8.b1,Leaf8.b2,Leaf8.b3,Leaf8.b4,Leaf8.b5,Leaf8.b6] := by decide +kernel

theorem raw_b : raw.b = fun k => [Leaf58.b0,Leaf58.b1,Leaf58.b2,Leaf58.b3,Leaf58.b4,Leaf58.b5,Leaf58.b6].getD k [] := by
  funext k
  change [Leaf8.b0,Leaf8.b1,Leaf8.b2,Leaf8.b3,Leaf8.b4,Leaf8.b5,Leaf8.b6].getD k [] = [Leaf58.b0,Leaf58.b1,Leaf58.b2,Leaf58.b3,Leaf58.b4,Leaf58.b5,Leaf58.b6].getD k []
  rw [biases_eq]

theorem claims_eq : raw.claims = Leaf58.claims := rfl

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
    · exact Proof58.packedNC0
    · exact Proof58.packedNC1
    · exact Proof58.packedNC2
    · exact Proof58.packedNC3
    · exact Proof58.packedNC4
    · exact Proof58.packedNC5
  · intro k hk
    interval_cases k <;> (simp only [RawReceipt.cost,RawReceipt.a,raw_b]; rfl)
  · simp only [RawReceipt.cost,RawReceipt.a,raw_b]
    rfl
  · intro k hk
    rw [raw_b,claims_eq]
    interval_cases k
    · have hh := Proof58.endpointsNC0
      change Leaf58.endpoints0 = true at hh
      simp only [Leaf58.endpoints0, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof58.endpointsNC1
      change Leaf58.endpoints1 = true at hh
      simp only [Leaf58.endpoints1, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof58.endpointsNC2
      change Leaf58.endpoints2 = true at hh
      simp only [Leaf58.endpoints2, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof58.endpointsNC3
      change Leaf58.endpoints3 = true at hh
      simp only [Leaf58.endpoints3, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof58.endpointsNC4
      change Leaf58.endpoints4 = true at hh
      simp only [Leaf58.endpoints4, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof58.endpointsNC5
      change Leaf58.endpoints5 = true at hh
      simp only [Leaf58.endpoints5, List.take_take, Nat.min_self] at hh
      exact hh
  · have hh := Proof58.marginNC
    unfold Leaf58.marginCheck at hh
    have hn := of_decide_eq_true hh
    rw [slice_head] at hn
    rw [claims_eq]
    exact hn

#print axioms valid
end Instance58
