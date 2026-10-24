import ACASChecked.RawLeafSound
import ACASChecked.Common
import ACASChecked.N37.AcceptNC
noncomputable section
namespace Instance37
open CertSound RouteA RouteNC SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def raw : RawReceipt where
  w := ACASCommon.weights
  b := ACASCommon.biases
  l k := [Leaf37.lo0,Leaf37.lo1,Leaf37.lo2,Leaf37.lo3,Leaf37.lo4,Leaf37.lo5].getD k []
  u k := [Leaf37.hi0,Leaf37.hi1,Leaf37.hi2,Leaf37.hi3,Leaf37.hi4,Leaf37.hi5].getD k []
  v k := [Leaf37.v0,Leaf37.v1,Leaf37.v2,Leaf37.v3,Leaf37.v4,Leaf37.v5].getD k []
  c k := [Leaf37.c0,Leaf37.c1,Leaf37.c2,Leaf37.c3,Leaf37.c4,Leaf37.c5].getD k []
  s k := [Leaf37.s0,Leaf37.s1,Leaf37.s2,Leaf37.s3,Leaf37.s4,Leaf37.s5].getD k []
  afinal := Leaf37.afinal
  boxl := Leaf37.boxl
  boxu := Leaf37.boxu

theorem biases_eq : [Leaf37.b0,Leaf37.b1,Leaf37.b2,Leaf37.b3,Leaf37.b4,Leaf37.b5,Leaf37.b6] = [Leaf8.b0,Leaf8.b1,Leaf8.b2,Leaf8.b3,Leaf8.b4,Leaf8.b5,Leaf8.b6] := by decide +kernel

theorem raw_b : raw.b = fun k => [Leaf37.b0,Leaf37.b1,Leaf37.b2,Leaf37.b3,Leaf37.b4,Leaf37.b5,Leaf37.b6].getD k [] := by
  funext k
  change [Leaf8.b0,Leaf8.b1,Leaf8.b2,Leaf8.b3,Leaf8.b4,Leaf8.b5,Leaf8.b6].getD k [] = [Leaf37.b0,Leaf37.b1,Leaf37.b2,Leaf37.b3,Leaf37.b4,Leaf37.b5,Leaf37.b6].getD k []
  rw [biases_eq]

theorem claims_eq : raw.claims = Leaf37.claims := rfl

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
    · exact Proof37.packedNC0
    · exact Proof37.packedNC1
    · exact Proof37.packedNC2
    · exact Proof37.packedNC3
    · exact Proof37.packedNC4
    · exact Proof37.packedNC5
  · intro k hk
    interval_cases k <;> (simp only [RawReceipt.cost,RawReceipt.a,raw_b]; rfl)
  · simp only [RawReceipt.cost,RawReceipt.a,raw_b]
    rfl
  · intro k hk
    rw [raw_b,claims_eq]
    interval_cases k
    · have hh := Proof37.endpointsNC0
      change Leaf37.endpoints0 = true at hh
      simp only [Leaf37.endpoints0, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof37.endpointsNC1
      change Leaf37.endpoints1 = true at hh
      simp only [Leaf37.endpoints1, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof37.endpointsNC2
      change Leaf37.endpoints2 = true at hh
      simp only [Leaf37.endpoints2, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof37.endpointsNC3
      change Leaf37.endpoints3 = true at hh
      simp only [Leaf37.endpoints3, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof37.endpointsNC4
      change Leaf37.endpoints4 = true at hh
      simp only [Leaf37.endpoints4, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof37.endpointsNC5
      change Leaf37.endpoints5 = true at hh
      simp only [Leaf37.endpoints5, List.take_take, Nat.min_self] at hh
      exact hh
  · have hh := Proof37.marginNC
    unfold Leaf37.marginCheck at hh
    have hn := of_decide_eq_true hh
    rw [slice_head] at hn
    rw [claims_eq]
    exact hn

#print axioms valid
end Instance37
