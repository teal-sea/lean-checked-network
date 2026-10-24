import ACASChecked.RawLeafSound
import ACASChecked.Common
import ACASChecked.N52.AcceptNC
noncomputable section
namespace Instance52
open CertSound RouteA RouteNC SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def raw : RawReceipt where
  w := ACASCommon.weights
  b := ACASCommon.biases
  l k := [Leaf52.lo0,Leaf52.lo1,Leaf52.lo2,Leaf52.lo3,Leaf52.lo4,Leaf52.lo5].getD k []
  u k := [Leaf52.hi0,Leaf52.hi1,Leaf52.hi2,Leaf52.hi3,Leaf52.hi4,Leaf52.hi5].getD k []
  v k := [Leaf52.v0,Leaf52.v1,Leaf52.v2,Leaf52.v3,Leaf52.v4,Leaf52.v5].getD k []
  c k := [Leaf52.c0,Leaf52.c1,Leaf52.c2,Leaf52.c3,Leaf52.c4,Leaf52.c5].getD k []
  s k := [Leaf52.s0,Leaf52.s1,Leaf52.s2,Leaf52.s3,Leaf52.s4,Leaf52.s5].getD k []
  afinal := Leaf52.afinal
  boxl := Leaf52.boxl
  boxu := Leaf52.boxu

theorem biases_eq : [Leaf52.b0,Leaf52.b1,Leaf52.b2,Leaf52.b3,Leaf52.b4,Leaf52.b5,Leaf52.b6] = [Leaf8.b0,Leaf8.b1,Leaf8.b2,Leaf8.b3,Leaf8.b4,Leaf8.b5,Leaf8.b6] := by decide +kernel

theorem raw_b : raw.b = fun k => [Leaf52.b0,Leaf52.b1,Leaf52.b2,Leaf52.b3,Leaf52.b4,Leaf52.b5,Leaf52.b6].getD k [] := by
  funext k
  change [Leaf8.b0,Leaf8.b1,Leaf8.b2,Leaf8.b3,Leaf8.b4,Leaf8.b5,Leaf8.b6].getD k [] = [Leaf52.b0,Leaf52.b1,Leaf52.b2,Leaf52.b3,Leaf52.b4,Leaf52.b5,Leaf52.b6].getD k []
  rw [biases_eq]

theorem claims_eq : raw.claims = Leaf52.claims := rfl

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
    · exact Proof52.packedNC0
    · exact Proof52.packedNC1
    · exact Proof52.packedNC2
    · exact Proof52.packedNC3
    · exact Proof52.packedNC4
    · exact Proof52.packedNC5
  · intro k hk
    interval_cases k <;> (simp only [RawReceipt.cost,RawReceipt.a,raw_b]; rfl)
  · simp only [RawReceipt.cost,RawReceipt.a,raw_b]
    rfl
  · intro k hk
    rw [raw_b,claims_eq]
    interval_cases k
    · have hh := Proof52.endpointsNC0
      change Leaf52.endpoints0 = true at hh
      simp only [Leaf52.endpoints0, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof52.endpointsNC1
      change Leaf52.endpoints1 = true at hh
      simp only [Leaf52.endpoints1, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof52.endpointsNC2
      change Leaf52.endpoints2 = true at hh
      simp only [Leaf52.endpoints2, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof52.endpointsNC3
      change Leaf52.endpoints3 = true at hh
      simp only [Leaf52.endpoints3, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof52.endpointsNC4
      change Leaf52.endpoints4 = true at hh
      simp only [Leaf52.endpoints4, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof52.endpointsNC5
      change Leaf52.endpoints5 = true at hh
      simp only [Leaf52.endpoints5, List.take_take, Nat.min_self] at hh
      exact hh
  · have hh := Proof52.marginNC
    unfold Leaf52.marginCheck at hh
    have hn := of_decide_eq_true hh
    rw [slice_head] at hn
    rw [claims_eq]
    exact hn

#print axioms valid
end Instance52
