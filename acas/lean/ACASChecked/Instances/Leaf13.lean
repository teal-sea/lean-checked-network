import ACASChecked.RawLeafSound
import ACASChecked.Common
import ACASChecked.N13.AcceptNC
noncomputable section
namespace Instance13
open CertSound RouteA RouteNC SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def raw : RawReceipt where
  w := ACASCommon.weights
  b := ACASCommon.biases
  l k := [Leaf13.lo0,Leaf13.lo1,Leaf13.lo2,Leaf13.lo3,Leaf13.lo4,Leaf13.lo5].getD k []
  u k := [Leaf13.hi0,Leaf13.hi1,Leaf13.hi2,Leaf13.hi3,Leaf13.hi4,Leaf13.hi5].getD k []
  v k := [Leaf13.v0,Leaf13.v1,Leaf13.v2,Leaf13.v3,Leaf13.v4,Leaf13.v5].getD k []
  c k := [Leaf13.c0,Leaf13.c1,Leaf13.c2,Leaf13.c3,Leaf13.c4,Leaf13.c5].getD k []
  s k := [Leaf13.s0,Leaf13.s1,Leaf13.s2,Leaf13.s3,Leaf13.s4,Leaf13.s5].getD k []
  afinal := Leaf13.afinal
  boxl := Leaf13.boxl
  boxu := Leaf13.boxu

theorem biases_eq : [Leaf13.b0,Leaf13.b1,Leaf13.b2,Leaf13.b3,Leaf13.b4,Leaf13.b5,Leaf13.b6] = [Leaf8.b0,Leaf8.b1,Leaf8.b2,Leaf8.b3,Leaf8.b4,Leaf8.b5,Leaf8.b6] := by decide +kernel

theorem raw_b : raw.b = fun k => [Leaf13.b0,Leaf13.b1,Leaf13.b2,Leaf13.b3,Leaf13.b4,Leaf13.b5,Leaf13.b6].getD k [] := by
  funext k
  change [Leaf8.b0,Leaf8.b1,Leaf8.b2,Leaf8.b3,Leaf8.b4,Leaf8.b5,Leaf8.b6].getD k [] = [Leaf13.b0,Leaf13.b1,Leaf13.b2,Leaf13.b3,Leaf13.b4,Leaf13.b5,Leaf13.b6].getD k []
  rw [biases_eq]

theorem claims_eq : raw.claims = Leaf13.claims := rfl

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
    · exact Proof13.packedNC0
    · exact Proof13.packedNC1
    · exact Proof13.packedNC2
    · exact Proof13.packedNC3
    · exact Proof13.packedNC4
    · exact Proof13.packedNC5
  · intro k hk
    interval_cases k <;> (simp only [RawReceipt.cost,RawReceipt.a,raw_b]; rfl)
  · simp only [RawReceipt.cost,RawReceipt.a,raw_b]
    rfl
  · intro k hk
    rw [raw_b,claims_eq]
    interval_cases k
    · have hh := Proof13.endpointsNC0
      change Leaf13.endpoints0 = true at hh
      simp only [Leaf13.endpoints0, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof13.endpointsNC1
      change Leaf13.endpoints1 = true at hh
      simp only [Leaf13.endpoints1, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof13.endpointsNC2
      change Leaf13.endpoints2 = true at hh
      simp only [Leaf13.endpoints2, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof13.endpointsNC3
      change Leaf13.endpoints3 = true at hh
      simp only [Leaf13.endpoints3, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof13.endpointsNC4
      change Leaf13.endpoints4 = true at hh
      simp only [Leaf13.endpoints4, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof13.endpointsNC5
      change Leaf13.endpoints5 = true at hh
      simp only [Leaf13.endpoints5, List.take_take, Nat.min_self] at hh
      exact hh
  · have hh := Proof13.marginNC
    unfold Leaf13.marginCheck at hh
    have hn := of_decide_eq_true hh
    rw [slice_head] at hn
    rw [claims_eq]
    exact hn

#print axioms valid
end Instance13
