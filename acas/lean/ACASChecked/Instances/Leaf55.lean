import ACASChecked.RawLeafSound
import ACASChecked.Common
import ACASChecked.N55.AcceptNC
noncomputable section
namespace Instance55
open CertSound RouteA RouteNC SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def raw : RawReceipt where
  w := ACASCommon.weights
  b := ACASCommon.biases
  l k := [Leaf55.lo0,Leaf55.lo1,Leaf55.lo2,Leaf55.lo3,Leaf55.lo4,Leaf55.lo5].getD k []
  u k := [Leaf55.hi0,Leaf55.hi1,Leaf55.hi2,Leaf55.hi3,Leaf55.hi4,Leaf55.hi5].getD k []
  v k := [Leaf55.v0,Leaf55.v1,Leaf55.v2,Leaf55.v3,Leaf55.v4,Leaf55.v5].getD k []
  c k := [Leaf55.c0,Leaf55.c1,Leaf55.c2,Leaf55.c3,Leaf55.c4,Leaf55.c5].getD k []
  s k := [Leaf55.s0,Leaf55.s1,Leaf55.s2,Leaf55.s3,Leaf55.s4,Leaf55.s5].getD k []
  afinal := Leaf55.afinal
  boxl := Leaf55.boxl
  boxu := Leaf55.boxu

theorem biases_eq : [Leaf55.b0,Leaf55.b1,Leaf55.b2,Leaf55.b3,Leaf55.b4,Leaf55.b5,Leaf55.b6] = [Leaf8.b0,Leaf8.b1,Leaf8.b2,Leaf8.b3,Leaf8.b4,Leaf8.b5,Leaf8.b6] := by decide +kernel

theorem raw_b : raw.b = fun k => [Leaf55.b0,Leaf55.b1,Leaf55.b2,Leaf55.b3,Leaf55.b4,Leaf55.b5,Leaf55.b6].getD k [] := by
  funext k
  change [Leaf8.b0,Leaf8.b1,Leaf8.b2,Leaf8.b3,Leaf8.b4,Leaf8.b5,Leaf8.b6].getD k [] = [Leaf55.b0,Leaf55.b1,Leaf55.b2,Leaf55.b3,Leaf55.b4,Leaf55.b5,Leaf55.b6].getD k []
  rw [biases_eq]

theorem claims_eq : raw.claims = Leaf55.claims := rfl

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
    · exact Proof55.packedNC0
    · exact Proof55.packedNC1
    · exact Proof55.packedNC2
    · exact Proof55.packedNC3
    · exact Proof55.packedNC4
    · exact Proof55.packedNC5
  · intro k hk
    interval_cases k <;> (simp only [RawReceipt.cost,RawReceipt.a,raw_b]; rfl)
  · simp only [RawReceipt.cost,RawReceipt.a,raw_b]
    rfl
  · intro k hk
    rw [raw_b,claims_eq]
    interval_cases k
    · have hh := Proof55.endpointsNC0
      change Leaf55.endpoints0 = true at hh
      simp only [Leaf55.endpoints0, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof55.endpointsNC1
      change Leaf55.endpoints1 = true at hh
      simp only [Leaf55.endpoints1, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof55.endpointsNC2
      change Leaf55.endpoints2 = true at hh
      simp only [Leaf55.endpoints2, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof55.endpointsNC3
      change Leaf55.endpoints3 = true at hh
      simp only [Leaf55.endpoints3, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof55.endpointsNC4
      change Leaf55.endpoints4 = true at hh
      simp only [Leaf55.endpoints4, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof55.endpointsNC5
      change Leaf55.endpoints5 = true at hh
      simp only [Leaf55.endpoints5, List.take_take, Nat.min_self] at hh
      exact hh
  · have hh := Proof55.marginNC
    unfold Leaf55.marginCheck at hh
    have hn := of_decide_eq_true hh
    rw [slice_head] at hn
    rw [claims_eq]
    exact hn

#print axioms valid
end Instance55
