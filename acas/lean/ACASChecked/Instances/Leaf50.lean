import ACASChecked.RawLeafSound
import ACASChecked.Common
import ACASChecked.N50.AcceptNC
noncomputable section
namespace Instance50
open CertSound RouteA RouteNC SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def raw : RawReceipt where
  w := ACASCommon.weights
  b := ACASCommon.biases
  l k := [Leaf50.lo0,Leaf50.lo1,Leaf50.lo2,Leaf50.lo3,Leaf50.lo4,Leaf50.lo5].getD k []
  u k := [Leaf50.hi0,Leaf50.hi1,Leaf50.hi2,Leaf50.hi3,Leaf50.hi4,Leaf50.hi5].getD k []
  v k := [Leaf50.v0,Leaf50.v1,Leaf50.v2,Leaf50.v3,Leaf50.v4,Leaf50.v5].getD k []
  c k := [Leaf50.c0,Leaf50.c1,Leaf50.c2,Leaf50.c3,Leaf50.c4,Leaf50.c5].getD k []
  s k := [Leaf50.s0,Leaf50.s1,Leaf50.s2,Leaf50.s3,Leaf50.s4,Leaf50.s5].getD k []
  afinal := Leaf50.afinal
  boxl := Leaf50.boxl
  boxu := Leaf50.boxu

theorem biases_eq : [Leaf50.b0,Leaf50.b1,Leaf50.b2,Leaf50.b3,Leaf50.b4,Leaf50.b5,Leaf50.b6] = [Leaf8.b0,Leaf8.b1,Leaf8.b2,Leaf8.b3,Leaf8.b4,Leaf8.b5,Leaf8.b6] := by decide +kernel

theorem raw_b : raw.b = fun k => [Leaf50.b0,Leaf50.b1,Leaf50.b2,Leaf50.b3,Leaf50.b4,Leaf50.b5,Leaf50.b6].getD k [] := by
  funext k
  change [Leaf8.b0,Leaf8.b1,Leaf8.b2,Leaf8.b3,Leaf8.b4,Leaf8.b5,Leaf8.b6].getD k [] = [Leaf50.b0,Leaf50.b1,Leaf50.b2,Leaf50.b3,Leaf50.b4,Leaf50.b5,Leaf50.b6].getD k []
  rw [biases_eq]

theorem claims_eq : raw.claims = Leaf50.claims := rfl

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
    · exact Proof50.packedNC0
    · exact Proof50.packedNC1
    · exact Proof50.packedNC2
    · exact Proof50.packedNC3
    · exact Proof50.packedNC4
    · exact Proof50.packedNC5
  · intro k hk
    interval_cases k <;> (simp only [RawReceipt.cost,RawReceipt.a,raw_b]; rfl)
  · simp only [RawReceipt.cost,RawReceipt.a,raw_b]
    rfl
  · intro k hk
    rw [raw_b,claims_eq]
    interval_cases k
    · have hh := Proof50.endpointsNC0
      change Leaf50.endpoints0 = true at hh
      simp only [Leaf50.endpoints0, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof50.endpointsNC1
      change Leaf50.endpoints1 = true at hh
      simp only [Leaf50.endpoints1, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof50.endpointsNC2
      change Leaf50.endpoints2 = true at hh
      simp only [Leaf50.endpoints2, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof50.endpointsNC3
      change Leaf50.endpoints3 = true at hh
      simp only [Leaf50.endpoints3, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof50.endpointsNC4
      change Leaf50.endpoints4 = true at hh
      simp only [Leaf50.endpoints4, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof50.endpointsNC5
      change Leaf50.endpoints5 = true at hh
      simp only [Leaf50.endpoints5, List.take_take, Nat.min_self] at hh
      exact hh
  · have hh := Proof50.marginNC
    unfold Leaf50.marginCheck at hh
    have hn := of_decide_eq_true hh
    rw [slice_head] at hn
    rw [claims_eq]
    exact hn

#print axioms valid
end Instance50
