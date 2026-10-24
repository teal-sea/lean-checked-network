import ACASChecked.RawLeafSound
import ACASChecked.Common
import ACASChecked.N54.AcceptNC
noncomputable section
namespace Instance54
open CertSound RouteA RouteNC SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def raw : RawReceipt where
  w := ACASCommon.weights
  b := ACASCommon.biases
  l k := [Leaf54.lo0,Leaf54.lo1,Leaf54.lo2,Leaf54.lo3,Leaf54.lo4,Leaf54.lo5].getD k []
  u k := [Leaf54.hi0,Leaf54.hi1,Leaf54.hi2,Leaf54.hi3,Leaf54.hi4,Leaf54.hi5].getD k []
  v k := [Leaf54.v0,Leaf54.v1,Leaf54.v2,Leaf54.v3,Leaf54.v4,Leaf54.v5].getD k []
  c k := [Leaf54.c0,Leaf54.c1,Leaf54.c2,Leaf54.c3,Leaf54.c4,Leaf54.c5].getD k []
  s k := [Leaf54.s0,Leaf54.s1,Leaf54.s2,Leaf54.s3,Leaf54.s4,Leaf54.s5].getD k []
  afinal := Leaf54.afinal
  boxl := Leaf54.boxl
  boxu := Leaf54.boxu

theorem biases_eq : [Leaf54.b0,Leaf54.b1,Leaf54.b2,Leaf54.b3,Leaf54.b4,Leaf54.b5,Leaf54.b6] = [Leaf8.b0,Leaf8.b1,Leaf8.b2,Leaf8.b3,Leaf8.b4,Leaf8.b5,Leaf8.b6] := by decide +kernel

theorem raw_b : raw.b = fun k => [Leaf54.b0,Leaf54.b1,Leaf54.b2,Leaf54.b3,Leaf54.b4,Leaf54.b5,Leaf54.b6].getD k [] := by
  funext k
  change [Leaf8.b0,Leaf8.b1,Leaf8.b2,Leaf8.b3,Leaf8.b4,Leaf8.b5,Leaf8.b6].getD k [] = [Leaf54.b0,Leaf54.b1,Leaf54.b2,Leaf54.b3,Leaf54.b4,Leaf54.b5,Leaf54.b6].getD k []
  rw [biases_eq]

theorem claims_eq : raw.claims = Leaf54.claims := rfl

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
    · exact Proof54.packedNC0
    · exact Proof54.packedNC1
    · exact Proof54.packedNC2
    · exact Proof54.packedNC3
    · exact Proof54.packedNC4
    · exact Proof54.packedNC5
  · intro k hk
    interval_cases k <;> (simp only [RawReceipt.cost,RawReceipt.a,raw_b]; rfl)
  · simp only [RawReceipt.cost,RawReceipt.a,raw_b]
    rfl
  · intro k hk
    rw [raw_b,claims_eq]
    interval_cases k
    · have hh := Proof54.endpointsNC0
      change Leaf54.endpoints0 = true at hh
      simp only [Leaf54.endpoints0, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof54.endpointsNC1
      change Leaf54.endpoints1 = true at hh
      simp only [Leaf54.endpoints1, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof54.endpointsNC2
      change Leaf54.endpoints2 = true at hh
      simp only [Leaf54.endpoints2, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof54.endpointsNC3
      change Leaf54.endpoints3 = true at hh
      simp only [Leaf54.endpoints3, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof54.endpointsNC4
      change Leaf54.endpoints4 = true at hh
      simp only [Leaf54.endpoints4, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof54.endpointsNC5
      change Leaf54.endpoints5 = true at hh
      simp only [Leaf54.endpoints5, List.take_take, Nat.min_self] at hh
      exact hh
  · have hh := Proof54.marginNC
    unfold Leaf54.marginCheck at hh
    have hn := of_decide_eq_true hh
    rw [slice_head] at hn
    rw [claims_eq]
    exact hn

#print axioms valid
end Instance54
