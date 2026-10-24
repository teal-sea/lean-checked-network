import ACASChecked.RawLeafSound
import ACASChecked.Common
import ACASChecked.N64.AcceptNC
noncomputable section
namespace Instance64
open CertSound RouteA RouteNC SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def raw : RawReceipt where
  w := ACASCommon.weights
  b := ACASCommon.biases
  l k := [Leaf64.lo0,Leaf64.lo1,Leaf64.lo2,Leaf64.lo3,Leaf64.lo4,Leaf64.lo5].getD k []
  u k := [Leaf64.hi0,Leaf64.hi1,Leaf64.hi2,Leaf64.hi3,Leaf64.hi4,Leaf64.hi5].getD k []
  v k := [Leaf64.v0,Leaf64.v1,Leaf64.v2,Leaf64.v3,Leaf64.v4,Leaf64.v5].getD k []
  c k := [Leaf64.c0,Leaf64.c1,Leaf64.c2,Leaf64.c3,Leaf64.c4,Leaf64.c5].getD k []
  s k := [Leaf64.s0,Leaf64.s1,Leaf64.s2,Leaf64.s3,Leaf64.s4,Leaf64.s5].getD k []
  afinal := Leaf64.afinal
  boxl := Leaf64.boxl
  boxu := Leaf64.boxu

theorem biases_eq : [Leaf64.b0,Leaf64.b1,Leaf64.b2,Leaf64.b3,Leaf64.b4,Leaf64.b5,Leaf64.b6] = [Leaf8.b0,Leaf8.b1,Leaf8.b2,Leaf8.b3,Leaf8.b4,Leaf8.b5,Leaf8.b6] := by decide +kernel

theorem raw_b : raw.b = fun k => [Leaf64.b0,Leaf64.b1,Leaf64.b2,Leaf64.b3,Leaf64.b4,Leaf64.b5,Leaf64.b6].getD k [] := by
  funext k
  change [Leaf8.b0,Leaf8.b1,Leaf8.b2,Leaf8.b3,Leaf8.b4,Leaf8.b5,Leaf8.b6].getD k [] = [Leaf64.b0,Leaf64.b1,Leaf64.b2,Leaf64.b3,Leaf64.b4,Leaf64.b5,Leaf64.b6].getD k []
  rw [biases_eq]

theorem claims_eq : raw.claims = Leaf64.claims := rfl

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
    · exact Proof64.packedNC0
    · exact Proof64.packedNC1
    · exact Proof64.packedNC2
    · exact Proof64.packedNC3
    · exact Proof64.packedNC4
    · exact Proof64.packedNC5
  · intro k hk
    interval_cases k <;> (simp only [RawReceipt.cost,RawReceipt.a,raw_b]; rfl)
  · simp only [RawReceipt.cost,RawReceipt.a,raw_b]
    rfl
  · intro k hk
    rw [raw_b,claims_eq]
    interval_cases k
    · have hh := Proof64.endpointsNC0
      change Leaf64.endpoints0 = true at hh
      simp only [Leaf64.endpoints0, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof64.endpointsNC1
      change Leaf64.endpoints1 = true at hh
      simp only [Leaf64.endpoints1, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof64.endpointsNC2
      change Leaf64.endpoints2 = true at hh
      simp only [Leaf64.endpoints2, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof64.endpointsNC3
      change Leaf64.endpoints3 = true at hh
      simp only [Leaf64.endpoints3, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof64.endpointsNC4
      change Leaf64.endpoints4 = true at hh
      simp only [Leaf64.endpoints4, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof64.endpointsNC5
      change Leaf64.endpoints5 = true at hh
      simp only [Leaf64.endpoints5, List.take_take, Nat.min_self] at hh
      exact hh
  · have hh := Proof64.marginNC
    unfold Leaf64.marginCheck at hh
    have hn := of_decide_eq_true hh
    rw [slice_head] at hn
    rw [claims_eq]
    exact hn

#print axioms valid
end Instance64
