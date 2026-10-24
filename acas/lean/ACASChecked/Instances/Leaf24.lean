import ACASChecked.RawLeafSound
import ACASChecked.Common
import ACASChecked.N24.AcceptNC
noncomputable section
namespace Instance24
open CertSound RouteA RouteNC SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def raw : RawReceipt where
  w := ACASCommon.weights
  b := ACASCommon.biases
  l k := [Leaf24.lo0,Leaf24.lo1,Leaf24.lo2,Leaf24.lo3,Leaf24.lo4,Leaf24.lo5].getD k []
  u k := [Leaf24.hi0,Leaf24.hi1,Leaf24.hi2,Leaf24.hi3,Leaf24.hi4,Leaf24.hi5].getD k []
  v k := [Leaf24.v0,Leaf24.v1,Leaf24.v2,Leaf24.v3,Leaf24.v4,Leaf24.v5].getD k []
  c k := [Leaf24.c0,Leaf24.c1,Leaf24.c2,Leaf24.c3,Leaf24.c4,Leaf24.c5].getD k []
  s k := [Leaf24.s0,Leaf24.s1,Leaf24.s2,Leaf24.s3,Leaf24.s4,Leaf24.s5].getD k []
  afinal := Leaf24.afinal
  boxl := Leaf24.boxl
  boxu := Leaf24.boxu

theorem biases_eq : [Leaf24.b0,Leaf24.b1,Leaf24.b2,Leaf24.b3,Leaf24.b4,Leaf24.b5,Leaf24.b6] = [Leaf8.b0,Leaf8.b1,Leaf8.b2,Leaf8.b3,Leaf8.b4,Leaf8.b5,Leaf8.b6] := by decide +kernel

theorem raw_b : raw.b = fun k => [Leaf24.b0,Leaf24.b1,Leaf24.b2,Leaf24.b3,Leaf24.b4,Leaf24.b5,Leaf24.b6].getD k [] := by
  funext k
  change [Leaf8.b0,Leaf8.b1,Leaf8.b2,Leaf8.b3,Leaf8.b4,Leaf8.b5,Leaf8.b6].getD k [] = [Leaf24.b0,Leaf24.b1,Leaf24.b2,Leaf24.b3,Leaf24.b4,Leaf24.b5,Leaf24.b6].getD k []
  rw [biases_eq]

theorem claims_eq : raw.claims = Leaf24.claims := rfl

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
    · exact Proof24.packedNC0
    · exact Proof24.packedNC1
    · exact Proof24.packedNC2
    · exact Proof24.packedNC3
    · exact Proof24.packedNC4
    · exact Proof24.packedNC5
  · intro k hk
    interval_cases k <;> (simp only [RawReceipt.cost,RawReceipt.a,raw_b]; rfl)
  · simp only [RawReceipt.cost,RawReceipt.a,raw_b]
    rfl
  · intro k hk
    rw [raw_b,claims_eq]
    interval_cases k
    · have hh := Proof24.endpointsNC0
      change Leaf24.endpoints0 = true at hh
      simp only [Leaf24.endpoints0, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof24.endpointsNC1
      change Leaf24.endpoints1 = true at hh
      simp only [Leaf24.endpoints1, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof24.endpointsNC2
      change Leaf24.endpoints2 = true at hh
      simp only [Leaf24.endpoints2, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof24.endpointsNC3
      change Leaf24.endpoints3 = true at hh
      simp only [Leaf24.endpoints3, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof24.endpointsNC4
      change Leaf24.endpoints4 = true at hh
      simp only [Leaf24.endpoints4, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof24.endpointsNC5
      change Leaf24.endpoints5 = true at hh
      simp only [Leaf24.endpoints5, List.take_take, Nat.min_self] at hh
      exact hh
  · have hh := Proof24.marginNC
    unfold Leaf24.marginCheck at hh
    have hn := of_decide_eq_true hh
    rw [slice_head] at hn
    rw [claims_eq]
    exact hn

#print axioms valid
end Instance24
