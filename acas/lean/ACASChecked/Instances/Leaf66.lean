import ACASChecked.RawLeafSound
import ACASChecked.Common
import ACASChecked.N66.AcceptNC
noncomputable section
namespace Instance66
open CertSound RouteA RouteNC SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def raw : RawReceipt where
  w := ACASCommon.weights
  b := ACASCommon.biases
  l k := [Leaf66.lo0,Leaf66.lo1,Leaf66.lo2,Leaf66.lo3,Leaf66.lo4,Leaf66.lo5].getD k []
  u k := [Leaf66.hi0,Leaf66.hi1,Leaf66.hi2,Leaf66.hi3,Leaf66.hi4,Leaf66.hi5].getD k []
  v k := [Leaf66.v0,Leaf66.v1,Leaf66.v2,Leaf66.v3,Leaf66.v4,Leaf66.v5].getD k []
  c k := [Leaf66.c0,Leaf66.c1,Leaf66.c2,Leaf66.c3,Leaf66.c4,Leaf66.c5].getD k []
  s k := [Leaf66.s0,Leaf66.s1,Leaf66.s2,Leaf66.s3,Leaf66.s4,Leaf66.s5].getD k []
  afinal := Leaf66.afinal
  boxl := Leaf66.boxl
  boxu := Leaf66.boxu

theorem biases_eq : [Leaf66.b0,Leaf66.b1,Leaf66.b2,Leaf66.b3,Leaf66.b4,Leaf66.b5,Leaf66.b6] = [Leaf8.b0,Leaf8.b1,Leaf8.b2,Leaf8.b3,Leaf8.b4,Leaf8.b5,Leaf8.b6] := by decide +kernel

theorem raw_b : raw.b = fun k => [Leaf66.b0,Leaf66.b1,Leaf66.b2,Leaf66.b3,Leaf66.b4,Leaf66.b5,Leaf66.b6].getD k [] := by
  funext k
  change [Leaf8.b0,Leaf8.b1,Leaf8.b2,Leaf8.b3,Leaf8.b4,Leaf8.b5,Leaf8.b6].getD k [] = [Leaf66.b0,Leaf66.b1,Leaf66.b2,Leaf66.b3,Leaf66.b4,Leaf66.b5,Leaf66.b6].getD k []
  rw [biases_eq]

theorem claims_eq : raw.claims = Leaf66.claims := rfl

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
    · exact Proof66.packedNC0
    · exact Proof66.packedNC1
    · exact Proof66.packedNC2
    · exact Proof66.packedNC3
    · exact Proof66.packedNC4
    · exact Proof66.packedNC5
  · intro k hk
    interval_cases k <;> (simp only [RawReceipt.cost,RawReceipt.a,raw_b]; rfl)
  · simp only [RawReceipt.cost,RawReceipt.a,raw_b]
    rfl
  · intro k hk
    rw [raw_b,claims_eq]
    interval_cases k
    · have hh := Proof66.endpointsNC0
      change Leaf66.endpoints0 = true at hh
      simp only [Leaf66.endpoints0, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof66.endpointsNC1
      change Leaf66.endpoints1 = true at hh
      simp only [Leaf66.endpoints1, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof66.endpointsNC2
      change Leaf66.endpoints2 = true at hh
      simp only [Leaf66.endpoints2, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof66.endpointsNC3
      change Leaf66.endpoints3 = true at hh
      simp only [Leaf66.endpoints3, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof66.endpointsNC4
      change Leaf66.endpoints4 = true at hh
      simp only [Leaf66.endpoints4, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof66.endpointsNC5
      change Leaf66.endpoints5 = true at hh
      simp only [Leaf66.endpoints5, List.take_take, Nat.min_self] at hh
      exact hh
  · have hh := Proof66.marginNC
    unfold Leaf66.marginCheck at hh
    have hn := of_decide_eq_true hh
    rw [slice_head] at hn
    rw [claims_eq]
    exact hn

#print axioms valid
end Instance66
