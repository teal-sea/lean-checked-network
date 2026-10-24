import ACASChecked.RawLeafSound
import ACASChecked.Common
import ACASChecked.N29.AcceptNC
noncomputable section
namespace Instance29
open CertSound RouteA RouteNC SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def raw : RawReceipt where
  w := ACASCommon.weights
  b := ACASCommon.biases
  l k := [Leaf29.lo0,Leaf29.lo1,Leaf29.lo2,Leaf29.lo3,Leaf29.lo4,Leaf29.lo5].getD k []
  u k := [Leaf29.hi0,Leaf29.hi1,Leaf29.hi2,Leaf29.hi3,Leaf29.hi4,Leaf29.hi5].getD k []
  v k := [Leaf29.v0,Leaf29.v1,Leaf29.v2,Leaf29.v3,Leaf29.v4,Leaf29.v5].getD k []
  c k := [Leaf29.c0,Leaf29.c1,Leaf29.c2,Leaf29.c3,Leaf29.c4,Leaf29.c5].getD k []
  s k := [Leaf29.s0,Leaf29.s1,Leaf29.s2,Leaf29.s3,Leaf29.s4,Leaf29.s5].getD k []
  afinal := Leaf29.afinal
  boxl := Leaf29.boxl
  boxu := Leaf29.boxu

theorem biases_eq : [Leaf29.b0,Leaf29.b1,Leaf29.b2,Leaf29.b3,Leaf29.b4,Leaf29.b5,Leaf29.b6] = [Leaf8.b0,Leaf8.b1,Leaf8.b2,Leaf8.b3,Leaf8.b4,Leaf8.b5,Leaf8.b6] := by decide +kernel

theorem raw_b : raw.b = fun k => [Leaf29.b0,Leaf29.b1,Leaf29.b2,Leaf29.b3,Leaf29.b4,Leaf29.b5,Leaf29.b6].getD k [] := by
  funext k
  change [Leaf8.b0,Leaf8.b1,Leaf8.b2,Leaf8.b3,Leaf8.b4,Leaf8.b5,Leaf8.b6].getD k [] = [Leaf29.b0,Leaf29.b1,Leaf29.b2,Leaf29.b3,Leaf29.b4,Leaf29.b5,Leaf29.b6].getD k []
  rw [biases_eq]

theorem claims_eq : raw.claims = Leaf29.claims := rfl

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
    · exact Proof29.packedNC0
    · exact Proof29.packedNC1
    · exact Proof29.packedNC2
    · exact Proof29.packedNC3
    · exact Proof29.packedNC4
    · exact Proof29.packedNC5
  · intro k hk
    interval_cases k <;> (simp only [RawReceipt.cost,RawReceipt.a,raw_b]; rfl)
  · simp only [RawReceipt.cost,RawReceipt.a,raw_b]
    rfl
  · intro k hk
    rw [raw_b,claims_eq]
    interval_cases k
    · have hh := Proof29.endpointsNC0
      change Leaf29.endpoints0 = true at hh
      simp only [Leaf29.endpoints0, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof29.endpointsNC1
      change Leaf29.endpoints1 = true at hh
      simp only [Leaf29.endpoints1, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof29.endpointsNC2
      change Leaf29.endpoints2 = true at hh
      simp only [Leaf29.endpoints2, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof29.endpointsNC3
      change Leaf29.endpoints3 = true at hh
      simp only [Leaf29.endpoints3, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof29.endpointsNC4
      change Leaf29.endpoints4 = true at hh
      simp only [Leaf29.endpoints4, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof29.endpointsNC5
      change Leaf29.endpoints5 = true at hh
      simp only [Leaf29.endpoints5, List.take_take, Nat.min_self] at hh
      exact hh
  · have hh := Proof29.marginNC
    unfold Leaf29.marginCheck at hh
    have hn := of_decide_eq_true hh
    rw [slice_head] at hn
    rw [claims_eq]
    exact hn

#print axioms valid
end Instance29
