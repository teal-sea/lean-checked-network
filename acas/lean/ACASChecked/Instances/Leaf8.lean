import ACASChecked.RawLeafSound
import ACASChecked.Common
import ACASChecked.N8.AcceptNC
noncomputable section
namespace Instance8
open CertSound RouteA RouteNC SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def raw : RawReceipt where
  w := ACASCommon.weights
  b := ACASCommon.biases
  l k := [Leaf8.lo0,Leaf8.lo1,Leaf8.lo2,Leaf8.lo3,Leaf8.lo4,Leaf8.lo5].getD k []
  u k := [Leaf8.hi0,Leaf8.hi1,Leaf8.hi2,Leaf8.hi3,Leaf8.hi4,Leaf8.hi5].getD k []
  v k := [Leaf8.v0,Leaf8.v1,Leaf8.v2,Leaf8.v3,Leaf8.v4,Leaf8.v5].getD k []
  c k := [Leaf8.c0,Leaf8.c1,Leaf8.c2,Leaf8.c3,Leaf8.c4,Leaf8.c5].getD k []
  s k := [Leaf8.s0,Leaf8.s1,Leaf8.s2,Leaf8.s3,Leaf8.s4,Leaf8.s5].getD k []
  afinal := Leaf8.afinal
  boxl := Leaf8.boxl
  boxu := Leaf8.boxu

theorem biases_eq : [Leaf8.b0,Leaf8.b1,Leaf8.b2,Leaf8.b3,Leaf8.b4,Leaf8.b5,Leaf8.b6] = [Leaf8.b0,Leaf8.b1,Leaf8.b2,Leaf8.b3,Leaf8.b4,Leaf8.b5,Leaf8.b6] := by decide +kernel

theorem raw_b : raw.b = fun k => [Leaf8.b0,Leaf8.b1,Leaf8.b2,Leaf8.b3,Leaf8.b4,Leaf8.b5,Leaf8.b6].getD k [] := by
  funext k
  change [Leaf8.b0,Leaf8.b1,Leaf8.b2,Leaf8.b3,Leaf8.b4,Leaf8.b5,Leaf8.b6].getD k [] = [Leaf8.b0,Leaf8.b1,Leaf8.b2,Leaf8.b3,Leaf8.b4,Leaf8.b5,Leaf8.b6].getD k []
  rw [biases_eq]

theorem claims_eq : raw.claims = Leaf8.claims := rfl

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
    · exact Proof8.packedNC0
    · exact Proof8.packedNC1
    · exact Proof8.packedNC2
    · exact Proof8.packedNC3
    · exact Proof8.packedNC4
    · exact Proof8.packedNC5
  · intro k hk
    interval_cases k <;> (simp only [RawReceipt.cost,RawReceipt.a,raw_b]; rfl)
  · simp only [RawReceipt.cost,RawReceipt.a,raw_b]
    rfl
  · intro k hk
    rw [raw_b,claims_eq]
    interval_cases k
    · have hh := Proof8.endpointsNC0
      change Leaf8.endpoints0 = true at hh
      simp only [Leaf8.endpoints0, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof8.endpointsNC1
      change Leaf8.endpoints1 = true at hh
      simp only [Leaf8.endpoints1, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof8.endpointsNC2
      change Leaf8.endpoints2 = true at hh
      simp only [Leaf8.endpoints2, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof8.endpointsNC3
      change Leaf8.endpoints3 = true at hh
      simp only [Leaf8.endpoints3, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof8.endpointsNC4
      change Leaf8.endpoints4 = true at hh
      simp only [Leaf8.endpoints4, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof8.endpointsNC5
      change Leaf8.endpoints5 = true at hh
      simp only [Leaf8.endpoints5, List.take_take, Nat.min_self] at hh
      exact hh
  · have hh := Proof8.marginNC
    unfold Leaf8.marginCheck at hh
    have hn := of_decide_eq_true hh
    rw [slice_head] at hn
    rw [claims_eq]
    exact hn

#print axioms valid
end Instance8
