import ACASChecked.RawLeafSound
import ACASChecked.Common
import ACASChecked.N34.AcceptNC
noncomputable section
namespace Instance34
open CertSound RouteA RouteNC SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def raw : RawReceipt where
  w := ACASCommon.weights
  b := ACASCommon.biases
  l k := [Leaf34.lo0,Leaf34.lo1,Leaf34.lo2,Leaf34.lo3,Leaf34.lo4,Leaf34.lo5].getD k []
  u k := [Leaf34.hi0,Leaf34.hi1,Leaf34.hi2,Leaf34.hi3,Leaf34.hi4,Leaf34.hi5].getD k []
  v k := [Leaf34.v0,Leaf34.v1,Leaf34.v2,Leaf34.v3,Leaf34.v4,Leaf34.v5].getD k []
  c k := [Leaf34.c0,Leaf34.c1,Leaf34.c2,Leaf34.c3,Leaf34.c4,Leaf34.c5].getD k []
  s k := [Leaf34.s0,Leaf34.s1,Leaf34.s2,Leaf34.s3,Leaf34.s4,Leaf34.s5].getD k []
  afinal := Leaf34.afinal
  boxl := Leaf34.boxl
  boxu := Leaf34.boxu

theorem biases_eq : [Leaf34.b0,Leaf34.b1,Leaf34.b2,Leaf34.b3,Leaf34.b4,Leaf34.b5,Leaf34.b6] = [Leaf8.b0,Leaf8.b1,Leaf8.b2,Leaf8.b3,Leaf8.b4,Leaf8.b5,Leaf8.b6] := by decide +kernel

theorem raw_b : raw.b = fun k => [Leaf34.b0,Leaf34.b1,Leaf34.b2,Leaf34.b3,Leaf34.b4,Leaf34.b5,Leaf34.b6].getD k [] := by
  funext k
  change [Leaf8.b0,Leaf8.b1,Leaf8.b2,Leaf8.b3,Leaf8.b4,Leaf8.b5,Leaf8.b6].getD k [] = [Leaf34.b0,Leaf34.b1,Leaf34.b2,Leaf34.b3,Leaf34.b4,Leaf34.b5,Leaf34.b6].getD k []
  rw [biases_eq]

theorem claims_eq : raw.claims = Leaf34.claims := rfl

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
    · exact Proof34.packedNC0
    · exact Proof34.packedNC1
    · exact Proof34.packedNC2
    · exact Proof34.packedNC3
    · exact Proof34.packedNC4
    · exact Proof34.packedNC5
  · intro k hk
    interval_cases k <;> (simp only [RawReceipt.cost,RawReceipt.a,raw_b]; rfl)
  · simp only [RawReceipt.cost,RawReceipt.a,raw_b]
    rfl
  · intro k hk
    rw [raw_b,claims_eq]
    interval_cases k
    · have hh := Proof34.endpointsNC0
      change Leaf34.endpoints0 = true at hh
      simp only [Leaf34.endpoints0, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof34.endpointsNC1
      change Leaf34.endpoints1 = true at hh
      simp only [Leaf34.endpoints1, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof34.endpointsNC2
      change Leaf34.endpoints2 = true at hh
      simp only [Leaf34.endpoints2, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof34.endpointsNC3
      change Leaf34.endpoints3 = true at hh
      simp only [Leaf34.endpoints3, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof34.endpointsNC4
      change Leaf34.endpoints4 = true at hh
      simp only [Leaf34.endpoints4, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof34.endpointsNC5
      change Leaf34.endpoints5 = true at hh
      simp only [Leaf34.endpoints5, List.take_take, Nat.min_self] at hh
      exact hh
  · have hh := Proof34.marginNC
    unfold Leaf34.marginCheck at hh
    have hn := of_decide_eq_true hh
    rw [slice_head] at hn
    rw [claims_eq]
    exact hn

#print axioms valid
end Instance34
