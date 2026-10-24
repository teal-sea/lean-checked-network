import ACASChecked.RawLeafSound
import ACASChecked.Common
import ACASChecked.N30.AcceptNC
noncomputable section
namespace Instance30
open CertSound RouteA RouteNC SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def raw : RawReceipt where
  w := ACASCommon.weights
  b := ACASCommon.biases
  l k := [Leaf30.lo0,Leaf30.lo1,Leaf30.lo2,Leaf30.lo3,Leaf30.lo4,Leaf30.lo5].getD k []
  u k := [Leaf30.hi0,Leaf30.hi1,Leaf30.hi2,Leaf30.hi3,Leaf30.hi4,Leaf30.hi5].getD k []
  v k := [Leaf30.v0,Leaf30.v1,Leaf30.v2,Leaf30.v3,Leaf30.v4,Leaf30.v5].getD k []
  c k := [Leaf30.c0,Leaf30.c1,Leaf30.c2,Leaf30.c3,Leaf30.c4,Leaf30.c5].getD k []
  s k := [Leaf30.s0,Leaf30.s1,Leaf30.s2,Leaf30.s3,Leaf30.s4,Leaf30.s5].getD k []
  afinal := Leaf30.afinal
  boxl := Leaf30.boxl
  boxu := Leaf30.boxu

theorem biases_eq : [Leaf30.b0,Leaf30.b1,Leaf30.b2,Leaf30.b3,Leaf30.b4,Leaf30.b5,Leaf30.b6] = [Leaf8.b0,Leaf8.b1,Leaf8.b2,Leaf8.b3,Leaf8.b4,Leaf8.b5,Leaf8.b6] := by decide +kernel

theorem raw_b : raw.b = fun k => [Leaf30.b0,Leaf30.b1,Leaf30.b2,Leaf30.b3,Leaf30.b4,Leaf30.b5,Leaf30.b6].getD k [] := by
  funext k
  change [Leaf8.b0,Leaf8.b1,Leaf8.b2,Leaf8.b3,Leaf8.b4,Leaf8.b5,Leaf8.b6].getD k [] = [Leaf30.b0,Leaf30.b1,Leaf30.b2,Leaf30.b3,Leaf30.b4,Leaf30.b5,Leaf30.b6].getD k []
  rw [biases_eq]

theorem claims_eq : raw.claims = Leaf30.claims := rfl

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
    · exact Proof30.packedNC0
    · exact Proof30.packedNC1
    · exact Proof30.packedNC2
    · exact Proof30.packedNC3
    · exact Proof30.packedNC4
    · exact Proof30.packedNC5
  · intro k hk
    interval_cases k <;> (simp only [RawReceipt.cost,RawReceipt.a,raw_b]; rfl)
  · simp only [RawReceipt.cost,RawReceipt.a,raw_b]
    rfl
  · intro k hk
    rw [raw_b,claims_eq]
    interval_cases k
    · have hh := Proof30.endpointsNC0
      change Leaf30.endpoints0 = true at hh
      simp only [Leaf30.endpoints0, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof30.endpointsNC1
      change Leaf30.endpoints1 = true at hh
      simp only [Leaf30.endpoints1, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof30.endpointsNC2
      change Leaf30.endpoints2 = true at hh
      simp only [Leaf30.endpoints2, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof30.endpointsNC3
      change Leaf30.endpoints3 = true at hh
      simp only [Leaf30.endpoints3, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof30.endpointsNC4
      change Leaf30.endpoints4 = true at hh
      simp only [Leaf30.endpoints4, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof30.endpointsNC5
      change Leaf30.endpoints5 = true at hh
      simp only [Leaf30.endpoints5, List.take_take, Nat.min_self] at hh
      exact hh
  · have hh := Proof30.marginNC
    unfold Leaf30.marginCheck at hh
    have hn := of_decide_eq_true hh
    rw [slice_head] at hn
    rw [claims_eq]
    exact hn

#print axioms valid
end Instance30
