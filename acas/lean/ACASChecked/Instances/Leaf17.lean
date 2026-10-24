import ACASChecked.RawLeafSound
import ACASChecked.Common
import ACASChecked.N17.AcceptNC
noncomputable section
namespace Instance17
open CertSound RouteA RouteNC SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def raw : RawReceipt where
  w := ACASCommon.weights
  b := ACASCommon.biases
  l k := [Leaf17.lo0,Leaf17.lo1,Leaf17.lo2,Leaf17.lo3,Leaf17.lo4,Leaf17.lo5].getD k []
  u k := [Leaf17.hi0,Leaf17.hi1,Leaf17.hi2,Leaf17.hi3,Leaf17.hi4,Leaf17.hi5].getD k []
  v k := [Leaf17.v0,Leaf17.v1,Leaf17.v2,Leaf17.v3,Leaf17.v4,Leaf17.v5].getD k []
  c k := [Leaf17.c0,Leaf17.c1,Leaf17.c2,Leaf17.c3,Leaf17.c4,Leaf17.c5].getD k []
  s k := [Leaf17.s0,Leaf17.s1,Leaf17.s2,Leaf17.s3,Leaf17.s4,Leaf17.s5].getD k []
  afinal := Leaf17.afinal
  boxl := Leaf17.boxl
  boxu := Leaf17.boxu

theorem biases_eq : [Leaf17.b0,Leaf17.b1,Leaf17.b2,Leaf17.b3,Leaf17.b4,Leaf17.b5,Leaf17.b6] = [Leaf8.b0,Leaf8.b1,Leaf8.b2,Leaf8.b3,Leaf8.b4,Leaf8.b5,Leaf8.b6] := by decide +kernel

theorem raw_b : raw.b = fun k => [Leaf17.b0,Leaf17.b1,Leaf17.b2,Leaf17.b3,Leaf17.b4,Leaf17.b5,Leaf17.b6].getD k [] := by
  funext k
  change [Leaf8.b0,Leaf8.b1,Leaf8.b2,Leaf8.b3,Leaf8.b4,Leaf8.b5,Leaf8.b6].getD k [] = [Leaf17.b0,Leaf17.b1,Leaf17.b2,Leaf17.b3,Leaf17.b4,Leaf17.b5,Leaf17.b6].getD k []
  rw [biases_eq]

theorem claims_eq : raw.claims = Leaf17.claims := rfl

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
    · exact Proof17.packedNC0
    · exact Proof17.packedNC1
    · exact Proof17.packedNC2
    · exact Proof17.packedNC3
    · exact Proof17.packedNC4
    · exact Proof17.packedNC5
  · intro k hk
    interval_cases k <;> (simp only [RawReceipt.cost,RawReceipt.a,raw_b]; rfl)
  · simp only [RawReceipt.cost,RawReceipt.a,raw_b]
    rfl
  · intro k hk
    rw [raw_b,claims_eq]
    interval_cases k
    · have hh := Proof17.endpointsNC0
      change Leaf17.endpoints0 = true at hh
      simp only [Leaf17.endpoints0, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof17.endpointsNC1
      change Leaf17.endpoints1 = true at hh
      simp only [Leaf17.endpoints1, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof17.endpointsNC2
      change Leaf17.endpoints2 = true at hh
      simp only [Leaf17.endpoints2, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof17.endpointsNC3
      change Leaf17.endpoints3 = true at hh
      simp only [Leaf17.endpoints3, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof17.endpointsNC4
      change Leaf17.endpoints4 = true at hh
      simp only [Leaf17.endpoints4, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof17.endpointsNC5
      change Leaf17.endpoints5 = true at hh
      simp only [Leaf17.endpoints5, List.take_take, Nat.min_self] at hh
      exact hh
  · have hh := Proof17.marginNC
    unfold Leaf17.marginCheck at hh
    have hn := of_decide_eq_true hh
    rw [slice_head] at hn
    rw [claims_eq]
    exact hn

#print axioms valid
end Instance17
