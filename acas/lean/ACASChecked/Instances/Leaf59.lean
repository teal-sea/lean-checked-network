import ACASChecked.RawLeafSound
import ACASChecked.Common
import ACASChecked.N59.AcceptNC
noncomputable section
namespace Instance59
open CertSound RouteA RouteNC SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def raw : RawReceipt where
  w := ACASCommon.weights
  b := ACASCommon.biases
  l k := [Leaf59.lo0,Leaf59.lo1,Leaf59.lo2,Leaf59.lo3,Leaf59.lo4,Leaf59.lo5].getD k []
  u k := [Leaf59.hi0,Leaf59.hi1,Leaf59.hi2,Leaf59.hi3,Leaf59.hi4,Leaf59.hi5].getD k []
  v k := [Leaf59.v0,Leaf59.v1,Leaf59.v2,Leaf59.v3,Leaf59.v4,Leaf59.v5].getD k []
  c k := [Leaf59.c0,Leaf59.c1,Leaf59.c2,Leaf59.c3,Leaf59.c4,Leaf59.c5].getD k []
  s k := [Leaf59.s0,Leaf59.s1,Leaf59.s2,Leaf59.s3,Leaf59.s4,Leaf59.s5].getD k []
  afinal := Leaf59.afinal
  boxl := Leaf59.boxl
  boxu := Leaf59.boxu

theorem biases_eq : [Leaf59.b0,Leaf59.b1,Leaf59.b2,Leaf59.b3,Leaf59.b4,Leaf59.b5,Leaf59.b6] = [Leaf8.b0,Leaf8.b1,Leaf8.b2,Leaf8.b3,Leaf8.b4,Leaf8.b5,Leaf8.b6] := by decide +kernel

theorem raw_b : raw.b = fun k => [Leaf59.b0,Leaf59.b1,Leaf59.b2,Leaf59.b3,Leaf59.b4,Leaf59.b5,Leaf59.b6].getD k [] := by
  funext k
  change [Leaf8.b0,Leaf8.b1,Leaf8.b2,Leaf8.b3,Leaf8.b4,Leaf8.b5,Leaf8.b6].getD k [] = [Leaf59.b0,Leaf59.b1,Leaf59.b2,Leaf59.b3,Leaf59.b4,Leaf59.b5,Leaf59.b6].getD k []
  rw [biases_eq]

theorem claims_eq : raw.claims = Leaf59.claims := rfl

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
    · exact Proof59.packedNC0
    · exact Proof59.packedNC1
    · exact Proof59.packedNC2
    · exact Proof59.packedNC3
    · exact Proof59.packedNC4
    · exact Proof59.packedNC5
  · intro k hk
    interval_cases k <;> (simp only [RawReceipt.cost,RawReceipt.a,raw_b]; rfl)
  · simp only [RawReceipt.cost,RawReceipt.a,raw_b]
    rfl
  · intro k hk
    rw [raw_b,claims_eq]
    interval_cases k
    · have hh := Proof59.endpointsNC0
      change Leaf59.endpoints0 = true at hh
      simp only [Leaf59.endpoints0, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof59.endpointsNC1
      change Leaf59.endpoints1 = true at hh
      simp only [Leaf59.endpoints1, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof59.endpointsNC2
      change Leaf59.endpoints2 = true at hh
      simp only [Leaf59.endpoints2, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof59.endpointsNC3
      change Leaf59.endpoints3 = true at hh
      simp only [Leaf59.endpoints3, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof59.endpointsNC4
      change Leaf59.endpoints4 = true at hh
      simp only [Leaf59.endpoints4, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof59.endpointsNC5
      change Leaf59.endpoints5 = true at hh
      simp only [Leaf59.endpoints5, List.take_take, Nat.min_self] at hh
      exact hh
  · have hh := Proof59.marginNC
    unfold Leaf59.marginCheck at hh
    have hn := of_decide_eq_true hh
    rw [slice_head] at hn
    rw [claims_eq]
    exact hn

#print axioms valid
end Instance59
