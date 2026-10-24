import ACASChecked.RawLeafSound
import ACASChecked.Common
import ACASChecked.N33.AcceptNC
noncomputable section
namespace Instance33
open CertSound RouteA RouteNC SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def raw : RawReceipt where
  w := ACASCommon.weights
  b := ACASCommon.biases
  l k := [Leaf33.lo0,Leaf33.lo1,Leaf33.lo2,Leaf33.lo3,Leaf33.lo4,Leaf33.lo5].getD k []
  u k := [Leaf33.hi0,Leaf33.hi1,Leaf33.hi2,Leaf33.hi3,Leaf33.hi4,Leaf33.hi5].getD k []
  v k := [Leaf33.v0,Leaf33.v1,Leaf33.v2,Leaf33.v3,Leaf33.v4,Leaf33.v5].getD k []
  c k := [Leaf33.c0,Leaf33.c1,Leaf33.c2,Leaf33.c3,Leaf33.c4,Leaf33.c5].getD k []
  s k := [Leaf33.s0,Leaf33.s1,Leaf33.s2,Leaf33.s3,Leaf33.s4,Leaf33.s5].getD k []
  afinal := Leaf33.afinal
  boxl := Leaf33.boxl
  boxu := Leaf33.boxu

theorem biases_eq : [Leaf33.b0,Leaf33.b1,Leaf33.b2,Leaf33.b3,Leaf33.b4,Leaf33.b5,Leaf33.b6] = [Leaf8.b0,Leaf8.b1,Leaf8.b2,Leaf8.b3,Leaf8.b4,Leaf8.b5,Leaf8.b6] := by decide +kernel

theorem raw_b : raw.b = fun k => [Leaf33.b0,Leaf33.b1,Leaf33.b2,Leaf33.b3,Leaf33.b4,Leaf33.b5,Leaf33.b6].getD k [] := by
  funext k
  change [Leaf8.b0,Leaf8.b1,Leaf8.b2,Leaf8.b3,Leaf8.b4,Leaf8.b5,Leaf8.b6].getD k [] = [Leaf33.b0,Leaf33.b1,Leaf33.b2,Leaf33.b3,Leaf33.b4,Leaf33.b5,Leaf33.b6].getD k []
  rw [biases_eq]

theorem claims_eq : raw.claims = Leaf33.claims := rfl

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
    · exact Proof33.packedNC0
    · exact Proof33.packedNC1
    · exact Proof33.packedNC2
    · exact Proof33.packedNC3
    · exact Proof33.packedNC4
    · exact Proof33.packedNC5
  · intro k hk
    interval_cases k <;> (simp only [RawReceipt.cost,RawReceipt.a,raw_b]; rfl)
  · simp only [RawReceipt.cost,RawReceipt.a,raw_b]
    rfl
  · intro k hk
    rw [raw_b,claims_eq]
    interval_cases k
    · have hh := Proof33.endpointsNC0
      change Leaf33.endpoints0 = true at hh
      simp only [Leaf33.endpoints0, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof33.endpointsNC1
      change Leaf33.endpoints1 = true at hh
      simp only [Leaf33.endpoints1, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof33.endpointsNC2
      change Leaf33.endpoints2 = true at hh
      simp only [Leaf33.endpoints2, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof33.endpointsNC3
      change Leaf33.endpoints3 = true at hh
      simp only [Leaf33.endpoints3, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof33.endpointsNC4
      change Leaf33.endpoints4 = true at hh
      simp only [Leaf33.endpoints4, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof33.endpointsNC5
      change Leaf33.endpoints5 = true at hh
      simp only [Leaf33.endpoints5, List.take_take, Nat.min_self] at hh
      exact hh
  · have hh := Proof33.marginNC
    unfold Leaf33.marginCheck at hh
    have hn := of_decide_eq_true hh
    rw [slice_head] at hn
    rw [claims_eq]
    exact hn

#print axioms valid
end Instance33
