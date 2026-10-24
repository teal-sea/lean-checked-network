import ACASChecked.RawLeafSound
import ACASChecked.Common
import ACASChecked.N31.AcceptNC
noncomputable section
namespace Instance31
open CertSound RouteA RouteNC SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def raw : RawReceipt where
  w := ACASCommon.weights
  b := ACASCommon.biases
  l k := [Leaf31.lo0,Leaf31.lo1,Leaf31.lo2,Leaf31.lo3,Leaf31.lo4,Leaf31.lo5].getD k []
  u k := [Leaf31.hi0,Leaf31.hi1,Leaf31.hi2,Leaf31.hi3,Leaf31.hi4,Leaf31.hi5].getD k []
  v k := [Leaf31.v0,Leaf31.v1,Leaf31.v2,Leaf31.v3,Leaf31.v4,Leaf31.v5].getD k []
  c k := [Leaf31.c0,Leaf31.c1,Leaf31.c2,Leaf31.c3,Leaf31.c4,Leaf31.c5].getD k []
  s k := [Leaf31.s0,Leaf31.s1,Leaf31.s2,Leaf31.s3,Leaf31.s4,Leaf31.s5].getD k []
  afinal := Leaf31.afinal
  boxl := Leaf31.boxl
  boxu := Leaf31.boxu

theorem biases_eq : [Leaf31.b0,Leaf31.b1,Leaf31.b2,Leaf31.b3,Leaf31.b4,Leaf31.b5,Leaf31.b6] = [Leaf8.b0,Leaf8.b1,Leaf8.b2,Leaf8.b3,Leaf8.b4,Leaf8.b5,Leaf8.b6] := by decide +kernel

theorem raw_b : raw.b = fun k => [Leaf31.b0,Leaf31.b1,Leaf31.b2,Leaf31.b3,Leaf31.b4,Leaf31.b5,Leaf31.b6].getD k [] := by
  funext k
  change [Leaf8.b0,Leaf8.b1,Leaf8.b2,Leaf8.b3,Leaf8.b4,Leaf8.b5,Leaf8.b6].getD k [] = [Leaf31.b0,Leaf31.b1,Leaf31.b2,Leaf31.b3,Leaf31.b4,Leaf31.b5,Leaf31.b6].getD k []
  rw [biases_eq]

theorem claims_eq : raw.claims = Leaf31.claims := rfl

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
    · exact Proof31.packedNC0
    · exact Proof31.packedNC1
    · exact Proof31.packedNC2
    · exact Proof31.packedNC3
    · exact Proof31.packedNC4
    · exact Proof31.packedNC5
  · intro k hk
    interval_cases k <;> (simp only [RawReceipt.cost,RawReceipt.a,raw_b]; rfl)
  · simp only [RawReceipt.cost,RawReceipt.a,raw_b]
    rfl
  · intro k hk
    rw [raw_b,claims_eq]
    interval_cases k
    · have hh := Proof31.endpointsNC0
      change Leaf31.endpoints0 = true at hh
      simp only [Leaf31.endpoints0, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof31.endpointsNC1
      change Leaf31.endpoints1 = true at hh
      simp only [Leaf31.endpoints1, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof31.endpointsNC2
      change Leaf31.endpoints2 = true at hh
      simp only [Leaf31.endpoints2, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof31.endpointsNC3
      change Leaf31.endpoints3 = true at hh
      simp only [Leaf31.endpoints3, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof31.endpointsNC4
      change Leaf31.endpoints4 = true at hh
      simp only [Leaf31.endpoints4, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof31.endpointsNC5
      change Leaf31.endpoints5 = true at hh
      simp only [Leaf31.endpoints5, List.take_take, Nat.min_self] at hh
      exact hh
  · have hh := Proof31.marginNC
    unfold Leaf31.marginCheck at hh
    have hn := of_decide_eq_true hh
    rw [slice_head] at hn
    rw [claims_eq]
    exact hn

#print axioms valid
end Instance31
