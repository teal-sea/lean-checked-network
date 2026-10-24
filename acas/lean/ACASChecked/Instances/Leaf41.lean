import ACASChecked.RawLeafSound
import ACASChecked.Common
import ACASChecked.N41.AcceptNC
noncomputable section
namespace Instance41
open CertSound RouteA RouteNC SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def raw : RawReceipt where
  w := ACASCommon.weights
  b := ACASCommon.biases
  l k := [Leaf41.lo0,Leaf41.lo1,Leaf41.lo2,Leaf41.lo3,Leaf41.lo4,Leaf41.lo5].getD k []
  u k := [Leaf41.hi0,Leaf41.hi1,Leaf41.hi2,Leaf41.hi3,Leaf41.hi4,Leaf41.hi5].getD k []
  v k := [Leaf41.v0,Leaf41.v1,Leaf41.v2,Leaf41.v3,Leaf41.v4,Leaf41.v5].getD k []
  c k := [Leaf41.c0,Leaf41.c1,Leaf41.c2,Leaf41.c3,Leaf41.c4,Leaf41.c5].getD k []
  s k := [Leaf41.s0,Leaf41.s1,Leaf41.s2,Leaf41.s3,Leaf41.s4,Leaf41.s5].getD k []
  afinal := Leaf41.afinal
  boxl := Leaf41.boxl
  boxu := Leaf41.boxu

theorem biases_eq : [Leaf41.b0,Leaf41.b1,Leaf41.b2,Leaf41.b3,Leaf41.b4,Leaf41.b5,Leaf41.b6] = [Leaf8.b0,Leaf8.b1,Leaf8.b2,Leaf8.b3,Leaf8.b4,Leaf8.b5,Leaf8.b6] := by decide +kernel

theorem raw_b : raw.b = fun k => [Leaf41.b0,Leaf41.b1,Leaf41.b2,Leaf41.b3,Leaf41.b4,Leaf41.b5,Leaf41.b6].getD k [] := by
  funext k
  change [Leaf8.b0,Leaf8.b1,Leaf8.b2,Leaf8.b3,Leaf8.b4,Leaf8.b5,Leaf8.b6].getD k [] = [Leaf41.b0,Leaf41.b1,Leaf41.b2,Leaf41.b3,Leaf41.b4,Leaf41.b5,Leaf41.b6].getD k []
  rw [biases_eq]

theorem claims_eq : raw.claims = Leaf41.claims := rfl

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
    · exact Proof41.packedNC0
    · exact Proof41.packedNC1
    · exact Proof41.packedNC2
    · exact Proof41.packedNC3
    · exact Proof41.packedNC4
    · exact Proof41.packedNC5
  · intro k hk
    interval_cases k <;> (simp only [RawReceipt.cost,RawReceipt.a,raw_b]; rfl)
  · simp only [RawReceipt.cost,RawReceipt.a,raw_b]
    rfl
  · intro k hk
    rw [raw_b,claims_eq]
    interval_cases k
    · have hh := Proof41.endpointsNC0
      change Leaf41.endpoints0 = true at hh
      simp only [Leaf41.endpoints0, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof41.endpointsNC1
      change Leaf41.endpoints1 = true at hh
      simp only [Leaf41.endpoints1, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof41.endpointsNC2
      change Leaf41.endpoints2 = true at hh
      simp only [Leaf41.endpoints2, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof41.endpointsNC3
      change Leaf41.endpoints3 = true at hh
      simp only [Leaf41.endpoints3, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof41.endpointsNC4
      change Leaf41.endpoints4 = true at hh
      simp only [Leaf41.endpoints4, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof41.endpointsNC5
      change Leaf41.endpoints5 = true at hh
      simp only [Leaf41.endpoints5, List.take_take, Nat.min_self] at hh
      exact hh
  · have hh := Proof41.marginNC
    unfold Leaf41.marginCheck at hh
    have hn := of_decide_eq_true hh
    rw [slice_head] at hn
    rw [claims_eq]
    exact hn

#print axioms valid
end Instance41
