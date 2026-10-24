import ACASChecked.RawLeafSound
import ACASChecked.Common
import ACASChecked.N65.AcceptNC
noncomputable section
namespace Instance65
open CertSound RouteA RouteNC SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def raw : RawReceipt where
  w := ACASCommon.weights
  b := ACASCommon.biases
  l k := [Leaf65.lo0,Leaf65.lo1,Leaf65.lo2,Leaf65.lo3,Leaf65.lo4,Leaf65.lo5].getD k []
  u k := [Leaf65.hi0,Leaf65.hi1,Leaf65.hi2,Leaf65.hi3,Leaf65.hi4,Leaf65.hi5].getD k []
  v k := [Leaf65.v0,Leaf65.v1,Leaf65.v2,Leaf65.v3,Leaf65.v4,Leaf65.v5].getD k []
  c k := [Leaf65.c0,Leaf65.c1,Leaf65.c2,Leaf65.c3,Leaf65.c4,Leaf65.c5].getD k []
  s k := [Leaf65.s0,Leaf65.s1,Leaf65.s2,Leaf65.s3,Leaf65.s4,Leaf65.s5].getD k []
  afinal := Leaf65.afinal
  boxl := Leaf65.boxl
  boxu := Leaf65.boxu

theorem biases_eq : [Leaf65.b0,Leaf65.b1,Leaf65.b2,Leaf65.b3,Leaf65.b4,Leaf65.b5,Leaf65.b6] = [Leaf8.b0,Leaf8.b1,Leaf8.b2,Leaf8.b3,Leaf8.b4,Leaf8.b5,Leaf8.b6] := by decide +kernel

theorem raw_b : raw.b = fun k => [Leaf65.b0,Leaf65.b1,Leaf65.b2,Leaf65.b3,Leaf65.b4,Leaf65.b5,Leaf65.b6].getD k [] := by
  funext k
  change [Leaf8.b0,Leaf8.b1,Leaf8.b2,Leaf8.b3,Leaf8.b4,Leaf8.b5,Leaf8.b6].getD k [] = [Leaf65.b0,Leaf65.b1,Leaf65.b2,Leaf65.b3,Leaf65.b4,Leaf65.b5,Leaf65.b6].getD k []
  rw [biases_eq]

theorem claims_eq : raw.claims = Leaf65.claims := rfl

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
    · exact Proof65.packedNC0
    · exact Proof65.packedNC1
    · exact Proof65.packedNC2
    · exact Proof65.packedNC3
    · exact Proof65.packedNC4
    · exact Proof65.packedNC5
  · intro k hk
    interval_cases k <;> (simp only [RawReceipt.cost,RawReceipt.a,raw_b]; rfl)
  · simp only [RawReceipt.cost,RawReceipt.a,raw_b]
    rfl
  · intro k hk
    rw [raw_b,claims_eq]
    interval_cases k
    · have hh := Proof65.endpointsNC0
      change Leaf65.endpoints0 = true at hh
      simp only [Leaf65.endpoints0, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof65.endpointsNC1
      change Leaf65.endpoints1 = true at hh
      simp only [Leaf65.endpoints1, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof65.endpointsNC2
      change Leaf65.endpoints2 = true at hh
      simp only [Leaf65.endpoints2, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof65.endpointsNC3
      change Leaf65.endpoints3 = true at hh
      simp only [Leaf65.endpoints3, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof65.endpointsNC4
      change Leaf65.endpoints4 = true at hh
      simp only [Leaf65.endpoints4, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof65.endpointsNC5
      change Leaf65.endpoints5 = true at hh
      simp only [Leaf65.endpoints5, List.take_take, Nat.min_self] at hh
      exact hh
  · have hh := Proof65.marginNC
    unfold Leaf65.marginCheck at hh
    have hn := of_decide_eq_true hh
    rw [slice_head] at hn
    rw [claims_eq]
    exact hn

#print axioms valid
end Instance65
