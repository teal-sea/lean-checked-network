import ACASChecked.RawLeafSound
import ACASChecked.Common
import ACASChecked.N56.AcceptNC
noncomputable section
namespace Instance56
open CertSound RouteA RouteNC SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def raw : RawReceipt where
  w := ACASCommon.weights
  b := ACASCommon.biases
  l k := [Leaf56.lo0,Leaf56.lo1,Leaf56.lo2,Leaf56.lo3,Leaf56.lo4,Leaf56.lo5].getD k []
  u k := [Leaf56.hi0,Leaf56.hi1,Leaf56.hi2,Leaf56.hi3,Leaf56.hi4,Leaf56.hi5].getD k []
  v k := [Leaf56.v0,Leaf56.v1,Leaf56.v2,Leaf56.v3,Leaf56.v4,Leaf56.v5].getD k []
  c k := [Leaf56.c0,Leaf56.c1,Leaf56.c2,Leaf56.c3,Leaf56.c4,Leaf56.c5].getD k []
  s k := [Leaf56.s0,Leaf56.s1,Leaf56.s2,Leaf56.s3,Leaf56.s4,Leaf56.s5].getD k []
  afinal := Leaf56.afinal
  boxl := Leaf56.boxl
  boxu := Leaf56.boxu

theorem biases_eq : [Leaf56.b0,Leaf56.b1,Leaf56.b2,Leaf56.b3,Leaf56.b4,Leaf56.b5,Leaf56.b6] = [Leaf8.b0,Leaf8.b1,Leaf8.b2,Leaf8.b3,Leaf8.b4,Leaf8.b5,Leaf8.b6] := by decide +kernel

theorem raw_b : raw.b = fun k => [Leaf56.b0,Leaf56.b1,Leaf56.b2,Leaf56.b3,Leaf56.b4,Leaf56.b5,Leaf56.b6].getD k [] := by
  funext k
  change [Leaf8.b0,Leaf8.b1,Leaf8.b2,Leaf8.b3,Leaf8.b4,Leaf8.b5,Leaf8.b6].getD k [] = [Leaf56.b0,Leaf56.b1,Leaf56.b2,Leaf56.b3,Leaf56.b4,Leaf56.b5,Leaf56.b6].getD k []
  rw [biases_eq]

theorem claims_eq : raw.claims = Leaf56.claims := rfl

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
    · exact Proof56.packedNC0
    · exact Proof56.packedNC1
    · exact Proof56.packedNC2
    · exact Proof56.packedNC3
    · exact Proof56.packedNC4
    · exact Proof56.packedNC5
  · intro k hk
    interval_cases k <;> (simp only [RawReceipt.cost,RawReceipt.a,raw_b]; rfl)
  · simp only [RawReceipt.cost,RawReceipt.a,raw_b]
    rfl
  · intro k hk
    rw [raw_b,claims_eq]
    interval_cases k
    · have hh := Proof56.endpointsNC0
      change Leaf56.endpoints0 = true at hh
      simp only [Leaf56.endpoints0, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof56.endpointsNC1
      change Leaf56.endpoints1 = true at hh
      simp only [Leaf56.endpoints1, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof56.endpointsNC2
      change Leaf56.endpoints2 = true at hh
      simp only [Leaf56.endpoints2, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof56.endpointsNC3
      change Leaf56.endpoints3 = true at hh
      simp only [Leaf56.endpoints3, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof56.endpointsNC4
      change Leaf56.endpoints4 = true at hh
      simp only [Leaf56.endpoints4, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof56.endpointsNC5
      change Leaf56.endpoints5 = true at hh
      simp only [Leaf56.endpoints5, List.take_take, Nat.min_self] at hh
      exact hh
  · have hh := Proof56.marginNC
    unfold Leaf56.marginCheck at hh
    have hn := of_decide_eq_true hh
    rw [slice_head] at hn
    rw [claims_eq]
    exact hn

#print axioms valid
end Instance56
