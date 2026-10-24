import ACASChecked.RawLeafSound
import ACASChecked.Common
import ACASChecked.N36.AcceptNC
noncomputable section
namespace Instance36
open CertSound RouteA RouteNC SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def raw : RawReceipt where
  w := ACASCommon.weights
  b := ACASCommon.biases
  l k := [Leaf36.lo0,Leaf36.lo1,Leaf36.lo2,Leaf36.lo3,Leaf36.lo4,Leaf36.lo5].getD k []
  u k := [Leaf36.hi0,Leaf36.hi1,Leaf36.hi2,Leaf36.hi3,Leaf36.hi4,Leaf36.hi5].getD k []
  v k := [Leaf36.v0,Leaf36.v1,Leaf36.v2,Leaf36.v3,Leaf36.v4,Leaf36.v5].getD k []
  c k := [Leaf36.c0,Leaf36.c1,Leaf36.c2,Leaf36.c3,Leaf36.c4,Leaf36.c5].getD k []
  s k := [Leaf36.s0,Leaf36.s1,Leaf36.s2,Leaf36.s3,Leaf36.s4,Leaf36.s5].getD k []
  afinal := Leaf36.afinal
  boxl := Leaf36.boxl
  boxu := Leaf36.boxu

theorem biases_eq : [Leaf36.b0,Leaf36.b1,Leaf36.b2,Leaf36.b3,Leaf36.b4,Leaf36.b5,Leaf36.b6] = [Leaf8.b0,Leaf8.b1,Leaf8.b2,Leaf8.b3,Leaf8.b4,Leaf8.b5,Leaf8.b6] := by decide +kernel

theorem raw_b : raw.b = fun k => [Leaf36.b0,Leaf36.b1,Leaf36.b2,Leaf36.b3,Leaf36.b4,Leaf36.b5,Leaf36.b6].getD k [] := by
  funext k
  change [Leaf8.b0,Leaf8.b1,Leaf8.b2,Leaf8.b3,Leaf8.b4,Leaf8.b5,Leaf8.b6].getD k [] = [Leaf36.b0,Leaf36.b1,Leaf36.b2,Leaf36.b3,Leaf36.b4,Leaf36.b5,Leaf36.b6].getD k []
  rw [biases_eq]

theorem claims_eq : raw.claims = Leaf36.claims := rfl

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
    · exact Proof36.packedNC0
    · exact Proof36.packedNC1
    · exact Proof36.packedNC2
    · exact Proof36.packedNC3
    · exact Proof36.packedNC4
    · exact Proof36.packedNC5
  · intro k hk
    interval_cases k <;> (simp only [RawReceipt.cost,RawReceipt.a,raw_b]; rfl)
  · simp only [RawReceipt.cost,RawReceipt.a,raw_b]
    rfl
  · intro k hk
    rw [raw_b,claims_eq]
    interval_cases k
    · have hh := Proof36.endpointsNC0
      change Leaf36.endpoints0 = true at hh
      simp only [Leaf36.endpoints0, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof36.endpointsNC1
      change Leaf36.endpoints1 = true at hh
      simp only [Leaf36.endpoints1, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof36.endpointsNC2
      change Leaf36.endpoints2 = true at hh
      simp only [Leaf36.endpoints2, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof36.endpointsNC3
      change Leaf36.endpoints3 = true at hh
      simp only [Leaf36.endpoints3, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof36.endpointsNC4
      change Leaf36.endpoints4 = true at hh
      simp only [Leaf36.endpoints4, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof36.endpointsNC5
      change Leaf36.endpoints5 = true at hh
      simp only [Leaf36.endpoints5, List.take_take, Nat.min_self] at hh
      exact hh
  · have hh := Proof36.marginNC
    unfold Leaf36.marginCheck at hh
    have hn := of_decide_eq_true hh
    rw [slice_head] at hn
    rw [claims_eq]
    exact hn

#print axioms valid
end Instance36
