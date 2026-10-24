import ACASChecked.RawLeafSound
import ACASChecked.Common
import ACASChecked.N57.AcceptNC
noncomputable section
namespace Instance57
open CertSound RouteA RouteNC SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def raw : RawReceipt where
  w := ACASCommon.weights
  b := ACASCommon.biases
  l k := [Leaf57.lo0,Leaf57.lo1,Leaf57.lo2,Leaf57.lo3,Leaf57.lo4,Leaf57.lo5].getD k []
  u k := [Leaf57.hi0,Leaf57.hi1,Leaf57.hi2,Leaf57.hi3,Leaf57.hi4,Leaf57.hi5].getD k []
  v k := [Leaf57.v0,Leaf57.v1,Leaf57.v2,Leaf57.v3,Leaf57.v4,Leaf57.v5].getD k []
  c k := [Leaf57.c0,Leaf57.c1,Leaf57.c2,Leaf57.c3,Leaf57.c4,Leaf57.c5].getD k []
  s k := [Leaf57.s0,Leaf57.s1,Leaf57.s2,Leaf57.s3,Leaf57.s4,Leaf57.s5].getD k []
  afinal := Leaf57.afinal
  boxl := Leaf57.boxl
  boxu := Leaf57.boxu

theorem biases_eq : [Leaf57.b0,Leaf57.b1,Leaf57.b2,Leaf57.b3,Leaf57.b4,Leaf57.b5,Leaf57.b6] = [Leaf8.b0,Leaf8.b1,Leaf8.b2,Leaf8.b3,Leaf8.b4,Leaf8.b5,Leaf8.b6] := by decide +kernel

theorem raw_b : raw.b = fun k => [Leaf57.b0,Leaf57.b1,Leaf57.b2,Leaf57.b3,Leaf57.b4,Leaf57.b5,Leaf57.b6].getD k [] := by
  funext k
  change [Leaf8.b0,Leaf8.b1,Leaf8.b2,Leaf8.b3,Leaf8.b4,Leaf8.b5,Leaf8.b6].getD k [] = [Leaf57.b0,Leaf57.b1,Leaf57.b2,Leaf57.b3,Leaf57.b4,Leaf57.b5,Leaf57.b6].getD k []
  rw [biases_eq]

theorem claims_eq : raw.claims = Leaf57.claims := rfl

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
    · exact Proof57.packedNC0
    · exact Proof57.packedNC1
    · exact Proof57.packedNC2
    · exact Proof57.packedNC3
    · exact Proof57.packedNC4
    · exact Proof57.packedNC5
  · intro k hk
    interval_cases k <;> (simp only [RawReceipt.cost,RawReceipt.a,raw_b]; rfl)
  · simp only [RawReceipt.cost,RawReceipt.a,raw_b]
    rfl
  · intro k hk
    rw [raw_b,claims_eq]
    interval_cases k
    · have hh := Proof57.endpointsNC0
      change Leaf57.endpoints0 = true at hh
      simp only [Leaf57.endpoints0, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof57.endpointsNC1
      change Leaf57.endpoints1 = true at hh
      simp only [Leaf57.endpoints1, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof57.endpointsNC2
      change Leaf57.endpoints2 = true at hh
      simp only [Leaf57.endpoints2, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof57.endpointsNC3
      change Leaf57.endpoints3 = true at hh
      simp only [Leaf57.endpoints3, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof57.endpointsNC4
      change Leaf57.endpoints4 = true at hh
      simp only [Leaf57.endpoints4, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof57.endpointsNC5
      change Leaf57.endpoints5 = true at hh
      simp only [Leaf57.endpoints5, List.take_take, Nat.min_self] at hh
      exact hh
  · have hh := Proof57.marginNC
    unfold Leaf57.marginCheck at hh
    have hn := of_decide_eq_true hh
    rw [slice_head] at hn
    rw [claims_eq]
    exact hn

#print axioms valid
end Instance57
