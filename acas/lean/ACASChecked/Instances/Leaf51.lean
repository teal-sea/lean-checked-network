import ACASChecked.RawLeafSound
import ACASChecked.Common
import ACASChecked.N51.AcceptNC
noncomputable section
namespace Instance51
open CertSound RouteA RouteNC SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def raw : RawReceipt where
  w := ACASCommon.weights
  b := ACASCommon.biases
  l k := [Leaf51.lo0,Leaf51.lo1,Leaf51.lo2,Leaf51.lo3,Leaf51.lo4,Leaf51.lo5].getD k []
  u k := [Leaf51.hi0,Leaf51.hi1,Leaf51.hi2,Leaf51.hi3,Leaf51.hi4,Leaf51.hi5].getD k []
  v k := [Leaf51.v0,Leaf51.v1,Leaf51.v2,Leaf51.v3,Leaf51.v4,Leaf51.v5].getD k []
  c k := [Leaf51.c0,Leaf51.c1,Leaf51.c2,Leaf51.c3,Leaf51.c4,Leaf51.c5].getD k []
  s k := [Leaf51.s0,Leaf51.s1,Leaf51.s2,Leaf51.s3,Leaf51.s4,Leaf51.s5].getD k []
  afinal := Leaf51.afinal
  boxl := Leaf51.boxl
  boxu := Leaf51.boxu

theorem biases_eq : [Leaf51.b0,Leaf51.b1,Leaf51.b2,Leaf51.b3,Leaf51.b4,Leaf51.b5,Leaf51.b6] = [Leaf8.b0,Leaf8.b1,Leaf8.b2,Leaf8.b3,Leaf8.b4,Leaf8.b5,Leaf8.b6] := by decide +kernel

theorem raw_b : raw.b = fun k => [Leaf51.b0,Leaf51.b1,Leaf51.b2,Leaf51.b3,Leaf51.b4,Leaf51.b5,Leaf51.b6].getD k [] := by
  funext k
  change [Leaf8.b0,Leaf8.b1,Leaf8.b2,Leaf8.b3,Leaf8.b4,Leaf8.b5,Leaf8.b6].getD k [] = [Leaf51.b0,Leaf51.b1,Leaf51.b2,Leaf51.b3,Leaf51.b4,Leaf51.b5,Leaf51.b6].getD k []
  rw [biases_eq]

theorem claims_eq : raw.claims = Leaf51.claims := rfl

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
    · exact Proof51.packedNC0
    · exact Proof51.packedNC1
    · exact Proof51.packedNC2
    · exact Proof51.packedNC3
    · exact Proof51.packedNC4
    · exact Proof51.packedNC5
  · intro k hk
    interval_cases k <;> (simp only [RawReceipt.cost,RawReceipt.a,raw_b]; rfl)
  · simp only [RawReceipt.cost,RawReceipt.a,raw_b]
    rfl
  · intro k hk
    rw [raw_b,claims_eq]
    interval_cases k
    · have hh := Proof51.endpointsNC0
      change Leaf51.endpoints0 = true at hh
      simp only [Leaf51.endpoints0, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof51.endpointsNC1
      change Leaf51.endpoints1 = true at hh
      simp only [Leaf51.endpoints1, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof51.endpointsNC2
      change Leaf51.endpoints2 = true at hh
      simp only [Leaf51.endpoints2, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof51.endpointsNC3
      change Leaf51.endpoints3 = true at hh
      simp only [Leaf51.endpoints3, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof51.endpointsNC4
      change Leaf51.endpoints4 = true at hh
      simp only [Leaf51.endpoints4, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof51.endpointsNC5
      change Leaf51.endpoints5 = true at hh
      simp only [Leaf51.endpoints5, List.take_take, Nat.min_self] at hh
      exact hh
  · have hh := Proof51.marginNC
    unfold Leaf51.marginCheck at hh
    have hn := of_decide_eq_true hh
    rw [slice_head] at hn
    rw [claims_eq]
    exact hn

#print axioms valid
end Instance51
