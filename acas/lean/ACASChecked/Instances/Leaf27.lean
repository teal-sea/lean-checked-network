import ACASChecked.RawLeafSound
import ACASChecked.Common
import ACASChecked.N27.AcceptNC
noncomputable section
namespace Instance27
open CertSound RouteA RouteNC SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def raw : RawReceipt where
  w := ACASCommon.weights
  b := ACASCommon.biases
  l k := [Leaf27.lo0,Leaf27.lo1,Leaf27.lo2,Leaf27.lo3,Leaf27.lo4,Leaf27.lo5].getD k []
  u k := [Leaf27.hi0,Leaf27.hi1,Leaf27.hi2,Leaf27.hi3,Leaf27.hi4,Leaf27.hi5].getD k []
  v k := [Leaf27.v0,Leaf27.v1,Leaf27.v2,Leaf27.v3,Leaf27.v4,Leaf27.v5].getD k []
  c k := [Leaf27.c0,Leaf27.c1,Leaf27.c2,Leaf27.c3,Leaf27.c4,Leaf27.c5].getD k []
  s k := [Leaf27.s0,Leaf27.s1,Leaf27.s2,Leaf27.s3,Leaf27.s4,Leaf27.s5].getD k []
  afinal := Leaf27.afinal
  boxl := Leaf27.boxl
  boxu := Leaf27.boxu

theorem biases_eq : [Leaf27.b0,Leaf27.b1,Leaf27.b2,Leaf27.b3,Leaf27.b4,Leaf27.b5,Leaf27.b6] = [Leaf8.b0,Leaf8.b1,Leaf8.b2,Leaf8.b3,Leaf8.b4,Leaf8.b5,Leaf8.b6] := by decide +kernel

theorem raw_b : raw.b = fun k => [Leaf27.b0,Leaf27.b1,Leaf27.b2,Leaf27.b3,Leaf27.b4,Leaf27.b5,Leaf27.b6].getD k [] := by
  funext k
  change [Leaf8.b0,Leaf8.b1,Leaf8.b2,Leaf8.b3,Leaf8.b4,Leaf8.b5,Leaf8.b6].getD k [] = [Leaf27.b0,Leaf27.b1,Leaf27.b2,Leaf27.b3,Leaf27.b4,Leaf27.b5,Leaf27.b6].getD k []
  rw [biases_eq]

theorem claims_eq : raw.claims = Leaf27.claims := rfl

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
    · exact Proof27.packedNC0
    · exact Proof27.packedNC1
    · exact Proof27.packedNC2
    · exact Proof27.packedNC3
    · exact Proof27.packedNC4
    · exact Proof27.packedNC5
  · intro k hk
    interval_cases k <;> (simp only [RawReceipt.cost,RawReceipt.a,raw_b]; rfl)
  · simp only [RawReceipt.cost,RawReceipt.a,raw_b]
    rfl
  · intro k hk
    rw [raw_b,claims_eq]
    interval_cases k
    · have hh := Proof27.endpointsNC0
      change Leaf27.endpoints0 = true at hh
      simp only [Leaf27.endpoints0, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof27.endpointsNC1
      change Leaf27.endpoints1 = true at hh
      simp only [Leaf27.endpoints1, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof27.endpointsNC2
      change Leaf27.endpoints2 = true at hh
      simp only [Leaf27.endpoints2, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof27.endpointsNC3
      change Leaf27.endpoints3 = true at hh
      simp only [Leaf27.endpoints3, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof27.endpointsNC4
      change Leaf27.endpoints4 = true at hh
      simp only [Leaf27.endpoints4, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof27.endpointsNC5
      change Leaf27.endpoints5 = true at hh
      simp only [Leaf27.endpoints5, List.take_take, Nat.min_self] at hh
      exact hh
  · have hh := Proof27.marginNC
    unfold Leaf27.marginCheck at hh
    have hn := of_decide_eq_true hh
    rw [slice_head] at hn
    rw [claims_eq]
    exact hn

#print axioms valid
end Instance27
