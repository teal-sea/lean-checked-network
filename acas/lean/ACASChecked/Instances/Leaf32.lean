import ACASChecked.RawLeafSound
import ACASChecked.Common
import ACASChecked.N32.AcceptNC
noncomputable section
namespace Instance32
open CertSound RouteA RouteNC SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def raw : RawReceipt where
  w := ACASCommon.weights
  b := ACASCommon.biases
  l k := [Leaf32.lo0,Leaf32.lo1,Leaf32.lo2,Leaf32.lo3,Leaf32.lo4,Leaf32.lo5].getD k []
  u k := [Leaf32.hi0,Leaf32.hi1,Leaf32.hi2,Leaf32.hi3,Leaf32.hi4,Leaf32.hi5].getD k []
  v k := [Leaf32.v0,Leaf32.v1,Leaf32.v2,Leaf32.v3,Leaf32.v4,Leaf32.v5].getD k []
  c k := [Leaf32.c0,Leaf32.c1,Leaf32.c2,Leaf32.c3,Leaf32.c4,Leaf32.c5].getD k []
  s k := [Leaf32.s0,Leaf32.s1,Leaf32.s2,Leaf32.s3,Leaf32.s4,Leaf32.s5].getD k []
  afinal := Leaf32.afinal
  boxl := Leaf32.boxl
  boxu := Leaf32.boxu

theorem biases_eq : [Leaf32.b0,Leaf32.b1,Leaf32.b2,Leaf32.b3,Leaf32.b4,Leaf32.b5,Leaf32.b6] = [Leaf8.b0,Leaf8.b1,Leaf8.b2,Leaf8.b3,Leaf8.b4,Leaf8.b5,Leaf8.b6] := by decide +kernel

theorem raw_b : raw.b = fun k => [Leaf32.b0,Leaf32.b1,Leaf32.b2,Leaf32.b3,Leaf32.b4,Leaf32.b5,Leaf32.b6].getD k [] := by
  funext k
  change [Leaf8.b0,Leaf8.b1,Leaf8.b2,Leaf8.b3,Leaf8.b4,Leaf8.b5,Leaf8.b6].getD k [] = [Leaf32.b0,Leaf32.b1,Leaf32.b2,Leaf32.b3,Leaf32.b4,Leaf32.b5,Leaf32.b6].getD k []
  rw [biases_eq]

theorem claims_eq : raw.claims = Leaf32.claims := rfl

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
    · exact Proof32.packedNC0
    · exact Proof32.packedNC1
    · exact Proof32.packedNC2
    · exact Proof32.packedNC3
    · exact Proof32.packedNC4
    · exact Proof32.packedNC5
  · intro k hk
    interval_cases k <;> (simp only [RawReceipt.cost,RawReceipt.a,raw_b]; rfl)
  · simp only [RawReceipt.cost,RawReceipt.a,raw_b]
    rfl
  · intro k hk
    rw [raw_b,claims_eq]
    interval_cases k
    · have hh := Proof32.endpointsNC0
      change Leaf32.endpoints0 = true at hh
      simp only [Leaf32.endpoints0, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof32.endpointsNC1
      change Leaf32.endpoints1 = true at hh
      simp only [Leaf32.endpoints1, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof32.endpointsNC2
      change Leaf32.endpoints2 = true at hh
      simp only [Leaf32.endpoints2, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof32.endpointsNC3
      change Leaf32.endpoints3 = true at hh
      simp only [Leaf32.endpoints3, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof32.endpointsNC4
      change Leaf32.endpoints4 = true at hh
      simp only [Leaf32.endpoints4, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof32.endpointsNC5
      change Leaf32.endpoints5 = true at hh
      simp only [Leaf32.endpoints5, List.take_take, Nat.min_self] at hh
      exact hh
  · have hh := Proof32.marginNC
    unfold Leaf32.marginCheck at hh
    have hn := of_decide_eq_true hh
    rw [slice_head] at hn
    rw [claims_eq]
    exact hn

#print axioms valid
end Instance32
