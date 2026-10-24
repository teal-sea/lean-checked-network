import ACASChecked.RawLeafSound
import ACASChecked.Common
import ACASChecked.N40.AcceptNC
noncomputable section
namespace Instance40
open CertSound RouteA RouteNC SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def raw : RawReceipt where
  w := ACASCommon.weights
  b := ACASCommon.biases
  l k := [Leaf40.lo0,Leaf40.lo1,Leaf40.lo2,Leaf40.lo3,Leaf40.lo4,Leaf40.lo5].getD k []
  u k := [Leaf40.hi0,Leaf40.hi1,Leaf40.hi2,Leaf40.hi3,Leaf40.hi4,Leaf40.hi5].getD k []
  v k := [Leaf40.v0,Leaf40.v1,Leaf40.v2,Leaf40.v3,Leaf40.v4,Leaf40.v5].getD k []
  c k := [Leaf40.c0,Leaf40.c1,Leaf40.c2,Leaf40.c3,Leaf40.c4,Leaf40.c5].getD k []
  s k := [Leaf40.s0,Leaf40.s1,Leaf40.s2,Leaf40.s3,Leaf40.s4,Leaf40.s5].getD k []
  afinal := Leaf40.afinal
  boxl := Leaf40.boxl
  boxu := Leaf40.boxu

theorem biases_eq : [Leaf40.b0,Leaf40.b1,Leaf40.b2,Leaf40.b3,Leaf40.b4,Leaf40.b5,Leaf40.b6] = [Leaf8.b0,Leaf8.b1,Leaf8.b2,Leaf8.b3,Leaf8.b4,Leaf8.b5,Leaf8.b6] := by decide +kernel

theorem raw_b : raw.b = fun k => [Leaf40.b0,Leaf40.b1,Leaf40.b2,Leaf40.b3,Leaf40.b4,Leaf40.b5,Leaf40.b6].getD k [] := by
  funext k
  change [Leaf8.b0,Leaf8.b1,Leaf8.b2,Leaf8.b3,Leaf8.b4,Leaf8.b5,Leaf8.b6].getD k [] = [Leaf40.b0,Leaf40.b1,Leaf40.b2,Leaf40.b3,Leaf40.b4,Leaf40.b5,Leaf40.b6].getD k []
  rw [biases_eq]

theorem claims_eq : raw.claims = Leaf40.claims := rfl

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
    · exact Proof40.packedNC0
    · exact Proof40.packedNC1
    · exact Proof40.packedNC2
    · exact Proof40.packedNC3
    · exact Proof40.packedNC4
    · exact Proof40.packedNC5
  · intro k hk
    interval_cases k <;> (simp only [RawReceipt.cost,RawReceipt.a,raw_b]; rfl)
  · simp only [RawReceipt.cost,RawReceipt.a,raw_b]
    rfl
  · intro k hk
    rw [raw_b,claims_eq]
    interval_cases k
    · have hh := Proof40.endpointsNC0
      change Leaf40.endpoints0 = true at hh
      simp only [Leaf40.endpoints0, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof40.endpointsNC1
      change Leaf40.endpoints1 = true at hh
      simp only [Leaf40.endpoints1, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof40.endpointsNC2
      change Leaf40.endpoints2 = true at hh
      simp only [Leaf40.endpoints2, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof40.endpointsNC3
      change Leaf40.endpoints3 = true at hh
      simp only [Leaf40.endpoints3, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof40.endpointsNC4
      change Leaf40.endpoints4 = true at hh
      simp only [Leaf40.endpoints4, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof40.endpointsNC5
      change Leaf40.endpoints5 = true at hh
      simp only [Leaf40.endpoints5, List.take_take, Nat.min_self] at hh
      exact hh
  · have hh := Proof40.marginNC
    unfold Leaf40.marginCheck at hh
    have hn := of_decide_eq_true hh
    rw [slice_head] at hn
    rw [claims_eq]
    exact hn

#print axioms valid
end Instance40
