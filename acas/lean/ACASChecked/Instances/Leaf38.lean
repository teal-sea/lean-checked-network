import ACASChecked.RawLeafSound
import ACASChecked.Common
import ACASChecked.N38.AcceptNC
noncomputable section
namespace Instance38
open CertSound RouteA RouteNC SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def raw : RawReceipt where
  w := ACASCommon.weights
  b := ACASCommon.biases
  l k := [Leaf38.lo0,Leaf38.lo1,Leaf38.lo2,Leaf38.lo3,Leaf38.lo4,Leaf38.lo5].getD k []
  u k := [Leaf38.hi0,Leaf38.hi1,Leaf38.hi2,Leaf38.hi3,Leaf38.hi4,Leaf38.hi5].getD k []
  v k := [Leaf38.v0,Leaf38.v1,Leaf38.v2,Leaf38.v3,Leaf38.v4,Leaf38.v5].getD k []
  c k := [Leaf38.c0,Leaf38.c1,Leaf38.c2,Leaf38.c3,Leaf38.c4,Leaf38.c5].getD k []
  s k := [Leaf38.s0,Leaf38.s1,Leaf38.s2,Leaf38.s3,Leaf38.s4,Leaf38.s5].getD k []
  afinal := Leaf38.afinal
  boxl := Leaf38.boxl
  boxu := Leaf38.boxu

theorem biases_eq : [Leaf38.b0,Leaf38.b1,Leaf38.b2,Leaf38.b3,Leaf38.b4,Leaf38.b5,Leaf38.b6] = [Leaf8.b0,Leaf8.b1,Leaf8.b2,Leaf8.b3,Leaf8.b4,Leaf8.b5,Leaf8.b6] := by decide +kernel

theorem raw_b : raw.b = fun k => [Leaf38.b0,Leaf38.b1,Leaf38.b2,Leaf38.b3,Leaf38.b4,Leaf38.b5,Leaf38.b6].getD k [] := by
  funext k
  change [Leaf8.b0,Leaf8.b1,Leaf8.b2,Leaf8.b3,Leaf8.b4,Leaf8.b5,Leaf8.b6].getD k [] = [Leaf38.b0,Leaf38.b1,Leaf38.b2,Leaf38.b3,Leaf38.b4,Leaf38.b5,Leaf38.b6].getD k []
  rw [biases_eq]

theorem claims_eq : raw.claims = Leaf38.claims := rfl

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
    · exact Proof38.packedNC0
    · exact Proof38.packedNC1
    · exact Proof38.packedNC2
    · exact Proof38.packedNC3
    · exact Proof38.packedNC4
    · exact Proof38.packedNC5
  · intro k hk
    interval_cases k <;> (simp only [RawReceipt.cost,RawReceipt.a,raw_b]; rfl)
  · simp only [RawReceipt.cost,RawReceipt.a,raw_b]
    rfl
  · intro k hk
    rw [raw_b,claims_eq]
    interval_cases k
    · have hh := Proof38.endpointsNC0
      change Leaf38.endpoints0 = true at hh
      simp only [Leaf38.endpoints0, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof38.endpointsNC1
      change Leaf38.endpoints1 = true at hh
      simp only [Leaf38.endpoints1, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof38.endpointsNC2
      change Leaf38.endpoints2 = true at hh
      simp only [Leaf38.endpoints2, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof38.endpointsNC3
      change Leaf38.endpoints3 = true at hh
      simp only [Leaf38.endpoints3, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof38.endpointsNC4
      change Leaf38.endpoints4 = true at hh
      simp only [Leaf38.endpoints4, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof38.endpointsNC5
      change Leaf38.endpoints5 = true at hh
      simp only [Leaf38.endpoints5, List.take_take, Nat.min_self] at hh
      exact hh
  · have hh := Proof38.marginNC
    unfold Leaf38.marginCheck at hh
    have hn := of_decide_eq_true hh
    rw [slice_head] at hn
    rw [claims_eq]
    exact hn

#print axioms valid
end Instance38
