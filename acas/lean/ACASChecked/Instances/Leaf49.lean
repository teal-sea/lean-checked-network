import ACASChecked.RawLeafSound
import ACASChecked.Common
import ACASChecked.N49.AcceptNC
noncomputable section
namespace Instance49
open CertSound RouteA RouteNC SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def raw : RawReceipt where
  w := ACASCommon.weights
  b := ACASCommon.biases
  l k := [Leaf49.lo0,Leaf49.lo1,Leaf49.lo2,Leaf49.lo3,Leaf49.lo4,Leaf49.lo5].getD k []
  u k := [Leaf49.hi0,Leaf49.hi1,Leaf49.hi2,Leaf49.hi3,Leaf49.hi4,Leaf49.hi5].getD k []
  v k := [Leaf49.v0,Leaf49.v1,Leaf49.v2,Leaf49.v3,Leaf49.v4,Leaf49.v5].getD k []
  c k := [Leaf49.c0,Leaf49.c1,Leaf49.c2,Leaf49.c3,Leaf49.c4,Leaf49.c5].getD k []
  s k := [Leaf49.s0,Leaf49.s1,Leaf49.s2,Leaf49.s3,Leaf49.s4,Leaf49.s5].getD k []
  afinal := Leaf49.afinal
  boxl := Leaf49.boxl
  boxu := Leaf49.boxu

theorem biases_eq : [Leaf49.b0,Leaf49.b1,Leaf49.b2,Leaf49.b3,Leaf49.b4,Leaf49.b5,Leaf49.b6] = [Leaf8.b0,Leaf8.b1,Leaf8.b2,Leaf8.b3,Leaf8.b4,Leaf8.b5,Leaf8.b6] := by decide +kernel

theorem raw_b : raw.b = fun k => [Leaf49.b0,Leaf49.b1,Leaf49.b2,Leaf49.b3,Leaf49.b4,Leaf49.b5,Leaf49.b6].getD k [] := by
  funext k
  change [Leaf8.b0,Leaf8.b1,Leaf8.b2,Leaf8.b3,Leaf8.b4,Leaf8.b5,Leaf8.b6].getD k [] = [Leaf49.b0,Leaf49.b1,Leaf49.b2,Leaf49.b3,Leaf49.b4,Leaf49.b5,Leaf49.b6].getD k []
  rw [biases_eq]

theorem claims_eq : raw.claims = Leaf49.claims := rfl

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
    · exact Proof49.packedNC0
    · exact Proof49.packedNC1
    · exact Proof49.packedNC2
    · exact Proof49.packedNC3
    · exact Proof49.packedNC4
    · exact Proof49.packedNC5
  · intro k hk
    interval_cases k <;> (simp only [RawReceipt.cost,RawReceipt.a,raw_b]; rfl)
  · simp only [RawReceipt.cost,RawReceipt.a,raw_b]
    rfl
  · intro k hk
    rw [raw_b,claims_eq]
    interval_cases k
    · have hh := Proof49.endpointsNC0
      change Leaf49.endpoints0 = true at hh
      simp only [Leaf49.endpoints0, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof49.endpointsNC1
      change Leaf49.endpoints1 = true at hh
      simp only [Leaf49.endpoints1, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof49.endpointsNC2
      change Leaf49.endpoints2 = true at hh
      simp only [Leaf49.endpoints2, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof49.endpointsNC3
      change Leaf49.endpoints3 = true at hh
      simp only [Leaf49.endpoints3, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof49.endpointsNC4
      change Leaf49.endpoints4 = true at hh
      simp only [Leaf49.endpoints4, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof49.endpointsNC5
      change Leaf49.endpoints5 = true at hh
      simp only [Leaf49.endpoints5, List.take_take, Nat.min_self] at hh
      exact hh
  · have hh := Proof49.marginNC
    unfold Leaf49.marginCheck at hh
    have hn := of_decide_eq_true hh
    rw [slice_head] at hn
    rw [claims_eq]
    exact hn

#print axioms valid
end Instance49
