import ACASChecked.RawLeafSound
import ACASChecked.Common
import ACASChecked.N39.AcceptNC
noncomputable section
namespace Instance39
open CertSound RouteA RouteNC SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def raw : RawReceipt where
  w := ACASCommon.weights
  b := ACASCommon.biases
  l k := [Leaf39.lo0,Leaf39.lo1,Leaf39.lo2,Leaf39.lo3,Leaf39.lo4,Leaf39.lo5].getD k []
  u k := [Leaf39.hi0,Leaf39.hi1,Leaf39.hi2,Leaf39.hi3,Leaf39.hi4,Leaf39.hi5].getD k []
  v k := [Leaf39.v0,Leaf39.v1,Leaf39.v2,Leaf39.v3,Leaf39.v4,Leaf39.v5].getD k []
  c k := [Leaf39.c0,Leaf39.c1,Leaf39.c2,Leaf39.c3,Leaf39.c4,Leaf39.c5].getD k []
  s k := [Leaf39.s0,Leaf39.s1,Leaf39.s2,Leaf39.s3,Leaf39.s4,Leaf39.s5].getD k []
  afinal := Leaf39.afinal
  boxl := Leaf39.boxl
  boxu := Leaf39.boxu

theorem biases_eq : [Leaf39.b0,Leaf39.b1,Leaf39.b2,Leaf39.b3,Leaf39.b4,Leaf39.b5,Leaf39.b6] = [Leaf8.b0,Leaf8.b1,Leaf8.b2,Leaf8.b3,Leaf8.b4,Leaf8.b5,Leaf8.b6] := by decide +kernel

theorem raw_b : raw.b = fun k => [Leaf39.b0,Leaf39.b1,Leaf39.b2,Leaf39.b3,Leaf39.b4,Leaf39.b5,Leaf39.b6].getD k [] := by
  funext k
  change [Leaf8.b0,Leaf8.b1,Leaf8.b2,Leaf8.b3,Leaf8.b4,Leaf8.b5,Leaf8.b6].getD k [] = [Leaf39.b0,Leaf39.b1,Leaf39.b2,Leaf39.b3,Leaf39.b4,Leaf39.b5,Leaf39.b6].getD k []
  rw [biases_eq]

theorem claims_eq : raw.claims = Leaf39.claims := rfl

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
    · exact Proof39.packedNC0
    · exact Proof39.packedNC1
    · exact Proof39.packedNC2
    · exact Proof39.packedNC3
    · exact Proof39.packedNC4
    · exact Proof39.packedNC5
  · intro k hk
    interval_cases k <;> (simp only [RawReceipt.cost,RawReceipt.a,raw_b]; rfl)
  · simp only [RawReceipt.cost,RawReceipt.a,raw_b]
    rfl
  · intro k hk
    rw [raw_b,claims_eq]
    interval_cases k
    · have hh := Proof39.endpointsNC0
      change Leaf39.endpoints0 = true at hh
      simp only [Leaf39.endpoints0, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof39.endpointsNC1
      change Leaf39.endpoints1 = true at hh
      simp only [Leaf39.endpoints1, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof39.endpointsNC2
      change Leaf39.endpoints2 = true at hh
      simp only [Leaf39.endpoints2, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof39.endpointsNC3
      change Leaf39.endpoints3 = true at hh
      simp only [Leaf39.endpoints3, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof39.endpointsNC4
      change Leaf39.endpoints4 = true at hh
      simp only [Leaf39.endpoints4, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof39.endpointsNC5
      change Leaf39.endpoints5 = true at hh
      simp only [Leaf39.endpoints5, List.take_take, Nat.min_self] at hh
      exact hh
  · have hh := Proof39.marginNC
    unfold Leaf39.marginCheck at hh
    have hn := of_decide_eq_true hh
    rw [slice_head] at hn
    rw [claims_eq]
    exact hn

#print axioms valid
end Instance39
