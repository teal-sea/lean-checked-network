import ACASChecked.RawLeafSound
import ACASChecked.Common
import ACASChecked.N42.AcceptNC
noncomputable section
namespace Instance42
open CertSound RouteA RouteNC SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def raw : RawReceipt where
  w := ACASCommon.weights
  b := ACASCommon.biases
  l k := [Leaf42.lo0,Leaf42.lo1,Leaf42.lo2,Leaf42.lo3,Leaf42.lo4,Leaf42.lo5].getD k []
  u k := [Leaf42.hi0,Leaf42.hi1,Leaf42.hi2,Leaf42.hi3,Leaf42.hi4,Leaf42.hi5].getD k []
  v k := [Leaf42.v0,Leaf42.v1,Leaf42.v2,Leaf42.v3,Leaf42.v4,Leaf42.v5].getD k []
  c k := [Leaf42.c0,Leaf42.c1,Leaf42.c2,Leaf42.c3,Leaf42.c4,Leaf42.c5].getD k []
  s k := [Leaf42.s0,Leaf42.s1,Leaf42.s2,Leaf42.s3,Leaf42.s4,Leaf42.s5].getD k []
  afinal := Leaf42.afinal
  boxl := Leaf42.boxl
  boxu := Leaf42.boxu

theorem biases_eq : [Leaf42.b0,Leaf42.b1,Leaf42.b2,Leaf42.b3,Leaf42.b4,Leaf42.b5,Leaf42.b6] = [Leaf8.b0,Leaf8.b1,Leaf8.b2,Leaf8.b3,Leaf8.b4,Leaf8.b5,Leaf8.b6] := by decide +kernel

theorem raw_b : raw.b = fun k => [Leaf42.b0,Leaf42.b1,Leaf42.b2,Leaf42.b3,Leaf42.b4,Leaf42.b5,Leaf42.b6].getD k [] := by
  funext k
  change [Leaf8.b0,Leaf8.b1,Leaf8.b2,Leaf8.b3,Leaf8.b4,Leaf8.b5,Leaf8.b6].getD k [] = [Leaf42.b0,Leaf42.b1,Leaf42.b2,Leaf42.b3,Leaf42.b4,Leaf42.b5,Leaf42.b6].getD k []
  rw [biases_eq]

theorem claims_eq : raw.claims = Leaf42.claims := rfl

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
    · exact Proof42.packedNC0
    · exact Proof42.packedNC1
    · exact Proof42.packedNC2
    · exact Proof42.packedNC3
    · exact Proof42.packedNC4
    · exact Proof42.packedNC5
  · intro k hk
    interval_cases k <;> (simp only [RawReceipt.cost,RawReceipt.a,raw_b]; rfl)
  · simp only [RawReceipt.cost,RawReceipt.a,raw_b]
    rfl
  · intro k hk
    rw [raw_b,claims_eq]
    interval_cases k
    · have hh := Proof42.endpointsNC0
      change Leaf42.endpoints0 = true at hh
      simp only [Leaf42.endpoints0, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof42.endpointsNC1
      change Leaf42.endpoints1 = true at hh
      simp only [Leaf42.endpoints1, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof42.endpointsNC2
      change Leaf42.endpoints2 = true at hh
      simp only [Leaf42.endpoints2, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof42.endpointsNC3
      change Leaf42.endpoints3 = true at hh
      simp only [Leaf42.endpoints3, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof42.endpointsNC4
      change Leaf42.endpoints4 = true at hh
      simp only [Leaf42.endpoints4, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof42.endpointsNC5
      change Leaf42.endpoints5 = true at hh
      simp only [Leaf42.endpoints5, List.take_take, Nat.min_self] at hh
      exact hh
  · have hh := Proof42.marginNC
    unfold Leaf42.marginCheck at hh
    have hn := of_decide_eq_true hh
    rw [slice_head] at hn
    rw [claims_eq]
    exact hn

#print axioms valid
end Instance42
