import ACASChecked.RawLeafSound
import ACASChecked.Common
import ACASChecked.N46.AcceptNC
noncomputable section
namespace Instance46
open CertSound RouteA RouteNC SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def raw : RawReceipt where
  w := ACASCommon.weights
  b := ACASCommon.biases
  l k := [Leaf46.lo0,Leaf46.lo1,Leaf46.lo2,Leaf46.lo3,Leaf46.lo4,Leaf46.lo5].getD k []
  u k := [Leaf46.hi0,Leaf46.hi1,Leaf46.hi2,Leaf46.hi3,Leaf46.hi4,Leaf46.hi5].getD k []
  v k := [Leaf46.v0,Leaf46.v1,Leaf46.v2,Leaf46.v3,Leaf46.v4,Leaf46.v5].getD k []
  c k := [Leaf46.c0,Leaf46.c1,Leaf46.c2,Leaf46.c3,Leaf46.c4,Leaf46.c5].getD k []
  s k := [Leaf46.s0,Leaf46.s1,Leaf46.s2,Leaf46.s3,Leaf46.s4,Leaf46.s5].getD k []
  afinal := Leaf46.afinal
  boxl := Leaf46.boxl
  boxu := Leaf46.boxu

theorem biases_eq : [Leaf46.b0,Leaf46.b1,Leaf46.b2,Leaf46.b3,Leaf46.b4,Leaf46.b5,Leaf46.b6] = [Leaf8.b0,Leaf8.b1,Leaf8.b2,Leaf8.b3,Leaf8.b4,Leaf8.b5,Leaf8.b6] := by decide +kernel

theorem raw_b : raw.b = fun k => [Leaf46.b0,Leaf46.b1,Leaf46.b2,Leaf46.b3,Leaf46.b4,Leaf46.b5,Leaf46.b6].getD k [] := by
  funext k
  change [Leaf8.b0,Leaf8.b1,Leaf8.b2,Leaf8.b3,Leaf8.b4,Leaf8.b5,Leaf8.b6].getD k [] = [Leaf46.b0,Leaf46.b1,Leaf46.b2,Leaf46.b3,Leaf46.b4,Leaf46.b5,Leaf46.b6].getD k []
  rw [biases_eq]

theorem claims_eq : raw.claims = Leaf46.claims := rfl

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
    · exact Proof46.packedNC0
    · exact Proof46.packedNC1
    · exact Proof46.packedNC2
    · exact Proof46.packedNC3
    · exact Proof46.packedNC4
    · exact Proof46.packedNC5
  · intro k hk
    interval_cases k <;> (simp only [RawReceipt.cost,RawReceipt.a,raw_b]; rfl)
  · simp only [RawReceipt.cost,RawReceipt.a,raw_b]
    rfl
  · intro k hk
    rw [raw_b,claims_eq]
    interval_cases k
    · have hh := Proof46.endpointsNC0
      change Leaf46.endpoints0 = true at hh
      simp only [Leaf46.endpoints0, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof46.endpointsNC1
      change Leaf46.endpoints1 = true at hh
      simp only [Leaf46.endpoints1, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof46.endpointsNC2
      change Leaf46.endpoints2 = true at hh
      simp only [Leaf46.endpoints2, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof46.endpointsNC3
      change Leaf46.endpoints3 = true at hh
      simp only [Leaf46.endpoints3, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof46.endpointsNC4
      change Leaf46.endpoints4 = true at hh
      simp only [Leaf46.endpoints4, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof46.endpointsNC5
      change Leaf46.endpoints5 = true at hh
      simp only [Leaf46.endpoints5, List.take_take, Nat.min_self] at hh
      exact hh
  · have hh := Proof46.marginNC
    unfold Leaf46.marginCheck at hh
    have hn := of_decide_eq_true hh
    rw [slice_head] at hn
    rw [claims_eq]
    exact hn

#print axioms valid
end Instance46
