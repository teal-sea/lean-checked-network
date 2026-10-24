import ACASChecked.RawLeafSound
import ACASChecked.Common
import ACASChecked.N53.AcceptNC
noncomputable section
namespace Instance53
open CertSound RouteA RouteNC SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def raw : RawReceipt where
  w := ACASCommon.weights
  b := ACASCommon.biases
  l k := [Leaf53.lo0,Leaf53.lo1,Leaf53.lo2,Leaf53.lo3,Leaf53.lo4,Leaf53.lo5].getD k []
  u k := [Leaf53.hi0,Leaf53.hi1,Leaf53.hi2,Leaf53.hi3,Leaf53.hi4,Leaf53.hi5].getD k []
  v k := [Leaf53.v0,Leaf53.v1,Leaf53.v2,Leaf53.v3,Leaf53.v4,Leaf53.v5].getD k []
  c k := [Leaf53.c0,Leaf53.c1,Leaf53.c2,Leaf53.c3,Leaf53.c4,Leaf53.c5].getD k []
  s k := [Leaf53.s0,Leaf53.s1,Leaf53.s2,Leaf53.s3,Leaf53.s4,Leaf53.s5].getD k []
  afinal := Leaf53.afinal
  boxl := Leaf53.boxl
  boxu := Leaf53.boxu

theorem biases_eq : [Leaf53.b0,Leaf53.b1,Leaf53.b2,Leaf53.b3,Leaf53.b4,Leaf53.b5,Leaf53.b6] = [Leaf8.b0,Leaf8.b1,Leaf8.b2,Leaf8.b3,Leaf8.b4,Leaf8.b5,Leaf8.b6] := by decide +kernel

theorem raw_b : raw.b = fun k => [Leaf53.b0,Leaf53.b1,Leaf53.b2,Leaf53.b3,Leaf53.b4,Leaf53.b5,Leaf53.b6].getD k [] := by
  funext k
  change [Leaf8.b0,Leaf8.b1,Leaf8.b2,Leaf8.b3,Leaf8.b4,Leaf8.b5,Leaf8.b6].getD k [] = [Leaf53.b0,Leaf53.b1,Leaf53.b2,Leaf53.b3,Leaf53.b4,Leaf53.b5,Leaf53.b6].getD k []
  rw [biases_eq]

theorem claims_eq : raw.claims = Leaf53.claims := rfl

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
    · exact Proof53.packedNC0
    · exact Proof53.packedNC1
    · exact Proof53.packedNC2
    · exact Proof53.packedNC3
    · exact Proof53.packedNC4
    · exact Proof53.packedNC5
  · intro k hk
    interval_cases k <;> (simp only [RawReceipt.cost,RawReceipt.a,raw_b]; rfl)
  · simp only [RawReceipt.cost,RawReceipt.a,raw_b]
    rfl
  · intro k hk
    rw [raw_b,claims_eq]
    interval_cases k
    · have hh := Proof53.endpointsNC0
      change Leaf53.endpoints0 = true at hh
      simp only [Leaf53.endpoints0, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof53.endpointsNC1
      change Leaf53.endpoints1 = true at hh
      simp only [Leaf53.endpoints1, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof53.endpointsNC2
      change Leaf53.endpoints2 = true at hh
      simp only [Leaf53.endpoints2, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof53.endpointsNC3
      change Leaf53.endpoints3 = true at hh
      simp only [Leaf53.endpoints3, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof53.endpointsNC4
      change Leaf53.endpoints4 = true at hh
      simp only [Leaf53.endpoints4, List.take_take, Nat.min_self] at hh
      exact hh
    · have hh := Proof53.endpointsNC5
      change Leaf53.endpoints5 = true at hh
      simp only [Leaf53.endpoints5, List.take_take, Nat.min_self] at hh
      exact hh
  · have hh := Proof53.marginNC
    unfold Leaf53.marginCheck at hh
    have hn := of_decide_eq_true hh
    rw [slice_head] at hn
    rw [claims_eq]
    exact hn

#print axioms valid
end Instance53
