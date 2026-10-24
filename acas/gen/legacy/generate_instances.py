from pathlib import Path
import json
ids=json.load(open('../route-a-all/leaves.json'))
Path('Instances').mkdir(exist_ok=True)
for node in ids:
 L=f'Leaf{node}'
 bs='['+','.join(f'{L}.b{k}' for k in range(7))+']'
 b8='['+','.join(f'Leaf8.b{k}' for k in range(7))+']'
 out=f'''import RawLeafSound
import Common
import N{node}.AcceptNC
noncomputable section
namespace Instance{node}
open CertSound RouteA RouteNC SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def raw : RawReceipt where
  w := ACASCommon.weights
  b := ACASCommon.biases
'''
 for f,stem in [('l','lo'),('u','hi'),('v','v'),('c','c'),('s','s')]:
  out+=f'  {f} k := ['+','.join(f'{L}.{stem}{k}' for k in range(6))+'].getD k []\n'
 out+=f'''  afinal := {L}.afinal
  boxl := {L}.boxl
  boxu := {L}.boxu

theorem biases_eq : {bs} = {b8} := by decide +kernel

theorem raw_b : raw.b = fun k => {bs}.getD k [] := by
  funext k
  change {b8}.getD k [] = {bs}.getD k []
  rw [biases_eq]

theorem claims_eq : raw.claims = {L}.claims := rfl

theorem valid : raw.Valid := by
  constructor
'''
 # first 10 shapes numeric only
 for idx in range(6):
  out+='  · intro k hk\n    interval_cases k <;> decide +kernel\n'
 out+='  · decide +kernel\n  · decide +kernel\n  · decide +kernel\n  · decide +kernel\n  · decide +kernel\n'
 # blocks
 out+='  · intro k hk\n    interval_cases k\n'
 for k in range(6):out+=f'    · exact Proof{node}.packedNC{k}\n'
 out+='''  · intro k hk
    interval_cases k <;> (simp only [RawReceipt.cost,RawReceipt.a,raw_b]; rfl)
  · simp only [RawReceipt.cost,RawReceipt.a,raw_b]
    rfl
  · intro k hk
    rw [raw_b,claims_eq]
    interval_cases k
'''
 for k in range(6):
  # native original endpointk may double take100 first2
  out+=f'''    · have hh := Proof{node}.endpointsNC{k}
      change {L}.endpoints{k} = true at hh
      simp only [{L}.endpoints{k}, List.take_take, Nat.min_self] at hh
      exact hh
'''
 out+=f'''  · have hh := Proof{node}.marginNC
    unfold {L}.marginCheck at hh
    have hn := of_decide_eq_true hh
    rw [slice_head] at hn
    rw [claims_eq]
    exact hn

#print axioms valid
end Instance{node}
'''
 Path(f'Instances/Leaf{node}.lean').write_text(out)
