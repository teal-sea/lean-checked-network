/- Optional float64-range certificate, part 1: the table-driven evaluators equal the generated cells. -/
import lean.FloatTables
import lean.Fwd3
namespace Lexnet
open Cell
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def inputVec (x : Features) (h : FState) : List Int :=
  (List.range 13).map (fun i => x.flags.getD i 0) ++ [x.code] ++
  (List.range 13).map (fun i => h.auto.getD i 0) ++ [h.W, h.N, h.d, h.h1, h.h2]

/-- The table-driven evaluator computes exactly the generated forward cell. -/
theorem fwd_bridge (x : Features) (h : FState) :
    (forward x h).2 = foIdx.map (fun i => (evalCell fwdCell (inputVec x h)).getD i 0) ∧
    (forward x h).1.auto = (fsIdx.take 13).map (fun i => (evalCell fwdCell (inputVec x h)).getD i 0) ∧
    (forward x h).1.W = (evalCell fwdCell (inputVec x h)).getD (fsIdx.getD 13 0) 0 ∧
    (forward x h).1.N = (evalCell fwdCell (inputVec x h)).getD (fsIdx.getD 14 0) 0 ∧
    (forward x h).1.d = (evalCell fwdCell (inputVec x h)).getD (fsIdx.getD 15 0) 0 ∧
    (forward x h).1.h1 = (evalCell fwdCell (inputVec x h)).getD (fsIdx.getD 16 0) 0 ∧
    (forward x h).1.h2 = (evalCell fwdCell (inputVec x h)).getD (fsIdx.getD 17 0) 0 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

def bwdIn (f h : List Int) : List Int :=
  (List.range 15).map (fun i => f.getD i 0) ++ (List.range 7).map (fun i => h.getD i 0)

def headLayer : Layer := ⟨headRows, []⟩

theorem bwd_bridge (f h : List Int) :
    (backward f h).1 = bsIdx.map (fun i => (evalCell bwdCell (bwdIn f h)).getD i 0) ∧
    (backward f h).2 = headRows.map (fun r => r.raw (evalCell bwdCell (bwdIn f h))) :=
  ⟨rfl, rfl⟩
end Lexnet
