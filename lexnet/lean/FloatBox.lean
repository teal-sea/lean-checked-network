/- Optional float64-range certificate, part 2: interval propagation from three input boxes. -/
import lean.FloatTables
namespace Lexnet
open Cell
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def bits13 : List Iv := (List.range 13).map (fun _ => ((0 : Int), (1 : Int)))
def boxCommon : List Iv := bits13 ++ [((0 : Int), (63 : Int))] ++ bits13
/-- W = 1, word shorter than 8 bytes so far (counter d >= 8): h1 below 64^7 = 2^42. -/
def boxA : List Iv := boxCommon ++ [(1, 1), (0, 1), (8, 14), (0, 2 ^ 42 - 1), (0, 2 ^ 36 - 1)]
/-- W = 1, counter below 8. -/
def boxB : List Iv := boxCommon ++ [(1, 1), (0, 1), (0, 7), (0, 2 ^ 48 - 1), (0, 2 ^ 36 - 1)]
/-- W = 0. -/
def boxC : List Iv := boxCommon ++ [(0, 0), (0, 1), (0, 14), (0, 2 ^ 48 - 1), (0, 2 ^ 36 - 1)]
def boxBwd : List Iv :=
  (List.range 15).map (fun _ => ((0 : Int), (1 : Int))) ++ (List.range 7).map (fun _ => ((0 : Int), (1 : Int)))

def fwdMax (b : List Iv) : Int := (cellIv fwdCell b).2
def bwdMax : Int := (cellIv (bwdCell ++ [⟨headRows, []⟩]) boxBwd).2
end Lexnet
namespace Lexnet
#eval (fwdMax boxA, fwdMax boxB, fwdMax boxC, bwdMax)
theorem cert_fwd : [fwdMax boxA, fwdMax boxB, fwdMax boxC].all (fun m => decide (m ≤ 2 ^ 53)) = true := by
  decide +kernel
theorem cert_not_vacuous : decide (fwdMax boxA ≤ 2 ^ 50) = false := by decide +kernel
theorem cert_bwd : decide (bwdMax ≤ 2 ^ 53) = true := by decide +kernel
end Lexnet
