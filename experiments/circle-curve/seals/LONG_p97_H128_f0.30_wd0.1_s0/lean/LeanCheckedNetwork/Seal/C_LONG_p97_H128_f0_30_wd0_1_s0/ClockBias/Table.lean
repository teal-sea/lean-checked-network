import LeanCheckedNetwork.Fast
import LeanCheckedNetwork.WrongSet
import LeanCheckedNetwork.Seal.C_LONG_p97_H128_f0_30_wd0_1_s0.ClockBias.Weights

namespace LeanCheckedNetwork.Seal.C_LONG_p97_H128_f0_30_wd0_1_s0.ClockBias

/-- Every read-out row has 131 entries, each in [-128, 127]: the condition the fast evaluator needs. -/
theorem table_ok : tableOk W2 131 = true := by decide +kernel

/-- The explicit list of wrong pairs is the row-by-row list, flattened. -/
theorem wrongPairs_eq : wrongPairs = rowsToPairs wrongRows 0 := by decide +kernel

/-- How many pairs the list holds. -/
theorem wrongPairs_length : wrongPairs.length = 10 := by decide +kernel

/-- The list is strictly increasing in lexicographic order, so no pair appears twice. -/
theorem wrongPairs_strictLex : strictLex wrongPairs = true := by decide +kernel

theorem wrongPairs_nodup : wrongPairs.Nodup := nodup_of_strictLex _ wrongPairs_strictLex

/-- Every listed pair is an input: both entries below 97. -/
theorem wrongPairs_in_range :
    wrongPairs.all (fun x => decide (x.1 < 97) && decide (x.2 < 97)) = true := by decide +kernel

end LeanCheckedNetwork.Seal.C_LONG_p97_H128_f0_30_wd0_1_s0.ClockBias
