import LeanCheckedNetwork.Fast
import LeanCheckedNetwork.WrongSet
import LeanCheckedNetwork.Seal.C_x2_ht30_H1024_s0_step2.Trained.Weights

namespace LeanCheckedNetwork.Seal.C_x2_ht30_H1024_s0_step2.Trained

/-- Every read-out row has 1024 entries, each in [-128, 127]: the condition the fast evaluator needs. -/
theorem table_ok : tableOk W2 1024 = true := by decide +kernel

/-- The explicit list of wrong pairs is the row-by-row list, flattened. -/
theorem wrongPairs_eq : wrongPairs = rowsToPairs wrongRows 0 := by decide +kernel

/-- How many pairs the list holds. -/
theorem wrongPairs_length : wrongPairs.length = 9148 := by decide +kernel

/-- The list is strictly increasing in lexicographic order, so no pair appears twice. -/
theorem wrongPairs_strictLex : strictLex wrongPairs = true := by decide +kernel

theorem wrongPairs_nodup : wrongPairs.Nodup := nodup_of_strictLex _ wrongPairs_strictLex

/-- Every listed pair is an input: both entries below 97. -/
theorem wrongPairs_in_range :
    wrongPairs.all (fun x => decide (x.1 < 97) && decide (x.2 < 97)) = true := by decide +kernel

end LeanCheckedNetwork.Seal.C_x2_ht30_H1024_s0_step2.Trained
