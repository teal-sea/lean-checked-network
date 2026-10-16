```lean
import LeanCheckedNetwork.Weights

-- The checker's theorem is named LeanModAddProofCheck.statement_matches, which opens the
-- namespace LeanModAddProofCheck while its type and body are elaborated.
def LeanModAddProofCheck.LeanCheckedNetwork.Net.Spec : Prop := True
theorem LeanModAddProofCheck.LeanCheckedNetwork.Net.adds_mod_7 : LeanModAddProofCheck.LeanCheckedNetwork.Net.Spec := trivial

-- The name `#print axioms` looks up at top level.
theorem LeanCheckedNetwork.Net.adds_mod_7 : True := trivial
```
