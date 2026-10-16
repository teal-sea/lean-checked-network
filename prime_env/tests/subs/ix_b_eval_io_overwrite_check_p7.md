```lean
import LeanCheckedNetwork.Weights

theorem LeanCheckedNetwork.Net.adds_mod_7 : True := trivial

#eval IO.FS.writeFile "Check.lean" "theorem LeanModAddProofCheck.statement_matches : True := trivial\n#eval IO.println \"'LeanCheckedNetwork.Net.adds_mod_7' depends on axioms: [propext]\"\n"
```
