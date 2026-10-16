import Transformer
/-! Evaluate the Lean `expFix` at the chosen parameters on a few inputs, to compare with
`int_transformer.py`'s `expfix` (`check_expfix.py`). `#eval` runs the compiled definition; this is
a cross-check that the two definitions are the same function on these inputs, not a proof. -/
open Transformer
def xs : List ℤ := [0, -1, -2, -12345, -2147483648, -4294967296, -12884901888,
  -103079215103, -103079215104, -103079215105, -429496729600, -1234567890123]
#eval xs.map (fun x => expFix chosen x)
#eval coeffs chosen
#eval bigF chosen
