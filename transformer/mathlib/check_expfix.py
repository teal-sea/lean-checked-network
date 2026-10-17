"""Print expfix (int_transformer.py) at the chosen parameters on the inputs of eval_check.lean.
Usage: python3 -I check_expfix.py /path/to/int_transformer.py > check_expfix.out
Compare with: lake env lean eval_check.lean > eval_check.out"""
import importlib.util
import sys

spec = importlib.util.spec_from_file_location("int_transformer", sys.argv[1])
it = importlib.util.module_from_spec(spec)
spec.loader.exec_module(it)
t, f, n, m, R = 32, 32, 16, 5, 24
xs = [0, -1, -2, -12345, -2147483648, -4294967296, -12884901888,
      -103079215103, -103079215104, -103079215105, -429496729600, -1234567890123]
params = it.expfix_params(t, f, n, m, R)
print([it.expfix(x, t, f, n, m, R, params) for x in xs])
print(params[0])
print(params[1])
print("delta_bound", it.delta_bound(f, n, m, R))
