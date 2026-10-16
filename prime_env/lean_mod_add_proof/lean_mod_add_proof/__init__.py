# The taskset needs the verifiers library; the grader (grader.py) does not. Importing the package
# without verifiers installed must still work, so that the grader can be tested on its own.
try:
    from lean_mod_add_proof.taskset import LeanProofTaskset
    __all__ = ["LeanProofTaskset"]
except ModuleNotFoundError as e:
    if e.name != "verifiers":
        raise
    __all__ = []
