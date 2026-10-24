# A checked certificate for ACAS Xu

Lean proves that the frozen ACAS Xu network 1_1 satisfies property 1 throughout its
normalized input box, using exact real arithmetic and the exact binary32 parameter values.

The exported theorem is:

```lean
theorem ACASChecked.acas_1_1_property1 : Frozen.ACASXu_1_1_Property1
```

Its proposition, in [Spec.lean](lean/ACASChecked/Spec.lean), is:

```lean
∀ x : Tensor ℝ [5],
  (∀ i : Fin 5, lo i ≤ x.getScalar i ∧ x.getScalar i ≤ hi i) →
  (network.model.forward x).getScalar 0 < threshold
```

The mathematical constants are exact: `lo = (3/5, -1/2, -1/2, 9/20, -1/2)`,
`hi = (679857769/1000000000, 1/2, 1/2, 1/2, -9/20)`, and
`threshold = 3991125645861615/1000000000000000`. The box is closed and the output
comparison is strict. Output index zero is `Y_0`. These are the frozen specification,
not measurements or floating approximations.

An instrumented alpha-beta-CROWN run supplies a covering input split tree. An untrusted
emitter supplies dyadic dual receipts. Lean checks their arithmetic and proves that
acceptance implies this proposition. There are **34 leaves (measured)** in the committed
certificate. [METHOD.md](METHOD.md) explains the proof; [STATUS.md](STATUS.md) records
the gates, costs and unsuccessful routes.

The ONNX-to-Lean importer is audited and hash-pinned; its correctness is not proved in Lean.
The theorem does not cover IEEE floating-point execution, other networks or properties,
or aircraft behavior. Search, conversion and the Python verifier are outside the trusted
proof boundary. Kernel checking relies on Lean and its three standard axioms;
independent nanoda replay has a separate gate in STATUS.md.

## Re-check

Use the toolchain named in `lean/lean-toolchain`. A Linux user systemd session is required
by the resource wrapper. The package manifest pins TorchLean and its transitive Mathlib.
No GPU, LibTorch installation, solver account or Gurobi solve is needed for checking.

```sh
cd acas
python3 gen/fetch_inputs.py
python3 -m venv .venv
. .venv/bin/activate
python3 -m pip install -r gen/requirements.txt
python3 -m pytest
python3 gen/regenerate.py --check
cd lean
lake update
lake exe cache get
cd ..
python3 gen/build.py --all --replay
python3 gen/audit.py
python3 gen/nanoda.py
python3 gen/independent.py
```

`build.py` is the documented source-build command. It schedules at most four Lean jobs
with two threads each, each in `certcheck.slice` with `MemoryMax=16G`, and replays new
modules under an explicit `env -i` environment. Those are resource settings. It builds
TorchLean's needed modules from the pinned sources and accepts Mathlib's official cache;
it never copies local ACAS or TorchLean objects. Logs, object hashes and resumable state
are written to ignored `work/build/`. A fresh build should start with that directory absent.

The original benchmark files are fetched by hash rather than committed: no explicit
benchmark license was found in the inspected VNN-COMP checkout. See
[producer/README.md](producer/README.md) for CPU search reproduction and input provenance.
The committed Lean parameter constants remain inspectable without downloading a model.

## Prior work

[TorchLean](https://github.com/lean-dojo/TorchLean/tree/a207636b40f1076981994b4a28e272a9bdc71750/NN/Verification/Cert)
already provides exact rational artifact checkers, binary32 decoding, graph soundness,
IBP and local alpha-CROWN rules. This project uses its exact network semantics and
proves the receipt and complete input-tree composition around them.
[alpha-beta-CROWN](https://github.com/Verified-Intelligence/alpha-beta-CROWN/tree/b58d83ccb32469fc7ae9304fa1d33568ea76b00e)
is the untrusted search producer; the export patch retains domains before they are discarded.
[APTP](https://github.com/dynaroars/APTPchecker/tree/b70765ddde9c9a3fcc36ecddac46305cb7900054)
exports proof trees from modified producers, with Gurobi in its checking path.
[Marabou/Imandra](https://github.com/rdesmartin/imandra-marabou-proof-checking/tree/b8f2ae1d4cac0528bb92bade91e1c46fe7e79660/imandrax)
provides proved constraint-level tree and Farkas checking, with configuration and
preprocessing limits. No novelty claim is made.
