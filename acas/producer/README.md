# Reproduce the untrusted producer on CPU

The committed `certificate.json` is the normalized split-tree export from alpha-beta-CROWN
at `b58d83ccb32469fc7ae9304fa1d33568ea76b00e`, with auto_LiRPA submodule
`e3930353a3589f7d10879f1e71223d1eefb57196`. Its SHA256 is
`89d8742b8a08f2259dfb99f8dcac061cad9276db1fb75fb2d5a896ed89cc0b0f`
(measured). It contains **34 terminal leaves (measured)**. Search is untrusted; Lean
checks the exact frozen problem rather than accepting the producer's status or endpoints.

The original benchmark files are fetched from VNN-COMP's
[pinned benchmark checkout](https://github.com/VNN-COMP/vnncomp2023_benchmarks/tree/d9e7b2feeaf534dcc557729ee7c920bd5b97099c/benchmarks/acasxu).
No explicit benchmark license was found in that checkout's tree. We do not bundle the
ONNX or VNNLIB files. `../gen/fetch_inputs.py` downloads the gzip files and checks the
SHA256 of their decompressed bytes:

| Input | Measured SHA256 |
| --- | --- |
| ONNX | `843f7110bf5a8b7f0eeb9b1c548d9d558db9099328b392423d5a7444a0656dd4` |
| VNNLIB | `7a9a9930711817c6cc39940f5c1d0f8c51f2ed82f38e203c4b5de03c19bd4ced` |

The restricted stdlib importer validates these hashes, permits only the frozen affine/ReLU
chain and zero input subtraction, transposes ONNX `[in,out]` matrices once, and embeds
binary32 parameters as exact rationals. It does not execute ONNX. Original input coordinates
are already normalized. The decimal property is parsed and retained exactly.

## Search commands

Run from this directory. Use a Python environment separate from the lightweight checker.
The recorded supported environment was Python 3.11.17, PyTorch 2.11.0+cpu,
torchvision 0.26.0, ONNX 1.23.2 and NumPy 2.4.6 (measured installed versions).
The captured distribution versions are in `environment-record.json`; install CPU Torch
wheels separately, then the remaining pinned packages from `requirements-cpu.txt`. Some upstream imports require `gurobipy`; this input-split
CROWN configuration does not invoke a Gurobi solve and requires no paid solver account.

```sh
python3 ../gen/fetch_inputs.py
python3 -m venv .venv
. .venv/bin/activate
python3 -m pip install torch==2.11.0+cpu torchvision==0.26.0+cpu --index-url https://download.pytorch.org/whl/cpu
python3 -m pip install -r requirements-cpu.txt
git clone https://github.com/Verified-Intelligence/alpha-beta-CROWN.git abc
git -C abc checkout b58d83ccb32469fc7ae9304fa1d33568ea76b00e
git -C abc submodule update --init --recursive
git -C abc apply ../instrument.patch
python3 outward.py
export OMP_NUM_THREADS=8 MKL_NUM_THREADS=8 OPENBLAS_NUM_THREADS=8
export PYTHONPATH="$PWD/abc/auto_LiRPA"
export W2_CAPTURE="$PWD/events.jsonl"
taskset -c 0-7 python3 abc/complete_verifier/abcrown.py --config cli-crown-outward.yaml
python3 export_events.py events.jsonl certificate-new.json 1_1
```

Thread counts and affinity above reproduce the configured producer allocation. For a
long run, use a persistent systemd user unit with a memory cap and its own log.
The hook is opt-in through `W2_CAPTURE`. It retains every input split and bound event
before terminal filtering discards accepted domains. The normalizer reconstructs both
children and checks complete root coverage. Attacks, clipping, beta multipliers, cuts
and activation splitting are disabled in this configuration.

`outward.py` encloses exact decimal input bounds in binary32 for search only. The original
strict decimal threshold and original decimal input region remain the theorem's target.
Search diagnostics, paths and timing metadata can change across runs. A fresh producer
run is not expected to reproduce the committed JSON byte-for-byte. Regeneration of the
committed proof uses the committed, hashed certificate and must be byte-identical.

The supplied `producer.py` also contains the earlier restricted auto_LiRPA driver, for
reference. It is not the CLI path that produced this ordinary CROWN certificate.
`crownint-weight-mutation.json` is a negative fixture: output weight `[0,25]` is changed
to the exact integer `1000000`. The tests verify a real in-box rational counterexample;
the Lean negative control rejects the stale receipt for this changed objective.
