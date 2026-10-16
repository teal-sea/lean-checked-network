# lean-mod-add-proof

A verifiers v1 taskset (an environment for the Prime Intellect Environments Hub) in which the
model has to prove, in Lean 4, that a frozen integer neural network adds modulo p on every
input pair. The reward is whether Lean's kernel accepts the proof. There is no model judge and
no partial credit, so the reward cannot be argued with.

## The task

Each task is one frozen network for addition mod p (p in 5, 7, 11, 13, 17, 19, 23; 8, 16 or
32 neurons; three seeds). The networks were trained with `train.py` from
https://github.com/teal-sea/lean-checked-network (two layers: embed, add, square, read out;
weights rounded to whole numbers in [-127, 127]) and only networks that are right on all p*p
pairs, checked in numpy exactly as the Lean definition evaluates, were kept. 13 of the 52 were
trained on 90% of the pairs and generalize to the rest; 39 saw every pair during training
(`train_fraction` in `tasks/tasks.jsonl` says which). 11 of the 63 (p, H, seed) combinations
never froze to a fully correct network at these settings and are absent (all the 8-neuron
networks for p >= 17, and two of the 8-neuron ones for p = 13).

The prompt contains:

- the task statement,
- `LeanCheckedNetwork/Network.lean` from the repository above, verbatim (the network defined
  in plain integer arithmetic: `nth`, `hidden`, `dot`, `scores`, `argmax`, `answer`),
- `LeanCheckedNetwork/Weights.lean` for this network, verbatim: `E1`, `E2`, `W2` as Lean
  lists of `Int` constructors, `answer a b`, and `Spec`, the proposition to prove,
- the required theorem name and signature:
  `theorem LeanCheckedNetwork.Net.adds_mod_<p> : ∀ a, a < p → ∀ b, b < p → LeanCheckedNetwork.Net.answer a b = (a + b) % p`,
- the rules (allowed imports, forbidden tokens, the time limit).

The model answers with one ```lean code block, which is the whole file
`LeanCheckedNetwork/Submission.lean`. The repository's `Fast.lean` (the packed big-number
evaluator) is not given. For small p a plain `decide +kernel` works; the kernel's cost grows
with p squared times the number of neurons, so the larger tasks push towards a faster route.

Splits: seeds 0 and 1 are `train` (35 tasks), seed 2 is `eval` (17 tasks).

## The reward

`kernel_accepts` is 1.0 only if all of the following hold, in this order, and 0.0 otherwise:

1. Text guard (a first filter, before Lean runs): the file contains none of `sorry`, `admit`,
   `native_decide`, `decide +native`, `ofReduceBool`, `axiom`, `opaque`, `implemented_by`,
   `extern`, `unsafe`, `partial`, `set_option debug.*`, `macro`, `macro_rules`, `elab`,
   `elab_rules`, `syntax`, `notation`, `infix`/`infixl`/`infixr`/`prefix`/`postfix`,
   `initialize`, and imports only `LeanCheckedNetwork.Network` and
   `LeanCheckedNetwork.Weights`. The match is on whole words anywhere in the file, comments
   included.
2. A fresh Lake package (toolchain `leanprover/lean4:v4.35.0-rc2`, no dependencies) with
   `Network.lean`, `Weights.lean` and the submission: `lake build LeanCheckedNetwork.Submission`
   succeeds within the time limit.
3. `lake env leanchecker LeanCheckedNetwork.Submission` accepts the module. This replays every
   declaration through the kernel from the compiled file, so `set_option debug.skipKernelTC`
   cannot hide a bad proof (tested below).
4. A file written by the grader, `Check.lean`, elaborates:
   `theorem ... : LeanCheckedNetwork.Net.Spec := LeanCheckedNetwork.Net.adds_mod_<p>`.
   `Spec` is defined in `Weights.lean`, so its meaning is fixed before any submitted text is
   read; a theorem with the required name but a weaker or different statement fails here.
5. `#print axioms LeanCheckedNetwork.Net.adds_mod_<p>` lists nothing outside
   `propext`, `Classical.choice`, `Quot.sound`. By default (`axioms_mode = "subset"`) a proof
   that uses fewer of them passes too (a `decide` proof typically depends on `propext` only);
   `axioms_mode = "exact"` demands all three and nothing else.

The reason a submission failed, the stage it reached, the axiom list, the timings and the
tail of each command's output are stored on the trace under `trace.info["lean_grader"]`, and
the metric `lean_stages` records `guard_passed`, `build_passed`, `leanchecker_passed`,
`statement_passed`, `axioms_passed` and `grader_seconds` per rollout.

The time limit covers build, replay and check together: `--env.taskset.task.timeout-s`,
default 300 seconds. On timeout the whole process group is killed and the reward is 0.0.

Grading runs on the machine that runs the taskset (the verifiers worker), not inside the
model's sandbox. That machine needs elan with the pinned toolchain at `~/.elan/bin`
(`leanchecker` ships with the toolchain). Each grade uses its own throwaway package directory
(`--env.taskset.task.work-root`, default the system temp dir) and `LEAN_NUM_THREADS=1`, so
concurrent rollouts do not interfere, but each costs one core and up to about 2 GB while the
kernel runs.

## Layout

```
lean_mod_add_proof/
  taskset.py      the TaskData / Task / Taskset classes, the prompt, the reward and metric
  grader.py       the pipeline above; no verifiers dependency, testable on its own
  gen_dataset.py  turns train.py .npz files into tasks/<id>/Weights.lean + tasks.jsonl
  Network.lean    copied from the repository
  tasks/          52 tasks: tasks.jsonl plus one folder per task
```

## Running

```bash
uv venv && uv pip install verifiers          # verifiers 0.4.0 was used
uv pip install -e .                          # this package
uv run vf-eval lean-mod-add-proof --dry-run -n 2 --no-push    # resolves and prints the config, runs nothing
uv run vf-eval lean-mod-add-proof -n 5 --no-push              # needs a model endpoint, see below
uv run vf-eval lean-mod-add-proof --env.taskset.split eval --env.taskset.max-p 11 --env.taskset.task.timeout-s 600
```

Configurable from the command line or a TOML file: `env.taskset.split` (train, eval, all),
`env.taskset.max_p`, `env.taskset.tasks_dir`, `env.taskset.task.timeout_s`,
`env.taskset.task.axioms_mode`, `env.taskset.task.work_root`, `env.taskset.task.keep_packages`.

Rebuilding the dataset: train networks with the repository's `train.py`, then
`python3 gen_dataset.py tasks RUN1.npz RUN2.npz ...` (networks that are wrong on any pair or
have a tie are skipped).

## What `vf-eval` and `prime env push` need that was not available here

- A model endpoint. `vf-eval` sends the prompts to an OpenAI-compatible endpoint; by default
  that is Prime Inference (`https://api.pinference.ai/api/v1`) with the key in `PRIME_API_KEY`
  (or from `prime login`), model `deepseek/deepseek-v4-flash` unless `-m` says otherwise.
  Another endpoint is set with `--client.base-url` and `--client.api-key-var`.
- A runtime for the model's harness. The default runtime type is `prime` (a Prime sandbox,
  which needs the same account and key). Locally, `--env.agent.runtime.type subprocess` or
  `docker` avoids that; the harness is `bash` by default and `--env.agent.harness.id null` is
  the plain chat loop.
- `--push` (on by default) uploads the run to the platform and needs `PRIME_API_KEY`;
  `--no-push` keeps it local.
- `prime env push` needs the Prime CLI (`uv tool install prime`), `prime login`, a username
  set on the account profile, and is run inside this directory. `--visibility PRIVATE` keeps
  it private, `--team <team>` pushes to a team.

None of these were run: this container has no Prime Intellect account, key or model endpoint.
The taskset was exercised with its own classes (`Task.score` on hand-built traces) and with
`vf-eval --dry-run`.

## Limits

- The text guard is coarse on purpose and also rejects the banned words in comments.
- The statement check accepts any theorem whose type is definitionally equal to `Spec`.
- Axioms are read from the text output of `#print axioms`; the parser expects Lean 4.35's
  wording.
- The tasks are all small (p <= 23); brute force by `decide +kernel` is feasible on every
  task, slower on the bigger ones (measured times are in `../tests/logs/`). The difficulty gradient is time, not possibility.
- Grading needs a Lean toolchain on the grading machine; nothing installs it. Running the
  grader in a container through `IsolatedVerifierEnv` (a `@vf.reward` taking `runtime`) was
  not done.
- No memory limit is set on the Lean processes.
