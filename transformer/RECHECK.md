# Re-checking the transformer release

`verify-release.sh` is the standalone verifier for the `transformer-final-raw-evidence`
release. Main previously contained only `mathlib/verify.sh`, the older source-build
CI gate. That gate remains unchanged; it is not the standalone release verifier.

The compatibility repair uses elan's stable `ELAN_TOOLCHAIN` selector with `elan
which lean`, not `elan which --toolchain`. Without elan, real `lean` and
`leanchecker` on caller PATH can locate a toolchain, including the normal
`bin/lean` layout. Hardlinked/symlinked elan shims are not mistaken for a toolchain.
An explicit `--toolchain DIR` still works. Only the pinned official Linux runtime
bytes pass the existing SHA256 checks. `lean --version` runs on those authenticated
bytes and must report exactly 4.35.0, not a release candidate or development build.
Caller PATH is passed as discovery data, never copied into the Lean/Lake runtime
environment. All original hash inventories, module isolation, proposition/axiom
checks, replay and paired-control checks remain intact.

## Overlay installation

The original release archive still embeds the broken script. Until a repaired
archive is published, explicitly overlay the standalone repaired verifier after
extracting. Run from a directory containing the downloaded original archive and a
checkout of this revision at `lean-checked-network`:

```sh
tar --zstd -xf transformer-final-raw-evidence.tar.zst
cp lean-checked-network/transformer/verify-release.sh transformer-final-raw-evidence/verify.sh
cd transformer-final-raw-evidence
bash ./verify.sh --controls
```

Default replay covers the 20 new modules and checks the final theorem proposition
and transitive axioms. `--full` replays all project modules. `--packages DIR` uses
an existing pinned package cache read-only; its bytes are authenticated and copied
into a fresh isolated view. Without it, the original authenticated Lake/cache
bootstrap remains available. Neither this verifier nor its repair adds a nanoda
invocation. See `STATUS.md` for the independent-checker evidence and scope.

Fast regressions (no release download required):

```sh
python3 -m unittest discover -s transformer/tests -p test_release_verifier.py -v
```
