# Verify the published raw transformer evidence

This is the only canonical reader command block. Launch notes and comments should link here. The r2 prerelease supersedes transformer-final-raw-evidence; historical release assets remain in place. No overlay is required.

Tested gate platform: Ubuntu 24.04 on Linux x86_64. Prerequisites: Bash, Python 3.11+, curl, git, tar, zstd, CA certificates and a C compiler/linker. On Ubuntu install ca-certificates curl git python3 zstd xz-utils build-essential with apt-get. Use a fresh directory and allow at least 30 GB free disk space. Network access is needed for GitHub, the Lean distribution and the Mathlib cache. The 3 to 5 minute job duration is a target pending measurement, not a promise.

The checksum list covers the archive and every extracted file, including verify.sh, lean-toolchain and the internal SHA256SUMS. The SHA256SUMS digest below is also published in the prerelease notes. These integrity checks assume the authenticity of the notes or this document; same-host checksums do not establish publisher identity.

```bash
# DOC-START
set -euo pipefail
mkdir -p lean-evidence-r2
cd lean-evidence-r2
base=https://github.com/teal-sea/lean-checked-network/releases/download/transformer-final-raw-evidence-r2
curl -fSL --retry 2 "$base/SHA256SUMS" -o SHA256SUMS
printf '%s  %s\n' 417e2c5059ecc8a495752b17c1ce847c7a99563c05afe9622f2721d2ef3d96e5 SHA256SUMS | sha256sum -c -
curl -fSL --retry 2 "$base/transformer-final-raw-evidence-r2.tar.zst" -o transformer-final-raw-evidence-r2.tar.zst
grep '  transformer-final-raw-evidence-r2.tar.zst$' SHA256SUMS | sha256sum -c -
tar --zstd -xf transformer-final-raw-evidence-r2.tar.zst
sha256sum --quiet -c SHA256SUMS
cd transformer-final-raw-evidence-r2
curl -fsSL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -o "$HOME/lean-evidence-elan-init.sh"
sh "$HOME/lean-evidence-elan-init.sh" -y --default-toolchain none
export PATH="$HOME/.elan/bin:$PATH"
lean --version
bash ./verify.sh --work "$HOME/verify-work"
# DOC-END
```

The default must print the proposition, its audited axioms, `leanchecker replay passed: 20 new modules`, and PASS. `--full` additionally replays all project objects; it can take hours. `--controls` runs the 18 existing paired data controls and adds substantial time. The default always elaborates the small proved KernelControl.lean fixture with kernel reduction. CI mutates its true statement to a false one in a scratch copy, deliberately rehashes that scratch fixture to pass the integrity layer, and requires Lean's mathematical rejection.

## What this proves and assumes

The default run verifies the shipped theorem term against the printed proposition, audits its standard axioms, and replays the 20 new modules through Lean's kernel checker. It assumes authenticated earlier project objects, pinned Mathlib and core objects, the checker implementation, host runtime, hardware and release origin. It does not establish that every shipped object was compiled from the supplied src/ tree, or that the mathematical statement matches every informal claim.

`bash ./verify.sh --from-source` rebuilds only TransformerCore.Model from bundled source using the authenticated core toolchain and compares the output object's SHA256 with the shipped object. It writes verify-work/from-source.json, reports both hashes and exits nonzero on a difference. A match establishes byte reproduction for that single core-only module, conditional on the toolchain and its core objects. It does not establish reproducibility of Mathlib-dependent modules or the whole bundle. The manifest records hashes and historical provenance rather than a complete source-to-object build attestation for every module. Measured on Ubuntu 24.04 with the pinned Lean 4.35.0: TransformerCore.Model recompiles successfully, but its bytes differ (shipped 950cfc7e79f0878b24813aa23bb64ce66b6e7c5edc4c420ef6be21e6c6e47d5b; rebuilt 4bb28b599c3b5b29e5b315e6d02f05feb08d94fa51e00ee2dcb49f773b2f571c). This does not show a mathematical discrepancy; the original complete build recipe has not been reproduced. Treat the shipped objects as supplied proof artifacts, with replay and the stated assumptions.

A reader establishing the rest must rebuild every project module from src/ with the exact pinned Lean and dependency revisions, account for compiler options and generated inputs, compare each object and investigate differences. Pinned dependencies may themselves require rebuilding for a source-only trust chain.

## One release gate

verify-release.yml has one Ubuntu job and no matrix. It sends only this document and the test harness through standard input to a fresh ubuntu:24.04 container. The container receives no checkout mount, credentials, host HOME, Lean installation or cache. It downloads the published URLs anonymously and runs the block verbatim, then tests checksum corruption, a mathematically false declaration and the exactly one-line missing-Lean diagnostic. The same gate runs for relevant pull requests, release publication and weekly decay checks. Repository administrators must require this job in branch protection to make it a merge requirement; the workflow itself fails closed.
