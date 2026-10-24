# Release verification evidence

These records apply to the packaged Lean sources identified by `source-tree.json`
and `verification-manifest.json`. The source subtree is stable across the later
reporting commits. The module manifest records SHA256 of each new source and accepted
`.olean`, together with compilation/replay completion. `audit.json` records the exact
final axiom line and frozen specification binding.

`module-logs.tar.gz` contains raw module stdout/stderr and GNU time records under
`logs/`. `state.json.gz` maps accepted source/object fingerprints to successful commands
and log names. `runs.jsonl.gz` preserves all runs, including setup failures and the
explicitly interrupted optional FloatLib dependency replay. Paths in the records name
the original clean-clone location; log basenames map to the archive. Timings are
measured; CPU and elapsed sums in `timing-summary.json` are derived. The dependency
log captures fresh checkout/cache acquisition before source compilation.

`nanoda/objects.json.gz` preserves the uncompressed object manifest whose SHA256 is
in `nanoda/result.json`. It hashes the exact `.olean` files and companion files on the
export search path, including pinned dependencies and the toolchain. The nanoda driver
checks that these bytes do not change during export and replay. `nanoda/nanoda.json`
records the hard standard-axiom allowlist and enabled natural-number extension.
The raw success line, resource measurements and export hash are retained alongside it.
The exported declaration stream and compiled objects are deliberately not committed;
`gen/nanoda.py` regenerates them from a fresh build.

`files.sha256.json` binds the archived evidence files. Adjacent release Python logs and
`release-ci-initial-head.json` preserve the lightweight gates and initial published-head
CI result. The final PR head's CI is recorded in the external release report to avoid
requiring a new commit solely to name its own hash.
