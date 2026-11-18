# Coordinator acceptance after packaging repair

The coordinator independently exercised the repaired package, rather than accepting the worker's completion message:

- All 36 harness tests passed. Some deliberately use labelled Lean/checker stubs to test directory handling and subprocess failure propagation. Those tests are not mathematical proof evidence.
- All three generators reproduced the committed Lean byte for byte. Pinned input and Lean source hashes passed.
- Shell syntax checks passed.
- The changed-weight control was rerun with the real pinned Lean toolchain: `Reference` and mutant `Pilot` exited 0, unchanged `Bwd` exited 1 with the intended false-proposition diagnostic. The stricter control parser accepted it.
- The real `verify.sh` refused `LEXNET_WORK` pointing to the package itself, exited 2, and left the complete package file inventory and contents unchanged.
- Independent malformed-log assertions that previously passed incorrectly now fail: a missing axiom inventory, an added audit error, a second Lean error in the negative control, and missing prerequisite exits.
- Every one of the 28 Lean source/include files is byte-identical to the accepted proof package. No mathematical statement, proof, frozen weight or generated Lean file was changed by the repair.

The full source compilation and fresh kernel replay in `../packaging/` preceded the wrapper repair. They were not repeated here: the repair changed work-directory handling, log checks and documentation, not the proof sources or compiler commands. The separately implemented nanoda result remains scoped to the object and export hashes in `../nanoda/`.

`receipts.json` records actual process exits and elapsed times. `MANIFEST.json` pairs original and public-copy hashes. Local directory names were replaced by `<scratch>` and `<package>` in public copies; the original logs are preserved separately. The source-preservation receipt's commit identifies that local historical proof package, not a public repository URL.
