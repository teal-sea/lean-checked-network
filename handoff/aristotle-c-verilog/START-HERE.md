# Start here: the packet in one page

Written 2026-10-27. Plain-English cover sheet for the full packet in `README.md`.

## What this is

Harmonic's Aristotle can now check C code and Verilog chip designs. Your $500 of credits run out on
2026-11-27. This packet is the plan for using them on this project. It has four ideas, the research
behind them, and two small scripts that measure baseline numbers so Aristotle's answers can be
checked against known truth.

## Do this first

Make one small test submission before anything else. Put the 12-neuron network into a short C
program, submit it to Aristotle, and write down what comes back. The one thing to look for is
whether Aristotle gives you a proof file that Lean can re-check on its own. That decides how
strongly any result can be described in the README:

- **Lean proof files come back.** Re-check them with `leanchecker`. Then the result can be called
  kernel-checked, with Aristotle's C assumptions named.
- **Some other proof format comes back.** Name the checker and say so.
- **Only a verdict and a report come back.** Call it a tool verdict, which is weaker than anything
  in the README today.

## The four ideas

1. **The explanation becomes the chip.** The interpretability finding says the network adds by
   rotating around a circle. Build the chip from that explanation and prove it matches the chip
   built from the trained weights.
2. **Survives broken memory.** Prove that no single flipped bit in the weight memory changes any
   answer. Expected to hold for the big network and fail for the small one.
3. **The adder that never goes wrong.** The small trained adder that handles numbers of any length,
   as a chip, proved correct no matter how many clock cycles it runs.
4. **One object, three proofs.** Lean proves the math, then C and Verilog versions of the same
   network are proved to match, with every assumption written down.

## Two things measured while writing this

**Fault test.** Every bit of every weight was flipped one at a time and all 12,769 additions rerun.

| network | flips tested | flips that broke an answer |
| --- | ---: | ---: |
| big trained network | 347,136 | 0 |
| small 12-neuron network | 32,544 | 8,578 |

The big network wins by a wide margin, so one damaged weight cannot overturn an answer. The small
one has a thin margin and is fragile. These numbers are the known-answer test for idea 2: Aristotle
should say proved for the big one and refuted for the small one, with a count that matches 8,578.

**Rounding quirk.** The small networks are made from cosine waves rounded to whole numbers. At three
angles the exact value is 63.5, and floating-point noise rounded some copies to 63 and others to 64.
That affects 6 of 4,068 cells in the 12-neuron network. No proof is affected, because Lean proves
things about the numbers actually in the file. It does break idea 1 as first stated, because the
shared cosine table does not exactly match the existing network. The fix is a new network defined
straight from the shared table, checked by Lean in minutes.

## What is needed from you

1. Which proofs in this repository did Aristotle help with before the Lean pause? The README names
   only Claude Code and Codex, so the credit line needs correcting.
2. Do you still have any Aristotle job logs or returned proof files outside the repository?
3. Publish the C and chip code right away, or wait until the proof-file question is answered?
4. Is it fine to add one new named network for idea 1?

## Files

| File | What it is |
| --- | --- |
| `START-HERE.md` | this page |
| `README.md` | the full plan, exact property wording, budget and order of work |
| `research-note-2026-10-27.md` | the research behind it, with sources |
| `fault_census.py` | regenerates the fault-test numbers |
| `mechanism_rom_check.py` | regenerates the rounding-quirk numbers |

The scripts need only numpy and run from the repository root.
