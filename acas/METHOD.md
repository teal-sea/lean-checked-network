# Checking dual receipts

The producer searches. The emitter chooses witnesses. Lean checks exact identities and
inequalities, then connects the accepted leaves to the frozen real network. Python
agreement is a regression check and is not a proof premise.

## The local identity

For an affine/ReLU chain write `z_k = W_k y_(k-1) + b_k` and
`y_k = max(0, z_k)`. To bound a scalar objective, supply arbitrary dyadic dual vectors
`nu_k`. After collecting affine coefficients, each unit contributes a residual of the form
`a * max(0,z) - nu * z`. On a previously established interval `[l,u]`, this function
has its minimum at an endpoint or at zero when zero is in the interval. Checking these
values gives a valid lower bound for any chosen dual; the dual need not reproduce the
producer's floating slopes.

Summing the affine equalities and local residual bounds cancels internal terms. The
remaining input-affine form is minimized coordinatewise over the input box. Bias sums
and input costs are checked as well. The resulting lower bound for `-Y_0`, plus the exact
decimal threshold, must be strictly positive. Equality rejects.

All grid constants are mathematical choices rather than measurements: `Q = 2^50`;
parameters, duals and endpoints are integers divided by Q; receipt totals use `Q^3`.
Every original parameter is checked to be exactly representable on this grid. Integer
floor/ceiling bounds are outward, with a proved positive-divisor invariant.

## Intermediate bounds are proved before use

The first affine layer uses exact interval bound propagation. For each later hidden
preactivation, a positive and a negative objective give lower and upper endpoint witnesses.
Their valid bounds use only earlier established intervals. Outward rounding and
intersection with a sound IBP enclosure produce the next interval. Supplied endpoints
are never admitted as assumptions. Final witnesses use the resulting proved intervals.

`LocalReceipt`, `Telescoping`, `BackwardLists`, `SelectedWitness` and `FinalWitness`
prove the algebra. `EndpointRules`, `LeafSafety` and `RawLeafSound` establish the
ordered enclosure invariant and complete leaf soundness. `Parameters`, `ParamChunks`,
`FrozenFunctions` and `FrozenParameters` connect the checked integer parameters and
execution to output zero of the actual frozen TorchLean model for every real input.

## Packed supplied products

All witnesses that use the same weight matrix are batched into `W^T V = C` checks.
The kernel traverses the original integer lists, checks dimensions and magnitude bounds,
packs them, adjusts signed offsets, and checks the resulting integer identities. It does
not trust an asserted hash, prepacked integer or digit extraction.

`RouteA.packed_inj` in `Injectivity` is the bounded-digit injectivity argument also used in
[the transformer packing method](../transformer/mathlib/KRONECKER.md).
`MatrixSound` proves the generic matrix rule. `PackingBridge` proves the correspondence
between the executable lists/Nat offsets and entrywise integer equality. The base and
bounds are exact design constants: base `2^160`, weight/dual bound `2^60`, product bound
`2^127`. The no-carry condition is checked in Lean. This is checking supplied products;
it does not compute CROWN by decoding a packed convolution.

The weakest-leaf pilot's first block had operands of **80,049 and 80,101 bits (measured)**.
Its packed check cost **3.19 CPU seconds**, versus **21.44 CPU seconds** for the same
product checked by scalar dot products (measured, imports included). The derived ratio
is **6.72**. The scalar comparator omits packed-specific shape/range checks, so this is
not a whole-checker speedup. Source: `evidence/route-a-timing-summary.json` and the
captured pilot times in `evidence/history/`.

## Coverage

`Coverage` checks root containment of the exact decimal box, inherited child boxes,
strictly interior shared closed cuts, valid indices, terminal classification and complete
exactly-once traversal. `CoverageSound.check_covers` proves the geometric meaning of
that Boolean check. `CoverageInstance` binds the actual tree and receipt boxes.
`Final` combines coverage with every leaf's strict safety theorem. Removing a real
terminal is a negative control.

## Why not recompute backward CROWN in the kernel?

The alternative recomputation drivers were measured on the same real weak leaf. The
TorchLean forward rational query exhausted its configured memory; a compiled query also
timed out before producing a final margin. Monolithic integer backward recomputation
also exhausted memory. Checkpointing separate declarations in one module was stopped
unfinished at **1,422.52 CPU seconds (measured)**. Its conservative uniform full-tree
projection was **13.4349 CPU-hours (derived)**, before remaining work or replay. These
are failed or censored runs, not completed leaf throughputs.

The compiled backward checker counted **8,454,522 source arithmetic/comparison operations
(derived sum of measured counters)**. Receipt checking removes the repeated search-style
backward arithmetic, retains local proof obligations, and shares the matrix contractions.
The full historical results, including the sparse route B that failed its cost gate,
are in [STATUS.md](STATUS.md). A larger-model scaling claim is not established.
