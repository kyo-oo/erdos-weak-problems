<!-- ======================================================================
<!-- CHRONOLOGICAL LABEL -- #0817 / 1132
<!--    Path         : branches/sol_physical-phase-crossing-implementation/docs/GST_V2_HANDWRITTEN_COMPLEMENT_AND_DUAL_RADIX_COORDINATE.md
<!--    Ref          : origin/sol/physical-phase-crossing-implementation
<!--    First-commit : 2026-08-17 05:43:26 +0530  (1749c78)
<!--    Last-commit  : 2026-08-17 05:43:26 +0530  (1749c78)
<!--    Total commits: 1
<!-- ======================================================================
<!-- GIT HISTORY (chronological, oldest first)
<!-- ======================================================================
<!-- [01/1] 2026-08-17 05:43:26 +0530  1749c78  (ker07-dev)
<!--        Derive complement coordinate from handwritten V2 kernel
<!-- ====================================================================== -->

# GST V2 Handwritten Kernel — Complement and Dual-Radix Coordinate

This is the exact follow-up to `GST_V2_HANDWRITTEN_EQUATION_EXPERIMENT_2026-08-17.md`.

## 1. Exact mixed-radix information object

For any `k>=1`, put

`B=2^k`, `M=3^k`, `S=B*M=6^k`.

A mixed-radix state consists of

`0<=C<B`, `0<=w<M`

and the information integer

`m=C+B*w`, `0<=m<S`.

The opposite 3-world reading is the Euclidean division of the same `m` by `M`:

`m=e+M*C'`,

with `0<=e<M`, `0<=C'<B`.

Thus

`C+B*w = e+M*C'`.

This is the exact simultaneous two-world decomposition. It is a stronger and safer interpretation of Boss's handwritten multiply/divide-at-once symbol than an invented mirror operation.

## 2. Complement coordinate

Define the deviation from the maximal fixed information state by

`delta := S-1-m`.

Then the same complement has two exact mixed-radix readings:

`delta = (B-1-C) + B*(M-1-w)`

and

`delta = (M-1-e) + M*(B-1-C')`.

Proof: subtract the two decompositions of `m` from

`S-1 = (B-1) + B*(M-1) = (M-1) + M*(B-1)`.

Therefore `delta` is coordinate-independent information: the 2-world and 3-world see different quotient/remainder components but reconstruct the identical complement integer.

## 3. Boss kernel becomes a basis-independent resolvent

The handwritten `7/(x-6)` generalizes at scale `k` to

`7/(m-6^k)`.

Because `6^k-m=1+delta`, its magnitude is exactly

`K_k(delta)=7/(1+delta)`.

Thus the kernel depends only on the coordinate-independent deviation from the maximal fixed/SURVIVE information state.

At `delta=0` it is maximal, equal to `7`.

## 4. Re-encoding orbit

If the opposite tuple `(C',e)` is re-encoded back in the original B-by-M ordering,

`m_rot := C' + B*e`,

then

`m_rot == B*m (mod S-1)`.

Consequently, with

`delta_rot := S-1-m_rot`,

one has

`delta_rot == B*delta (mod S-1)`.

For GST x4/two-trit scale `k=2`, this is

`delta_rot == 4*delta (mod35)`.

The proper ALT- deviation orbit is exactly

`{7,14,21,28}`,

and the kernel ceiling on it is

`7/(1+7)=7/8`.

## 5. Exact versus experimental operator

EXACT core:

- same information integer `m`;
- two mixed-radix decompositions;
- same complement `delta` in both spaces;
- kernel `7/(1+delta)`;
- multiplicative re-encoding orbit of `delta` modulo `6^k-1`.

EXPERIMENTAL layer:

The dual swap-scaling operator

`ALT_a(u,v)=(a*v,u/a)`

is a possible mathematical realization of Boss's simultaneous multiply/divide energy intuition. It conserves `u*v` and is hyperbolic on both proper ALT two-cycles, but it is not yet identified with existing Lean carrier coordinates. It must not be used in the proof until that identification is derived.

## 6. Relevance to the final seam

This complement coordinate suggests a new inverse-limit attack:

- complete avoidance of SURVIVE means `delta` never reaches zero in the relevant physical/subspace intersection coordinate;
- at the aligned `6^2` ALT sector, nonzero bad information is forced into a 7-multiple deviation orbit;
- canonical origin coordinates are already embedded exactly in every finite `6^k` universe by `Q_t(b) mod Q_t(6^k)=Q_t(b mod6^k)`;
- therefore the missing global theorem may be expressible as compatibility of nonzero deviation classes across all k;
- if those compatible classes force a genuinely nonterminating origin ray, `finite_origin_contradictionS` closes the natural-number case.

The next experiment is to compute the compatible deviation classes under the canonical origin embedding across `k=1,2,3,...` and compare them with the actual finite-support origin cylinders.
