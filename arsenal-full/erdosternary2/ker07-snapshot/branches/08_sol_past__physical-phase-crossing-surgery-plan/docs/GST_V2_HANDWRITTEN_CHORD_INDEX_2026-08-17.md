<!-- ======================================================================
<!-- CHRONOLOGICAL LABEL -- #0842 / 1132
<!--    Path         : branches/sol_physical-phase-crossing-surgery-plan/docs/GST_V2_HANDWRITTEN_CHORD_INDEX_2026-08-17.md
<!--    Ref          : origin/sol/physical-phase-crossing-surgery-plan
<!--    First-commit : 2026-08-17 05:57:05 +0530  (b0d0382)
<!--    Last-commit  : 2026-08-17 05:57:05 +0530  (b0d0382)
<!--    Total commits: 1
<!-- ======================================================================
<!-- GIT HISTORY (chronological, oldest first)
<!-- ======================================================================
<!-- [01/1] 2026-08-17 05:57:05 +0530  b0d0382  (ker07-dev)
<!--        Index handwritten x-6 half-phase V2 chord
<!-- ====================================================================== -->

# GST V2 handwritten chord — indexed frontier — 2026-08-17

Branch: `sol/physical-phase-crossing-surgery`

This index records the exact mathematical layer generated from Boss's handwritten intuition seed.  The handwriting itself was intentionally not forced into a literal theorem because several symbols/bounds are ambiguous.  Only structures that were reconstructed as exact GST arithmetic are promoted below.

## Stored files

### `docs/GST_V2_HANDWRITTEN_SEED_RECONSTRUCTION_2026-08-17.md`
Commit: `4f6ffabccc28131e57a8e0657ef3c1c2dc7da4c3`

Contains:
- fundamental x2/base-3 six-state bridge;
- x4 GST as two x2 bridge layers;
- exact `x=6` hidden/exposed BIG2 fibre;
- binary half-phase `U_s=2^(3^s)`;
- dual cubic half-phase tower `h_s` and exact bridge to `c_s`;
- seven-axis origin transducer with simultaneous division-by-3 and canonical multiplication;
- finite `6^k` origin-resolvent reconstruction of the handwritten weighted sum/product.

### `experiments/handwritten_seed_v2_experiment.py`
Commit: `ae0ce016eb8115a99e6d874f45a432da0f8b3543`

Exact finite arithmetic checks only.  No external packages, no theorem claim, no hidden approximation.

Checks:
- only valid x4 cells on `x=m1+m2=6` are `(2,4)` and `(4,2)`;
- dual `h_s/c_s` identities;
- universal six-sector half-phase table at the forced row;
- universal origin modulus samples;
- exact finite origin transducer/product exponent identity.

### `docs/GST_V2_HANDWRITTEN_X6_CYCLOTOMIC_CHORD.md`
Commit: `c28c9a16082a119cd3fae6229b631973c942ddbf`

Contains:
- six-sector exact mass cycle;
- handwritten coordinates `x=m1+m2`, `z=m2-m1`;
- cyclotomic factorization of `x-6`;
- exact six-space affine factorization of Navigation successor;
- deeper `6*3^q` inverse-system refinement warning.

## Central exact chord

At the forced phase row the half-phase sectors are

```text
(0,0), (1,3), (2,4), (5,5), (4,2), (3,1).
```

Define

```text
x = m1+m2
z = m2-m1.
```

Then

```text
(x,z) =
(0,0), (4,2), (6,2), (10,0), (6,-2), (4,-2).
```

Therefore

```text
x=6
```

selects exactly

```text
(2,4) = CREATE -> DESTROY = hidden phase-one BIG2
(4,2) = DESTROY -> CREATE = exposed NULL SURVIVE.
```

Both have

```text
|z|=2,
m1*m2=8.
```

Thus the handwritten `|z/(x-6)|` has an exact finite V2 meaning:

- the pole selects the conjugate BIG2 phase fibre;
- the sign records orientation;
- the absolute value removes orientation and leaves the same BIG2 magnitude.

## Cyclotomic form

For `zeta=exp(i*pi*j/3)`, the six finite-sector data satisfy

```text
z_j = (4/sqrt(3))*sin(pi*j/3)

x_j = 5 - 4*cos(pi*j/3) - (-1)^j
```

and

```text
zeta*(x-6)
 = -(zeta^2+zeta+1)*(zeta^2-zeta+2).
```

The first factor is `Phi_3(zeta)`.  Hence the singular fibre is exactly the two nontrivial physical three-phase characters inside the six half-phase group.

This is a finite cyclic/Fourier encoding only; complex analysis is not required for the arithmetic theorem.

## Exact `U` operator supplied by the arithmetic

Set

```text
U_s = 2^(3^s)
A_s = U_s^2 = 4^(3^s).
```

Thus `U_s` is the exact binary half-phase of one physical x4 phase.

Define

```text
h_s = (U_s+1)/3^(s+1).
```

Then

```text
U_s = -1 + 3^(s+1) h_s

h_(s+1)
 = h_s - 3^(s+1)h_s^2 + 3^(2s+1)h_s^3

c_s = 3^(s+1)h_s^2 - 2h_s.
```

Compare the canonical tower

```text
c_(s+1)
 = c_s + 3^(s+1)c_s^2 + 3^(2s+1)c_s^3.
```

The 2-world half-phase tower and 4-world canonical tower are therefore joined by an exact quadratic bridge, with opposite-sign quadratic terms in their cubic recurrences.

Since `h_s == 1 (mod 9)`, this immediately implies `c_s == 7 (mod 9)` and therefore recovers the canonical low ALT- block from the binary half-phase.

## Six subspaces factor Navigation successor exactly

At cut depth `s+2`, the six half-phase sectors have affine high-tail maps

```text
Y_(j+1) = U_s*Y_j + mu_(s,j).
```

Their full composition is

```text
Y_6 = c_(s+1) + A_(s+1)*Y_0.
```

Hence

```text
Y_0 = Q_(s+1)(n)
```

implies

```text
Y_6 = Q_(s+1)(n+1).
```

So `U_s` gives an exact **sixth-root factorization of the Navigation successor** through six binary/ternary subspaces.

In particular the target prefix-one parent is the `j=2` high-tail sector.

## Deeper universe

The first six-sector quotient must not be mistaken for a global six-state transport.

At modulus `3^(s+2+q)`:

```text
ord(U_s) = 6*3^q
ord(A_s) = 3^(q+1).
```

Therefore the phase spaces refine as

```text
physical: 3 -> 9 -> 27 -> ...
half-phase: 6 -> 18 -> 54 -> ...
```

The final theorem is therefore a Hensel/inverse-limit orientation problem, not a fixed six-cycle theorem.

## New exact final formulation

The first quotient contains both conjugate BIG2 orientations:

```text
hidden  : x=6, z=+2
exposed : x=6, z=-2 = NULL SURVIVE.
```

Complete phase-one badness says the canonical lift never realizes a physical SURVIVE at any deeper level.

The next mathematical blade is:

> prove that a natural canonical origin cannot Hensel-lift the `x=6,z=+2` hidden orientation through all compatible `6*3^q` phase quotients while avoiding every SURVIVE orientation.

Desired exact consequence:

```text
canonical hidden-BIG2 lift forever
-> nonzero origin information at arbitrarily deep ternary scales
-> InfiniteTernarySupport
-> contradiction for Nat.
```

The existing `FiniteSupportScratch.lean` is already the final consumer.

## Prohibited regressions

- no global mirror;
- no automatic horizontal 36-state transport;
- no terminal NULL;
- no unrestricted affine lift;
- no claim that the finite product/resolvent itself proves the theorem;
- no infinite-product convergence assumption;
- no residual-Omega resurrection;
- no `sorry`, `admit`, custom axiom, or hidden computation shortcut.
