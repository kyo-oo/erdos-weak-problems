# GST Problem 406 — Mathbox/Deep Research exact-origin proof attempt (2026-10-30)

**Starting revision**: `e304d61c588f8bc264a87102c5e9ad521d633aaf` (direct hGate audit).
**Research branch**: `gpt6/problem406-exact-origin-gate-research-20261030`.
**Authoritative goal**: no new axioms, no `sorry`, prove for every `K>=5, K!=7`
`CommonTwo K`, i.e. one SAME positive base-3 row has value 2 in
`4^K` and `4^(K+1)`. The final benchmark is still conditional on
`gst_four_power_third_wave_gate`; do not change production until
that exact proposition has a binder-free kernel proof.

## New verified arithmetic from Deep Research

`GSTProblem406BinaryOriginExponentScale.lean` now includes
`physicalBinaryThreshold`, `physical_source_exact_binary_threshold`
and `physical_scales_at_three_step`. These are universal exact
arithmetic identities, independent of the universal gate:

For K>=13, let L(K)=floor((4K-1)/3) and t(K)=floor(3L(K)/2)+1.
Then

| K mod 3 | L(K) | t(K) | 4^K |
| --- | --- | --- | --- |
| K=3q | 4q-1 | 6q-1 | 2^(t+1) |
| K=3q+1 | 4q+1 | 6q+2 | 2^t |
| K=3q+2 | 4q+2 | 6q+4 | 2^t |

And L(K+3)=L(K)+4; t(K+3)=t(K)+6.

Strict Lean kernel proof and axiom check:
https://github.com/kyo-oo/erdosternary2/actions/runs/41019532498 .

**Calibration**: the identity identifies the original source in
binary units. It does NOT exclude any actual BAD exponent and does
NOT itself solve the hGate. Stating a new lemma that these exact
binary values cannot be BAD would be merely renaming the goal.

## Signed U2D rectangle: explicit negative discriminator

Existing strict audit:
`derivations/GPT6_DIRECT_HGATE_GST_KERNEL_OBLIGATIONS_20261030.md`
shows the right-BAD-to-full-rectangle sign implication is missing.

The new `GSTProblem406U2DRightBadCountermodel.lean`
constructs a concrete physical x4 source-neighbor matrix with
source A=55 and horizontal width N=3:

- A mod 27=1 (same initial low-prefix form as a canonical cut).
- The left edge A=55 and 4A=220 have a common digit two at p=3.
- The right edge 4^3 A=3520 and 4^4 A=14080 has **no common
  digit 2 at any ternary row p>=0**, not merely a finite sample.
  Proof: exact inspection for p<8, and 3520<3^8 for p>=8.
- The full GST crossing charge
  `weightedCrossPrefix demoCarry demoDigit 3 4`
  is **+41661 > 0** by the full exact 12-cell cross-density table,
  with demoDigit(t,p)=digit3(55*4^t,p) and
  demoCarry(t,p)=floor(4*(55*4^t mod3^p)/3^p).

This is a counterexample to the **generic**
`right all-depth BAD => weightedCrossPrefix <=0`
transport argument (even with A mod27=1). It is **not** a
counterexample to the original theorem: 55 is not a power 4^K.

An independent WolframLanguageEvaluator computation reproduced
all digits and the exact 41661 weighted sum. Strict Lean kernel validation and #print-axioms audit **PASS**:
https://github.com/kyo-oo/erdosternary2/actions/runs/41021108173 .

## What the new countermodel says about the actual GST proof

The **canonical** rectangle in
`GSTFinalPrefixOneDirectU2DCollision.lean` is NOT an arbitrary
integer A. Definitions in
`GSTGraphV2HandwrittenOmegaUBlock.lean` give

```text
residualEnergy s 1 n = 4^(3^(s+1)*n),
residualWidth s = 3^s,
parent exponent = 3^s*(1+3*n).
```

Thus a valid signed-rectangle solution must derive a new,
specific constraint on the interior `reverseSurviveCode`
and terminal carry/digit potentials from exactly this
perfect-power source. A proof using only the generic 12-cell
sign table, right-BAD inequality and a zero lower-left carry
cannot work; the explicit countermodel satisfies all three
of those weaker ingredients.

The exact direct statement that would finish this
canonical propagation route is still UNPROVED:

```text
for s>=1,n>=1:
  if the canonical left source 4^(3^(s+1)*n) has a Happy row
  then the right source 4^(3^s*(1+3n)) has a Happy row.
```

It must be established from GST source identities and the full
nonlinear interior, without assuming the desired right witness.

## Fixed binary modulus obstruction to proposed finite product states

Any claim that storing only (carry, source residue mod 64)
eliminates all BAD sources is false, even for arbitrarily
deep ternary words. Let m=2^j for j>=1 and

```text
R_j = (3^(2^j)-1)/2 = 1+3+...+3^(2^j-1).
```

Every base-3 digit of R_j is 1, so R_j and 4R_j
cannot have a COMMON digit 2. By the 2-adic LTE formula

```text
v_2(3^(2^j)-1) = j+2,
v_2(R_j) = j+1.
```

This gives BAD integers with binary valuation as high as
desired. The ratio v_2(R_j)/ternary length = (j+1)/2^j
decreases to 0, so these examples do NOT refute the much
stronger proposed barrier v_2(R)>1.5*L; instead they show
a fixed 64-state tag cannot capture the **growing**
binary-vs-ternary constraint that the actual power 4^K
satisfies. Exact finite checks were independently
run with Wolfram for j=1..8.

## Remaining original theorem — no hypothesis promotion

Even after the new Lean-verified arithmetic identities,
the core `gst_four_power_third_wave_gate` remains
equivalent to the universal quantified `CommonTwo`
assertion. The all-source valuation-barrier
proposed previously remains an unproved conjecture;
4,812,489 checks through L=240 are not a proof.
A fixed ternary prefix/residue-class classification and
a finite-state binary tag alone do not yield the missing
origin-specific all-scale contradiction.

**Status:** strict exact-origin arithmetic proved, strict U2D
countermodel kernel check passed;
U2D generic sign closure refuted by exact integer data;
the original universal Problem 406 theorem remains open
in the checked Lean proof tree. Production untouched.

## Continuation 2026-10-30: tightened all-K origin geometry and dyadic BAD injection

### Lean-kernel-verified improved Archimedean origin

`GSTProblem406TightPhysicalCut.lean` proves with no `hGate` premise:

```lean
def tighterPhysicalCut (K : Nat) : Nat := (24*K+18)/19
physical_source_lt_tighter_cut:
  ∀ K≥13, 4^K < 3^(tighterPhysicalCut K)
tighter_cut_le_old_cut:
  ∀ K≥13, tighterPhysicalCut K ≤ physicalShortCut K
tighter_cut_high_binary_order:
  ∀ K≥13, 2^((3*tighterPhysicalCut K)/2+1) ∣ 4^K
original_commonTwo_iff_tighter_cut:
  ∀ K≥13, CommonTwo K ↔
    ∃ p, 1≤p ∧ p<tighterPhysicalCut K ∧
      digit3 (4^K) p=2 ∧ digit3 (4^(K+1)) p=2
```

The proof is an exact 19-step induction from
`4^19=274877906944 < 282429536481=3^24`
with base exponents 13..31, followed by floor-arithmetic.
The binary-order margin is **linearly growing**, unlike the
original floor(4K/3) cut:

```text
L = ceil(24K/19)
t = floor(3L/2)+1
delta = 2K-t
19*t <= 36*K+46
2K <= 19*delta+46   (all K>=13).
```

In particular for K=1000, old L=1333, new L=1264,
t=1897 and delta=103.

**Strict proof certificate**:
https://github.com/kyo-oo/erdosternary2/actions/runs/41023507250
(also earlier smaller proof:
https://github.com/kyo-oo/erdosternary2/actions/runs/41023014578).

This improves the *necessary physical BAD packet* but does not
prove its impossibility.

### New exhaustive dyadic separation experiment

`scripts/gst_406_bad_dyadic_injectivity_audit.cpp`
enumerates **every** ternary word R of length L with d0=1,
whose x4 neighbor 4R never has digit2 at the same positive row.
The exact four-state carry transitions are:
```text
c=0: (d,c')=(0,0),(1,1)
c=1: (0,0),(1,1),(2,3)
c=2: (0,0),(1,2),(2,3)
c=3: (0,1),(1,2).
```
The initial state after reading d0=1 is c1=1.
Leading zeros are allowed; all words 0<R<3^L,
R%3=1 are covered exactly. For each word, compute
R mod 2^t where t=floor(3L/2)+1.
Use a lossless 1-bit-per-residue bitmap; count collisions
and residue zero. No sampling, floating point, or early exit.

New observations, independently executed locally:
- L=9, t=14: 1,676 BAD words; exactly ONE residue-zero word:
  `R=16384=4^7`, the known exceptional exponent.
- L=18, t=28: 5,974,880 BAD words; residues all distinct
  and zero absent.
- L=19, t=29: 14,824,832 BAD words; residues distinct,
  zero absent.
- L=20, t=31: 36,783,296 BAD words; residues distinct,
  zero absent.
- L=21, t=32: 91,266,496 BAD words; residues distinct,
  zero absent.
- L=22, t=34: 226,449,920 BAD words; residues distinct,
  zero absent. The largest observed v2 among these words
  is 29, attained at `R=18790481920`, far below t=34.

**Independent CI replay passed** for L=9,10,18,22:
https://github.com/kyo-oo/erdosternary2/actions/runs/41023985606 .

**New possible GST proof route**: prove all-L dyadic separation
from the x4-BAD automaton by an induction on the difference of
two admissible ternary words. If two length-L bad words with
d0=1 collide modulo 2^t, their difference is a nonzero
multiple of 2^t. Extending an (L−1)-trit word by digits
d,d' changes this difference by
```text
    (d-d') 3^(L-1),   d-d' ∈ {-2,-1,0,1,2},
```
while t increases by one or two. Ordinary
injectivity at depth L−1 is NOT enough to prevent the
cross-digit collision: the necessary induction invariant
must also exclude those shifted differences for the
appropriate pairs of carry states. The analogous
root-carry-zero language already has pairwise modular
collisions at short lengths (e.g. 9,11), so the
physical initial d0=1 state cannot be discarded.

**What this evidence does NOT establish**:
L=22 is not the all-length theorem. Absence of the residue
zero and observed injectivity through L=22 cannot be
extrapolated to arbitrary L. The actual K≥13 hGate
still requires a proof that no literal `4^K` survives,
not a restatement of that exclusion.

### Source context

The public Erdős Problem 406 status remains open as of this
research date (https://www.erdosproblems.com/406).
This independently indicates that the missing universal
arithmetic implication is substantive, not a routine Lean
binder/tactic mismatch.
