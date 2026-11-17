# GST infinity-control program: noncircular origin-path obligation

Date: 2026-10-29. Research owner: Mathbox investigation; repo kyo-oo/erdosternary2.
Exact verified checkpoint: original main proof still has hypothesis
gst_four_power_third_wave_gate. The strict Problem 406 comparator rejects it.
This document does not assert the full conjecture has been proved.

## Exact target

For every natural n >= 9, noTernaryDigitTwo (2^n) = false,
without any additional gate, bridge, shadow, eventual-zero, transfer
or infinite-support premise.

Equivalent even-exponent target: for every K >= 5,
some ternary digit of 4^K is two. Need handle odd n separately via
previously established elementary route.

## What the original infinity-control branch actually proves

1. GSTOmegaInfiniteBadTrace(s,k,m) = ALL j belong to the bad set.
   This is stronger than any bounded finite prefix and is a real
   all-depth proposition.
2. The exact GST omega universal equation advances descent by /3,
   conserves energy, and propagates both parent and child carries.
3. The ordinary natural exponent m has eventually-zero trits:
   natural_not_infinite_ternary_supportS.
4. The following forcing implication is a DEFINITION of a proposition,
   rather than an assumption-free established theorem:

   GSTCanonicalResidualInfiniteSupportBridgeS :=
      forall s n, 1<=s -> 1<=n -> n%3!=0 ->
      childNavigation(s+1,n) ->
      GSTOmegaInfiniteBadTrace(s,1,n) ->
      InfiniteTernarySupportS(n).

   The consumer gst_residual_prefix_one_no_bad_of_infinite_support_bridgeS
   explicitly takes hbridge as an input, so does not close the gap.

5. The new GSTInfinityBridgeAudit.lean proves a sharper logical identity:
   this forcing proposition is EQUIVALENT to the claimed prefix-one
   residual Omega termination under the exact child and origin premises.
   A proof of this bridge would thus close the specified seam;
   replacing it by an all-depth Omega equation does not prove it.

## The historically advertised three-step universal theorem was NOT green

Source: GSTInfiniteFourPowerNavigation.lean, lines 122-176, 178-260.

Isolated Lean module build:
https://github.com/kyo-oo/erdosternary2/actions/runs/40785543486

- The ordinary production Lake targets omitted this file.
- On adding it as a standalone audited library, Lean failed at line 176:
  "linarith failed to find a contradiction".
- #print axioms shows sorryAx in:
  power_three_step_collision,
  four_power_happy_ge_three,
  gst_four_power_navigation_universal.
- The earlier power-width conservation and local U derivative compile,
  but they do not entail the claimed global collision as assembled.

Therefore the universal statement is NOT kernel certified. Do not import
this module as evidence of a completed proof.

## Delayed-gate theorem: exact nonlocal obstruction

In GSTInfiniteDelayAudit.lean, Lean independently kernel-verified:
- HappyCell(4^8,row 4);
- no HappyCell of 4^11 at any row 3<=p<10;
- HappyCell(4^11,row 10).

Wolfram independently computed the cells:
- 4^8 at p=4: (digit,carry)=(2,0);
- 4^11 at p=3,4: (1,2), (1,2);
- 4^11 at p=10: (2,0).
In 193 observed exponent pairs K to K+3 with K=8..200, many
parent gates were delayed past the first child gate. This is
evidence against SHORT same-index transport, not against a
hypothetical delayed universal theorem.

The exact finite-window evidence in the failed line-176 tactic
allows this delayed behavior; a new monotone global invariant,
source-specific future constraint, or strict well-founded
potential is needed to obtain a contradiction. Re-running
omega, nlinarith, or norm_num does not supply that implication.

## All-depth finite-source terminal law

The new GSTOmegaAbsorbingZero.lean formalizes the exact formula
for any finite seed D and tail X:

  J = D+4X+1,
  forall j >= J:
     digit_3(X,j)=0 and affineCarry(4,D,X,j)=0.

The proof is elementary but importantly UNBOUNDED in j, D and X:
the raw finite word X and carry seed D can always be bounded by
the power 3^j after a sufficient explicit cutoff.

Thus the (0,0) state is an absorbing BAD state, and generic
infinite seeded-bad traces can coexist with finite origin words.
In particular GSTSeededAffineBadTrace(0,1) holds, although origin
1 has finite support. This is a counterexample to an inference
"complete bad graph trace -> infinite input support" that forgets
the POWER-ORIGIN child Navigation and carry-shift hypotheses.

The original residual-source bridge may be true, but it must
use those source-specific constraints. It is not deducible by
generic infinite-time conservation alone.

## Next exact obligation

Prove, without importing a theorem with hGate, sorryAx, an
unverified status, or a copy of the requested conclusion:

  forall s n, 1<=s -> 1<=n -> n%3!=0 ->
      GSTNavigationWitness(gstNavigationConstant(s+1,n)) ->
      GSTOmegaInfiniteBadTrace(s,1,n) ->
      False.

To use origin finite support, derive independently:
  for every natural L there is some q>=L with
  ternaryOriginDigitS(n,q) != 0
from the bad trace and child gate. This implication is
the genuine missing arrow.

Any proof that only obtains a finite child gate, a descending
future coordinate reaching zero, the equality of past/future
energies, or a finite prefix census has NOT supplied this arrow.

## Verification contract

Use the strict problem406 comparator on the exact proposition
forall n>=9, noTernaryDigitTwo(2^n)=false; check #print axioms and
reject sorryAx. A build-only comparator green is insufficient.

Current certificate links:
- infinity universal failed: runs/40785543486
- exact delayed gate passed: runs/40785737189
- other infinity support and absorbing-zero kernel runs must be
  checked before status promotion.

The original conjecture remains unresolved in this checkpoint.


## Stronger exact canonical-seed/offset stress test (Wolfram)

The preceding arbitrary coupled-state counterexample is not the end of
the stress test. Instantiate the actual prefix-one affine coordinates
s=1, k=1. In the source:

 c_1 = 7, A=4^(3^1)=64,
 bridge seed D=(4*(c_1 mod 3))/3=1,
 offset z=floor(c_1/3)=2.

Choose child T=46 (three-free: T mod3=1). It has a genuine child
Navigation gate at j=2. The correct affine parent trace is

 X=z+A*T=2+64*46=2946.

With the exact seeded carry
 C_j=(1+4*(2946 mod 3^j))/3^j,
the parent has NO Happy vertex at any j>=0: for j<=8, the exact
digit/carry table includes two-free or ALT-minus at every step; for
j>=9 both the finite source input and seed carry are zero.
Wolfram independently checked all values j=0..12.

This child also matches a canonical low-exponent residue:
 c_2 mod 27 = 16 and 46 mod27 = (13*16) mod27 =19,
with n=13 three-free. That proves even the exact seed, offset,
power multiplier, and first three child coefficient trits do not
force parent navigation.

**Crucial distinction:** T=46 is NOT the full canonical child
T=gstNavigationConstant(2,13). Therefore it does NOT falsify
GSTCanonicalResidualInfiniteSupportBridgeS, the Erdős conjecture,
or a theorem using the full power-origin identity. It identifies
exactly why the full origin fingerprint (and not any fixed
finite residue alone) must occur in the missing forcing proof.

Source: GSTCanonicalSeedCountermodel.lean (verify CI separately).
