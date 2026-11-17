# Mathbox direct closure audit — 2026-10-30

**Exact mathematical objective (unchanged):**
```lean
∀ K : Nat, 5 ≤ K → K ≠ 7 →
  ∃ p : Nat, 1 ≤ p ∧
    GSTFourPowerDirectResidue.digit3 (4^K) p=2 ∧
    GSTFourPowerDirectResidue.digit3 (4^(K+1)) p=2
```

## Established universal source facts (do not reproach or re-prove)

For every K≥13 the axiom-free file
`GSTProblem406TightPhysicalCut.lean` proves
`4^K < 3^ceil(24K/19)`. The literal source has binary
valuation `v2(4^K)=2K`. These arithmetic results are valid,
but, without another mathematical implication, do not
exclude BAD ternary trajectories.

## Decisive falsification of the 4L/3 all-source BAD barrier

The suggested general theorem

```text
∀ L≥11, ∀ R, 0<R<3^L, R mod3=1, BAD(R)
  -> v2(R) ≤ floor(4L/3)
```

is FALSE, and cannot be used as the final bridge.

At `L=47`, the exact witness
```text
R=21103075220323727048704
 =143*2^67
 =2288*2^63
```
obeys `0<R<3^47`, `R mod3=1` and
`v2(R)=67>floor(4*47/3)=62`.
All same-row positions for `R` and `4R` are BAD:
there is no p≥1 with digit3(R,p)=digit3(4R,p)=2.

**Formal kernel certificate:** `GSTProblem406BadValuationNoGo.lean`,
theorem `not_universal_bad_four_thirds_bound`.
The proof checks every p<47 by `Fin 47` decision,
and for p≥47 uses `R<3^47` to force source digit zero.

Independent Wolfram recomputation also verified the
decimal representation, valuation and complete digit absence.
**Strict Lean CI PASS**:
https://github.com/kyo-oo/erdosternary2/actions/runs/41039922733 .

This refutes the *all-R auxiliary statement*, NOT the
original theorem with R exactly 4^K. The witness is not 4^K.

### Better complete finite search was a check, not a proof

For a fixed L and binary exponent e, the earlier MITM method
enumerated trillions of BAD words to test zero divisibility.
This is unnecessary for zero residue: all candidates
are the direct finite list `R=j*2^e` with
`1≤j≤floor((3^L−1)/2^e)`.
For L=47 with e=floor(4L/3)+1=63, there are only
2882 multipliers to inspect; this yielded the exact witness
above. The earlier finite evidence through L=36 was
accurate in its checked range but did not support an all-L theorem.
Do not treat increased finite ranges as a proof mechanism.

## Original direct universal Lean route: actual failing premise

A separate CI on the original files
`GSTInfiniteFourPowerNavigation.lean` and
`GSTFourPowerDirectExistenceFromHappy.lean`
compiled all imported definitions and reran the exact
source without inserting a replacement hypothesis.
**Strict CI red**:
https://github.com/kyo-oo/erdosternary2/actions/runs/41039244379 .

Earliest source failure:
```text
GSTInfiniteFourPowerNavigation.lean:176:2:
  linarith failed to find a contradiction
```

The unresolved declaration is
`power_three_step_collision`, which is used to
derive `four_power_happy_ge_three` and then the
candidate unconditional `fourPowerDirectExistence_closed`.
The #print axioms report contains `sorryAx` for
`power_three_step_collision` and both downstream
universal theorems. An axiom-free production gate
was NOT certified by this route.

The source-specific 3-step BAD collision is not
a formal corollary of the existing exact width-three
conservation and local phase inequalities; a real
additional implication is needed to obtain `False`
from the physical source `4^K`.
The synthetic witness above also has a GOOD child
`R/64 = 143*2^61` at multiple rows, while its
parent `R` is all-depth BAD; this explicitly rules
out generalized 3-step propagation without literal
perfect-power origin.

## Fixed contract for further work

Keep the target `CommonTwo K` for all K≥13.
Do not replace the false 4L/3 bound with a renamed
hypothesis and call it proved. The older stronger
3L/2 dyadic threshold and other source-specific
transport routes still require genuine noncircular
all-length proofs. The new counterexample neither
settles nor refutes those.

**Net verified result:** negative universal auxiliary
lemma and red source-specific direct collision, both
documented with exact reproducible counter-evidence.
The all-K universal production gate remains unproved.
