# GST ternary-2 research: rational Perron barrier and exact cross-radix route
2026-10-30

## Unchanged theorem and strict proof status

The requested universal source-specific theorem remains:
`∀ K≥5, K≠7, ∃p≥1: digit3(4^K,p)=2 ∧ digit3(4^(K+1),p)=2`.

The project has an actual comparator PASS from September 6, 2026,
but historical Lean `#print axioms` included the custom existence axiom
`gst_four_power_direct_existence_inline`. Current production
`questions/deepmind_problem_406/Solution.lean` requires
`gst_four_power_third_wave_gate`. This document does not claim
to have discharged it.

## Discovery 1: exact four-state rational Perron supervector

In `GSTProblem406CarryEntropyBound.lean` the BAD-word transition
counts are `C_n(c)` for carries `c=0,1,2,3`, with `C_0(c)=1`.
Writing the vector `C_n=(C_n(0),C_n(1),C_n(2),C_n(3))^T`,
the original GST physical x4 carry recurrence is

```text
T = [ 1 1 0 0 ]
    [ 1 1 0 1 ]
    [ 1 0 1 1 ]
    [ 0 1 1 0 ]

C_(n+1) = T C_n.
```

New exact integer positive supervector:

```text
w      = [675,1000,1000,806]^T
T w    = [1675,2481,2481,2000]^T
2482*w - 1000*T*w = [350,1000,1000,492]^T >=0.
```

Therefore `1000*T*w <=2482*w` componentwise. Since
`675*C_0 <= w` componentwise and `T` has nonnegative entries,
monotonicity gives by induction for EVERY `n>=0`:

```text
675 * 1000^n * C_n <= 2482^n * w
```

in each component. In particular the original physical carry-one
survivor language satisfies

```text
675 * 1000^n * C_n(1) <= 1000 * 2482^n.
```

Thus its growth has exact rational base `2482/1000=2.482`, improving
the previous two-level `sqrt(7)≈2.64575` envelope. After dividing
by the 3^n total source trit strings, an explicit upper bound is
`(1000/675)*(2482/3000)^n`; it decreases exponentially.

**Exact Wolfram independent check**:
`CharacteristicPolynomial[T,z]=(z-1)*(z^3-2z^2-2z+2)`.
The dominant root is approximately `2.4811943040920156`,
so 2.482 is very close to the true Perron growth rate.
This root number is diagnostic and NOT used as a source axiom.
The theorem file `GSTProblem406RationalPerronBound.lean`
uses ONLY integer inequalities and induction.
New strict CI `gst_406_rational_perron_bound.yml`
must finish green before calling it Lean-kernel-verified.

## Discovery 2: exact first forward row-two hit for every exponent

Using the established `pow4_digit_period` theorem at p=2,
the first nonnegative shift j for a simultaneous row-two witness
in the genuine physical pair `(4^(K+j),4^(K+j+1))`
has K mod 9 table:

```
K mod 9: 0 1 2 3 4 5 6 7 8
least j: 5 4 3 2 1 0 0 7 6
```

The finite class certificate is now derived via the REPOSITORY'S
existing theorem `row_two_overlap_iff_mod9_five_or_six`, not by
asking Lean to synthesize a Decidable instance for an opaque
Boolean-looking custom predicate. Source file:
`GSTProblem406RowTwoFirstHit.lean`. Strict CI awaits verification.
This is an orbit row-two exact characterization, NOT a proof
of the all-row fixed-K original gate.

## Counterexample route and obstruction context

A strict all-source 4L/3 valuation barrier is FALSE, witnessed by the
separately kernel-certified 47-trit BAD source `143*2^67`.
The physically compatible 3L/2 BAD-exclusion criterion is stronger
and is still an unproved candidate. It might suffice for
physical K>=13 because the established exact 24/19 bound
gives `4^K<3^ceil(24K/19)` and a sufficiently high
binary valuation.

Independently, the exact GMP dyadic candidate-sweep from
prior research gave no counterexample for `L=11..260`.
Additional exact GMP runs completed for L=261..303 and
304..310, also no counterexamples in the checked set
`R=m*2^(floor(3L/2)+1)<3^L, R mod3=1`.
For every tested candidate, the arithmetic checked all source
digit positions until the source integer became zero,
using the exact four-carry x4 transducer. This is
a **finite exclusion experiment only**, not a proof for all L.

The more important exact all-depth negative mechanism, reproduced
from `gpt6/problem406-pure-power-nonlocal-contradiction-20261030`,
is `GSTProblem406PurePowerNonlocalTransport.lean`:
for ANY finite H>=9 it constructs a literal 4^K with a
child common-two at row 4 whose three-step parent remains
BAD through row H. It invalidates any UNIFORM finite-lookahead
parent propagation but not the original fixed-exponent theorem.

## Original universal target: exact remaining noncircular dependency

Neither a rational exponential density bound nor an arbitrary
finite dyadic audit can show that every actual
single-cofactor pure power `4^K` exits the BAD tree.
One needs a mechanism coupling the whole BAD path to
the single-bit binary-origin source, with a proof at every
K-dependent terminal depth (or a genuine universal all-R
3L/2 exclusion theorem). No new axiom or renamed target
is licensed. The final challenge's binder-free `#print axioms`
and comparator are the only acceptable production upgrade.
