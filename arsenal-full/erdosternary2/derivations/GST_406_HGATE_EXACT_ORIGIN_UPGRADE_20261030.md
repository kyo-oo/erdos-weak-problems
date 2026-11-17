# GST 406 hGate source-domain upgrade — strict CI 2026-10-30

## What the counterexample actually refutes

The exact source E=4339*2^24=4339*4^12 has a Happy
physical child at row 3, while R=64 E=4339*4^15 has
no Happy row at any ternary depth. Its seed has
E mod 27=1 and v2(E)=24. This falsifies the
**generalized three-step GST Happy propagation rule**
for arbitrary prefix-one, high-dyadic-order sources.
It does not falsify the main theorem for sources E=4^K:
the odd cofactor 4339 keeps E outside that domain.

Proof: GSTProblem406PrefixOneDyadicNoGo.lean.
Strict CI: https://github.com/kyo-oo/erdosternary2/actions/runs/41082831276

Independent Wolfram:
FactorInteger[E]={{2,24},{4339,1}}.
True shared-two rows for E vs 4E: {3,7,12,16,20}.
No shared-two rows for 64E vs 256E; higher rows vanish.

## What has changed in the hGate formalization

New module:
GSTProblem406HGateExactOriginUpgrade.lean

**Proved, not assumed**:

1. countermodel_not_a_four_power: for all natural K, E != 4^K.
2. countermodel_outside_exact_origin: E does not satisfy
   ExactFourPowerOrigin E.
3. exact_origin_hGate_iff_original:
   the guarded third-wave statement is exactly
   FourPowerDirectExistence, the user-requested theorem.
4. all_low_physical_exponents:
   K=5,6,8,9,10,11,12 are all directly discharged
   (and K=7 excluded by the unchanged target).
5. exact_origin_hGate_iff_strict_physical_cut:
   after the verified low cases, the original hGate is
   logically equivalent to the literal source-specific
   24/19 bounded row assertion

    ∀ K≥13, ∃ p: 1≤p<ceil(24K/19)
      and digit3(4^K,p)=digit3(4^(K+1),p)=2.

   This equivalence is now strict Lean kernel-verified,
   including its actual physical row bound.
6. corrected_scope_certificate:
   bundles source exclusion and exact bounded-gate
   equivalence without replacing the gate by a new axiom.

Strict CI PASS; no sorryAx in the declarations:
https://github.com/kyo-oo/erdosternary2/actions/runs/41090808804

## What has NOT changed

The production source questions/deepmind_problem_406/Solution.lean
still requires gst_four_power_third_wave_gate, and
ErdosTernary2.lean does not obtain that gate from the new module.

The updated module is a correct source-domain repair
and an exact reduction for future hGate attacks,
NOT a proof of the original universal theorem.

The false generalized propagation step must not be
reintroduced, even with a stronger finite binary-valuation
threshold, unless its new hypotheses are independently proven.

The remaining substantive all-K obligation is the
source-specific exclusion of a BAD trajectory for
the literal pure power 4^K, K≥13, in the physically
bounded rows. No finite search alone resolves this.
