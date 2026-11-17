# Exact Erdős 406 hGate discharge — adversarial GST kernel audit (2026-10-30)

Base: `712a0eff15566aa252e6d0fb0179920989eda211`
Research branch: `gpt6/problem406-direct-hgate-collision-audit-20261030`
Strict reproduced workflow: https://github.com/kyo-oo/erdosternary2/actions/runs/41011363348

## Mathematical contract — unchanged

Prove without extra premises the existing proposition

```lean
gst_four_power_third_wave_gate
```

which, by the green `GSTFourPowerThirdWave.thirdWave_iff_commonTwo`,
has exactly the type of

```lean
∀ K : Nat, 5 ≤ K → K ≠ 7 →
  ∃ p : Nat, 1 ≤ p ∧
    digit3 (4^K) p = 2 ∧ digit3 (4^(K+1)) p = 2
```

The final `Solution.lean` still takes `(hGate : ...)`, so a
true solution requires an independent term of the above type
followed by complete axiom auditing and checker type equality.

## New direct strict repro (three independent candidate closure stacks)

All local Lean import closures were generated and compiled by the
dedicated GitHub runner, and the original three proof files were each
typechecked with their actual definitions, without any new premise.

**A. Exact canonical signed U2D rectangle**

`GSTFinalPrefixOneDirectU2DCollision.lean:173:2`
in `canonical_right_bad_forces_weighted_cross_nonpositive`:

```text
Have: hRightPrefix: (weighted sum of right-column crossDensity) <= 0.
Have: hRect: exact rectangle identity, including interior
      reverseSurviveCode and signed potential/boundary terms.
Need: weightedCrossPrefix(left-to-right full rectangle) <= 0.
```

The right-column inequality does not by itself bound the
*whole rectangle*: `hRect` exposes additional uncontrolled
interior terms. `omega` correctly cannot deduce the
whole-rectangle sign. This is the first missing inference in this
candidate proof, not a syntactic problem. The later theorem
`canonical_perfect_power_block_collision_direct` depends on
`sorryAx` because of this failure.

**B. Perfect-power x4^3 propagation**

`GSTInfiniteFourPowerNavigation.lean:176:2`, theorem
`power_three_step_collision`:

The original physical source `E=4^K`, a left Happy row,
the hypothetical right all-depth BAD packet, an exact width-three
conservation identity, signed phase windows and the U-potential
telescope do *not* yield a contradiction by the final
`four_power_collision_arith` (linarith fails). No existing sign
invariant for the complete interior packet was provided.
Thus `four_power_happy_ge_three` and the purported
`GSTFourPowerDirectExistenceFromHappy.fourPowerDirectExistence_closed`
are NOT kernel-verified and carry `sorryAx`. The useful structural
identity `4^(K+3)=64*4^K` is proved; source-specific Happy
propagation across it is not.

**C. Residual perfect-power binary boundary**

`GSTFinalResidualCollision.lean:128:4` and `:174:4`:
both Null and Plus branches end in unsolved `False`.
The obtained binary first-boundary certificate does not imply
the forbidden two-bit right chord (both digit6 and digit8 are 2).
One constraint even says a relevant digit belongs to {0,1};
this is not a contradiction without an independent forcing
equation. `omega` exhibits satisfiable linearized bounds.
No source-specific bridge to the forbidden chord is proved.

## Historical circularity confirmed

`ErdosTernary2.lean` has a QUARANTINED (commented-out)
earlier alleged unconditional induction. Its
`gst_oscillation_from_navigation` now demands an explicit
`hnav` witness of the exact missing form and concludes `exact hnav`.
The older claimed generic oscillation implication is false
(e.g. R=7 with the original cited N/start), and cannot be
used without a new noncircular physical-origin argument.

The older `de11dc2c5ee340fee1929ba2adc6834a72ab9879`
comparator era had `gst_four_power_direct_existence_inline` as
a custom axiom. Its historical PASS did not remove this axiom.

## Exact outstanding mathematical task, not a new hypothesis

A rigorous origin-specific theorem would have to show at least
one of:

- On the literal perfect-power transition `4^K → 4^(K+3)`,
  a left Happy source cannot coexist with all-depth right BAD,
  using a mathematically derived cross-column invariant that
  controls the missing interior terms.
- Alternatively, directly rule out an all-row BAD trace for
  each literal original source `4^K`, without assuming the
  predicate or replacing it by an abstract 3-adic source.

Neither candidate has been established by this audit.
Do not transplant the three unverified declarations into
production, weaken the original theorem, or silently
reintroduce `hGate` as another theorem/axiom.

**VERDICT:** The original universally quantified Erdős 406 gate
has not been discharged. All three direct proposed proof seams
still have explicit noncircular mathematical obligations.
This is an exact countercheck of claimed proof dependencies,
not a counterexample to the conjecture and not a new universal
mathematical theorem.
