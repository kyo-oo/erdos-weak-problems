# 2026-11-19 — Wave 60: the positive-dimensional law LANDING (F7-F9) — GREEN, the complete reduction certified

## THE VERDICT (final, end of round)

* **F7 `GSTCyclicOrbitSpan.lean` + F8/F9
  `GSTPositiveDimensionalLawLanding.lean` — GREEN** (run 44642555839,
  the five-adjudication arc 44618664563 → 44624313890 → 44629232343 →
  44639002274 → 44642555839: zero errors, zero sorry; the law, the
  master package, and both cyclicities depend only on `[propext,
  Classical.choice, Quot.sound]`).

**THE POSITIVE-DIMENSIONAL LAW'S ENTIRE REDUCTION IS NOW CERTIFIED.**
Given the two letter gates + the two seed gates + the bigrading design,
the FULL `NativeGSTSingleFoldOrbitLaw` on the sphere-union world is
proved — and the ω-core is needed only for the LIVENESS receipts.

### The adjudication arc's root-caused diseases (the repair ledger)

* 60.1 (run 44618664563): the successor-split rewrite consumed the
  `M - t` pattern before `hsub` could fire (the residual `w + 1 - 1`
  closes by `Nat.add_sub_cancel`); the pin's mod-lemma spellings
  (`add_mul_mod_self_left` is `(a + n * b) % n`); the range-membership
  goal sits under a beta-redex (a `show` bridge surfaces the pattern).
* 60.2 (run 44624313890): the mod-lemma name swap — the arithmetic
  key's `(t + X * M)`-shape with modulus SECOND is
  `Nat.add_mul_mod_self_right`.
* 60.3 (run 44629232343): the tuple-with-ascription parse failure
  (`(1 : ℚ, R)` swallows the comma — every word respelled
  `((1 : ℚ), R)`); the missing `open GSTGeometricRealizationStage2D`;
  the span-image destructure's three-level template pattern; the
  cons-proof order swap; `apply_symm_apply` (not `symm_apply_apply`);
  `haveI` + `@Subsingleton.elim` (a Subsingleton hypothesis is a
  proposition, not a function).
* 60.4 (run 44634998857): the line-broken `.hodgeOrbit` projections
  parse as applications to dot-terms (same-line discipline); the
  independence statement takes the INDEX and then the membership; the
  empty-sum closes at the TERM level (the local `Finset.sum_empty`
  unifies first-order where rewrite/simp matches stall); the directed
  residue extraction; the direct classical pair-construction from
  ¬Subsingleton (the pin's `exists_pair_ne` spelling).
* 60.5 (run 44639002274): the forward explicit
  `Function.iterate_succ_apply'` (the reversed form substitutes a bare
  metavariable pattern); the pin's `Finset.sum_empty` takes no explicit
  function argument; the beta-reduced hypothesis takes the directed
  `if_pos rfl` directly; the RAW `Pi.single_apply` rewrites avoid
  simp's condition-normalization.

## WHAT LANDED THIS ROUND

**F7 — `GSTCyclicOrbitSpan.lean`** (the pure-algebra core):

* `cyclicPred_iterate_val` — the closed form: the n-th iterate of the
  cyclic predecessor started at 0 is `(n * (M - 1)) % M` (each step adds
  `M - 1` — the additive inverse of 1 mod M — and `Nat.mod_add_mod`
  accumulates the partial sums; the step's regrouping closes by `ring`);
* `arith_key` (private) — for `t < M`: `(M - t) * (M - 1) = (M - t - 1) * M + t`
  (the successor split `M - t = w + 1` removes every truncated subtraction,
  then `ring`);
* `exists_iterate_cyclicPred` — the orbit of 0 under the iterated
  predecessor visits EVERY index (target 0 at step 0; target `t > 0` at
  step `M - t`, where the closed form lands on the arithmetic key and
  `Nat.add_mul_mod_self_left` + `Nat.mod_eq_of_lt` reduce it to `t`);
* `span_range_cyclicIterate` — THE CYCLIC-ORBIT SPAN LAW: for any family
  `c` in any ℚ-module, the span of `n ↦ c ((cyclicPred M)^[n] 0)` is
  exactly the span of `c` (the orbit's range contains every `c i` by
  surjectivity; every orbit value is a value of `c`).

**F8/F9 — `GSTPositiveDimensionalLawLanding.lean`** (the closing module):

* §0 the raw/world transport: `rationalSingularCohomology_two_eq` (the
  corpus's `singularCohomologyOf_eq` rfl-chain + the space identification),
  `sphereUnionCoe`, the world family `spherePointClassWorld`, and the
  derived letter equation `spherePointClassWorld_rotate_of_pullback` (the
  green `cycle_pointClass` under the pullback-operator gate — the honesty
  documentation that the letter gate is exactly the green gate calculus);
* §1 the component family `sphereComponentClass` (the green component H⁰
  machine through `sphereUnion_cohomology_zero`) + the H⁰ spanning receipt
  `span_range_sphereComponentClass` (the 0-dim lane's span-image chain);
* §2 the designed weight-1 fiber equation `rationalHodgeSubspace_one_eq_span`
  (the kit's span engine `rationalHodgeSubspace_span_eq`);
* §3 the single-letter word algebra `realizedWordPair_single_`
  `cohomologyOperator` (`1 • T + 0 = T` through the word algebra's
  add/smul/zero);
* §4 THE WEIGHT-1 CERTIFICATE: the word-Hodge field (the letter rotates the
  family, hence preserves its span — which IS the fiber), the seed-Hodge
  field (the 0-th point class generates the span), the certificate, the
  orbit theorem (the orbit IS the rotated family), and the cyclicity
  (`span_range_subtype_eq_top_iff` + the cyclic-orbit span law);
* §5 THE WEIGHT-0 CERTIFICATE (mirror): the fiber is `⊤` for ANY Hodge
  data (`rationalHodgeSubspace_eq_top_of_degree_zero` — the 0-dim lane's
  generic law), the orbit theorem, the cyclicity (the component family
  spans H⁰);
* §6 **THE LAW**: `native_GST_single_fold_orbit_law_of_sphereUnion_gate` —
  the full `NativeGSTSingleFoldOrbitLaw` for the sphere-union world, given
  the two letter gates + the two seed gates + the bigrading design;
* §7 THE LIVENESS RECEIPTS: `spherePointClass_pair_ne` (the raw 0-th/1-st
  point classes differ — a nontrivial `(1, -1)`-relation would contradict
  the green gate independence), `spherePointClassWorld_pair_ne` (cast
  injectivity), `sphereComponentClass_pair_ne` (the component iso sends
  them to distinct indicators), `weightZero_fiber_not_subsingleton`,
  `weightOne_fiber_not_subsingleton` (the ω-gated receipt);
* §8 **THE MASTER PACKAGE**: `positive_dimensional_package_of_sphereUnion_gate`
  — the law + the exact-Hodge consequence + both liveness receipts + the
  no-free-lunch nonzero algebraic class (through the landing module's own
  green `exists_nonzero_algebraic_hodge_class_of_law`).

## THE ω-DISCLOSURE (stronger than the frozen design)

The frozen design placed the honest sphere class `ω ≠ 0` INSIDE the law's
gate.  This round's analysis found the truth is better: **the law does not
need it.**  The law's content at the live weight is the Krylov cyclicity of
the designed fiber, and cyclicity is a statement about the SPAN of the
point-class family — no nonvanishing required.  The ω-core enters exactly
one place: the LIVENESS receipts (the weight-1 fiber is not a subsingleton;
the no-free-lunch nonzero algebraic class).  Consequence: the
positive-dimensional law's remaining dependence on the fenced
sphere-machine core is exactly its honesty content, not its law content.

## THE GATES (the remaining classical inputs, precisely fenced)

1. THE LETTER GATES: genuine `RealizedFiniteClosedCorrespondence`s at
   weights 0 and 1 rotating the two honest families by the cyclic
   predecessor.  For the planned carrier: the graphs of the M-cycle
   automorphism; the derived-form lemma documents that the family equation
   is the green `cycle_pointClass` calculus.
2. THE SEED GATES: honest cycles whose classes are the 0-th component
   class (the generic-point cycle of the 0-th line) and the 0-th point
   class (a closed point on the 0-th line).
3. THE BIGRADING DESIGN: the span bigrading at weight 1 (honest for the
   curve world: all of H² is (1,1), spanned by the point classes) and the
   stash bigrading at weights ≥ 2 (honest for dimension reasons; free of
   vanishing proofs by the kit's engine).

## The state of the target (end of round)

| Target component | State |
|---|---|
| The kit (algebra engines) | GREEN (run 44382896351) |
| The component H⁰ machine | GREEN (run 44545624743) |
| The sphere-union component machine | GREEN (run 44545624743) |
| THE UNCONDITIONAL LIVE RANK-M ≥ 2 CORE | GREEN (run 44545624743) |
| The merged law + the sphere-union plug-point | GREEN (run 44545624743) |
| The maps module (wave 57) | GREEN (run 44601531424) |
| The point-class gate calculus (F1-F3) | GREEN (run 44604829367) |
| The cyclic-orbit span law (F7) | **GREEN (run 44642555839, this round)** |
| The law landing (F8/F9) | **GREEN (run 44642555839, this round)** |
| The honest sphere class ω ≠ 0 | THE FENCED CORE — needed only for LIVENESS now (not the law); the excision/comparison frontier |
| The scheme carrier `finiteLineWorld M` | the priced 6-10-wave battle (Route A) — supplies the letter/seed gates + the points classification |
| The carrier-side gate discharge | the plug-in design frozen: this module's gate fields are the carrier's construction targets |

## NEXT WAVES (the frozen order)

1. The carrier waves (F4-F6, Route A): the blocked-ring Proj, smoothness,
   projectivity, the M-cycle endomorphism, the ℂ-points classification,
   the analytification receipt, and the gate discharges (the letters as
   graphs of the M-cycle; the seeds as the honest point/component cycles).
2. The ω-core remains the campaign's fenced frontier (the liveness
   content): the sset-side computation (free) + the comparison theorem —
   or any future Mathlib upgrade that ships excision.

## PORT RISKS (all discharged in the GREEN arc)

* (LAW-1) the `rw [← singularCohomologyOf_eq]`-surfacing — FIRED GREEN;
* (WORD-1) the cons-equation `rfl` of `realizedWordPair` on the singleton
  list — FIRED GREEN;
* (STEP-1) the orbit-step `show`-bridges — FIRED GREEN;
* (SPANIMG-1) the component-family image-membership `rfl`s — FIRED GREEN
  (after the three-level destructure);
* (INJ-1) the `Equiv.injective` application up to the two local deltas —
  FIRED GREEN.

No `sorry`, no new axioms, no `native_decide`.  The GitHub CI lane
`gst-positive-dimensional-law-landing.yml` owns the kernel check.
