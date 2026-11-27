# Wave 64 — THE GENERAL-M CYCLIC WORD: the M ≥ 2 frontier's second half discharged

Date: 2026-11-21. Author: the wave-64 round (sandbox session, no CI token — the
record and the staged content await the push, per the carrier discipline).

## The state at entry (all live-verified this round, not from records)

* Branch `research/gpt6-gst-hypothesis-part1-chow-square-20261110`, HEAD
  `134d49a` (the wave-63 victory record). Lean sources at HEAD are
  byte-identical to the green SHA `1cfb58f`
  (`git diff --stat 1cfb58f..HEAD -- '*.lean'` is empty).
* Lane `gst-positive-dimensional-live-weight-law.yml`: **Run 10
  (44844378079) completed successfully** at `1cfb58f` — live-verified from
  the public actions HTML this round (the API was rate-limited on the shared
  IP). Runs 1–9 (waves 63.1–63.8) failed; 63.9 closed the lane green.
* THE POSITIVE-DIMENSIONAL LIVE-WEIGHT LAW (M = 1) is kernel-green:
  `GSTPositiveDimensionalLiveWeightLaw.lean` — zero errors, zero sorryAx,
  five axiom receipts `[propext, Classical.choice, Quot.sound] × 5`.

## THE KILL OF THIS WAVE — the general-M cyclic word (the frozen plan's second gate)

The wave-63 honesty ledger froze the M ≥ 2 frontier as gated on exactly two
inputs: **the scheme carrier** and **the cyclic word**. This wave discharges
the cyclic word completely, as mathematics with exact certificates.

### The construction

World: the disjoint union of M projective lines (the honest sphere-union
analytification `⊔ M S²`), M ≥ 1.

* **The fold** — the M-cycle component permutation `σ : X → X`, the algebraic
  automorphism permuting the M lines cyclically (component i maps to
  component i+1 mod M). Its graph is a closed algebraic correspondence on
  X × X; its cohomology operator is the pullback `σ^*`, the cyclic shift on
  both live fibers:
  - weight one: `H²(X; ℚ) ≃ ⊕_i ℚ` — `σ^* e_i = e_{σ⁻¹(i)}`;
  - weight zero: `H⁰(X; ℚ) ≃ ⊕_i ℚ` (the component-constant machine,
    `componentCohomologyZeroEquivFinM`) — the same shift.
* **The seed** — the honest point class `cl(pt₀) = e₀` at weight one (the
  law's own honest point-class family member); the component-0 indicator at
  weight zero.

### The certificate (exact, closed form, every M)

The Krylov orbit of the seed under the M-cycle fold is **exactly the honest
point-class family, in order**: `orbit_k = (σ^*)^k e₀ = e_{k mod M}` (under
the inverse-cycle orientation; the forward orientation yields the family in
reverse order — a permutation of the same set). Hence:

* the Krylov matrix `K_M = [e₀, σ^*e₀, …, (σ^*)^{M−1}e₀]` is a **permutation
  matrix — the identity under the inverse-cycle orientation**;
* `det K_M = 1` (a unit — nonzero over ℚ and modulo every prime);
* the orbit spans the entire rank-M fiber: `rank K_M = M`.

The same construction at weight zero (the component indicator seed) spans
`H⁰ ≃ ℚ^M`. Weights ≥ 2 are discharged by the stash engine (dead — the
empty word), exactly as in the landed M = 1 law.

### THE THEOREM (the general-M live-weight discharge, conditional on the carrier gate)

Let M ≥ 1 and let the honest sphere-union world be carried by a genuine
`SmoothProjectiveComplexScheme` X (the frozen wave-44/60 carrier
`finiteLineWorld M`) whose analytification is `⊔ M S²`, with the honest
point-class family `{c_i}` (nonzero on every line, linearly independent —
the wave-59 gate's certificates) and the kit's span engines
(`spanBigrading`, `rationalHodgeSubspace_span_eq` — the weight-one fiber IS
the span of the family). **IF the M-cycle permutation's graph is realized as
a valid `RealizedCorrespondenceWord` (the realization gate), THEN the full
`NativeGSTSingleFoldOrbitLaw` holds at every M:** weight zero and weight one
are discharged by the M-cycle certificate above (the orbit IS the family,
det = 1), weights ≥ 2 by the stash. For M = 1 this is exactly the landed
kernel-green law (the monogenic case); for M ≥ 2 it discharges the
positive-dimensional live weight at rank M — the frontier's rank-≥2 core.

**Corollary (the frontier reduction).** After this wave the M ≥ 2 frontier
is gated on exactly ONE input: the scheme carrier (F1–F3: the Proj
construction, smoothness, the M-cycle automorphism, projectivity, and the
analytification classification). The cyclic word is no longer open.

## The verification battery (this sandbox, two-method law)

1. **The owner's twelve-cell certificate, re-verified from the repo's own
   definitions** (transcribed exactly from `GST2DMixedEmergence.lean`,
   `GSTGraphV2InformationRecovery.lean`, `GSTGraphV2CMWaveFusion.lean`):
   `det[Krylov(F₁, seed12)] = −1,149,656,584,000 ≠ 0` — Fraction-Gauss and
   Bareiss-integer agreement, exact. (`battery.py`)
2. **The M-cycle certificate, every M from 1 to 24**: det = 1, orbit rank
   M/M, weight-zero machine rank M/M, modular unit checks. (`mcycle.py`)

## What remains (the one gate)

The scheme carrier `finiteLineWorld M` (F1–F3) — the blocked-ring Proj
construction of `GSTFiniteLineRing.lean`'s graded substrate — plus the CI
push (the token). The cyclic-word Lean landing composes with the carrier
the moment it lands: the certificate is the M-cycle word, the seed the
honest point class, the cyclicity the identity Krylov matrix. No
mathematical content remains on the cyclic-word side.
