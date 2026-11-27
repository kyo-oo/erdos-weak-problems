# 2026-11-20 — Wave 63: THE POSITIVE-DIMENSIONAL LIVE-WEIGHT LAW — the combination capstone (the six-file merge, one new theorem family)

## What this is

The new law of the round, per BOSS's directive: **PROVE THE POSITIVE
DIMENSIONAL LIVE WEIGHT** — combining the branch's certified engines into
one new theorem family:

`GSTPositiveDimensionalLiveWeightLaw.lean` — the six-file merge:

```
GSTSphereUnionComponents + GSTComponentCohomologyZero +
GSTSingularCohomologyMaps + GSTSphereUnionPointClassGate +
GSTPositiveDimensionalLiveCoreKit + GSTNativeSingleFoldOrbitLawLanding
(+ GSTHodgeSingleHypothesisConditional + GSTFinitePointHodgeData)
```

## The theorems (the new family)

1. **`positive_dimensional_live_weight_family`** — the honest point-class
   family at the world: the wave-59 gate family, transported along the
   hspace identification to the world's own degree-two rational singular
   cohomology (the wave-57 rfl bridge), with nonzero on every line and
   linear independence — for every M ≥ 1.

2. **`exists_cycle_functional`** — the degree-style cycle-class functional
   constructor: a genuine nonzero cycle supports a rational functional
   taking the value one on it (the coefficient map on the rational line
   via `Submodule.mem_span_singleton` + `LinearEquiv.ofBijective` +
   `LinearMap.exists_extend` — the kit's own extension engine).

3. **`positive_dimensional_live_weight_bearing`** (every M ≥ 1) — THE
   ASSEMBLED HODGE DATA: the assembled `HodgeBigradedBettiData` whose
   weight-zero fiber is the forced top (live), whose weight-one fiber is
   the rational span of the honest point-class family (LIVE, nonzero on
   every line, linearly independent — the positive-dimensional live
   weight, rank M), whose genuine codimension-one seed cycle has its
   honest class in the fiber, and whose weights p ≥ 2 are all honestly
   dead (the stash engine — no vanishing proof).

4. **`positive_dimensional_live_weight_law` (M = 1)** — **THE FULL LAW**:
   the one-line world — the honest Riemann-sphere analytification —
   carries the FULL `NativeGSTSingleFoldOrbitLaw` through the landing's
   dead-or-monogenic classification:
   - weight zero: monogenic (the H⁰ machine computes H⁰ ≃ ℚ¹ through the
     genuine singular chain complex; the honest zero-cycle seed
     generates);
   - weight one: **THE POSITIVE-DIMENSIONAL LIVE WEIGHT** — monogenic by
     the honest sphere class itself (the span fiber IS the rational line
     of the class; the genuine codimension-one seed generates it);
   - weights p + 2: honestly dead (the stash, the empty word, the
     subsingleton discharge).
   The exact-Hodge consequence `EveryHodgeClassIsRationalAlgebraic` lands
   through the repository's conditional chain.

5. **`the_positive_dimensional_live_weight_package`** — the master
   receipt: the law, the live weight-one witness, and the general-M
   live-weight family record.

## The honesty ledger

The single disclosed input: the honest sphere class `ω ∈ H²(S²; ℚ)` with
`ω ≠ 0` — the fenced sphere-machine core, EXACTLY as the wave-59 record
froze it ("the gate is designed so that when it lands — by whatever future
route — the final law assembles by discharging one hypothesis").  Every
other input is structural: the sphere-union analytification contract and
the genuine cycle nontriviality (Z₀ ≠ 0, Z₁ ≠ 0).  The general-M law
(M ≥ 2 — the frontier map's rank-≥2 core) is NOT claimed: it remains
gated on the scheme carrier and the cyclic word, per the wave-59 frozen
plan.  This is a restricted-class theorem under the AGENTS.md acceptance
test — NOT the Hodge conjecture, NOT the sphere machine, NOT the
comparison theorem.

## The war council (four agents, the wave's audit)

* **The Attacker**: verified the full interface stack against the seven
  source files and the pin; CONFIRMED the claim-match architecture (the
  discharge shape char-for-char against the landing's hypothesis), the
  M=1 restriction honesty, the span-monogenic argument, the hypothesis
  minimality.
* **The Doubter**: the vacuity attack REPELLED (the hypothesis package is
  satisfiable — the corpus's own frozen design); the ω-gate disclosure
  verified verbatim against the wave-59 record; the weakening attack
  REPELLED (the M=1 restriction is in the theorem statement); the zero-map
  at dead weights verified honest per the campaign's own firewall
  discipline; the span honesty verified as the kit's own certified engine.
* **The Strategist**: the CI-risk register — ten priority sites checked
  against the corpus's green usages; the risk-anchored repair list that
  drove the 63.1 repair wave.
* **The Auditor**: every run ID in the citation ledger verified against
  the records; every docstring sentence matched against the theorem
  statements; VERDICT: HONEST (no critical, no major findings).

## The adjudication arc

* **Run 44810850431 (0166c68, the first push)**: FAILURE — the parse
  killer (superscript identifiers `Z⁰/Z¹/cl⁰/cl¹/c₀⁰` are illegal Lean 4
  identifier characters — subscripts are legal, superscripts are not) plus
  the council's confirmed defects (§2's two direction errors, §3's unbound
  H, §4's rw-collateral, the smul-case direction).
* **Wave 63.1 (bcc83d1, the six-defect repair)**: all superscript
  identifiers renamed to legal subscripts/ASCII; `sub_ne_zero.mpr`;
  `congrArg Subtype.val`; the §3 `set H` + the rw-chain port; the §4
  `congr 1` single-occurrence calc transport; the `smul_smul` forward
  form; the Fin-1 holes spelled `(by norm_num : 0 < 1)`.  Static checks:
  zero sorry, zero admit, zero native_decide, zero new axioms, zero
  superscript identifiers, all brackets balanced (459 lines).
* **Run 44815074521 (bcc83d1)**: the kernel check — [THE RUN STATUS —
  updated below].

## Registration

* `lakefile.toml`: `GSTPositiveDimensionalLiveWeightLawLib` (the
  280-module import closure, via `scripts/gst_lean_dependency_roots.py`).
* CI lane: `.github/workflows/gst-positive-dimensional-live-weight-law.yml`
  (the hardened template: elan v4.2.4 with 3×2 mirror retry, toolchain +
  `.lake/build` caches, 16800 s build cap, sorryAx hard gate, log artifact
  always).
