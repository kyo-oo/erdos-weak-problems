# 2026-11-23 — WAVE 9 (THE FINAL WAVE): THE UNIVERSAL PRIMITIVE-X SOURCE EXECUTED — THE CAMPAIGN CLOSES

Written by the commander (the wave-9 execution round — the campaign's LAST
wave by BOSS's order: no next wave, only the end), branch
`research/gpt6-gst-hypothesis-part1-chow-square-20261110`, base HEAD `a199257`
(wave 9 design). Static verification only from this sandbox (the ARSENAL
law: no local Lean); the kernel verdict belongs to CI at the pushed SHA.

## What this is

THE FINAL MODULE of the finite-line unconditional round:
**`GSTFiniteLinePrimitiveXSource.lean`** (646 lines, 12 declarations, zero
sorry) — the lane's second promise executed from the frozen statement
design (`research/campaign/wave9-universal-source-battle-map.md`):

* **§1 THE SOURCE FAMILIES** — `finiteLineSourceZero M i` (the
  generic-point atom of line `i`, the R₀-orbit of the honest seed) and
  `finiteLineSourceOne M i` (the closed-point atom, the R₁-orbit) — the
  explicit carriers, spelled at the world's own cycle group (the honest
  data's green seed spelling at general index).
* **§2 THE CLASS EQUATIONS** — `finiteLineSourceZero_class` /
  `finiteLineSourceOne_class`: each carrier's class under the honest
  data's cycle-class map IS the matching component/point class (the honest
  atom formulas + the prime-lattice index receipts — the honest data's own
  seed equations at every index).
* **§3 THE INDEPENDENCE** — `finiteLineSourceZero_independent`
  UNCONDITIONAL (the transported standard basis: the `Pi.basisFun` singles
  under the component H⁰ machine's linear equiv — the green corpus's own
  `GSTPositiveDimensionalLiveCoreLaw` §2 route verbatim);
  `finiteLineSourceOne_independent` at the FENCED index `hω : ω ≠ 0` (the
  green `finiteLinePointClass_indep` — the corpus's disclosed liveness
  discipline; at `ω = 0` the family is identically zero, the unguarded
  statement is false).
* **§4 THE DECOMPOSITION MACHINERY** — `pi_single_sum_eq` (the
  function-space basis expansion) + `finiteLineComponentClass_decompose`
  (the E-readout identity: every degree-zero class is the explicit
  combination of the component family with its OWN
  `componentCohomologyZeroEquivFinM` coordinates).
* **§5 THE SPAN (the source theorem)** — three sector theorems:
  weight zero (EVERY degree-zero class — the free fiber — an explicit
  combination, the E-readout coordinates), weight one (every class of the
  honest weight-one fiber — the span bigrading's own rational fiber — an
  explicit combination, via `rationalHodgeSubspace_span_eq` +
  `Submodule.mem_span_range_iff_exists_fun` consumed as rewrites), above
  (every class of every weight `p ≥ 2` is ZERO — the stash design's dead
  fiber by `rationalHodgeSubspace_stash_eq_bot`; NO cohomology vanishing
  claimed — the sphere machine stays fenced).
* **§6 THE COMPILER** — `finiteLineSourceCompilerZero` (the EXPLICIT
  readout: `E α` coordinates times the carriers) + correctness for EVERY
  degree-zero class; `finiteLineSourceCompilerOne` (the §5-witness
  coordinates — `Classical.choose` of the span certificate, the honest
  noncomputable construction; the corpus has no green degree-two
  dual-basis machine) + correctness on the fiber.
* **§7 THE MASTER PACKAGE** — `the_universal_primitive_X_source_package`:
  the 8-conjunct ∀M master at the CONSTRUCTED unconditional
  analytification — both independence certificates, all three sector
  theorems, both compiler correctness receipts, AND the gate-free law
  itself (`native_GST_single_fold_orbit_law_finiteLine_unconditional_
  gatefree`): the lane's complete promise in ONE theorem, uniform in `M`.

## THE CI CALIBRATION (the meta-thinking kill of the round)

The three big lanes at `8acf848` all died: two of the stochastic runner
shutdown (exit 143 at ~23-25 min of compile — BEFORE their own 1500s
timeout, so NOTHING banked), one of its own 1500s timeout (banked).  The
`wave-8-C` "~32-minute kill law" was UNDER-CALIBRATED — the kill window
is wider (~23-33 min).  TWO fixes landed:

1. **THE 1200-LAW**: all cache-bank lanes' internal timeout 1500 → 1200
   (20 min — below the EARLIEST observed kill with 3 minutes of margin);
   every cycle now GUARANTEED to bank before the runner can strike.
2. **THE NEWEST-BANK LAW**: the restore-keys chains collapsed to the broad
   `hc-lean-incremental-Linux-finite-line-` prefix (after the dead exact
   `general-M-law` key) — every lane now restores the GLOBALLY NEWEST
   bank (the unconditional-source lane's 175 MB+ bank was unreachable
   behind the discharge lane's own-prefix preference — the two killed
   lanes kept re-riding the older 168 MB bank).

The new lane `gst-finite-line-primitive-x-source.yml` is born with both
laws (1200s + broad-prefix restore + the cache-bank save + the sorryAx
hard-fail + the artifact upload); `GSTFiniteLinePrimitiveXSourceLib`
registered in the lakefile.

## THE REGISTRATION

* `lakefile.toml`: `GSTFiniteLinePrimitiveXSourceLib` (root: the new
  module).
* CI lane: `.github/workflows/gst-finite-line-primitive-x-source.yml`
  (path filter: the new file + its direct import chain; the cache-bank
  discipline at the corrected calibration).
* The three big lanes re-calibrated (cycle-correspondence,
  unconditional-source, points-gate-discharge): the 1200-law + the
  newest-bank law.

## THE DESIGN'S DIVERGENCES (the honesty ledger)

The frozen design's single `∀p` span statement does not typecheck (the
`Fin M`-indexed family only exists at the two live weights — at `p ≥ 2`
the summands would be ill-typed); the honest form is the three sector
theorems + the 8-conjunct master.  The design's `§1` independence without
`hω` is FALSE at `ω = 0` (the design's own honesty law anticipated the
risk: "if either resists, it is documented in the module's ledger (NOT
stated)") — the statement carries the fence.  The design's "the
coordinates are read off the honest atom evaluation (a dual-basis
readout)" at weight one was over-optimistic (no green degree-two
dual-basis machine exists in the corpus — the sphere machine is the
fenced frontier) — the honest compiler takes the §5-witness (Classical
choice); the expected `Classical.choice` axiom receipt is the honesty
marker.  The design's "p ≥ 2 vacuity by the vanishing of H^{2p}" was
over-scoped — the honest route is the stash design's dead fiber (no
vanishing proof needed or claimed).

## THE CAMPAIGN CLOSES

This is the LAST wave of the unconditional round.  The task ledger (the
campaign's final accounting, each task's CI receipt):

* TASK 1 (the honest prime lattice — the point algebra): PROVED,
  unconditional — `GSTFiniteLinePointAlgebra` CI-GREEN (run 45225257813 @
  c37bd9a; the closed/generic point atoms, the coheight/component
  receipts, the honest seeds).
* TASK 2 (the chart classification — the analytification bridge): PROVED,
  unconditional — `GSTFiniteLineRiemann` + `GSTFiniteLineAnalytification`
  CI-GREEN (run 45225257888 @ c37bd9a; the Riemann sphere coordinate
  equivalence + the gate-form assembly).
* TASK 3+4 (the canonical cycle-class maps + the two M-cycle letters):
  the modules WRITTEN, zero sorry (`GSTFiniteLineCycleCorrespondence`,
  987 lines) — the kernel verdict at CI in the cache-bank cycle at the
  pushed SHA.
* TASK 5 (the honest Hodge data): PROVED, unconditional —
  `GSTFiniteLineHonestHodgeData` CI-GREEN (run 45225257718 @ c37bd9a).
* TASK 6 (THE UNCONDITIONAL LAW): the gate discharge WRITTEN, zero sorry
  (`GSTFiniteLinePointsGateCore` 809 lines +
  `GSTFiniteLinePointsGateDischarge` 976 lines: the constructed gate, the
  unconditional analytification, the gate-free law) — the kernel verdict
  at CI in the cache-bank cycle at the pushed SHA.
* TASK 7 (the universal primitive-X source — THIS wave): WRITTEN, zero
  sorry (646 lines) — the kernel verdict at CI in the cache-bank cycle at
  the pushed SHA.

The four already-green lanes carry their receipts; the three remaining
lanes ride the corrected cache-bank cycle to their verdicts.  No next
wave is designed; the residual ledger is empty by design — the ω-liveness
stays fenced (the law is ∀ω; no nonvanishing is fabricated) and the
arbitrary-X Clay claim was never this lane's (the campaign's acceptance
discipline).
