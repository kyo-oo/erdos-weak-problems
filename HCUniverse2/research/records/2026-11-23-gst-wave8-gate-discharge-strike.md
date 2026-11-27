# 2026-11-23 — WAVE 8: THE GATE-A FULL DISCHARGE STRIKE + THE CACHE-BANK TIMEOUT LAW

Written by the commander at the working tree (the wave-8 round), branch
`research/gpt6-gst-hypothesis-part1-chow-square-20261110`, base HEAD
`89c9d0b` (wave 8-B). Static verification only from this sandbox (the
ARSENAL law: no local Lean); the kernel verdict belongs to CI at the
pushed SHA.

## What this is

The wave that BREAKS the wave-7 residual's first item — GATE-A's full
discharge — plus the CI infrastructure repair that makes the big lanes
completable at all. Three landings:

1. **THE BREAKTHROUGH (the wave-8 meta-thinking kill)**: the wave-7
   residual ledger's verdict ("the section-decomposition needs the Proj
   universal property for morphisms INTO Proj — absent from the pinned
   Mathlib") was OVER-SCOPED. The pinned Mathlib DOES contain the
   open-RESTRICTION machinery (`research/pin/mathlib-51e6992/Restrict.lean`:
   `morphismRestrict` :569, `resLE` :775, `Scheme.topIso` :439,
   `pullbackRestrictIsoRestrict` :551, `resLE_comp_ι` :782) — and the
   gate does NOT need the universal property: it needs only the
   restriction of a ONE-POINT section to a chart basic open whose
   preimage is everything. The route was verified two-method (the W8-B
   dossier `research/records/2026-11-23-wave8-gate-restriction-dossier.md`
   — 454 lines, 26-row API table, five route cards; the commander's own
   pin-reading: `mk_mem_toSpec_base_apply` Scheme.lean:691 — the
   transport iff, `basicOpenIsoSpec_inv_ι` Basic.lean:190 — the
   chart-leg factorization) and frozen in the battle map
   `research/campaign/wave8-gate-discharge-battle-map.md` (the complete
   two-file design, every lemma's route card, the disease catalog).

2. **THE TWO NEW MODULES** (authored by the wave-8 sub-agent assault;
   both agents died of context deadline AFTER landing their files —
   the commander verified the static battery personally):

   * **`GSTFiniteLinePointsGateCore.lean`** (809 lines, 20 declarations,
     zero sorry) — FILE 1, the machinery: §0 the one-point preimage law
     (`complexBase_preimage_eq_top_of_mem`); §1 the section-into-chart
     head (`sectionInto` + `sectionInto_ι` — the topIso/resLE composite
     with the factorization receipt); §2 THE CHART LEG (`chartLeg` +
     `chartLeg_awayι` — the decomposition of an arbitrary section through
     its away chart, THE piece the wave-7 residual disclosed as open);
     §3 THE READING (`chartReading` — the Spec.homEquiv ring reading;
     `chartReading_mem` — the chartPointSpace membership; the coordinate
     identity `chartReading_eval`); §4 THE VALUE COMPUTATION AND THE
     TRANSPORT (`chartReading_ratio_eq_zero_of_mem` — the none-case
     value; `chartPoint_right_zero_mem` — the branch-decision receipt)
     through six authored in-module bridges (the Spec-map image point,
     the leg-is-the-Spec-of-its-reading counit, the kernel receipt, the
     affine basicOpen twin, the localization-element-is-chart-ratio, the
     away-transport membership iff).

   * **`GSTFiniteLinePointsGateDischarge.lean`** (976 lines, 27
     declarations, zero sorry) — FILE 2, the assembly: §1 the forward
     map (`finiteLinePointsGateForward` — the line index + the
     Option-coordinate by the left-chart branch); §2 the inverse laws
     (the mono-counit machinery: `chartLeg_eq_of_chartPointHomOf`,
     `chartLeg_eq_chartPoint`, `chartReading_of_chartPoint`, the
     LAW-R `finiteLinePointsGateForward_coordPoint` and the LAW-L
     `coordPoint_finiteLinePointsGateForward`); §3 THE GATE
     (`finiteLinePointsGate M : FiniteLinePointsGate M` — the full
     points-classification equiv) + THE UNCONDITIONAL ANALYTIFICATION
     (`finiteLineAnalytificationUnconditional` + its space receipt) +
     **THE GATE-FREE LAW**
     (`native_GST_single_fold_orbit_law_finiteLine_unconditional_gatefree`
     — the general-M NativeGSTSingleFoldOrbitLaw at the honest data with
     NO gate parameter, one substitution of the wave-7 gate-formed
     theorem).

   Both modules' honesty ledgers disclose the designated CI repair
   points (the authored bridges' defeq seams — the campaign's standard
   first-compile repair doctrine).

3. **THE CACHE-BANK TIMEOUT LAW (the CI repair)**: the two big lanes'
   runs keep dying of runner shutdown (exit 143) at ~47-48 minutes —
   BEFORE the wave-8-B `if: always()` cache-bank save can fire (the
   killed runner skips even the always-steps). The corpus recompile
   (60-90 min) can never fit the ~42-minute compile window. THE FIX:
   the internal `timeout 16800` shrunk to `timeout 2100` (35 min) in
   BOTH big lanes (`gst-finite-line-unconditional-source.yml`,
   `gst-finite-line-cycle-correspondence.yml`) and the NEW
   `gst-finite-line-points-gate-discharge.yml` lane — OUR timeout fires
   first, the step fails cleanly, the `if: always()` cache-save RUNS
   (35 min of compile progress banked), and each re-dispatch compiles
   strictly less (the corpus completes after 2-3 cycles). The discharge
   lane's compile step distinguishes real diagnostics (exit 1
   immediately) from the timeout cycle (the bank message).

## Registration

* `lakefile.toml`: `GSTFiniteLinePointsGateDischargeLib` (roots: the
  discharge + the core modules);
* CI lane: `.github/workflows/gst-finite-line-points-gate-discharge.yml`
  (the cache-bank discipline: restore-keys prefix
  `hc-lean-incremental-Linux-finite-line-points-gate-discharge` first,
  then the family chain; the save key
  `...-finite-line-points-gate-discharge-${{ github.run_id }}`; the 2100s
  timeout; the sorryAx hard-fail; the artifact upload).

## The CI ledger at the wave's write time

* GREEN lanes unchanged: point-algebra (63f6516, run 45120014552),
  analytification (63f6516, 45120014571), honest-hodge-data (63f6516,
  45120014581), points-gate cover (4cf9e85, 45186341908).
* The two big lanes at 89c9d0b: unconditional-source in flight
  (45197308649 — the last live run); cycle-correspondence died AGAIN of
  the ~47.5-min runner kill (45197293695, zero diagnostics, cache-bank
  save SKIPPED by the kill — the law this wave's timeout fix repairs);
  its superseded twin 45197281083 died identically. NO red is claimed:
  the campaign law (a lane that dies of infrastructure is NEVER assumed
  dirty) applies; both lanes re-dispatch under the timeout fix.

## The honest residual ledger (updated)

1. ~~GATE-A's full discharge~~ — THE MODULES ARE WRITTEN (zero sorry,
   the static battery clean: brackets balanced, namespace/end exact,
   every external name pin/corpus-cited). The kernel verdict belongs to
   the new CI lane at the pushed SHA; the authored bridges' defeq seams
   are the designated repair points.
2. **The ω-liveness** — unchanged (the fenced core; the research
   record's verdict stands — the ∀ω-unconditional law needs it never).
3. **The universal primitive-X source theorem** — statement design
   still open (the stub's second item; the next wave's target after the
   gate verdict lands).
