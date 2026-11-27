# 2026-11-23 — WAVE 7: THE TWO M-CYCLE LETTERS + THE POINTS-GATE COVER + THE GATE-FORMED UNCONDITIONAL SOURCE

Written by the commander (the wave-7 round) at the working tree, branch
`research/gpt6-gst-hypothesis-part1-chow-square-20261110`, base HEAD
`115f96f` (wave 6-G, the Riemann-green round).  Static verification only
from this sandbox (the ARSENAL law: no local Lean); the kernel verdict
belongs to CI at the pushed SHA.

## What this is

The GATE-L completion wave + the GATE-A cover strike + the Task-6
module's real body — the three landings of the wave-7 sub-agent assault
(4 agents dispatched per the standing wave order; W7-A died of context
deadline and its kill was taken by the commander personally; W7-B and
W7-D landed; W7-C's audit was taken by the commander in Third-Eye mode):

1. **`GSTFiniteLineCycleCorrespondence.lean` §3 (W7-A, the commander's
   kill)** — THE TWO M-CYCLE LETTERS: `finiteLineCycleLetterOne` (weight
   one: the graph correspondence of the M-cycle endomorphism with the
   sphere-cycle pullback `cohomologyPullbackOf (sphereCycle M) 2` as the
   cohomological operator) and `finiteLineCycleLetterZero` (weight zero:
   the same graph with the component-iso index shift — the conjugate of
   the `cyclicSucc`-precomposition through
   `componentCohomologyZeroEquivFinM`), both
   `RealizedFiniteClosedCorrespondence (finiteLineWorld M)
   (finiteLineHodgeDataHonest M (finiteLineAnalytificationOfGate M gate)
   (finiteLineAnalytificationOfGate_space M gate) ω) p`, both realized
   on points, with the rotation equations
   `finiteLineCycleLetterOne_rotate`/`finiteLineCycleLetterZero_rotate`
   in the engine's exact spelling.

   THE GATE-FORM DESIGN (the wave's decisive move): the letters take
   `gate : FiniteLinePointsGate M` as a parameter and are stated at
   `finiteLineAnalytificationOfGate M gate`, whose space
   `finiteLineSpace M` is DEFINITIONALLY `TopCat.of (sphereUnionSpace
   M)` (the `rfl` receipt at :423-426) — at this analytification every
   world/raw transport is definitional (the delta chain
   record-field → `finiteLineSpace` → `TopCat.of`), so the weight-one
   operator IS the pullback definitionally (`finiteLineCycleLetterOpOne
   := cohomologyPullbackOf (sphereCycle M) 2` — no cast records, no
   transport-linearity war), the weight-one rotation rides the
   transport receipt + the green `cycle_pointClass`, and the weight-zero
   rotation is pure linear algebra (the `Pi.single` rotation through
   `cyclicSucc_cyclicPred`/`cyclicPred_cyclicSucc` — no cohomology
   machinery at all, bypassing the pullback-component compatibility
   battle entirely).

   The realization chains: the graph's native image =
   `nativePointPushforward` (`graphCorrespondence_nativePointImage_eq`),
   the pushforward = the image atom (§1's residue-weight-one +
   §2b's coheight preservation inside `nativePointPushforward_eq`), the
   honest atom formulas evaluate the atoms' classes as the
   point/component classes of their lines, L6/L3 rotate the indices, the
   honest world bridges land the families, and the operators' rotations
   close the equations.

2. **`GSTFiniteLinePointsGate.lean` (W7-B, 602 lines, 20 declarations)**
   — THE POINTS-GATE COVER STRIKE: the variable cover of every complex
   point's image (`finiteLineComplexPoint_cover`, ideal- and
   `D₊`-forms), the unique-line law (a point on two lines forces the
   lines equal), the on-line characterization, and the section-side
   line-index machinery — the battle map's step (1) CLOSED at the point
   level.  The honest residual (steps 2-3, the full equiv): the
   section-decomposition — factoring an arbitrary section through
   `Proj.awayι` — needs the Proj universal property for morphisms INTO
   Proj, ABSENT from the pinned Mathlib (verified at
   `research/pin/mathlib-51e6992/Basic.lean`: only the construction
   direction `fromOfGlobalSections` exists, no converse); the frozen
   `finiteLinePointsGate`/`finiteLineAnalytificationUnconditional`
   names are honestly NOT stated — the residual is documented in the
   module's own ledger.  Registration: `GSTFiniteLinePointsGateLib`
   (lakefile :1675) + the lane
   `.github/workflows/gst-finite-line-points-gate.yml`.

3. **`GSTFiniteLineUnconditionalSource.lean` (W7-D's body, restated by
   the commander to the gate form, 296 lines)** — THE GENERAL-M LAW,
   GATE-FORMED: `native_GST_single_fold_orbit_law_finiteLine_unconditional
   (M) [NeZero M] (gate) (ω) : NativeGSTSingleFoldOrbitLaw (finiteLineWorld
   M) (finiteLineHodgeDataHonest M (finiteLineAnalytificationOfGate M
   gate) (finiteLineAnalytificationOfGate_space M gate) ω)` — a single
   exact instantiation of the wave-60 engine with all sixteen named
   arguments: GATE-L discharged by the §3 letters + rotations (W7-A),
   GATE-S by the honest seeds + the honest seed equations (the honest
   data's own receipts), GATE-A at the gate form (the `rfl` space
   receipt).  The consequences (exact Hodge + finite rational
   combination) and the master ∀M package ride the repository's
   conditional chain fed the law instance.  The stub is superseded; the
   module is decoupled from the cover file (no
   `GSTFiniteLinePointsGate` import — the gate-form needs only the
   analytification module, transitively imported through the cycle
   module).

## The CI ledger at the wave's write time

* The pre-wave state: the analytification lane GREEN at HEAD 115f96f
  (run 45107965587); the honest-hodge-data lane GREEN at ff48e2f (run
  45093883420); the world-discharge lane GREEN at 35aa0dc (run
  45090036794); the cycle lane's last REAL verdict the 9-error catalog
  of run 45097543257 at 6c9bc8a — every one of the nine addressed by
  wave 6-D's contravariant-API rebuild, but the lane's later runs (36bcdf4,
  the unconditional-source chain runs at 9555112/76df4d8/115f96f) all
  DIED mid-compile of infrastructure (step-6 `None`, no diagnostics
  artifact — the exit-143 masked-defect class; the campaign law applies:
  a lane that dies of infrastructure is NEVER assumed clean, and none is
  claimed).
* This wave's push carries: the §3 letters (987-line cycle module), the
  cover module (602 lines), the gate-formed unconditional source (296
  lines), the lakefile entry, the new lane.  The expected verdicts if
  the batch lands: the cycle lane's §3 receipts
  (`finiteLineCycleLetterOne`/`Zero` + rotations → `[propext,
  Classical.choice, Quot.sound]`), the unconditional-source lane's
  three theorem receipts, the points-gate lane's cover receipts.
  The designated CI repair points (the honest risk ledger):
  (a) §3's delta-unification at the gate form
  (`finiteLineGate_cohomology_two_defeq`'s `rfl` — the transport
  receipt's `rfl` is the one deep-defeq bet of the design);
  (b) the engine's `hspace`/seed-spelling unifications (LAW-A/LAW-S —
  the green wave-68 pattern); (c) the cover module's three flagged
  repair points (the carrier-X defeq, the `p.1 x` coercion shape, the
  `rw [Proj.mem_basicOpen]` matching).

## Registration

* `lakefile.toml`: `GSTFiniteLinePointsGateLib` (:1675); the existing
  `GSTFiniteLineCycleCorrespondenceLib` (:1657) and
  `GSTFiniteLineUnconditionalSourceLib` (:1669) own the other two.
* CI lanes: `gst-finite-line-cycle-correspondence.yml` (the §3 push
  re-triggers it), `gst-finite-line-unconditional-source.yml` (its path
  filter already carries the cycle module + the honest data + the
  analytification + the discharge chain), and the new
  `gst-finite-line-points-gate.yml` (the cover module + its direct
  import chain).

## The honest residual ledger (the assault's open front)

1. **GATE-A's full discharge** — the points-classification equiv
   (battle-map steps 2-3: the section-decomposition through the Proj
   universal property; the two-chart consistency; the assembly).
   Until it lands, the unconditional source stays gate-formed — one
   line of substitution (the gate term) completes it.
2. **The ω-liveness** — the canonical nonzero sphere class (the fenced
   core); the law and consequences are ∀ω-unconditional already, the
   liveness receipts stay ω-gated.
3. **The stub's "universal primitive-X source" theorem** — the lane's
   job title's second item; the next wave's target after the gate.
