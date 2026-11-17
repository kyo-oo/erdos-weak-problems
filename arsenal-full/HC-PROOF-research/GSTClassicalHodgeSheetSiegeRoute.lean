import GSTClassicalHodgeOmniversalNativeOrbitSeparation
import GSTClassicalHodgeOmniversalSeparatorGhostCrown
import GSTClassicalHodgeBranchPacketPlaneRealization
import GSTClassicalHodgeProjectiveDegreeTrace
import GSTClassicalHodgeRelativeSuccessorExactStratum
import GSTClassicalHodgeRelativeSuccessorLowerBound
import GSTClassicalHodgeRelativeSuccessorProjectivePrime
import GSTClassicalHodgeRelativeSuccessorNonempty
import GSTClassicalHodgeSeparatorRelativeCoheightOne
import GSTClassicalHodgeNativePointSeedDegreeUpgrade
import GSTClassicalHodgeCodimensionPointTower
import GSTClassicalHodgeStage2GSemanticRigidity

/-!
# GST CLASSICAL HODGE — SHEET SIEGE ROUTE (ROUTE S), V2

Companion module to `docs/GST_ROUTE_S_SIEGE_STUDY_20261007.tex`.

## STATUS (AUTHORITY 005 AUDIT — READ BEFORE USING)

This module decommissions the branch-packet law D
(`GSTBranchPacketPlaneRealization` = `GhostSeedTargetStrictClosure`, `rfl`)
as a *proof target* and installs the sheet siege in its place.  Nothing here
assumes D, and nothing here quantifies over ghosts in a premise.

V2 (lemma-attack turn, research Tasks 5-a/5-b/5-c) banks everything the
omniverse already proves around the three load-bearing lemmas, and shrinks
each lemma to its exact irreducible residue.

| Statement in this file | Status |
|---|---|
| `hodge_of_geometricPlaneCompleteness` | CITATION-COMPLETE (proof = two existing theorems) |
| `sheetSiege_sheet_mem_orbitSet` | CITATION-COMPLETE (orbit membership by definition) |
| `sheetSiege_sheet_mem_orbitModule` | CITATION-COMPLETE (span + subset_span) |
| `sheetSiege_successor_coheight_ge` | **THEOREM (V2)** — the lower-bound half of L1, for every finset member |
| `sheetSiegeCoheightAdditivity_iff_upperBound` | **THEOREM (V2)** — L1 is *equivalent* to its upper-bound half alone |
| `sheetSiege_separatorSuccessorExact_of_coheightAdditivity` | **THEOREM (V2)** — L1 implies the single-successor form that discharges every downstream `hExact` premise |
| `sheetSiegeLiveWeightSeeds_false_of_zeroCycleClassData` | **THEOREM (V2, FIREWALL)** — the unguarded L2 statement is refutable on the zero-cycle-class world |
| `sheetSiegeLiveWeightSeedsGuarded_of_spine_degreeTrace` | **THEOREM (V2)** — guarded L2 from spine + degree trace, one line |
| `sheetSiegeLiveWeightSeeds_of_spine_degreeTrace_uniformSurvival` | **THEOREM (V2)** — unguarded L2 on tower worlds, escape branch bypassed |
| `sheetSiegePointDegreeFunctional_of_degreeTrace` | **THEOREM (V2)** — forward half of the L3 core equivalence |
| `sheetSiegeDegreeTrace_of_pointDegreeFunctional` | **THEOREM (V2)** — backward half: positivity *is* the degree trace |
| `sheetSiegeDegreeTrace_iff_pointDegreeFunctional` | **THEOREM (V2)** — L3-a ⟺ one positivity statement |
| `sheetSiege_conditional_noGhost_of_monomialSaturation` | CONDITIONAL on the UNPROVEN saturation premise; proof = V3 monomial kill |
| `sheetSiege_conditional_hodge_of_monomialSaturation` | CONDITIONAL, same premise; proof = ghost iff |
| `SheetSiegeCoheightUpperBound` (L1 residue) | UNPROVEN — catenarity/height-additivity of the component domain; see docstring |
| `SheetSiegeSeparatorSuccessorExact` (L1-min) | UNPROVEN — follows from L1; discharges ~15 files of `hExact` premises |
| `SheetSiegeLiveWeightSeeds` (L2) | UNPROVEN — and REFUTABLE as stated (see the firewall theorem below); the guarded form is the canonical demand |
| `SheetSiegeLiveWeightSeedsGuarded` (L2 canonical) | UNPROVEN — reduced to spine + L3 + point supply by the V2 theorem above |
| `SheetSiegeDegreeTraceConstructed` (L3-a) | UNPROVEN — equivalent to `SheetSiegePointDegreeFunctional` by the V2 iff |

L3-b (word nativity) is NOT stated here: stating it correctly requires the
`GradedGeometricProgram` word-level interface, and a wrong statement would be
worse than an honest TODO.  It is specified in the study, §6.

## AUTHORITY 005 AUDIT OF THE REMAINING PREMISES

* `GeometricCycleClassSpine V H` (spine): independent semantic premise, never
  proven; countermodel `zeroCycleClassSpine` exists in-repo
  (`GeometricCycleClassSpine.lean:162-181`).  Every V2 theorem taking it
  flags it in its docstring.
* `ProjectiveDegreeTraceSemantics V H` (= L3-a): UNPROVEN, equivalent to the
  positivity core (this file).  The only in-repo constructor
  (`unitDegreeTraceOfNativeMassFactorization`,
  `VerticalRayMassFactorization.lean:70-75`) rests on
  `NativeMassCohomologyFactorization`, which is false for every genuine
  cycle-class map (conic minus twice a line: class `2h - 2h = 0`, mass
  `1 - 2 = -1 ≠ 0`) and on the zero-cycle world.  It is cited, never assumed.
* `NativePointSuccessorNonvanishing V` (tower law): UNPROVEN and refutable
  (`not_uniform_survival_of_next_stratum_empty`,
  `CodimensionPointTower.lean:212-217`) — it forces every stratum to be
  populated, i.e. ladder worlds.  Used only in the tower reduction, flagged.
* `Nonempty V.X`: apex supply, mild.

META-DESIGN LEVEL (AUTHORITY 002): no local Lean.  Namespace resolution and
the orientation-sensitive proof lines marked `-- COMPARE:` belong to the
brother's compile pass.  Every citation below is pinned to the audit state
`2694499` with file:line.
-/

set_option maxHeartbeats 120000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeSheetSiegeRoute

open GSTProjectiveOverC
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTNativeCodimensionCyclePresentation
open GSTClassicalHodgePointClosurePrincipalCut
open GSTClassicalHodgePointClosureRelativeCut
open GSTClassicalHodgePrincipalCutSuccessorOperator
open GSTClassicalHodgeSeparatorRelativeCoheightOne
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeGradedGeometricProgramOrbit
open GSTClassicalHodgeGradedGeometricOrbitAlgebra
open GSTClassicalHodgeOmniversalNativeOrbitSeparation
open GSTClassicalHodgeOmniversalSeparatorGhostCrown
open GSTClassicalHodgeSynchronizedDefectOrbit
open GSTClassicalHodgeRankFreeArsenalIrreducibility

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-! ## §1. The assembly — citation-complete

`GeometricGSTPlaneCompleteness` (every basis sheet of every weight is the
exact output of one verified program from the geometric origin;
`GSTClassicalHodgeOmniversalNativeOrbitSeparation.lean:65--70`) implies
Hodge through the existing four-link chain:

  coverage → orbit cyclicity (`orbitCyclic_of_geometricPlane`, same file :86)
          → ghost extinction (`no_omniversalSeparatorGhost_of_gradedGeo…`,
            `GSTClassicalHodgeOmniversalSeparatorGhostCrown.lean:235`)
          → Hodge (`hodge_of_gradedGeometricOrbitModuleCyclic_noGhost`,
            same file :246).

The previous plan never stated this assembly because it was staring through
the law D.  This theorem is the siege's front door.
-/

/-- **ROUTE S ASSEMBLY (CITATION-COMPLETE).**
Per-sheet program coverage of the classical plane implies the exact
finite rational Hodge statement.  The proof is two existing theorems. -/
theorem hodge_of_geometricPlaneCompleteness
    (G : GeometricCycleClassSpine V H)
    (hcov : GeometricGSTPlaneCompleteness G) :
    BigradedBettiHodgeStatement V H :=
  hodge_of_gradedGeometricOrbitModuleCyclic_noGhost G
    (orbitCyclic_of_geometricPlane G hcov)

/-- **ONE WON SHEET IS AN UNCONDITIONAL THEOREM (orbit-set form).**
A single program witnessing one basis sheet banks that sheet into the
verified orbit.  Partial credit: each battle is independent. -/
theorem sheetSiege_sheet_mem_orbitSet
    (G : GeometricCycleClassSpine V H)
    (q : Nat) (j : ClassicalHodgeBasisIndex V H q)
    (P : GradedGeometricProgram V 0 q)
    (hP : P.cohomologyEval G (geometricOriginClass V H) =
      (classicalHodgeBasis V H q j).1) :
    (classicalHodgeBasis V H q j).1 ∈ geometricProgramOrbitSet G q :=
  ⟨P, hP⟩
  -- COMPARE: if membership orients the other way, use `hP.symm`
  -- (the GhostCrown proof at :219--224 destructures with ⟨P, hP⟩).

/-- **ONE WON SHEET IS AN UNCONDITIONAL THEOREM (module form).** -/
theorem sheetSiege_sheet_mem_orbitModule
    (G : GeometricCycleClassSpine V H)
    (q : Nat) (j : ClassicalHodgeBasisIndex V H q)
    (P : GradedGeometricProgram V 0 q)
    (hP : P.cohomologyEval G (geometricOriginClass V H) =
      (classicalHodgeBasis V H q j).1) :
    (classicalHodgeBasis V H q j).1 ∈ geometricProgramOrbitModule G q := by
  rw [← geometricProgramOrbitSubspace_eq_module G q]
  exact Submodule.subset_span (sheetSiege_sheet_mem_orbitSet G q j P hP)

/-! ## §2. L1 — coheight additivity: bank the lower half, name the residue

The V2 research pass (Task 5-a) found that the lower-bound half of L1 is
already a theorem in the omniverse (`ambient_coheight_ge_succ`,
`RelativeSuccessorLowerBound.lean:80-90`), while the upper-bound half has
zero producers anywhere in the repo: it is the catenarity / saturated-chain
content of the homogeneous coordinate ring domain.  So L1 splits exactly
into a THEOREM plus one named residue, and the residue is where the
Krull-level content lives.
-/

/-- **THEOREM (V2) — L1 LOWER BOUND, every finset member.**
For a codimension-`p` source, every relative coheight-one successor selected
by the principal cut has ambient coheight at least `p + 1`.  This half of L1
is unconditional: no liveness, no Hodge data.  Proof: the existing ambient
lower bound plus the finset-membership bridge. -/
theorem sheetSiege_successor_coheight_ge
    (V : SmoothProjectiveComplexScheme)
    (p : Nat) (x : CodimensionPoint V.X p)
    (y : {y : pointClosureScheme V x.1 // Order.coheight y = 1})
    (hy : y ∈ relativeCodimensionOneFinset V x.1) :
    (p + 1 : ℕ∞) ≤ Order.coheight (ambientSuccessorPoint V x.1 y) :=
  GSTClassicalHodgeRelativeSuccessorLowerBound.ambient_coheight_ge_succ V p x y.1
    (GSTClassicalHodgeRelativeSuccessorProjectivePrime.
      mem_relativeCodimensionOneFinset_cut V x.1 y hy)
  -- COMPARE: `ambientSuccessorPoint V x.1 y` unfolds definitionally to
  -- `pointClosureι V x.1 y.1` (PrincipalCutSuccessorOperator.lean:48-53);
  -- if elaboration wants it aloud, `show (p + 1 : ℕ∞) ≤
  -- Order.coheight (pointClosureι V x.1 y.1)` first.

/-- **UNPROVEN PREMISE — L1 RESIDUE — COHEIGHT UPPER BOUND (catenarity).**
Every selected successor has ambient coheight at most `p + 1`.

This is the exact irreducible residue of L1: by the iff below, L1 holds if
and only if this upper bound holds.  The mathematical content is the
height-additivity / catenarity theorem for the homogeneous coordinate ring
domain of the irreducible component (`ht 𝔭_z = ht 𝔭_x + ht (𝔭_z/𝔭_x)`,
saturated chains); the repo contains every input around it — Krull's
principal ideal theorem (`KrullPrincipalCut.lean:49-53`), the ambient
prime-interval collapse
(`prime_between_source_separator_eq_endpoint`,
`SeparatorAmbientPrimeInterval.lean:32-75`), and the stalk bridge
(`stalk_dimension_eq_coheight`, `SchemeCodimensionStalk.lean:31-34`) — but
no catenarity theorem (the sole `catenar` hit in the repo is a disclaimer
docstring).  Whether the pinned Mathlib ships it is the brother's one-line
import probe.

Kill-switch: failure on smooth projective irreducible worlds kills Route S
at L1. -/
def SheetSiegeCoheightUpperBound (V : SmoothProjectiveComplexScheme) : Prop :=
  ∀ (p : Nat) (x : CodimensionPoint V.X p),
    ProjectivelyLiveSource V.projective.n (V.projective.immersion x) →
      ∀ y : {y : pointClosureScheme V x.1 // Order.coheight y = 1},
        y ∈ relativeCodimensionOneFinset V x.1 →
          Order.coheight (ambientSuccessorPoint V x.1 y) ≤ (p + 1 : ℕ∞)

/-- **UNPROVEN PREMISE L1 — COHEIGHT ADDITIVITY.**
Every live codimension-`p` point has separator successors of ambient
coheight exactly `p + 1`.

V2 status: the `≥ p+1` half is THEOREM `sheetSiege_successor_coheight_ge`
above; by `sheetSiegeCoheightAdditivity_iff_upperBound` below, the entire
remaining content of L1 is `SheetSiegeCoheightUpperBound`.  Original
obstruction note (kept for the record): `RelativeSuccessorAmbientExact`
(`GSTClassicalHodgeRelativeSuccessorExactStratum.lean:46--52`) is a premise
in every exact-stratum and successor-seed theorem; it has never been
discharged.  Ingredients are unconditional: `separatorClass_height_one`
(`ProjectiveSeparatorHeightOne.lean:61--63`),
`separator_minimalPrime_prime_height_one` (:80--84),
`finite_principal_cut_coheight_one`
(`ProperCutCodimensionOne.lean:196--200`).  The missing piece is the
bookkeeping bridge from ideal height 1 to ambient `Order.coheight` —
catenarity level, not Hodge-coded content.

Kill-switch: failure on smooth projective irreducible worlds kills Route S
at L1. -/
def SheetSiegeCoheightAdditivity (V : SmoothProjectiveComplexScheme) : Prop :=
  ∀ (p : Nat) (x : CodimensionPoint V.X p),
    ProjectivelyLiveSource V.projective.n (V.projective.immersion x) →
      GSTClassicalHodgeRelativeSuccessorExactStratum.RelativeSuccessorAmbientExact V p x

/-- **THEOREM (V2) — L1 IS EXACTLY ITS UPPER BOUND.**
Coheight additivity holds if and only if the upper-bound residue holds: the
lower bound is already a theorem, so the equality is antisymmetry.  This
compresses L1 to the catenarity core with zero loss. -/
theorem sheetSiegeCoheightAdditivity_iff_upperBound
    (V : SmoothProjectiveComplexScheme) :
    SheetSiegeCoheightAdditivity V ↔
      SheetSiegeCoheightUpperBound V := by
  constructor
  · intro hL1 p x hlive y hy
    exact le_of_eq (hL1 p x hlive y hy)
  · intro hup p x hlive y hy
    exact le_antisymm (hup p x hlive y hy)
      (sheetSiege_successor_coheight_ge V p x y hy)

/-- **UNPROVEN PREMISE — L1 SINGLE-SUCCESSOR FORM (L1-min).**
For every live source, the *constructed* separator successor
(`relativeHeightOneSeparatorSuccessor`) has ambient coheight exactly `p + 1`.

This is the form consumed as `hExact` by the entire downstream
survival/seed/escape chain — `separator_successor_survives_of_ambient_exact`
(`SingleExactSuccessorSurvival.lean:130-146`),
`separator_successor_seed_or_escape` / `separator_successor_seed_of_no_escape`
(`SuccessorSeedEscapeDichotomy.lean:120-194`),
`separator_successor_nativeHodgeSeed` (`ProjectiveDegreeTrace.lean:202-227`)
and the degree-certified compiler family (~15 files).  Proving L1-min
discharges every one of those premises at once.  It follows from full L1 by
`sheetSiege_separatorSuccessorExact_of_coheightAdditivity` below. -/
def SheetSiegeSeparatorSuccessorExact (V : SmoothProjectiveComplexScheme) : Prop :=
  ∀ (p : Nat) (x : CodimensionPoint V.X p)
    (hlive : ProjectivelyLiveSource V.projective.n (V.projective.immersion x)),
    Order.coheight
      (ambientSuccessorPoint V x.1
        (relativeHeightOneSeparatorSuccessor V x.1 hlive)) = p + 1

/-- **THEOREM (V2) — L1 IMPLIES L1-min.**
Full coheight additivity yields the single-successor exactness, because the
constructed separator successor is a member of the relative codimension-one
finset (`relativeHeightOneSeparatorSuccessor_mem_finset`,
`RelativeSuccessorNonempty.lean:35-40`). -/
theorem sheetSiege_separatorSuccessorExact_of_coheightAdditivity
    (V : SmoothProjectiveComplexScheme)
    (hL1 : SheetSiegeCoheightAdditivity V) :
    SheetSiegeSeparatorSuccessorExact V := by
  intro p x hlive
  exact hL1 p x hlive _
    (GSTClassicalHodgeRelativeSuccessorNonempty.
      relativeHeightOneSeparatorSuccessor_mem_finset V x.1 hlive)

/-! ## §3. L2 — live weight seeds: firewall, guard, and two reductions

The V2 research pass (Task 5-b) found that the *unguarded* L2 statement is
REFUTABLE inside the omniverse's own primitives: on the zero-cycle-class
world (`zeroCycleClassData`, `Stage2GSemanticRigidity.lean:42-46`) the seed
type is empty at every weight, since `class_eq` would force `hodge = 0`.
The unguarded statement is kept below for study-compatibility, but the
firewall theorem proves it is not a provable target; the guarded form is the
canonical demand shape (the repo's own crowns guard it,
e.g. `bigradedBettiHodge_of_synchronized_limitless_orbits`,
`SynchronizedDefectOrbit.lean:281-289`).  The escape dichotomy, which the
study priced as L2's burden, is bypassed entirely on the degree-trace route:
with `D` present, the separator successor's cycle class is nonzero
(`separator_successor_cycleClass_ne_zero`,
`ProjectiveDegreeTrace.lean:178-197`), so the escape branch never opens.
-/

/-- **UNPROVEN PREMISE L2 — LIVE WEIGHT SEEDS (unguarded; see firewall).**
Every weight carries a native Hodge orbit seed.

V2 status: REFUTABLE as stated — `sheetSiegeLiveWeightSeeds_false_of_
zeroCycleClassData` below proves the negation on the zero-cycle-class world,
and any dead weight (a `q` with vanishing Hodge fiber) empties the seed type
there.  This def is kept for study-compatibility only; the honest proof
target is `SheetSiegeLiveWeightSeedsGuarded`, and the unguarded form is a
*conclusion* on tower worlds
(`sheetSiegeLiveWeightSeeds_of_spine_degreeTrace_uniformSurvival`).

Kill-switch: if proving the guarded form requires per-sheet algebraicity
hypotheses, L2 is D in disguise; abort and re-audit. -/
def SheetSiegeLiveWeightSeeds
    (V : SmoothProjectiveComplexScheme) (H : HodgeBigradedBettiData V) : Prop :=
  ∀ q : Nat,
    Nonempty (NativeHodgeOrbitSeed (V := V) (H := H) (p := q))

/-- **THEOREM (V2, FIREWALL) — THE UNGUARDED L2 IS NOT A PROVABLE TARGET.**
On the zero-cycle-class world the seed type is empty at every weight:
`class_eq` reads `0 = hodge.1`, forcing `hodge = 0` against
`hodge_ne_zero`.  So no theorem quantified over arbitrary `H` can prove the
unguarded L2 — the firewall demands codimension-sensitivity, and this is it,
made explicit.  (Companion: `no_degreeTrace_for_zeroCycleClass_at_point`,
`NativePointSeedDegreeUpgrade.lean:98-111`.) -/
theorem sheetSiegeLiveWeightSeeds_false_of_zeroCycleClassData
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V) :
    ¬ SheetSiegeLiveWeightSeeds V
      (GSTClassicalHodgeStage2GSemanticRigidity.zeroCycleClassData H) := by
  intro hseeds
  obtain ⟨S⟩ := hseeds 0
  have h0 :
      (GSTClassicalHodgeStage2GSemanticRigidity.zeroCycleClassData H).cycleClass 0
        S.cycle = 0 := by
    rw [GSTClassicalHodgeStage2GSemanticRigidity.zeroCycleClassData_cycleClass]
    exact LinearMap.zero_apply S.cycle
  have hval : S.hodge.1 = 0 := S.class_eq.symm.trans h0
  exact S.hodge_ne_zero (Subtype.ext (by simpa using hval))
  -- COMPARE: if `Subtype.ext` needs the literal `(0 : ↥_).1 = 0` side,
  -- replace the last line with
  -- `exact S.hodge_ne_zero (Subtype.ext (by simpa using hval))` variant
  -- `refine S.hodge_ne_zero (Subtype.ext ?_); simpa using hval`.

/-- **UNPROVEN PREMISE — L2 CANONICAL (guarded).**
Every *populated* weight carries a native Hodge orbit seed.  The guard is
the repo's canonical demand shape: no point at weight `q`, no seed demand at
weight `q`.  Reduced to spine + degree trace by the V2 theorem below. -/
def SheetSiegeLiveWeightSeedsGuarded
    (V : SmoothProjectiveComplexScheme) (H : HodgeBigradedBettiData V) : Prop :=
  ∀ q : Nat, Nonempty (CodimensionPoint V.X q) →
    Nonempty (NativeHodgeOrbitSeed (V := V) (H := H) (p := q))

/-- **THEOREM (V2) — GUARDED L2 FROM SPINE + DEGREE TRACE.**
One actual codimension-`q` point plus the spine plus the degree trace gives
the weight-`q` seed: Hodge type from `G.pointClass_is_hodge`, nonvanishing
from `D.trace_point_cycleClass` + `D.pointDegree_pos`
(`nativeHodgeOrbitSeed_of_codimensionPoint`,
`NativePointSeedDegreeUpgrade.lean:74-79`).  Premises: the spine `G` and the
degree trace `D` are UNPROVEN (see the audit table); the point supply is the
only additional content.  The escape dichotomy never enters. -/
theorem sheetSiegeLiveWeightSeedsGuarded_of_spine_degreeTrace
    (G : GeometricCycleClassSpine V H)
    (D : GSTClassicalHodgeProjectiveDegreeTrace.ProjectiveDegreeTraceSemantics V H) :
    SheetSiegeLiveWeightSeedsGuarded V H := by
  intro q hx
  obtain ⟨x⟩ := hx
  exact ⟨GSTClassicalHodgeNativePointSeedSaturation.
    nativeHodgeOrbitSeed_of_codimensionPoint G D x⟩

/-- **THEOREM (V2) — UNGUARDED L2 ON TOWER WORLDS.**
Under the uniform survival law (`NativePointSuccessorNonvanishing`,
UNPROVEN and refutable on finite-dimensional worlds — it forces every
stratum to be populated), every weight has an actual codimension point
(`codimensionPoint_exists_of_nativePointSuccessorNonvanishing`,
`CodimensionPointTower.lean:79-85`), so spine + degree trace give the seed
at *every* weight, unguarded.  This is an honest conditional about ladder
worlds: `G` (spine), `D` (L3-a) and the tower law are all flagged UNPROVEN
in the audit table; the implication is theirs to discharge, not ours to
assume. -/
theorem sheetSiegeLiveWeightSeeds_of_spine_degreeTrace_uniformSurvival
    (G : GeometricCycleClassSpine V H)
    (D : GSTClassicalHodgeProjectiveDegreeTrace.ProjectiveDegreeTraceSemantics V H)
    [Nonempty V.X]
    (hstep : GSTClassicalHodgeCodimensionPointTower.NativePointSuccessorNonvanishing V) :
    SheetSiegeLiveWeightSeeds V H := by
  intro q
  obtain ⟨x⟩ :=
    GSTClassicalHodgeCodimensionPointTower.
      codimensionPoint_exists_of_nativePointSuccessorNonvanishing V hstep q
  exact ⟨GSTClassicalHodgeNativePointSeedSaturation.
    nativeHodgeOrbitSeed_of_codimensionPoint G D x⟩

/-! ## §4. L3-a — the degree trace is exactly a positivity statement

The V2 research pass (Task 5-c) field-audited the four fields of
`ProjectiveDegreeTraceSemantics` and found the compression: setting
`pointDegree := trace ∘ (cycle class of the point cycle)` makes
`trace_point_cycleClass` definitional (`rfl`), so the *entire* structure is
equivalent to one statement — a rational linear functional on each even
cohomology group, strictly positive on the cycle class of every codimension
point.  That statement is `SheetSiegePointDegreeFunctional` below.  The
classical recipe (cup with the hyperplane power, integrate over the
fundamental class) constructs it; the repo has every consumer wired and the
construction inputs (cup product, integration, hyperplane class, positivity)
are absent — see the docstring on the iff for the priced debt.

The only in-repo constructor,
`unitDegreeTraceOfNativeMassFactorization` (`VerticalRayMassFactorization.
lean:70-75`), rests on `NativeMassCohomologyFactorization`, which is false
for genuine cycle-class maps (conic minus twice a line) and on the
zero-cycle world.  It is cited here, never assumed.
-/

/-- **UNPROVEN PREMISE L3-a — DEGREE-TRACE CONSTRUCTION.**
The projective degree-trace semantics is constructed, not assumed.

V2 status: equivalent to `SheetSiegePointDegreeFunctional` by the iff below.
The classical recipe (cup with hyperplane power, integrate over the
fundamental class) is a construction task from Poincare duality + ampleness,
plus one classical positivity theorem (degree of an embedded subvariety is
a positive integer) — the kill-switch clause fires on exactly that item:
the debt is one positivity theorem larger than the "duality + ampleness"
phrasing.  It is impossible on the zero-cycle world
(`no_degreeTrace_for_zeroCycleClass_at_point`,
`NativePointSeedDegreeUpgrade.lean:98--111`) — exactly as the firewall
demands, so it must be BUILT from genuine geometry, never assumed.

Kill-switch: if the construction needs input beyond Poincare duality,
ampleness, and point-degree positivity, the debt is larger than priced;
re-audit. -/
def SheetSiegeDegreeTraceConstructed
    (V : SmoothProjectiveComplexScheme) (H : HodgeBigradedBettiData V) : Prop :=
  Nonempty (GSTClassicalHodgeProjectiveDegreeTrace.ProjectiveDegreeTraceSemantics V H)

/-- **UNPROVEN PREMISE — L3-a CORE (positivity form).**
For every weight `q`: a rational linear functional on `H^{2q}`, strictly
positive on the cycle class of every actual codimension-`q` point cycle.
This is the exact content of L3-a by the iff below — two of the four
structure fields are packaging. -/
def SheetSiegePointDegreeFunctional
    (V : SmoothProjectiveComplexScheme) (H : HodgeBigradedBettiData V) : Prop :=
  ∀ q : Nat,
    ∃ f : RationalSingularCohomology H.analytification (2 * q) →ₗ[ℚ] ℚ,
      ∀ x : CodimensionPoint V.X q,
        0 < f (H.cycleClass q (codimensionPointCycle V.X q x))

/-- **THEOREM (V2) — degree trace gives the positivity core.** -/
theorem sheetSiegePointDegreeFunctional_of_degreeTrace
    (D : GSTClassicalHodgeProjectiveDegreeTrace.ProjectiveDegreeTraceSemantics V H) :
    SheetSiegePointDegreeFunctional V H := by
  intro q
  refine ⟨D.trace q, fun x => ?_⟩
  rw [D.trace_point_cycleClass q x]
  exact D.pointDegree_pos q x

/-- **THEOREM (V2) — the positivity core BUILDS the degree trace.**
Given the positive functionals, set `pointDegree := f ∘ (cycle class of the
point cycle)`: positivity is the premise and the compatibility law is
`rfl`.  The two "free fields" of the audit are free precisely because this
construction absorbs them. -/
theorem sheetSiegeDegreeTrace_of_pointDegreeFunctional
    (hf : SheetSiegePointDegreeFunctional V H) :
    SheetSiegeDegreeTraceConstructed V H := by
  refine ⟨?_⟩
  choose f hpos using hf
  exact
    { trace := fun q => f q,
      pointDegree := fun q x =>
        f q (H.cycleClass q (codimensionPointCycle V.X q x)),
      pointDegree_pos := fun q x => hpos q x,
      trace_point_cycleClass := fun q x => rfl }

/-- **THEOREM (V2) — L3-a IS EXACTLY THE POSITIVITY CORE.**
`ProjectiveDegreeTraceSemantics` exists if and only if a positive
point-class functional family exists.  The remaining construction debt, in
the classical recipe's order: (1) graded cup product on rational singular
cohomology (repo has only premise-shaped `RationalProductCupTheory`,
`BettiCupGysinPrimitives.lean:39-48`); (2) integration over the fundamental
class `H^{2d} →ₗ[ℚ] ℚ` (nothing in repo or pinned Mathlib singular-cohomology
API); (3) the hyperplane cohomology class (the hyperplane *scheme* exists,
its class never formed); (4) point-degree positivity (the classical
theorem).  Items (1)-(3) are construction; item (4) is content. -/
theorem sheetSiegeDegreeTrace_iff_pointDegreeFunctional
    (V : SmoothProjectiveComplexScheme) (H : HodgeBigradedBettiData V) :
    SheetSiegeDegreeTraceConstructed V H ↔
      SheetSiegePointDegreeFunctional V H :=
  ⟨fun ⟨D⟩ => sheetSiegePointDegreeFunctional_of_degreeTrace D,
    sheetSiegeDegreeTrace_of_pointDegreeFunctional⟩

/-! ## §5. Conditional corollaries — the starvation engine, wired

The V3 monomial kill (`false_of_ghost_monomialSheetSeed`,
`BranchPacketPlaneRealization.lean:725-741`) is sheet-generic and
unconditional in its logic.  Full monomial saturation of the seed supply
starves every ghost: no sheet remains where a synchronized native seed can
be forced off-diagonal.  These corollaries are CONDITIONAL on the saturation
premise (which is NOT proven and is not claimed); their proofs are citations.
-/

/-- **CONDITIONAL — ghost starvation under full monomial saturation.**
If every sheet of every weight carries a synchronized native seed that is a
live multiple of that sheet, every omniversal separator ghost is refuted by
the V3 monomial kill.  The premise is UNPROVEN; the implication is not. -/
theorem sheetSiege_conditional_noGhost_of_monomialSaturation
    (G : GeometricCycleClassSpine V H)
    (hsat : ∀ (q : Nat) (j : ClassicalHodgeBasisIndex V H q),
      ∃ S : NativeHodgeOrbitSeed (V := V) (H := H) (p := q),
        hodgeMatrixUnit S.sourceIndex j S.hodge = S.hodge) :
    IsEmpty (OmniversalSeparatorGhost G) := by
  refine ⟨?_⟩
  intro E
  obtain ⟨S, hmono⟩ := hsat E.weight E.sheet
  exact GSTClassicalHodgeBranchPacketPlaneRealization.false_of_ghost_monomialSheetSeed
    G E S (congrArg Subtype.val hmono)

/-- **CONDITIONAL — Hodge under full monomial saturation.**
Same premise; closes through the ghost equivalence
(`hodge_iff_no_omniversalSeparatorGhost`, `GhostCrown.lean:116`). -/
theorem sheetSiege_conditional_hodge_of_monomialSaturation
    (G : GeometricCycleClassSpine V H)
    (hsat : ∀ (q : Nat) (j : ClassicalHodgeBasisIndex V H q),
      ∃ S : NativeHodgeOrbitSeed (V := V) (H := H) (p := q),
        hodgeMatrixUnit S.sourceIndex j S.hodge = S.hodge) :
    BigradedBettiHodgeStatement V H :=
  (hodge_iff_no_omniversalSeparatorGhost G).2
    (sheetSiege_conditional_noGhost_of_monomialSaturation G hsat)

#check hodge_of_geometricPlaneCompleteness
#check sheetSiege_sheet_mem_orbitSet
#check sheetSiege_sheet_mem_orbitModule
#check sheetSiege_successor_coheight_ge
#check SheetSiegeCoheightUpperBound
#check SheetSiegeCoheightAdditivity
#check sheetSiegeCoheightAdditivity_iff_upperBound
#check SheetSiegeSeparatorSuccessorExact
#check sheetSiege_separatorSuccessorExact_of_coheightAdditivity
#check SheetSiegeLiveWeightSeeds
#check sheetSiegeLiveWeightSeeds_false_of_zeroCycleClassData
#check SheetSiegeLiveWeightSeedsGuarded
#check sheetSiegeLiveWeightSeedsGuarded_of_spine_degreeTrace
#check sheetSiegeLiveWeightSeeds_of_spine_degreeTrace_uniformSurvival
#check SheetSiegeDegreeTraceConstructed
#check SheetSiegePointDegreeFunctional
#check sheetSiegePointDegreeFunctional_of_degreeTrace
#check sheetSiegeDegreeTrace_of_pointDegreeFunctional
#check sheetSiegeDegreeTrace_iff_pointDegreeFunctional
#check sheetSiege_conditional_noGhost_of_monomialSaturation
#check sheetSiege_conditional_hodge_of_monomialSaturation

#print axioms hodge_of_geometricPlaneCompleteness
#print axioms sheetSiege_sheet_mem_orbitSet
#print axioms sheetSiege_sheet_mem_orbitModule
#print axioms sheetSiege_successor_coheight_ge
#print axioms sheetSiegeCoheightAdditivity_iff_upperBound
#print axioms sheetSiege_separatorSuccessorExact_of_coheightAdditivity
#print axioms sheetSiegeLiveWeightSeeds_false_of_zeroCycleClassData
#print axioms sheetSiegeLiveWeightSeedsGuarded_of_spine_degreeTrace
#print axioms sheetSiegeLiveWeightSeeds_of_spine_degreeTrace_uniformSurvival
#print axioms sheetSiegePointDegreeFunctional_of_degreeTrace
#print axioms sheetSiegeDegreeTrace_of_pointDegreeFunctional
#print axioms sheetSiegeDegreeTrace_iff_pointDegreeFunctional
#print axioms sheetSiege_conditional_noGhost_of_monomialSaturation
#print axioms sheetSiege_conditional_hodge_of_monomialSaturation

end GSTClassicalHodgeSheetSiegeRoute
