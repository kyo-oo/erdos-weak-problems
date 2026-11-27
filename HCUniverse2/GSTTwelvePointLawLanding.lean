/-
Copyright (c) 2026. The HC-Proof owner's GST hypothesis program.
-/
import HCUniverse2.GSTTwelvePointFoldWord
import HCUniverse2.GSTNativeSingleFoldOrbitLawLanding
import HCUniverse2.GSTHypothesisSpanningCompilerFace

/-!
# THE TWELVE-POINT LAW LANDING — THE CAPSTONE OF THE FIRST GENUINE WORLD

`GSTTwelvePointFoldWord` (the parallel author wave) delivers the first concrete
`(V, H : HodgeBigradedBettiData V)` pair of the program: the twelve-point
world — `Spec(ℂ¹²)`, twelve disjoint complex points — with its genuine H⁰
iso `twelvePointCohomologyIso : H⁰ ≃ₗ[ℚ] (Fin 12 → ℚ)` and the owner's
twelve-cell fold `T = U + J + M` realized as the genuine correspondence word
`twelvePointFoldWord` (26 weighted point-pair letters; its cohomological
operator is the exact wave matrix `Twave` under the H⁰ iso).

This module discharges `NativeGSTSingleFoldOrbitLaw twelvePointWorld
twelvePointHodgeData` — **the first discharge at a LIVE weight (rank 12)** —
and composes the capstone package:

* `twelvePointCertificate`: the 26-letter word + the genuine seed cycle
  `p₀ + p₁` (two point cycles — `coordSeed`, the indicator of the two
  leading cells);
* `twelvePointHodgeOrbit_coords`: the certificate's Hodge orbit IS Face 2's
  Krylov table `C` (the twelve iterates of `coordSeed` under `Twave`);
* `twelvePointCertificate_isKrylovCyclic`: the orbit spans the whole weight-0
  fiber — Face 2's coordinate spanning law `span_range_C_eq_top` carried
  through the H⁰ iso (`Submodule.span_induction` transport);
* `twelvePoint_law`: the law at every weight — weight 0 by the certificate,
  dead weights `p ≥ 1` by the empty word (`H^{2p} = 0`, subsingleton fiber);
* `twelvePoint_FS`: the native⇒typed bridge `gst_FS_of_native_law`,
  INSTANTIATED AND FED for the first time;
* `twelvePoint_everyHodge`: `EveryHodgeClassIsRationalAlgebraic` through the
  repository's conditional chain `exactHodge_of_one_GST_fold_orbit`;
* `the_twelve_point_native_world_package`: the master capstone receipt.

## The reused tables

Face 2 (`GSTHypothesisSpanningCompilerFace`) contributes the coordinate
certificate as PLAIN world constants (no frame parameter): `coordSeed`, the
Krylov orbit `C` (with `C_zero`/`C_succ`), `Twave`, and the spanning law
`span_range_C_eq_top` — consumed here directly, as the `Fin 12 → ℚ`-side of
the same certificate the twelve-point world hosts natively.

## The upstream contract (parallel wave; exact names consumed below)

`twelvePointWorld : SmoothProjectiveComplexScheme`,
`twelvePointHodgeData : HodgeBigradedBettiData twelvePointWorld` (with
`twelvePointHodgeData.analytification` definitionally `twelvePointAnalytification`),
`twelvePointEquiv : Fin 12 ≃ CodimensionPoint twelvePointWorld.X 0`,
`twelvePointCohomologyIso : RationalSingularCohomology
twelvePointAnalytification 0 ≃ₗ[ℚ] (Fin 12 → ℚ)`,
`zeroCycleClass_point` (the i-th point class is `Pi.single i 1` under the iso),
`zeroFiber_eq_top` (the weight-0 rational Hodge fiber is `⊤`),
`deadFiber_subsingleton : ∀ p, 0 < p → Subsingleton (ClassicalHodgeFiber … p)`,
`twelvePointFoldWord : RealizedCorrespondenceWord twelvePointWorld
twelvePointHodgeData 0`, `twelvePointFoldWord_hodge`,
`twelvePointFoldMatrix : Matrix (Fin 12) (Fin 12) ℚ` (equal to `Twave`
entrywise, proved below), and `twelvePointFoldWord_op`.  These are assumed at ROOT namespace, as the wave's task
sheets spell them; the merge wave only adds `open`s if the carrier wave
namespaces them.

## Scope (audit-accurate)

The world is zero-dimensional: the discharge's content is the twelve-cell
spanning at weight 0; the Hodge conclusion is honest but elementary (every
class of a 0-dimensional space is (0,0)-type and every 0-class is the class of
a genuine 0-cycle).  This is a restricted lemma under the AGENTS.md
acceptance test, not the Hodge conjecture; the campaign's
positive-dimensional worlds were subsequently CONSTRUCTED and
kernel-certified (the one-line positive-dimensional world, CI run
44844378079; the general-M finite-line family, run 44928010015; both
merged in the capstone `the_complete_single_fold_orbit_law_package`,
run 44943810713).  No `sorry`, no new axioms; the
GitHub CI lane `gst-twelve-point-native-world` owns the kernel check.
-/

set_option maxHeartbeats 200000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTNativeCodimensionCyclePresentation
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeCycleOperatorNaturality
open GSTClassicalHodgeRealizedClosedCorrespondenceAlgebra
open GSTClassicalHodgeRealizedCorrespondenceKrylovFinale
open GSTClassicalHodgeExactClayStatement
open GSTHodgeSingleHypothesisConditional
open GSTHypothesisSpanningCompilerFace
open GSTNativeSingleFoldOrbitLawLanding
open GSTTwelvePointWorldCarrier
open GSTTwelvePointAnalytification
open GSTTwelvePointCohomology
open GSTTwelvePointHodgeData
open GSTTwelvePointFoldWord

namespace GSTTwelvePointLawLanding

/-! ## §1 THE SEED — the genuine two-point cycle of the live weight 0

The certificate's native seed is the sum of the point cycles of the two
leading closed points of the twelve-point world.  Its Hodge class, read in
coordinates through the H⁰ iso, is exactly Face 2's coordinate seed
`coordSeed` — the indicator of the two leading cells. -/

/-- The i-th closed point of the twelve-point world, as a genuine
codimension-zero point (the eta-expansion of the upstream point
identification `twelvePointEquiv`). -/
abbrev twelvePointPt (i : Fin 12) : CodimensionPoint twelvePointWorld.X 0 :=
  ⟨(twelvePointEquiv i).1, (twelvePointEquiv i).2⟩

/-- **THE SEED CYCLE.**  The genuine native 0-cycle `p₀ + p₁`: the two
leading points of the twelve-point world, each with multiplicity one. -/
noncomputable def twelvePointSeedCycle : codimensionCycles twelvePointWorld.X 0 :=
  codimensionPointCycle twelvePointWorld.X 0 (twelvePointPt 0) +
    codimensionPointCycle twelvePointWorld.X 0 (twelvePointPt 1)

/-- The seed's class lies in the weight-0 rational Hodge fiber: at weight 0
the fiber is the whole `H⁰` (upstream `zeroFiber_eq_top`). -/
theorem twelvePointSeed_hodge :
    twelvePointHodgeData.cycleClass 0 twelvePointSeedCycle ∈
      rationalHodgeSubspace (twelvePointHodgeData.hodgeBigrading 0) := by
  -- W2-D D4 (wave 15): `zeroFiber_eq_top` is stated over the constant
  -- `zeroBigrading` (HodgeData:248); the goal spells the projection
  -- `twelvePointHodgeData.hodgeBigrading 0`.  The dead-export bridge
  -- `twelvePointHodgeData_bigrading_zero` (HodgeData:293, `= zeroBigrading`
  -- by rfl) rewrites the projection syntactically first; then the fiber
  -- lemma fires on the constant.
  -- WAVE 20 (W4-B R1 hardening): the fiber equation is hoisted as a ground
  -- have at the goal's own projection spelling — the interior `rw` is
  -- syntactic, the `exact zeroFiber_eq_top` unifies at default
  -- transparency, and the outer `rw [hfib]` is purely syntactic — every
  -- step green under both rw-matching models.
  have hfib : rationalHodgeSubspace (twelvePointHodgeData.hodgeBigrading 0) = ⊤ := by
    rw [twelvePointHodgeData_bigrading_zero]
    exact zeroFiber_eq_top
  rw [hfib]
  -- WAVE 21 (run-20 arity disease): mem_top's element is implicit at the
  -- pin (Submodule/Lattice.lean:143, `lemma mem_top {x : M}`) — the term is
  -- already the full proposition; the `_` was a "Function expected".
  exact Submodule.mem_top

/-- **THE SEED COORDINATES.**  Under the H⁰ iso the seed's class is exactly
the Face-2 coordinate seed `coordSeed`: two point classes `Pi.single 0 1` and
`Pi.single 1 1`.

AUDIT (contract/API): consumes upstream `zeroCycleClass_point` in the form
`∀ i : Fin 12, twelvePointCohomologyIso (twelvePointHodgeData.cycleClass 0
(codimensionPointCycle twelvePointWorld.X 0 (twelvePointPt i))) =
Pi.single i 1`; the two `map_add`s fire first on the cycle-class map and then
on the H⁰ iso (if the second does not fire on the `≃ₗ` coercion, replace it
by `LinearEquiv.map_add`). -/
theorem twelvePointSeed_coords :
    twelvePointCohomologyIso (twelvePointHodgeData.cycleClass 0 twelvePointSeedCycle) =
      coordSeed := by
  have hseed : twelvePointSeedCycle =
      codimensionPointCycle twelvePointWorld.X 0 (twelvePointPt 0) +
        codimensionPointCycle twelvePointWorld.X 0 (twelvePointPt 1) := rfl
  -- WAVE 19 (pre-emptive, W1-D R2+R3): supersedes the wave-15 bridge
  -- design.  The seed's class carries the cycleClass field spelling
  -- `twelvePointHodgeData.analytification (2 * 0)`; the iso-side rewrites
  -- are stuck against it at instances transparency — the second `map_add`'s
  -- pattern pins the iso's `twelvePointAnalytification 0` domain, and after
  -- the `twelvePointHodgeData_cycleClass_zero` projection transport the
  -- point-class application would still sit at the `(2 * 0)`-spelled
  -- functor while `zeroCycleClass_point` is stated at the `zeroCycleClass`
  -- codomain (plus the HodgeData `def`/LawLanding `abbrev` `twelvePointPt`
  -- seam).  Hoist both facts as ground haves at the fiber's own `(2 * 0)`
  -- spelling; elaborator-level defeq on the from-terms, syntactic match on
  -- every subsequent rewrite.
  have hiso : ∀ X Y : RationalSingularCohomology
      twelvePointHodgeData.analytification (2 * 0),
      twelvePointCohomologyIso (X + Y) =
        twelvePointCohomologyIso X + twelvePointCohomologyIso Y :=
    fun X Y => cohomologyIso_add X Y
  have hpt : ∀ i : Fin 12, twelvePointCohomologyIso
      (twelvePointHodgeData.cycleClass 0
        (codimensionPointCycle twelvePointWorld.X 0 (twelvePointPt i))) =
      Pi.single i (1 : ℚ) := fun i => zeroCycleClass_point i
  rw [hseed, map_add, hiso, hpt 0, hpt 1]
  -- W2-D D1 (wave 15): the ℚ-valued cell goals are closed by the
  -- corpus-green `simp […] <;> norm_num` idiom (the exact green twin of
  -- this computation is Face 2's `coordSeed_eq_Cvec0`:
  -- `funext i; fin_cases i <;> simp [coordSeed, Cvec] <;> norm_num`);
  -- `decide` cannot reduce ℚ arithmetic at the pin.
  funext i
  fin_cases i <;> simp [coordSeed, Pi.add_apply, Pi.single_apply] <;> norm_num

/-- **THE SEED CLASS IS NONZERO.**  The seed's Hodge class is nonzero: its
coordinate vector is `coordSeed`, whose 0-th entry is `1 ≠ 0`.  This is the
live-weight receipt — the certificate's seed is a genuine algebraic cycle
with nonzero Hodge class (no-free-lunch, satisfied honestly).

AUDIT (API): the `map_zero` is the same LinearEquiv-coercion mark as the
second `map_add` in `twelvePointSeed_coords` (fallback
`LinearEquiv.map_zero`). -/
theorem twelvePointSeed_class_ne_zero :
    twelvePointHodgeData.cycleClass 0 twelvePointSeedCycle ≠ 0 := by
  intro h0
  have hcoords := twelvePointSeed_coords
  -- WAVE 19 (pre-emptive, W1-D R3): `map_zero`'s pattern pins the iso's
  -- `twelvePointAnalytification 0` domain while the zero h0 supplies is at
  -- the cycleClass field spelling `twelvePointHodgeData.analytification
  -- (2 * 0)` (stuck at instances transparency) — hoist the zero image as a
  -- ground have at the fiber's own spelling; the rewrite is then syntactic.
  have hz : twelvePointCohomologyIso
      (0 : RationalSingularCohomology twelvePointHodgeData.analytification (2 * 0)) = 0 :=
    map_zero twelvePointCohomologyIso.toLinearMap
  rw [h0, hz] at hcoords
  exact one_ne_zero
    (show (1 : ℚ) = (0 : ℚ) from congrFun hcoords.symm (0 : Fin 12))

/-! ## §2 THE CERTIFICATE — the 26-letter fold word with the seed -/

/-- **THE KR YLOV CERTIFICATE OF THE LIVE WEIGHT.**  The owner's realized
correspondence word `twelvePointFoldWord` (the 26 weighted point-pair
letters of `Twave`) with the genuine two-point seed cycle.  The two Hodge
fields are exactly the upstream `twelvePointFoldWord_hodge` and the
`⊤`-fiber membership of the seed's class. -/
noncomputable def twelvePointCertificate :
    RealizedCorrespondenceKrylovCertificate twelvePointWorld twelvePointHodgeData 0 where
  word := twelvePointFoldWord
  word_hodge := twelvePointFoldWord_hodge
  seedCycle := twelvePointSeedCycle
  seed_hodge := twelvePointSeed_hodge

/-! ## §3 THE ORBIT IS THE KR YLOV TABLE `C`

Under the H⁰ iso, the underlying classes of the certificate's Hodge orbit
are exactly Face 2's coordinate Krylov orbit `C` — by induction on the step
equation, since the word's operator IS the wave matrix (`twelvePointFoldWord_op`). -/

/-- AUDIT (contract): the fold matrix IS the owner's `Twave`.  The parallel
wave assembles `twelvePointFoldMatrix` as the letter-data sum (not
definitionally `Twave`), so the equality is proved entrywise: every one of
the 144 `Fin 12 × Fin 12` entries is discharged by `fin_cases` + `simp` +
`norm_num` (the same entrywise sweep as `Twave_bridge`), through
`Matrix.ext`. -/
theorem twelvePointFoldMatrix_eq_Twave :
    twelvePointFoldMatrix = Twave := by
  -- W2-D D2 (wave 15): the 144-entry sweep mirrors the corpus-green
  -- `Twave_bridge` idiom (`fin_cases i <;> fin_cases j <;>
  -- simp [Twave, N12_val, eCell, …] <;> norm_num`) — `decide` cannot
  -- reduce the ℚ-valued `List.sum` arithmetic at the pin; simp's
  -- ite/decide simprocs evaluate the Fin-literal guards and `norm_num`
  -- closes the rational sums.
  -- WAVE 33 (run-32 :251 receipt): `Matrix.ext fun r c => by …` is a TERM
  -- in tactic position — "unknown tactic"; the refine-form fixes it
  -- (Matrix.ext is the @[ext]-registered lemma, applied with a fun
  -- hypothesis).
  -- WAVE 34 (run-33 :257 receipt): the six green-twin names
  -- (N12_val, eCell, shuffleCell, mirrorCell, cmSign, ownerSource) live in
  -- the SpanningProof/Complete namespaces (not opened here — unknown
  -- identifiers) AND were never needed: THIS file's `Twave` is the
  -- CompilerFace's DIRECT ite-literal matrix (the N12-form lives only in
  -- the twin's own statement), and `twelvePointFoldMatrix` is the explicit
  -- foldWordData map-sum — both sides reduce to rational literals through
  -- the three-name simp-set + norm_num.
  refine Matrix.ext fun r c => ?_
  fin_cases r <;> fin_cases c <;>
    simp [twelvePointFoldMatrix, Twave, foldWordData] <;>
    norm_num

/-- **THE ORBIT IS THE KR YLOV TABLE.**  `iso (hodgeOrbit n) = C n` for every
`n`: the orbit starts at the seed (`C 0 = coordSeed`) and every step is one
`Twave.mulVec` on both sides (`twelvePointFoldWord_op` vs `C_succ`). -/
theorem twelvePointHodgeOrbit_coords (n : Nat) :
    twelvePointCohomologyIso ((twelvePointCertificate.hodgeOrbit n).1) = C n := by
  induction n with
  | zero => exact twelvePointSeed_coords.trans C_zero.symm
  | succ n ih =>
      have hstep : (twelvePointCertificate.hodgeOrbit (n + 1)).1 =
          (realizedWordPair twelvePointFoldWord).cohomologyOperator
            (twelvePointCertificate.hodgeOrbit n).1 := rfl
      rw [hstep, twelvePointFoldWord_op, ih, C_succ, twelvePointFoldMatrix_eq_Twave]

/-- The underlying class of the n-th Hodge-orbit vector is the inverse-iso
image of the n-th Face-2 Krylov value (the coordinate theorem read through
`LinearEquiv.symm_apply_apply`). -/
theorem twelvePointHodgeOrbit_symm (n : Nat) :
    (twelvePointCertificate.hodgeOrbit n).1 =
      twelvePointCohomologyIso.symm (C n) :=
  (twelvePointCohomologyIso.symm_apply_apply
      ((twelvePointCertificate.hodgeOrbit n).1)).symm.trans
    (congrArg twelvePointCohomologyIso.symm (twelvePointHodgeOrbit_coords n))

/-! ## §4 CYCLICITY — the orbit spans the whole live fiber -/

/-- **THE AMBIENT SPAN.**  The rational span of the underlying orbit classes
is the whole `H⁰`: Face 2's coordinate spanning law
`span_range_C_eq_top : span ℚ (range C) = ⊤`, transported backwards through
the H⁰ iso by the universal-property induction of `Submodule.span`.

AUDIT (API): the span-induction cases use `LinearEquiv.map_zero`,
`LinearEquiv.map_add`, `LinearEquiv.map_smul` on the inverse iso; if any of
these names is absent in the pinned Mathlib, the generic `map_zero` /
`map_add` / `map_smul` (AddHomClass on the `≃ₗ` coercion) is the drop-in
replacement. -/
theorem twelvePoint_orbitUnderlying_span :
    Submodule.span ℚ
      (Set.range fun n : Nat => @id (RationalSingularCohomology
        twelvePointAnalytification 0) (twelvePointCertificate.hodgeOrbit n).1) = ⊤ := by
  apply top_unique
  intro u _
  have hEu : twelvePointCohomologyIso u ∈ Submodule.span ℚ (Set.range C) := by
    rw [span_range_C_eq_top]
    -- WAVE 21 (run-20 arity disease): mem_top's element is implicit at the
    -- pin (Submodule/Lattice.lean:143) — drop the argument.
    exact Submodule.mem_top
  -- WAVE 36 (run-35 :345/:352/:353 receipts): the span-induction block is
  -- DEAD — three waves of haveI spellings (def, projection, both) never
  -- matched the hodgeOrbit elements' internally-spelled type
  -- (`rationalSingularCohomologyObj twelvePointHodgeData.analytification
  -- (2 * 0)` under the ModuleCat carrier coe) — fresh instance synthesis
  -- on that type is unwinnable from this file's scope (the failing goals
  -- display normalized to the abbrev, so every haveI targets the wrong
  -- term).  THE ACTUAL TRUTH: the instances must ARRIVE INSIDE TERM
  -- TYPES — the green sibling's own architecture.  THE RESTRUCTURE: the
  -- membership transports through the span-IMAGE chain, every instance
  -- carried by the iso's own green-elaborated type —
  -- (1) the orbit-range IS the iso-symmetry image of the coordinate
  --     range (entrywise by twelvePointHodgeOrbit_symm, the green
  --     in-file theorem);
  -- (2) the span of an image is the map of the span
  --     (Submodule.span_image, Span/Basic.lean:254, @[simp], used by
  --     Mathlib itself at :265);
  -- (3) the membership in the map is the witness pair
  --     (Submodule.mem_map, the pinned Span/Basic.lean:443's own
  --     obtain-shape) — the coordinates membership is hEu, the symmetry
  --     round-trip is the iso's own symm_apply_apply.
  -- ZERO fresh instance synthesis anywhere: the map's Module-arguments
  -- flow from the ascribed LinearMap type, itself elaborated from
  -- twelvePointCohomologyIso's green declaration.  (The block also
  -- carried three latent corrupted lines `rw ap_zero]`/`rw ap_add]`/
  -- `rw ap_smul]` — a wave-20-era edit casualty, never exposed because
  -- the block always died above them — deleted with the block.)
  have himg : Set.range (fun n : Nat => @id (RationalSingularCohomology
          twelvePointAnalytification 0) (twelvePointCertificate.hodgeOrbit n).1) =
      twelvePointCohomologyIso.symm.toLinearMap '' Set.range C := by
    ext y
    constructor
    · rintro ⟨n, rfl⟩
      exact ⟨C n, ⟨n, rfl⟩, (twelvePointHodgeOrbit_symm n).symm⟩
    · rintro ⟨c, ⟨n, rfl⟩, rfl⟩
      exact ⟨n, twelvePointHodgeOrbit_symm n⟩
  rw [himg, Submodule.span_image]
  exact Submodule.mem_map.mpr ⟨twelvePointCohomologyIso u, hEu,
    twelvePointCohomologyIso.symm_apply_apply u⟩

/-- **CYCLICITY.**  The certificate is Krylov-cyclic: the rational span of its
Hodge orbit is the whole weight-0 fiber.  Route: the subtype-span statement
transports through `Submodule.span_range_subtype_eq_top_iff` (the landing file's own
`§7` bridge pattern, here in the `.mpr` direction) to the ambient span of the
underlying classes, which is `twelvePoint_orbitUnderlying_span` at the
`⊤`-fiber `zeroFiber_eq_top`.

AUDIT (API): `Submodule.span_range_subtype_eq_top_iff` is consumed with named
implicit arguments `p`/`s` and the membership witness, mirroring the landing
file's `.mp` usage; the `.mpr` direction supplies the ambient span. -/
theorem twelvePointCertificate_isKrylovCyclic :
    twelvePointCertificate.IsKrylovCyclic :=
  (Submodule.span_range_subtype_eq_top_iff
    (p := rationalHodgeSubspace (twelvePointHodgeData.hodgeBigrading 0))
    (s := fun n : Nat => (twelvePointCertificate.hodgeOrbit n).1)
    (fun n => (twelvePointCertificate.hodgeOrbit n).2)).mpr
      (by
        -- W2-D D4 (wave 15): the iff's RHS (pinned Span/Basic.lean:462) is
        -- `span R (Set.range s) = p` with `p` the submodule itself — the
        -- goal spells the projection `twelvePointHodgeData.hodgeBigrading
        -- 0`; the bridge rewrites it to the constant `zeroBigrading`
        -- first, then the fiber lemma fires.
        -- WAVE 20 (W4-B R1 hardening): the same ground-have hoist as the
        -- seed-membership site — syntactic in, default-transparency
        -- exact inside, syntactic out.
        have hfib : rationalHodgeSubspace (twelvePointHodgeData.hodgeBigrading 0) = ⊤ := by
          rw [twelvePointHodgeData_bigrading_zero]
          exact zeroFiber_eq_top
        rw [hfib]
        exact twelvePoint_orbitUnderlying_span)

/-! ## §5 THE LAW — every weight of the first genuine world -/

/-- **THE NATIVE GST SINGLE-FOLD ORBIT LAW, DISCHARGED ON THE FIRST GENUINE
WORLD.**  Weight 0 (the LIVE rank-12 fiber): the 26-letter fold-word
certificate, cyclic by the twelve-cell spanning.  Dead weights `p ≥ 1`
(`H^{2p} = 0`): the empty-word certificate with the zero seed, cyclic by the
subsingleton argument — the landing module's own cheap-class machinery. -/
theorem twelvePoint_law :
    NativeGSTSingleFoldOrbitLaw twelvePointWorld twelvePointHodgeData := by
  intro p
  by_cases hp : 0 < p
  · refine ⟨emptyWordKrylovCertificate (p := p) 0
      (zeroCycleClass_mem_hodgeFiber twelvePointHodgeData p), ?_⟩
    exact isKrylovCyclic_of_subsingleton (deadFiber_subsingleton p hp) _
  · have hp0 : p = 0 := by omega
    subst hp0
    exact ⟨twelvePointCertificate, twelvePointCertificate_isKrylovCyclic⟩

/-! ## §6 THE BRIDGE INSTANTIATION — the FS law, fed for the first time -/

/-- **THE TYPED FS LAW, INSTANTIATED.**  Through the landing module's
native⇒typed bridge `gst_FS_of_native_law`, the law yields — for every
weight — a genuine typed `GSTHypothesisData` over the native cycle module
and the rational singular cohomology whose complete GST hypothesis holds
with the GENUINE rational Hodge fiber of that weight.

AUDIT (contract): WAVE 33 (run-32 :375 receipt) — the statement is now spelled
with `twelvePointHodgeData.analytification`, the bridge `gst_FS_of_native_law`'s
OWN result spelling — the previous def-spelled statement forced a projection-vs-
def isDefEq that burned the full 100M-heartbeat budget; the respell eliminates
the comparison entirely (the term provides the type syntactically).  The master
package's third conjunct is respelled identically so the ⟨…, twelvePoint_FS, …⟩
component also checks syntactically. -/
theorem twelvePoint_FS : ∀ p : Nat,
    ∃ D : GSTHypothesisComplete.GSTHypothesisData
        (codimensionCycles twelvePointWorld.X p)
        (RationalSingularCohomology twelvePointHodgeData.analytification (2 * p)),
      GSTHypothesisComplete.GSTHypothesisComplete D ∧
      D.hodgeFiber = rationalHodgeSubspace (twelvePointHodgeData.hodgeBigrading p) :=
  gst_FS_of_native_law twelvePoint_law

/-! ## §7 THE EXACT-HODGE CONSEQUENCE -/

/-- **EVERY HODGE CLASS OF THE TWELVE-POINT WORLD IS RATIONAL ALGEBRAIC.**
Through the repository's conditional chain
`exactHodge_of_one_GST_fold_orbit` — for the first time applied at a world
that discharges its own hypothesis at a live weight.  Honest scope: on a
zero-dimensional world every rational class is (0,0)-type and the degree map
is an iso, so this carries no transcendental content; the content of the
law it consumes is the twelve-cell spanning at weight 0. -/
theorem twelvePoint_everyHodge :
    EveryHodgeClassIsRationalAlgebraic twelvePointHodgeData :=
  exactHodge_of_one_GST_fold_orbit twelvePoint_law

/-! ## §8 THE MASTER CAPSTONE — THE FIRST GENUINE GEOMETRIC WORLD PACKAGE

The complete receipt of the twelve-point native world:

* the law itself, discharged at the live rank-12 weight 0 and free above;
* the exact-Hodge consequence through the repository's conditional chain;
* the per-weight typed FS law with the genuine rational Hodge fiber
  (the native⇒typed bridge, instantiated and fed);
* the dead-weight fact: the weight-1 fiber is a subsingleton (by dimension,
  `H² = 0`);
* the live-weight receipt: a genuine algebraic 0-cycle with nonzero Hodge
  class at the live weight — the seed `p₀ + p₁` itself, the honest
  no-free-lunch witness (cyclicity at a live weight forces exactly this). -/
theorem the_twelve_point_native_world_package :
    NativeGSTSingleFoldOrbitLaw twelvePointWorld twelvePointHodgeData ∧
    EveryHodgeClassIsRationalAlgebraic twelvePointHodgeData ∧
    (∀ p : Nat,
      ∃ D : GSTHypothesisComplete.GSTHypothesisData
        (codimensionCycles twelvePointWorld.X p)
        (RationalSingularCohomology twelvePointHodgeData.analytification (2 * p)),
        GSTHypothesisComplete.GSTHypothesisComplete D ∧
        D.hodgeFiber = rationalHodgeSubspace (twelvePointHodgeData.hodgeBigrading p)) ∧
    Subsingleton (ClassicalHodgeFiber twelvePointWorld twelvePointHodgeData 1) ∧
    (∃ Z : codimensionCycles twelvePointWorld.X 0,
      twelvePointHodgeData.cycleClass 0 Z ∈
        rationalHodgeSubspace (twelvePointHodgeData.hodgeBigrading 0) ∧
      twelvePointHodgeData.cycleClass 0 Z ≠ 0) :=
  ⟨twelvePoint_law, twelvePoint_everyHodge, twelvePoint_FS,
    deadFiber_subsingleton 1 (by norm_num),
    ⟨twelvePointSeedCycle, twelvePointSeed_hodge, twelvePointSeed_class_ne_zero⟩⟩

/-! ## §9 Receipts -/

#check twelvePointPt
#check twelvePointSeedCycle
#check twelvePointSeed_hodge
#check twelvePointSeed_coords
#check twelvePointSeed_class_ne_zero
#check twelvePointCertificate
#check twelvePointFoldMatrix_eq_Twave
#check twelvePointHodgeOrbit_coords
#check twelvePointHodgeOrbit_symm
#check twelvePoint_orbitUnderlying_span
#check twelvePointCertificate_isKrylovCyclic
#check twelvePoint_law
#check twelvePoint_FS
#check twelvePoint_everyHodge
#check the_twelve_point_native_world_package

#print axioms twelvePointSeed_coords
#print axioms twelvePointSeed_class_ne_zero
#print axioms twelvePointHodgeOrbit_coords
#print axioms twelvePoint_orbitUnderlying_span
#print axioms twelvePointCertificate_isKrylovCyclic
#print axioms twelvePoint_law
#print axioms twelvePoint_FS
#print axioms twelvePoint_everyHodge
#print axioms the_twelve_point_native_world_package

end GSTTwelvePointLawLanding
