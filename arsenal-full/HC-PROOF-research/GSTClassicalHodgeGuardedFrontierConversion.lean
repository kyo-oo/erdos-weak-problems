import GSTClassicalHodgeDegreeCertifiedFrontier
import GSTClassicalHodgeGlobalSheetSaturation

/-!
# THE GUARDED FRONTIER CONVERSION — the hypothesis-combustion strike

The degree-certified frontier (`GSTClassicalHodgeDegreeCertifiedFrontier`) still
carried its seed family UNGUARDED: `seed : ∀ q : Nat, NativeHodgeOrbitSeed
(p := q)`.  The orbit audit exposes this as a hidden defect: a
`NativeHodgeOrbitSeed` at weight `q` carries `hodge_ne_zero`, which is
REFUTABLE whenever the rational Hodge subspace at `q` is `⊥` — so the
unguarded family secretly demands that EVERY weight be live, and the whole
hypothesis is EMPTY the moment a single weight dies (vanishing cohomology,
empty codimension locus — whatever the cause).  The same holds for the
green final frontier through `seed_of_finalFrontier`.

This file performs the conversion:

* **THE VACUITY RECEIPTS.**  Any `NativeHodgeOrbitSeed` at `q` forces
  `rationalHodgeSubspace (H.hodgeBigrading q) ≠ ⊥`, and both frontiers
  therefore force ALL weights live.  An unguarded frontier hypothesis is
  never satisfiable on a carrier with a single dead weight.
* **THE SEED-COMBUSTION THEOREM.**  Given the geometric spine, the seed
  hypothesis at any weight is EXACTLY the existence of one native cycle
  with nonzero cycle class: forward, the seed's own cycle; backward,
  `nativeChowOrbitSeedOfNonzeroClass` manufactures the seed from any such
  cycle.  The seed packaging is fully combusted into pure nonvanishing
  data.
* **THE GUARDED CROWN.**  The corrected seed family — demanded only at
  live weights, with the generator family guarded the same way — closes
  the exact bigraded statement.  Dead weights discharge by the zero class
  (the corpus's own synchronized-orbit pattern).  The guarded frontier is
  strictly weaker than the old one, and the old frontier converts into it.
* **THE DEAD-WEIGHT VACUITY LEMMA.**  At a dead weight the unrestricted
  Hodge basis index is EMPTY: the generator demand there was vacuous all
  along, and the guard makes that explicit instead of hiding it inside an
  unsatisfiable hypothesis.

The flagship interface theorem — `bigradedBettiHodge_of_spine_nonzeroClass_
family_generators` — reduces the exact Stage-2G statement to: the geometric
cycle-class spine, one nonzero cycle class at each live weight, and the
one-live-source projective two-generators on the manufactured Chow seeds.
Every remaining input is named irreducible content, certified genuine by
the corpus's own separation theorems (`spine_laws_do_not_force_hodge`,
`arbitrary_cycleClass_semantics_cannot_be_final_target`).

Zero sorry, zero new axioms, zero hypotheses beyond the named frontier.
-/

set_option maxHeartbeats 40000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry
open TopologicalSpace

namespace GSTClassicalHodgeGuardedFrontierConversion

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeLimitlessSpinePropagation
open GSTClassicalHodgeProjectiveTwoGeneratorExternalization
open GSTClassicalHodgeSynchronizedDefectOrbit
open GSTClassicalHodgeProjectiveDegreeTrace
open GSTNativeCodimensionCyclePresentation
open GSTClassicalHodgeCodimensionZeroFundamentalCycle
open GSTClassicalHodgeSuccessorGroundFloor
open GSTClassicalHodgeRelativeSuccessorNonempty
open GSTClassicalHodgeHeightOneProjectiveRelevance
open GSTClassicalHodgeLimitlessTowerOrbitCrown
open GSTClassicalHodgeNativeMassBridgeAudit
open GSTClassicalHodgeFinalFrontier
open GSTClassicalHodgeDegreeCertifiedFrontier
open GSTClassicalHodgeGlobalSheetSaturation

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-! ## Part I — the vacuity receipts: seeds force live weights
-/

/-- **THE SEED'S NONVANISHING CYCLE.**  Any native Hodge orbit seed carries
an actual native cycle with a nonzero genuine cycle class — the seed
hypothesis is never weaker than one nonzero algebraic class. -/
theorem exists_nonzeroCycleClass_of_nativeHodgeOrbitSeed
    {V : SmoothProjectiveComplexScheme} {H : HodgeBigradedBettiData V}
    {q : Nat}
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := q)) :
    ∃ Z : codimensionCycles V.X q, H.cycleClass q Z ≠ 0 := by
  refine ⟨S.cycle, fun h0 => S.hodge_ne_zero (Subtype.ext ?_)⟩
  rw [S.class_eq] at h0
  exact h0

/-- **THE LIVE-WEIGHT FORCING.**  A native Hodge orbit seed at weight `q`
exists only when the rational Hodge subspace at `q` is nonzero: the
`hodge_ne_zero` field dies on the zero fiber. -/
theorem nativeHodgeOrbitSeed_forces_liveWeight
    {V : SmoothProjectiveComplexScheme} {H : HodgeBigradedBettiData V}
    {q : Nat}
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := q)) :
    rationalHodgeSubspace (H.hodgeBigrading q) ≠ ⊥ := by
  intro hsub
  refine S.hodge_ne_zero (Subtype.ext ?_)
  have hmem :
      (S.hodge : RationalSingularCohomology H.analytification (2 * q)) ∈
        (rationalHodgeSubspace (H.hodgeBigrading q) :
          Submodule ℚ (RationalSingularCohomology H.analytification (2 * q))) :=
    S.hodge.2
  rw [hsub] at hmem
  exact (Submodule.mem_bot (R := ℚ)).mp hmem

/-- **THE DEGREE-CERTIFIED FRONTIER FORCES ALL WEIGHTS LIVE.**  The
unguarded `∀ q` seed family of the degree-certified frontier secretly
demands that every weight be live — the hypothesis is empty on any carrier
with a single dead weight. -/
theorem degreeCertifiedFrontier_forces_allLiveWeights
    (F : DegreeCertifiedFrontierNativeGeometry (V := V) (H := H))
    (q : Nat) :
    rationalHodgeSubspace (H.hodgeBigrading q) ≠ ⊥ :=
  nativeHodgeOrbitSeed_forces_liveWeight (F.seed q)

/-- **THE GREEN FINAL FRONTIER FORCES ALL WEIGHTS LIVE.**  The same receipt
for the earlier frontier, through its native-mass orbit seed. -/
theorem finalFrontier_forces_allLiveWeights
    (F : FinalFrontierNativeGeometry (V := V) (H := H))
    (q : Nat) :
    rationalHodgeSubspace (H.hodgeBigrading q) ≠ ⊥ :=
  nativeHodgeOrbitSeed_forces_liveWeight (seed_of_finalFrontier F q)

/-- **THE FRONTIER'S NONZERO CLASSES.**  Every weight of the degree-certified
frontier carries an actual native cycle with nonzero cycle class. -/
theorem degreeCertifiedFrontier_nonzeroClasses
    (F : DegreeCertifiedFrontierNativeGeometry (V := V) (H := H))
    (q : Nat) :
    ∃ Z : codimensionCycles V.X q, H.cycleClass q Z ≠ 0 :=
  exists_nonzeroCycleClass_of_nativeHodgeOrbitSeed (F.seed q)

/-- The same for the green final frontier. -/
theorem finalFrontier_nonzeroClasses
    (F : FinalFrontierNativeGeometry (V := V) (H := H))
    (q : Nat) :
    ∃ Z : codimensionCycles V.X q, H.cycleClass q Z ≠ 0 :=
  exists_nonzeroCycleClass_of_nativeHodgeOrbitSeed (seed_of_finalFrontier F q)

/-! ## Part II — the guarded crown: dead weights discharge
-/

/-- **THE GUARDED SEED-FAMILY CROWN.**  The exact bigraded Hodge statement
follows from a per-weight seed family demanded only at LIVE weights,
together with the one-live-source projective two-generators guarded the
same way.  Dead weights discharge by the zero class; the hypothesis is
satisfiable exactly where it is needed. -/
theorem bigradedBettiHodge_of_guarded_seed_family
    (S : ∀ q : Nat,
      rationalHodgeSubspace (H.hodgeBigrading q) ≠ ⊥ →
        NativeHodgeOrbitSeed (V := V) (H := H) (p := q))
    (R : ∀ q : Nat,
      ∀ hq : rationalHodgeSubspace (H.hodgeBigrading q) ≠ ⊥,
      ∀ j : ClassicalHodgeBasisIndex V H q,
        ProjectiveTwoGenerator (V := V) (H := H) (S q hq).sourceIndex j) :
    BigradedBettiHodgeStatement V H := by
  intro p alpha halpha
  by_cases hp : rationalHodgeSubspace (H.hodgeBigrading p) = ⊥
  · rw [hp] at halpha
    have h0 : alpha = 0 := (Submodule.mem_bot (R := ℚ)).mp halpha
    subst h0
    exact ⟨0, by simp⟩
  · exact (S p hp).hodge_weight (fun j => (R p hp j).toGeometryFirst) halpha

/-- **THE GUARDED FRONTIER.**  The corrected residual interface: the seed
family and the one-live-source projective two-generators, both confined to
live weights.  No all-live demand anywhere. -/
structure GuardedDegreeCertifiedFrontier
    (V : SmoothProjectiveComplexScheme) (H : HodgeBigradedBettiData V) where
  seed :
    ∀ q : Nat,
    rationalHodgeSubspace (H.hodgeBigrading q) ≠ ⊥ →
      NativeHodgeOrbitSeed (V := V) (H := H) (p := q)
  generator :
    ∀ q : Nat,
    ∀ hq : rationalHodgeSubspace (H.hodgeBigrading q) ≠ ⊥,
    ∀ j : ClassicalHodgeBasisIndex V H q,
      ProjectiveTwoGenerator (V := V) (H := H) (seed q hq).sourceIndex j

/-- **THE OLD FRONTIER CONVERTS INTO THE GUARDED FRONTIER.**  The
degree-certified frontier is a specialization: its unguarded family
instantiates the guarded one (the guard is simply ignored).  The guarded
frontier is strictly weaker — every old frontier is a guarded frontier. -/
noncomputable def degreeCertifiedFrontier_toGuarded
    (F : DegreeCertifiedFrontierNativeGeometry (V := V) (H := H)) :
    GuardedDegreeCertifiedFrontier V H where
  seed := fun q _hq => F.seed q
  generator := fun q _hq => F.generator q

/-- **THE GUARDED CROWN.**  The exact bigraded statement from the guarded
frontier alone. -/
theorem bigradedBettiHodge_of_guarded_frontier
    (F : GuardedDegreeCertifiedFrontier (V := V) (H := H)) :
    BigradedBettiHodgeStatement V H :=
  bigradedBettiHodge_of_guarded_seed_family F.seed F.generator

/-- **THE OLD CROWN REPROVED THROUGH THE GUARDED FRONTIER.**  The
degree-certified frontier routes through the guarded interface — the
structural conversion is conservative. -/
theorem bigradedBettiHodge_of_degreeCertified_via_guarded
    (F : DegreeCertifiedFrontierNativeGeometry (V := V) (H := H)) :
    BigradedBettiHodgeStatement V H :=
  bigradedBettiHodge_of_guarded_frontier (degreeCertifiedFrontier_toGuarded F)

/-- **THE CLASSICAL TARGET FROM THE GUARDED FRONTIER.** -/
theorem classicalHodgeTarget_of_guarded_frontier
    (F : GuardedDegreeCertifiedFrontier (V := V) (H := H)) :
    HodgeConjecture.ClassicalHodgeTarget V H :=
  bigradedBettiHodge_of_guarded_frontier F

/-- **ELEMENTWISE NATIVE-CYCLE FORM.**  Every rational `(p,p)` class is
literally the cycle class of an actual codimension-`p` rational algebraic
cycle, under the guarded frontier alone. -/
theorem every_hodge_class_has_native_cycle_of_guarded_frontier
    (F : GuardedDegreeCertifiedFrontier (V := V) (H := H))
    (p : Nat)
    (alpha : RationalSingularCohomology H.analytification (2 * p))
    (halpha : alpha ∈ rationalHodgeSubspace (H.hodgeBigrading p)) :
    ∃ Z : codimensionCycles V.X p, H.cycleClass p Z = alpha :=
  LinearMap.mem_range.mp
    (bigradedBettiHodge_of_guarded_frontier F p halpha)

/-! ## Part III — the seed combustion: nonvanishing is the whole content
-/

/-- **THE SEED-COMBUSTION THEOREM.**  Given the geometric spine, the seed
hypothesis at any weight is EXACTLY the existence of one native cycle with
nonzero cycle class: the seed's own cycle forward, the genuine Chow orbit
seed backward.  The seed family carries no content beyond nonvanishing. -/
theorem nativeHodgeOrbitSeed_nonempty_iff_exists_nonzeroCycleClass
    (G : GeometricCycleClassSpine V H)
    (q : Nat) :
    Nonempty (NativeHodgeOrbitSeed (V := V) (H := H) (p := q)) ↔
      ∃ Z : codimensionCycles V.X q, H.cycleClass q Z ≠ 0 :=
  ⟨fun ⟨S⟩ => exists_nonzeroCycleClass_of_nativeHodgeOrbitSeed S,
    fun ⟨Z, hZ⟩ => ⟨nativeChowOrbitSeedOfNonzeroClass G q Z hZ⟩⟩

/-- **THE FULLY-COMBUSTED CROWN.**  The exact bigraded Hodge statement from:
the geometric cycle-class spine; one native cycle with nonzero cycle class
at each live weight; and the one-live-source projective two-generators on
the manufactured Chow seeds.  Every hypothesis names irreducible content —
compatibility, nonvanishing, algebraization — with the packaging fully
combusted. -/
theorem bigradedBettiHodge_of_spine_nonzeroClass_family_generators
    (G : GeometricCycleClassSpine V H)
    (Z : ∀ q : Nat,
      rationalHodgeSubspace (H.hodgeBigrading q) ≠ ⊥ →
        codimensionCycles V.X q)
    (hZ : ∀ q : Nat,
      ∀ hq : rationalHodgeSubspace (H.hodgeBigrading q) ≠ ⊥,
        H.cycleClass q (Z q hq) ≠ 0)
    (R : ∀ q : Nat,
      ∀ hq : rationalHodgeSubspace (H.hodgeBigrading q) ≠ ⊥,
      ∀ j : ClassicalHodgeBasisIndex V H q,
        ProjectiveTwoGenerator (V := V) (H := H)
          (nativeChowOrbitSeedOfNonzeroClass G q (Z q hq) (hZ q hq)).sourceIndex j) :
    BigradedBettiHodgeStatement V H :=
  bigradedBettiHodge_of_guarded_seed_family
    (fun q hq => nativeChowOrbitSeedOfNonzeroClass G q (Z q hq) (hZ q hq)) R

/-! ## Part IV — dead-weight vacuity: the basis index emptiness
-/

/-- **THE DEAD-WEIGHT BASIS EMPTINESS.**  At a dead weight the
unrestricted Hodge basis index is empty: the basis of the zero fiber
cannot have a basis vector.  The generator demand at dead weights was
vacuous all along. -/
theorem classicalHodgeBasisIndex_isEmpty_of_deadWeight
    {V : SmoothProjectiveComplexScheme} {H : HodgeBigradedBettiData V}
    {q : Nat}
    (hq : rationalHodgeSubspace (H.hodgeBigrading q) = ⊥) :
    IsEmpty (ClassicalHodgeBasisIndex V H q) := by
  have hsub : Subsingleton (ClassicalHodgeFiber V H q) := by
    constructor
    intro x y
    have hx :
        (x : RationalSingularCohomology H.analytification (2 * q)) = 0 := by
      apply (Submodule.mem_bot (R := ℚ)).mp
      rw [← hq]
      exact x.2
    have hy :
        (y : RationalSingularCohomology H.analytification (2 * q)) = 0 := by
      apply (Submodule.mem_bot (R := ℚ)).mp
      rw [← hq]
      exact y.2
    exact Subtype.ext (by rw [hx, hy])
  refine (not_nonempty_iff).mp (fun hne => ?_)
  obtain ⟨i⟩ := hne
  have h1 : (Finsupp.single i (1 : ℚ) :
      ClassicalHodgeBasisIndex V H q →₀ ℚ) ≠ 0 :=
    Finsupp.single_ne_zero.mpr one_ne_zero
  apply h1
  have h2 : (classicalHodgeBasis V H q).repr.symm
      (Finsupp.single i (1 : ℚ)) = 0 :=
    Subsingleton.elim _ 0
  calc (Finsupp.single i (1 : ℚ))
      = (classicalHodgeBasis V H q).repr
          ((classicalHodgeBasis V H q).repr.symm
            (Finsupp.single i (1 : ℚ))) :=
        ((classicalHodgeBasis V H q).repr.apply_symm_apply _).symm
    _ = (classicalHodgeBasis V H q).repr 0 := by rw [h2]
    _ = 0 := map_zero _

/-- **THE UNGUARDED GENERATOR DEMAND IS VACUOUS AT DEAD WEIGHTS.**  Any
generator value over the empty basis index exists outright — the demand
there carried no content. -/
noncomputable def unguarded_generator_demand_vacuous_at_deadWeight
    {V : SmoothProjectiveComplexScheme} {H : HodgeBigradedBettiData V}
    {q : Nat}
    (hq : rationalHodgeSubspace (H.hodgeBigrading q) = ⊥)
    (i : ClassicalHodgeBasisIndex V H q) :
    ProjectiveTwoGenerator (V := V) (H := H) (p := q) i i := by
  exfalso
  exact (classicalHodgeBasisIndex_isEmpty_of_deadWeight hq).elim i

/-! ## Part V — the converted landings under the guarded interface
-/

/-- **WEIGHT ZERO, GUARDED FORM.**  The degree-certified fundamental seed
manufactures the guarded seed family at weight zero — the guard is ignored
because the seed exists unconditionally there. -/
noncomputable def guarded_seed_zero_of_degree
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (hne : (codimensionZeroPointFinset V).Nonempty) :
    ∀ _hq : rationalHodgeSubspace (H.hodgeBigrading 0) ≠ ⊥,
      NativeHodgeOrbitSeed (V := V) (H := H) (p := 0) :=
  fun _ => fundamentalClassDegreeSeed G D hne

/-- **WEIGHT ONE, GUARDED FORM.**  On an irreducible carrier with a
projectively live ground point, the green ground-floor discharge
manufactures the guarded seed family at weight one. -/
noncomputable def guarded_seed_one_of_ground
    [IrreducibleSpace V.X]
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (x : CodimensionPoint V.X 0)
    (hlive : ProjectivelyLiveSource V.projective.n
      (V.projective.immersion x.1)) :
    ∀ _hq : rationalHodgeSubspace (H.hodgeBigrading 1) ≠ ⊥,
      NativeHodgeOrbitSeed (V := V) (H := H) (p := 1) :=
  fun _ => D.separator_successor_nativeHodgeSeed_of_ground G x hlive

#check exists_nonzeroCycleClass_of_nativeHodgeOrbitSeed
#check nativeHodgeOrbitSeed_forces_liveWeight
#check degreeCertifiedFrontier_forces_allLiveWeights
#check finalFrontier_forces_allLiveWeights
#check degreeCertifiedFrontier_nonzeroClasses
#check finalFrontier_nonzeroClasses
#check bigradedBettiHodge_of_guarded_seed_family
#check GuardedDegreeCertifiedFrontier
#check degreeCertifiedFrontier_toGuarded
#check bigradedBettiHodge_of_guarded_frontier
#check bigradedBettiHodge_of_degreeCertified_via_guarded
#check classicalHodgeTarget_of_guarded_frontier
#check every_hodge_class_has_native_cycle_of_guarded_frontier
#check nativeHodgeOrbitSeed_nonempty_iff_exists_nonzeroCycleClass
#check bigradedBettiHodge_of_spine_nonzeroClass_family_generators
#check classicalHodgeBasisIndex_isEmpty_of_deadWeight
#check unguarded_generator_demand_vacuous_at_deadWeight
#check guarded_seed_zero_of_degree
#check guarded_seed_one_of_ground

#print axioms exists_nonzeroCycleClass_of_nativeHodgeOrbitSeed
#print axioms nativeHodgeOrbitSeed_forces_liveWeight
#print axioms degreeCertifiedFrontier_forces_allLiveWeights
#print axioms finalFrontier_forces_allLiveWeights
#print axioms degreeCertifiedFrontier_nonzeroClasses
#print axioms finalFrontier_nonzeroClasses
#print axioms bigradedBettiHodge_of_guarded_seed_family
#print axioms degreeCertifiedFrontier_toGuarded
#print axioms bigradedBettiHodge_of_guarded_frontier
#print axioms bigradedBettiHodge_of_degreeCertified_via_guarded
#print axioms classicalHodgeTarget_of_guarded_frontier
#print axioms every_hodge_class_has_native_cycle_of_guarded_frontier
#print axioms nativeHodgeOrbitSeed_nonempty_iff_exists_nonzeroCycleClass
#print axioms bigradedBettiHodge_of_spine_nonzeroClass_family_generators
#print axioms classicalHodgeBasisIndex_isEmpty_of_deadWeight
#print axioms unguarded_generator_demand_vacuous_at_deadWeight
#print axioms guarded_seed_zero_of_degree
#print axioms guarded_seed_one_of_ground

end GSTClassicalHodgeGuardedFrontierConversion
