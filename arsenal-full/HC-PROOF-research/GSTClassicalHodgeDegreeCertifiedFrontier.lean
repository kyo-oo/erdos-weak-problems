import GSTClassicalHodgeFinalFrontier
import GSTClassicalHodgeProjectiveDegreeTrace
import GSTClassicalHodgeNativeMassBridgeAudit
import GSTClassicalHodgeSuccessorGroundFloor
import GSTClassicalHodgeRelativeSuccessorNonempty

/-!
# THE DEGREE-CERTIFIED FRONTIER — the hypothesis-conversion strike

The green final frontier (`GSTClassicalHodgeFinalFrontier`) still carried the
GLOBAL `NativeMassCycleClassBridge` as its mass-side input.  The audit
(`GSTClassicalHodgeNativeMassBridgeAudit`) proved that bridge equivalent to
three laws whose third member — every native point having EXACTLY TWO exact
relative successors — is choice-dependent separator-divisor geometry, and that
a single terminal point (an empty exact-successor locus) makes the global
bridge EMPTY.  Closed points at maximal codimension are terminal on every
positive-dimensional carrier: the global bridge is unsatisfiable on honest
geometry.  It can never be converted into a theorem, because it is not true.

This file performs the structural conversion:

* **THE GLOBAL MASS BRIDGE IS ELIMINATED FROM THE CROWN INTERFACE.**  The
  per-weight orbit machinery (`NativeHodgeOrbitSeed.hodge_weight`) never
  consumed the global charge — only the per-weight SEED (a nonzero algebraic
  Hodge state with a native cycle representative).  The seed-family crown
  below makes that consumption explicit: any per-weight seed family plus the
  one-live-source projective two-generators closes the exact statement.  The
  old frontier's own crown is reproved through this route, exhibiting the
  global bridge as pure packaging around the seeds it happened to manufacture.
* **THE BASE NONVANISHING LAW IS CONVERTED INTO A THEOREM.**  The degree-trace
  artery (`ProjectiveDegreeTraceSemantics`, kernel-green) evaluates the
  fundamental cycle's class as the weighted sum of strictly positive component
  degrees; a nonempty component locus therefore forces the codimension-zero
  fundamental class to be nonzero.  `fundamentalClassDegreeSeed` turns that
  theorem directly into the weight-zero orbit seed.
* **THE WEIGHT-ONE GROUND SEED IS CONVERTED INTO AN INTERFACE THEOREM.**  The
  already-green ground-floor discharge (irreducible carrier, projectively live
  generic point) manufactures the weight-one seed with no exactness premise;
  this file composes it with the one-live-source generators.
* **THE TERMINAL-CUT PRODUCTION.**  Every closed point at maximal codimension
  is exhibited as a terminal cut, producing the audit's no-go hypothesis on
  honest carriers and sealing the impossibility receipt of the global bridge.
* **THE HORIZON-FAMILY CROWN.**  The audit's `FiniteHorizonNativeMassBridge`
  (the honest, terminal-cut-surviving replacement) is wired into the seed
  family: a horizon-q bridge manufactures the weight-q spine seed by conserved
  native mass, so the horizon family plus per-weight generators closes the
  statement with no global law anywhere.

What remains as the named irreducible frontier: the geometric cycle-class
spine, the projective degree-trace semantics, the per-weight seeds (converted
at weights zero and one above), and the one-live-source projective
two-generators.  The corpus's own separation theorems certify that none of
these is packaging.

Zero sorry, zero new axioms, zero hypotheses beyond the named frontier.
-/

set_option maxHeartbeats 40000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry
open TopologicalSpace

namespace GSTClassicalHodgeDegreeCertifiedFrontier

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
open GSTClassicalHodgeSingleExactSuccessorSurvival
open GSTClassicalHodgePointClosureRelativeCut
open GSTClassicalHodgePointClosureIrreducible
open GSTClassicalHodgePointClosurePrincipalCut
open GSTClassicalHodgePrincipalCutSuccessorOperator
open GSTClassicalHodgeNativeCycleCosmicShadow
open GSTClassicalHodgeSuccessorGroundFloor
open GSTClassicalHodgeRelativeSuccessorNonempty
open GSTClassicalHodgeHeightOneProjectiveRelevance
open GSTClassicalHodgeLimitlessTowerOrbitCrown
open GSTClassicalHodgeNativeMassBridgeAudit
open GSTClassicalHodgeFinalFrontier

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-! ## The seed-family crown — the global mass bridge structurally eliminated
-/

/-- **SEED-FAMILY PROJECTIVE CROWN.**
The exact bigraded Hodge statement follows from a per-weight family of nonzero
algebraic Hodge states with native cycle representatives, together with the
one-live-source projective two-generators.  No global conserved charge, no
global mass bridge, no all-pairs generator family: the per-weight orbit
extraction is the only consumer, and it is weight-local. -/
theorem bigradedBettiHodge_of_seed_family_projective_generators
    (S : ∀ q : Nat, NativeHodgeOrbitSeed (V := V) (H := H) (p := q))
    (R : ∀ q : Nat,
      ∀ j : ClassicalHodgeBasisIndex V H q,
        ProjectiveTwoGenerator (V := V) (H := H) (S q).sourceIndex j) :
    BigradedBettiHodgeStatement V H := by
  intro q alpha halpha
  exact (S q).hodge_weight (fun j => (R q j).toGeometryFirst) halpha

/-- The old green frontier manufactures exactly such a seed family through the
native-mass orbit seed; recorded as the compatibility witness. -/
noncomputable def seed_of_finalFrontier
    (F : FinalFrontierNativeGeometry (V := V) (H := H))
    (q : Nat) :
    NativeHodgeOrbitSeed (V := V) (H := H) (p := q) :=
  nativeMassSpineOrbitSeed F.spine F.mass q

/-- **THE GREEN CROWN REPROVED THROUGH THE SEED FAMILY.**  The global mass
bridge of the final frontier was never consumed as a global package: only the
seeds it manufactures enter the per-weight orbit extraction.  This alternate
proof of the green crown makes the structural fact explicit. -/
theorem bigradedBettiHodge_of_finalFrontier_via_seed_family
    (F : FinalFrontierNativeGeometry (V := V) (H := H)) :
    BigradedBettiHodgeStatement V H :=
  bigradedBettiHodge_of_seed_family_projective_generators
    (fun q => nativeMassSpineOrbitSeed F.spine F.mass q) F.generator

/-! ## The base nonvanishing law converted into a theorem
-/

open Classical in
/-- Exact coefficient shape of the canonical codimension-zero presentation. -/
theorem codimensionZeroPresentation_apply
    (V : SmoothProjectiveComplexScheme)
    (x : CodimensionPoint V.X 0) :
    codimensionZeroPresentation V x =
      (if x ∈ codimensionZeroPointFinset V then (1 : ℚ) else 0) := by
  classical
  simp [codimensionZeroPresentation, Finsupp.finsetSum_apply,
    Finsupp.single_apply, Finset.sum_ite_eq']

/-- Every coefficient of the canonical base presentation is nonnegative. -/
theorem codimensionZeroPresentation_nonneg
    (V : SmoothProjectiveComplexScheme)
    (x : CodimensionPoint V.X 0) :
    0 ≤ codimensionZeroPresentation V x := by
  classical
  by_cases hx : x ∈ codimensionZeroPointFinset V
  · rw [codimensionZeroPresentation_apply V x, if_pos hx]
    norm_num
  · rw [codimensionZeroPresentation_apply V x, if_neg hx]

/-- A nonempty component locus makes the canonical base presentation nonzero. -/
theorem codimensionZeroPresentation_ne_zero
    (V : SmoothProjectiveComplexScheme)
    (hne : (codimensionZeroPointFinset V).Nonempty) :
    codimensionZeroPresentation V ≠ 0 := by
  obtain ⟨x, hx⟩ := hne
  intro h0
  have h1 : codimensionZeroPresentation V x = 1 := by
    rw [codimensionZeroPresentation_apply V x, if_pos hx]
  rw [h0] at h1
  simp at h1

/-- **BASE NONVANISHING CONVERTED.**
The old `base_mass_ne_zero` field of the mass bridge — the codimension-zero
fundamental cycle has nonzero native mass — is superseded on the degree route
by this theorem: with the projective degree-trace semantics and a nonempty
component locus, the genuine Betti class of the fundamental cycle is nonzero.
The base mass law is no longer an input; it is a consequence of degree
positivity. -/
theorem fundamentalCycleClass_ne_zero_of_degree
    (D : ProjectiveDegreeTraceSemantics V H)
    (hne : (codimensionZeroPointFinset V).Nonempty) :
    H.cycleClass 0 (codimensionZeroFundamentalCycle V) ≠ 0 := by
  have hnz : codimensionZeroPresentation V ≠ 0 :=
    codimensionZeroPresentation_ne_zero V hne
  have hcoeff : ∀ x : CodimensionPoint V.X 0,
      0 ≤ codimensionZeroPresentation V x :=
    fun x => codimensionZeroPresentation_nonneg V x
  have hpos := D.trace_positive_of_effective_presentation 0
    (codimensionZeroPresentation V) hcoeff hnz
  intro hzero
  rw [show codimensionZeroFundamentalCycle V =
      realizeFiniteCodimensionPresentation V.X 0
        (codimensionZeroPresentation V) from rfl] at hzero
  rw [hzero, map_zero] at hpos
  exact lt_irrefl 0 hpos

/-- **THE WEIGHT-ZERO ORBIT SEED, CONVERTED.**  The fundamental class, certified
nonzero by positive projective degree, is a genuine native orbit seed at weight
zero — the base case of the seed family needs no mass bridge at all. -/
noncomputable def fundamentalClassDegreeSeed
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (hne : (codimensionZeroPointFinset V).Nonempty) :
    NativeHodgeOrbitSeed (V := V) (H := H) (p := 0) := by
  refine {
    cycle := codimensionZeroFundamentalCycle V
    hodge := ⟨H.cycleClass 0 (codimensionZeroFundamentalCycle V),
      G.codimensionZeroFundamentalClass_is_hodge⟩
    hodge_ne_zero := ?_
    class_eq := rfl
  }
  intro hz
  have hval : H.cycleClass 0 (codimensionZeroFundamentalCycle V) = 0 :=
    congrArg Subtype.val hz
  exact fundamentalCycleClass_ne_zero_of_degree D hne hval

/-- **WEIGHT-ZERO LANDING, CONVERTED.**  The full weight-zero Hodge statement
follows from the degree-certified fundamental seed and the one-live-source
projective two-generators — no mass law, no finiteness package. -/
theorem hodge_weight_zero_of_degree
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (hne : (codimensionZeroPointFinset V).Nonempty)
    (R : ∀ j : ClassicalHodgeBasisIndex V H 0,
      ProjectiveTwoGenerator (V := V) (H := H)
        (fundamentalClassDegreeSeed G D hne).sourceIndex j) :
    rationalHodgeSubspace (H.hodgeBigrading 0) ≤
      LinearMap.range (H.cycleClass 0) :=
  (fundamentalClassDegreeSeed G D hne).hodge_weight
    (fun j => (R j).toGeometryFirst)

/-! ## The weight-one ground seed — the green discharge, composed
-/

/-- **WEIGHT-ONE LANDING, CONVERTED.**  On an irreducible carrier with a
projectively live generic point, the green ground-floor discharge manufactures
the weight-one degree-certified seed with no exactness premise; the
one-live-source projective two-generators then close the weight-one Hodge
statement. -/
theorem hodge_weight_one_of_ground_degree
    [IrreducibleSpace V.X]
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (x : CodimensionPoint V.X 0)
    (hlive : ProjectivelyLiveSource V.projective.n
      (V.projective.immersion x.1))
    (R : ∀ j : ClassicalHodgeBasisIndex V H 1,
      ProjectiveTwoGenerator (V := V) (H := H)
        (D.separator_successor_nativeHodgeSeed_of_ground G x hlive).sourceIndex j) :
    rationalHodgeSubspace (H.hodgeBigrading 1) ≤
      LinearMap.range (H.cycleClass 1) :=
  (D.separator_successor_nativeHodgeSeed_of_ground G x hlive).hodge_weight
    (fun j => (R j).toGeometryFirst)

/-! ## The horizon-family crown — the honest terminal-cut-surviving replacement
-/

/-- A horizon-q native-mass bridge manufactures the weight-q spine seed by
conserved mass; the global charge is not needed anywhere. -/
noncomputable def horizonSpineSeed
    (G : GeometricCycleClassSpine V H)
    (q : Nat)
    (M : FiniteHorizonNativeMassBridge V H q) :
    NativeHodgeOrbitSeed (V := V) (H := H) (p := q) where
  cycle := spineNativeTower G q
  hodge := spineHodgeSeed G q
  hodge_ne_zero := M.spine_hodgeSeed_ne_zero G q (le_refl q)
  class_eq := spineNativeTower_cycleClass G q

/-- **HORIZON-FAMILY PROJECTIVE CROWN.**  The honest replacement of the dead
global bridge: a per-weight horizon family (each level's successor law only
strictly below that level, so terminal cuts at maximal codimension never
enter) plus the one-live-source projective two-generators closes the exact
bigraded statement. -/
theorem bigradedBettiHodge_of_horizon_family_projective_generators
    (G : GeometricCycleClassSpine V H)
    (M : ∀ q : Nat, FiniteHorizonNativeMassBridge V H q)
    (R : ∀ q : Nat,
      ∀ j : ClassicalHodgeBasisIndex V H q,
        ProjectiveTwoGenerator (V := V) (H := H)
          (horizonSpineSeed G q (M q)).sourceIndex j) :
    BigradedBettiHodgeStatement V H :=
  bigradedBettiHodge_of_seed_family_projective_generators
    (fun q => horizonSpineSeed G q (M q)) R

/-! ## The corrected frontier and its crowns
-/

/-- **THE DEGREE-CERTIFIED FRONTIER.**  The corrected residual native law
system: the geometric spine, the projective degree-trace semantics, the
per-weight nonzero algebraic seed family, and the one-live-source projective
two-generators.  The global mass bridge is gone — structurally eliminated, not
weakened — and the seeds at weights zero and one are theorems above whenever
the base nonemptiness / ground-floor liveness conditions hold. -/
structure DegreeCertifiedFrontierNativeGeometry where
  spine : GeometricCycleClassSpine V H
  degree : ProjectiveDegreeTraceSemantics V H
  seed : ∀ q : Nat, NativeHodgeOrbitSeed (V := V) (H := H) (p := q)
  generator :
    ∀ q : Nat,
    ∀ j : ClassicalHodgeBasisIndex V H q,
      ProjectiveTwoGenerator (V := V) (H := H)
        (seed q).sourceIndex j

/-- **THE DEGREE-CERTIFIED CROWN.**  The exact bigraded statement from the
corrected frontier alone. -/
theorem bigradedBettiHodge_of_degree_certified_frontier
    (F : DegreeCertifiedFrontierNativeGeometry (V := V) (H := H)) :
    BigradedBettiHodgeStatement V H :=
  bigradedBettiHodge_of_seed_family_projective_generators
    F.seed F.generator

/-- **THE CLASSICAL TARGET FROM THE DEGREE-CERTIFIED FRONTIER.** -/
theorem classicalHodgeTarget_of_degree_certified_frontier
    (F : DegreeCertifiedFrontierNativeGeometry (V := V) (H := H)) :
    HodgeConjecture.ClassicalHodgeTarget V H :=
  bigradedBettiHodge_of_degree_certified_frontier F

/-- **ELEMENTWISE NATIVE-CYCLE FORM.**  Every rational (p,p) class is literally
the cycle class of an actual codimension-p rational algebraic cycle, under the
degree-certified frontier alone. -/
theorem every_hodge_class_has_native_cycle_of_degree_certified_frontier
    (F : DegreeCertifiedFrontierNativeGeometry (V := V) (H := H))
    (p : Nat)
    (alpha : RationalSingularCohomology H.analytification (2 * p))
    (halpha : alpha ∈ rationalHodgeSubspace (H.hodgeBigrading p)) :
    ∃ Z : codimensionCycles V.X p, H.cycleClass p Z = alpha :=
  LinearMap.mem_range.mp
    (bigradedBettiHodge_of_degree_certified_frontier F p halpha)

/-! ## The terminal-cut production — the impossibility receipt of the global bridge
-/

/-- **GROUND-FLOOR COLLAPSE OF THE EXACT FILTER.**  At weight zero on an
irreducible carrier, every relative successor is exact: the audited exact
successor finset coincides with the raw separator-cut finset. -/
theorem exactRelativeSuccessorFinset_eq_relative_of_ground
    (V : SmoothProjectiveComplexScheme) [IrreducibleSpace V.X]
    (x : CodimensionPoint V.X 0) :
    exactRelativeSuccessorFinset V 0 x = relativeCodimensionOneFinset V x.1 := by
  refine Finset.ext fun y => ?_
  refine (mem_exactRelativeSuccessorFinset V 0 x y).trans ?_
  constructor
  · exact fun h => h.1
  · intro hy
    exact ⟨hy,
      relativeSuccessorAmbientExact_of_coheight_zero (V := V) x y hy⟩

/-- **THE GROUND SUCCESSOR CROWN.**  A projectively live ground point has a
nonempty exact successor locus, nonzero successor mass, and a nonzero
geometry-built principal-cut successor cycle — every component unconditional
on an irreducible carrier. -/
theorem ground_successor_crown_of_live
    (V : SmoothProjectiveComplexScheme) [IrreducibleSpace V.X]
    (x : CodimensionPoint V.X 0)
    (hlive : ProjectivelyLiveSource V.projective.n
      (V.projective.immersion x.1)) :
    (exactRelativeSuccessorFinset V 0 x).card =
        (relativeCodimensionOneFinset V x.1).card
      ∧ 0 < (exactRelativeSuccessorFinset V 0 x).card
      ∧ successorMass V 0 x ≠ 0
      ∧ successorNativeOperator V 0
          (codimensionPointCycle V.X 0 x) ≠ 0 := by
  have hne : (relativeCodimensionOneFinset V x.1).Nonempty :=
    relativeCodimensionOneFinset_nonempty V x.1 hlive
  have hcrown := relative_successor_exact_stratum_crown_of_ground (V := V) x hne
  have hcardEq := exactRelativeSuccessorFinset_eq_relative_of_ground V x
  refine ⟨by rw [hcardEq], ?_, hcrown.2.1, hcrown.2.2⟩
  rw [hcardEq]
  exact Finset.card_pos.mpr hne

/-- **THE HONEST PRICING OF THE DEAD LAW.**  At the ground weight, the old
pointwise successor-mass law is exactly the statement that the separator cut
has two irreducible components — a choice-dependent cardinality constraint on
an arbitrarily selected equation, not a theorem of the geometry. -/
theorem successor_point_mass_ground_iff_two_separator_components
    (V : SmoothProjectiveComplexScheme) [IrreducibleSpace V.X]
    (x : CodimensionPoint V.X 0) :
    successorMass V 0 x = successorScalar 0 ↔
      (relativeCodimensionOneFinset V x.1).card = 2 := by
  rw [successorMass_eq_successorScalar_iff_exactRelativeCard_two V 0 x,
    exactRelativeSuccessorFinset_eq_relative_of_ground V x]

/-- The global pointwise law would force every live ground separator cut to
have exactly two components — the receipt that it is false geometry. -/
theorem ground_pointMassLaw_forces_two_separator_components
    (V : SmoothProjectiveComplexScheme) [IrreducibleSpace V.X]
    (x : CodimensionPoint V.X 0)
    (hlive : ProjectivelyLiveSource V.projective.n
      (V.projective.immersion x.1))
    (hM : ∀ q : Nat, ∀ z : CodimensionPoint V.X q,
      successorMass V q z = successorScalar q) :
    (relativeCodimensionOneFinset V x.1).card = 2
      ∧ 0 < (relativeCodimensionOneFinset V x.1).card := by
  refine ⟨(successor_point_mass_ground_iff_two_separator_components V x).1
      (hM 0 x), relativeCodimensionOneFinset_card_pos V x.1 hlive⟩

/-- **TERMINAL-CUT PRODUCTION.**  A point whose closure is a singleton — every
closed point at maximal codimension — has an empty exact-successor locus. -/
theorem exactRelativeSuccessorFinset_eq_empty_of_closedPoint
    (V : SmoothProjectiveComplexScheme) (p : Nat)
    (x : CodimensionPoint V.X p)
    (hcl : closure ({x.1} : Set V.X) = ({x.1} : Set V.X)) :
    exactRelativeSuccessorFinset V p x = ∅ := by
  have hsub : ∀ y : pointClosureScheme V x.1,
      pointClosureι V x.1 y = x.1 := by
    intro y
    have hmem : pointClosureι V x.1 y ∈ Set.range (pointClosureι V x.1) :=
      ⟨y, rfl⟩
    rw [range_pointClosureι V x.1, hcl] at hmem
    exact Set.mem_singleton_iff.mp hmem
  have hgeneric : ∀ y : pointClosureScheme V x.1,
      y = closureGenericPoint V x.1 := by
    intro y
    apply (pointClosureι V x.1).isEmbedding.injective
    rw [hsub y, closureGenericPoint_maps_to_source]
  have hfalse : ∀ y : {y : pointClosureScheme V x.1 // Order.coheight y = 1},
      False := by
    intro y
    have hy1 := y.2
    rw [hgeneric y.1, closureGenericPoint_coheight_zero V x.1] at hy1
    norm_num at hy1
  refine Finset.ext fun y => ?_
  exact (hfalse y).elim

/-- **THE GLOBAL BRIDGE IS EMPTY ON EVERY CARRIER WITH A CLOSED POINT.**  The
terminal cut above produces the audit's no-go hypothesis, so the global
`NativeMassCycleClassBridge` is unsatisfiable there.  This is the
impossibility receipt that made the structural conversion necessary. -/
theorem no_global_nativeMassBridge_of_closedPoint
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat) (x : CodimensionPoint V.X p)
    (hcl : closure ({x.1} : Set V.X) = ({x.1} : Set V.X)) :
    IsEmpty (NativeMassCycleClassBridge V H) :=
  no_global_nativeMassBridge_of_terminalCut (V := V) (H := H) p x
    (exactRelativeSuccessorFinset_eq_empty_of_closedPoint V p x hcl)

/-- **HORIZON-ZERO BRIDGES ARE CHEAP.**  With the kernel law and the base
nonvanishing alone, a horizon-zero bridge exists: its successor field is
vacuous because no weight is strictly below zero. -/
theorem finiteHorizonBridge_zero_of_kernel_base
    {V : SmoothProjectiveComplexScheme} {H : HodgeBigradedBettiData V}
    (K : NativeMassKernelLaw (V := V) (H := H))
    (hb : nativeCycleMass V 0 (codimensionZeroFundamentalCycle V) ≠ 0) :
    Nonempty (FiniteHorizonNativeMassBridge V H 0) :=
  ⟨{
    kernel_mass_zero := fun p _hp Z hZ => K p Z hZ
    base_mass_ne_zero := hb
    successor_point_mass := fun p hp => absurd hp (Nat.not_lt_zero p)
  }⟩

#check bigradedBettiHodge_of_seed_family_projective_generators
#check seed_of_finalFrontier
#check bigradedBettiHodge_of_finalFrontier_via_seed_family
#check codimensionZeroPresentation_apply
#check codimensionZeroPresentation_nonneg
#check codimensionZeroPresentation_ne_zero
#check fundamentalCycleClass_ne_zero_of_degree
#check fundamentalClassDegreeSeed
#check hodge_weight_zero_of_degree
#check hodge_weight_one_of_ground_degree
#check horizonSpineSeed
#check bigradedBettiHodge_of_horizon_family_projective_generators
#check DegreeCertifiedFrontierNativeGeometry
#check bigradedBettiHodge_of_degree_certified_frontier
#check classicalHodgeTarget_of_degree_certified_frontier
#check every_hodge_class_has_native_cycle_of_degree_certified_frontier
#check exactRelativeSuccessorFinset_eq_relative_of_ground
#check ground_successor_crown_of_live
#check successor_point_mass_ground_iff_two_separator_components
#check ground_pointMassLaw_forces_two_separator_components
#check exactRelativeSuccessorFinset_eq_empty_of_closedPoint
#check no_global_nativeMassBridge_of_closedPoint
#check finiteHorizonBridge_zero_of_kernel_base

#print axioms bigradedBettiHodge_of_seed_family_projective_generators
#print axioms bigradedBettiHodge_of_finalFrontier_via_seed_family
#print axioms codimensionZeroPresentation_apply
#print axioms codimensionZeroPresentation_nonneg
#print axioms codimensionZeroPresentation_ne_zero
#print axioms fundamentalCycleClass_ne_zero_of_degree
#print axioms fundamentalClassDegreeSeed
#print axioms hodge_weight_zero_of_degree
#print axioms hodge_weight_one_of_ground_degree
#print axioms horizonSpineSeed
#print axioms bigradedBettiHodge_of_horizon_family_projective_generators
#print axioms bigradedBettiHodge_of_degree_certified_frontier
#print axioms classicalHodgeTarget_of_degree_certified_frontier
#print axioms every_hodge_class_has_native_cycle_of_degree_certified_frontier
#print axioms exactRelativeSuccessorFinset_eq_relative_of_ground
#print axioms ground_successor_crown_of_live
#print axioms successor_point_mass_ground_iff_two_separator_components
#print axioms ground_pointMassLaw_forces_two_separator_components
#print axioms exactRelativeSuccessorFinset_eq_empty_of_closedPoint
#print axioms no_global_nativeMassBridge_of_closedPoint
#print axioms finiteHorizonBridge_zero_of_kernel_base

end GSTClassicalHodgeDegreeCertifiedFrontier
