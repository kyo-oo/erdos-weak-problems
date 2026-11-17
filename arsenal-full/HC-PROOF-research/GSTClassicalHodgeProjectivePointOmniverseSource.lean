import GSTClassicalHodgeOmniverseStrictEventStability
import GSTClassicalHodgeProjectiveDegreeTrace
import GSTClassicalHodgePiUnboundedOmniverseCrown

/-!
# GST CLASSICAL HODGE — PROJECTIVE POINT OMNIVERSE SOURCE

The degree-certified omniverse route previously manufactured its nonzero
algebraic source through a selected principal-cut successor, which carried two
extra geometric premises (`ProjectivelyLiveSource` and an ambient exact-stratum
identity).  Those premises are unnecessary once the projective-degree trace is
available.

Every genuine codimension-p projective point already gives a unit algebraic
cycle.  Its Betti trace is its strictly positive projective degree, so its cycle
class is nonzero.  The geometric cycle-class spine says every algebraic cycle
class is Hodge.  Thus ANY codimension-p point is a canonical nonzero algebraic
Hodge source in weight p.

Feeding that source into the strict three-sector omniverse theorem makes every
Hodge basis sheet algebraic; finite-support reconstruction then gives the whole
weight.  No separator successor, native-mass bridge, cyclicity, saturation, or
preselected matrix unit is used.
-/

set_option maxHeartbeats 140000000
set_option maxRecDepth 1000000

noncomputable section

open scoped BigOperators
open AlgebraicGeometry

namespace GSTClassicalHodgeProjectivePointOmniverseSource

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeProjectiveDegreeTrace
open GSTClassicalHodgeOmniverseCausalBranchPacket
open GSTClassicalHodgeOmniverseStrictEventStability
open GSTClassicalHodgePiUnboundedOmniverseCrown

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- **PROJECTIVE POINT CLASSES NEVER VANISH.**
This is an immediate consequence of the genuine projective-degree/Betti trace:
if the point cycle class vanished, its trace would be zero, contradicting the
strict positivity of projective degree. -/
theorem pointCycle_cycleClass_ne_zero
    (D : ProjectiveDegreeTraceSemantics V H)
    (p : Nat)
    (x : CodimensionPoint V.X p) :
    H.cycleClass p (codimensionPointCycle V.X p x) ≠ 0 := by
  intro hzero
  have htrace := D.trace_point_cycleClass p x
  rw [hzero, LinearMap.map_zero] at htrace
  have hpos := D.pointDegree_pos p x
  rw [← htrace] at hpos
  exact lt_irrefl 0 hpos

/-- Any genuine codimension-p point therefore supplies a nonzero algebraic
Hodge state. -/
noncomputable def pointHodgeSource
    (G : GeometricCycleClassSpine V H)
    (p : Nat)
    (x : CodimensionPoint V.X p) : ClassicalHodgeFiber V H p :=
  ⟨H.cycleClass p (codimensionPointCycle V.X p x),
    G.algebraic_is_hodge p (codimensionPointCycle V.X p x)⟩

/-- The point source is nonzero by projective degree. -/
theorem pointHodgeSource_ne_zero
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (p : Nat)
    (x : CodimensionPoint V.X p) :
    pointHodgeSource G p x ≠ 0 := by
  intro hz
  have hval :
      H.cycleClass p (codimensionPointCycle V.X p x) = 0 :=
    congrArg Subtype.val hz
  exact pointCycle_cycleClass_ne_zero D p x hval

/-- The point source is literally in the true cycle-class range. -/
theorem pointHodgeSource_algebraic
    (G : GeometricCycleClassSpine V H)
    (p : Nat)
    (x : CodimensionPoint V.X p) :
    (pointHodgeSource G p x).1 ∈ LinearMap.range (H.cycleClass p) := by
  exact ⟨codimensionPointCycle V.X p x, rfl⟩

/-- **ARBITRARY PROJECTIVE POINT + FULL OMNIVERSE CROWN.**
An actual codimension-p projective point supplies the only seed needed by the
full strict omniverse.  Hence strict materialization of the primitive GST
branch events forces the entire rational Hodge weight p into the true cycle
class range. -/
theorem hodge_weight_of_projectivePoint_strictOmniverse
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (hgeom :
      ∀ {u v : HodgeBranchNode (V := V) (H := H) (p := p)},
        (hodgeBranchGraph (V := V) (H := H) (p := p)).Event u v →
          StrictlyMaterializedBranch u v) :
    rationalHodgeSubspace (H.hodgeBigrading p) ≤
      LinearMap.range (H.cycleClass p) := by
  exact hodge_weight_of_strictOmniverse
    (pointHodgeSource G p x)
    (pointHodgeSource_ne_zero G D p x)
    (pointHodgeSource_algebraic G p x)
    hgeom

/-- Weight-local existential form: it is enough that one codimension-p point
exists; no distinguished point or successor construction is needed. -/
theorem hodge_weight_of_nonempty_codimension_strictOmniverse
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (p : Nat)
    (hx : Nonempty (CodimensionPoint V.X p))
    (hgeom :
      ∀ {u v : HodgeBranchNode (V := V) (H := H) (p := p)},
        (hodgeBranchGraph (V := V) (H := H) (p := p)).Event u v →
          StrictlyMaterializedBranch u v) :
    rationalHodgeSubspace (H.hodgeBigrading p) ≤
      LinearMap.range (H.cycleClass p) := by
  let x := Classical.choice hx
  exact hodge_weight_of_projectivePoint_strictOmniverse G D p x hgeom

/-- **PI-WIDE POINT-SOURCE OMNIVERSE CROWN.**
For an arbitrary smooth complex projective variety, if every live Hodge weight
contains at least one genuine codimension-p projective point and all primitive
GST causal branches have the already-defined strict scheme materialization,
then the exact Stage-2G rational Hodge statement follows in every weight.

The live-weight condition is deliberately weaker than asking for points in
formally dead codimensions: when the rational (p,p) fiber is bottom, the Hodge
inclusion is vacuous. -/
theorem bigradedBettiHodge_of_projectivePoint_strictOmniverse
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (hpoint : ∀ p : Nat,
      rationalHodgeSubspace (H.hodgeBigrading p) ≠ ⊥ →
        Nonempty (CodimensionPoint V.X p))
    (hgeom : ∀ p : Nat,
      ∀ {u v : HodgeBranchNode (V := V) (H := H) (p := p)},
        (hodgeBranchGraph (V := V) (H := H) (p := p)).Event u v →
          StrictlyMaterializedBranch u v) :
    BigradedBettiHodgeStatement V H := by
  intro p alpha halpha
  by_cases hp : rationalHodgeSubspace (H.hodgeBigrading p) = ⊥
  · have hz : alpha = 0 := by
      have hbot : alpha ∈
          (⊥ : Submodule ℚ
            (RationalSingularCohomology H.analytification (2 * p))) := by
        simpa [hp] using halpha
      simpa using hbot
    subst alpha
    exact LinearMap.zero_mem _
  · exact hodge_weight_of_nonempty_codimension_strictOmniverse
      G D p (hpoint p hp) (hgeom p) halpha

#check pointCycle_cycleClass_ne_zero
#check pointHodgeSource
#check pointHodgeSource_ne_zero
#check pointHodgeSource_algebraic
#check hodge_weight_of_projectivePoint_strictOmniverse
#check hodge_weight_of_nonempty_codimension_strictOmniverse
#check bigradedBettiHodge_of_projectivePoint_strictOmniverse

#print axioms pointCycle_cycleClass_ne_zero
#print axioms pointHodgeSource_ne_zero
#print axioms hodge_weight_of_projectivePoint_strictOmniverse
#print axioms bigradedBettiHodge_of_projectivePoint_strictOmniverse

end GSTClassicalHodgeProjectivePointOmniverseSource
