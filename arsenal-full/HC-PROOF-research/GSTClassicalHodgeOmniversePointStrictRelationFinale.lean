import GSTClassicalHodgeProjectivePointOmniverseSource
import GSTClassicalHodgeDegreeCertifiedStrictRelationFinale
import GSTClassicalHodgeSynchronizedDefectOrbit
import GSTClassicalHodgeBasisCycleBridge

/-!
# GST CLASSICAL HODGE — PROJECTIVE-POINT / STRICT-RELATION FINALE

The strict-relation route previously specialized its algebraic source through a
principal-cut separator successor.  That introduced two source-side premises
which are unrelated to the actual target transfer problem:

* a `ProjectivelyLiveSource` witness;
* an exact ambient codimension identity for the chosen successor.

Projective degree makes both unnecessary.  Any genuine codimension-p point of
a smooth complex projective carrier already has a nonzero rational Betti cycle
class.  The geometric cycle-class spine places that class in the Hodge fiber,
so the point itself is a synchronized nonzero algebraic apex.

For each requested target basis sheet we now require only the lower-level raw
strict relation from `GSTClassicalHodgeDegreeCertifiedStrictRelationFinale`:

  leftPullback(apex)
    = rightPullback(sourceCoefficient * targetBasis).

A finite Betti trace makes the related target unique, hence derives the
push-pull source action.  Point-cycle compatibility gives an honest realized
finite closed correspondence, and the synchronized native operator then
constructs the target basis cycle.

Thus the fixed-weight frontier is stripped to:

  one actual codimension-p projective point
    + one raw bi-finite Betti relation per target sheet.

No separator successor, exact-stratum premise, ambient operator equation,
matrix-unit realization, code observable, native-mass bridge, cyclicity, or
all-event materialization is used.
-/

set_option maxHeartbeats 120000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeOmniversePointStrictRelationFinale

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeProjectiveDegreeTrace
open GSTClassicalHodgeProjectivePointOmniverseSource
open GSTClassicalHodgeSynchronizedDefectOrbit
open GSTClassicalHodgeSchemeFiniteCorrespondenceFirewall
open GSTClassicalHodgeFiniteClosedCorrespondence
open GSTClassicalHodgeStrictCorrespondenceAnalyticSpan
open GSTClassicalHodgeStrictCorrespondenceBettiTracePushPull
open GSTClassicalHodgeDegreeCertifiedStrictRelationFinale

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- Any genuine codimension-p projective point is a synchronized nonzero
algebraic apex.  Nonvanishing is certified by projective degree. -/
noncomputable def pointApexSeed
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (p : Nat)
    (x : CodimensionPoint V.X p) :
    NativeHodgeOrbitSeed (V := V) (H := H) (p := p) where
  cycle := codimensionPointCycle V.X p x
  hodge := pointHodgeSource G p x
  hodge_ne_zero := pointHodgeSource_ne_zero G D p x
  class_eq := rfl

/-- **ONE RAW STRICT RELATION -> TARGET BASIS CYCLE FROM A POINT APEX.** -/
theorem targetCycle_ofPointStrictRelation
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (j : ClassicalHodgeBasisIndex V H p)
    (K : SchemeBiFiniteClosedCorrespondence V)
    (T : RightFiniteBettiTrace H.analytification K (2 * p))
    (C : PointCycleCompatibility (n := p) K T)
    (hrel : BettiRelated H.analytification K (2 * p)
      (pointApexSeed G D p x).hodge.1
      ((classicalHodgeBasis V H p).repr
          (pointApexSeed G D p x).hodge
          (pointApexSeed G D p x).sourceIndex •
        (classicalHodgeBasis V H p j).1)) :
    ∃ Z : codimensionCycles V.X p,
      H.cycleClass p Z = (classicalHodgeBasis V H p j).1 := by
  exact targetCycle_ofStrictRelation
    G (pointApexSeed G D p x) j K T C hrel

/-- Explicit target cycle obtained from the strict-relation source-target
program. -/
noncomputable def pointStrictRelationTargetCycle
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (j : ClassicalHodgeBasisIndex V H p)
    (K : SchemeBiFiniteClosedCorrespondence V)
    (T : RightFiniteBettiTrace H.analytification K (2 * p))
    (C : PointCycleCompatibility (n := p) K T)
    (hrel : BettiRelated H.analytification K (2 * p)
      (pointApexSeed G D p x).hodge.1
      ((classicalHodgeBasis V H p).repr
          (pointApexSeed G D p x).hodge
          (pointApexSeed G D p x).sourceIndex •
        (classicalHodgeBasis V H p j).1)) :
    codimensionCycles V.X p :=
  (sourceTargetProgramOfStrictRelation
    G (pointApexSeed G D p x) j K T C hrel).targetCycle

/-- Exact cycle-class specification of the explicit point-apex target cycle. -/
theorem pointStrictRelationTargetCycle_spec
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (j : ClassicalHodgeBasisIndex V H p)
    (K : SchemeBiFiniteClosedCorrespondence V)
    (T : RightFiniteBettiTrace H.analytification K (2 * p))
    (C : PointCycleCompatibility (n := p) K T)
    (hrel : BettiRelated H.analytification K (2 * p)
      (pointApexSeed G D p x).hodge.1
      ((classicalHodgeBasis V H p).repr
          (pointApexSeed G D p x).hodge
          (pointApexSeed G D p x).sourceIndex •
        (classicalHodgeBasis V H p j).1)) :
    H.cycleClass p
        (pointStrictRelationTargetCycle G D p x j K T C hrel) =
      (classicalHodgeBasis V H p j).1 := by
  exact (sourceTargetProgramOfStrictRelation
    G (pointApexSeed G D p x) j K T C hrel).targetCycle_spec

/-- A family of raw strict relations from one projective-point apex supplies an
explicit basis-cycle bridge. -/
noncomputable def pointStrictRelationBasisBridge
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (K : ∀ j : ClassicalHodgeBasisIndex V H p,
      SchemeBiFiniteClosedCorrespondence V)
    (T : ∀ j : ClassicalHodgeBasisIndex V H p,
      RightFiniteBettiTrace H.analytification (K j) (2 * p))
    (C : ∀ j : ClassicalHodgeBasisIndex V H p,
      PointCycleCompatibility (n := p) (K j) (T j))
    (hrel : ∀ j : ClassicalHodgeBasisIndex V H p,
      BettiRelated H.analytification (K j) (2 * p)
        (pointApexSeed G D p x).hodge.1
        ((classicalHodgeBasis V H p).repr
            (pointApexSeed G D p x).hodge
            (pointApexSeed G D p x).sourceIndex •
          (classicalHodgeBasis V H p j).1)) :
    HodgeConjecture.HodgeBasisCycleBridge V H p where
  basisCycle j :=
    pointStrictRelationTargetCycle G D p x j (K j) (T j) (C j) (hrel j)
  basisCycle_spec j :=
    pointStrictRelationTargetCycle_spec
      G D p x j (K j) (T j) (C j) (hrel j)

/-- **PROJECTIVE-POINT / STRICT-RELATION FIXED-WEIGHT CROWN.**
One actual codimension-p point and one raw strict relation to each target basis
sheet force the entire rational Hodge weight into the genuine cycle-class
range. -/
theorem hodge_weight_of_pointStrictRelations
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (K : ∀ j : ClassicalHodgeBasisIndex V H p,
      SchemeBiFiniteClosedCorrespondence V)
    (T : ∀ j : ClassicalHodgeBasisIndex V H p,
      RightFiniteBettiTrace H.analytification (K j) (2 * p))
    (C : ∀ j : ClassicalHodgeBasisIndex V H p,
      PointCycleCompatibility (n := p) (K j) (T j))
    (hrel : ∀ j : ClassicalHodgeBasisIndex V H p,
      BettiRelated H.analytification (K j) (2 * p)
        (pointApexSeed G D p x).hodge.1
        ((classicalHodgeBasis V H p).repr
            (pointApexSeed G D p x).hodge
            (pointApexSeed G D p x).sourceIndex •
          (classicalHodgeBasis V H p j).1)) :
    rationalHodgeSubspace (H.hodgeBigrading p) ≤
      LinearMap.range (H.cycleClass p) := by
  intro alpha halpha
  exact HodgeConjecture.hodge_class_has_cycle_of_basis_bridge
    V H (pointStrictRelationBasisBridge G D p x K T C hrel)
      alpha halpha

#check pointApexSeed
#check targetCycle_ofPointStrictRelation
#check pointStrictRelationTargetCycle
#check pointStrictRelationTargetCycle_spec
#check pointStrictRelationBasisBridge
#check hodge_weight_of_pointStrictRelations

#print axioms targetCycle_ofPointStrictRelation
#print axioms pointStrictRelationTargetCycle_spec
#print axioms hodge_weight_of_pointStrictRelations

end GSTClassicalHodgeOmniversePointStrictRelationFinale
