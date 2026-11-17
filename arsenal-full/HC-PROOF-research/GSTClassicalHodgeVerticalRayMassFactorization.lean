import GSTClassicalHodgeNativeMassBridgeAudit
import GSTClassicalHodgeExactVerticalCutRay
import GSTClassicalHodgeOmniversalGhostBranchClosure

/-!
# GST CLASSICAL HODGE — VERTICAL RAY FROM NATIVE-MASS FACTORIZATION

The exact vertical-cut proof only needs a positive point-weight trace.  The
canonical native mass gives every unit codimension point weight `1`, which is
strictly positive.  Therefore once native mass factors through genuine cycle
class, the required Betti trace is manufactured automatically.

This removes two overstrong source-side burdens:

* no independent `ProjectiveDegreeTraceSemantics` package is needed;
* no law identifying native successor mass with the universal GST `L^2`
  coefficient is needed.

A single exact surviving vertical ray is then enough to make the canonical
projective cut class nonzero and hence to construct the canonical synchronized
native/Hodge seed in that weight.
-/

set_option maxHeartbeats 180000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeVerticalRayMassFactorization

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeNativeCycleCosmicShadow
open GSTClassicalHodgeNativeMassBridgeAudit
open GSTClassicalHodgeProjectiveDegreeTrace
open GSTClassicalHodgeExactVerticalCutRay
open GSTClassicalHodgeLiveApexSpineFanFinale
open GSTClassicalHodgeCanonicalCutProgramSpine
open GSTClassicalHodgeSynchronizedDefectOrbit
open GSTClassicalHodgeOmniversalSeparatorGhostCrown
open GSTClassicalHodgeOmniversalGhostBranchClosure

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- **UNIT-DEGREE TRACE FROM NATIVE MASS.**
Native-mass factorization already supplies a positive point trace: assign every
genuine codimension point degree `1`.  The trace/cycle-class compatibility is
then exactly the native-mass factorization theorem on unit point cycles. -/
noncomputable def unitDegreeTraceOfNativeMassKernel
    (K : NativeMassKernelLaw (V := V) (H := H)) :
    ProjectiveDegreeTraceSemantics V H where
  trace := fun q => nativeMassAmbientRead K q
  pointDegree := fun _ _ => 1
  pointDegree_pos := by
    intro q x
    norm_num
  trace_point_cycleClass := by
    intro q x
    rw [nativeMassAmbientRead_cycleClass K q]
    simp

/-- Factorization form of the same constructor. -/
noncomputable def unitDegreeTraceOfNativeMassFactorization
    (F : NativeMassCohomologyFactorization (V := V) (H := H)) :
    ProjectiveDegreeTraceSemantics V H :=
  unitDegreeTraceOfNativeMassKernel
    ((nativeMassKernelLaw_iff_cohomologyFactorization
      (V := V) (H := H)).2 F)

/-- One exact vertical ray plus native-mass factorization forces the canonical
projective cut class to be nonzero. -/
theorem cycleClass_projectiveCutTower_ne_zero_of_massKernel_and_ray
    (K : NativeMassKernelLaw (V := V) (H := H))
    {p : Nat}
    (C : ExactVerticalCutRayCertificate V p) :
    H.cycleClass p
      (GSTClassicalHodgeLimitlessProjectiveLefschetzTower.projectiveCutTower V p) ≠ 0 :=
  cycleClass_projectiveCutTower_ne_zero_of_certificate
    (unitDegreeTraceOfNativeMassKernel K) C

/-- Factorization version. -/
theorem cycleClass_projectiveCutTower_ne_zero_of_massFactorization_and_ray
    (F : NativeMassCohomologyFactorization (V := V) (H := H))
    {p : Nat}
    (C : ExactVerticalCutRayCertificate V p) :
    H.cycleClass p
      (GSTClassicalHodgeLimitlessProjectiveLefschetzTower.projectiveCutTower V p) ≠ 0 :=
  cycleClass_projectiveCutTower_ne_zero_of_certificate
    (unitDegreeTraceOfNativeMassFactorization F) C

/-- The exact ray therefore constructs the canonical synchronized native/Hodge
orbit seed directly. -/
noncomputable def canonicalCutOrbitSeedOfMassFactorizationRay
    (G : GeometricCycleClassSpine V H)
    (F : NativeMassCohomologyFactorization (V := V) (H := H))
    {p : Nat}
    (C : ExactVerticalCutRayCertificate V p) :
    NativeHodgeOrbitSeed (V := V) (H := H) (p := p) :=
  canonicalCutOrbitSeed G p
    (cycleClass_projectiveCutTower_ne_zero_of_massFactorization_and_ray F C)

/-- One actual Hodge basis index certifies that the corresponding Hodge weight
is live. -/
theorem hodgeWeightLive_of_basisIndex
    (p : Nat)
    (j : ClassicalHodgeBasisIndex V H p) :
    HodgeWeightLive H p := by
  intro hbot
  have hjmem := (classicalHodgeBasis V H p j).2
  rw [hbot] at hjmem
  have hz : classicalHodgeBasis V H p j = 0 := by
    simpa using hjmem
  exact (classicalHodgeBasis V H p).ne_zero j hz

/-- **LIVE-WEIGHT CANONICAL SOURCE THEOREM.**
Native-mass factorization plus one exact vertical ray on each live weight gives
a genuine nonzero synchronized native/Hodge seed on every live weight. -/
theorem liveWeightNativeSeed_of_massFactorization_verticalRays
    (G : GeometricCycleClassSpine V H)
    (F : NativeMassCohomologyFactorization (V := V) (H := H))
    (vertical : ∀ p : Nat, HodgeWeightLive H p →
      ExactVerticalCutRayCertificate V p) :
    ∀ p : Nat, HodgeWeightLive H p →
      Nonempty (NativeHodgeOrbitSeed (V := V) (H := H) (p := p)) := by
  intro p hlive
  exact ⟨canonicalCutOrbitSeedOfMassFactorizationRay
    G F (vertical p hlive)⟩

/-- The same data prove the exact live-tower nonvanishing input consumed by the
live apex/spine/fan finale. -/
theorem towerLive_of_massFactorization_verticalRays
    (F : NativeMassCohomologyFactorization (V := V) (H := H))
    (vertical : ∀ p : Nat, HodgeWeightLive H p →
      ExactVerticalCutRayCertificate V p) :
    ∀ p : Nat, HodgeWeightLive H p →
      H.cycleClass p
        (GSTClassicalHodgeLimitlessProjectiveLefschetzTower.projectiveCutTower V p) ≠ 0 := by
  intro p hlive
  exact cycleClass_projectiveCutTower_ne_zero_of_massFactorization_and_ray
    F (vertical p hlive)

/-- Every hypothetical separator ghost chooses an actual Hodge basis sheet, so
its weight is automatically live.  The vertical-ray theorem therefore supplies
the old ghost-weight source-survival package as a derived theorem. -/
theorem ghostWeightNativeSeedSurvival_of_massFactorization_verticalRays
    (G : GeometricCycleClassSpine V H)
    (F : NativeMassCohomologyFactorization (V := V) (H := H))
    (vertical : ∀ p : Nat, HodgeWeightLive H p →
      ExactVerticalCutRayCertificate V p) :
    GhostWeightNativeSeedSurvival G := by
  intro E
  have hlive : HodgeWeightLive H E.weight :=
    hodgeWeightLive_of_basisIndex E.weight E.sheet
  exact ⟨canonicalCutOrbitSeedOfMassFactorizationRay
    G F (vertical E.weight hlive)⟩

/-- The branch-closure Hodge theorem no longer needs source survival as an
independent premise once native-mass factorization and exact vertical rays have
been established. -/
theorem hodge_of_massFactorization_verticalRays_and_strictClosure
    (G : GeometricCycleClassSpine V H)
    (F : NativeMassCohomologyFactorization (V := V) (H := H))
    (vertical : ∀ p : Nat, HodgeWeightLive H p →
      ExactVerticalCutRayCertificate V p)
    (hclose : GhostWeightPrimitiveStrictClosure G) :
    BigradedBettiHodgeStatement V H := by
  exact hodge_of_survival_and_strictBranchClosure G
    (ghostWeightNativeSeedSurvival_of_massFactorization_verticalRays
      G F vertical)
    hclose

#check unitDegreeTraceOfNativeMassKernel
#check unitDegreeTraceOfNativeMassFactorization
#check cycleClass_projectiveCutTower_ne_zero_of_massKernel_and_ray
#check canonicalCutOrbitSeedOfMassFactorizationRay
#check hodgeWeightLive_of_basisIndex
#check liveWeightNativeSeed_of_massFactorization_verticalRays
#check towerLive_of_massFactorization_verticalRays
#check ghostWeightNativeSeedSurvival_of_massFactorization_verticalRays
#check hodge_of_massFactorization_verticalRays_and_strictClosure

#print axioms unitDegreeTraceOfNativeMassKernel
#print axioms cycleClass_projectiveCutTower_ne_zero_of_massKernel_and_ray
#print axioms hodgeWeightLive_of_basisIndex
#print axioms ghostWeightNativeSeedSurvival_of_massFactorization_verticalRays
#print axioms hodge_of_massFactorization_verticalRays_and_strictClosure

end GSTClassicalHodgeVerticalRayMassFactorization
