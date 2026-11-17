import GSTClassicalHodgeVerticalRayMassFactorization
import GSTClassicalHodgePlaneCompletenessTheorem

/-!
# GST CLASSICAL HODGE — HORIZONTAL GHOST-CLOSURE CIRCULARITY

The vertical/source side can now be established independently from canonical
native-mass factorization plus one exact cut ray on each live weight.
Once that is done, the remaining ghost-indexed horizontal closure predicates
must be audited on their own.

They are still indexed by `OmniversalSeparatorGhost`.  Hence Hodge makes them
vacuously true, while either closure together with the already-proved source
survival kills every ghost.  Therefore, under the independent vertical data,
each ghost-indexed horizontal closure is exactly equivalent to Hodge.

This means the final horizontal theorem cannot legitimately be stated as
"closure at every ghost weight".  It must be a non-ghost-indexed construction
from lower GST/correspondence geometry.
-/

set_option maxHeartbeats 120000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeHorizontalGhostClosureCircularity

open GSTProjectiveOverC
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeLiveApexSpineFanFinale
open GSTClassicalHodgeExactVerticalCutRay
open GSTClassicalHodgeNativeMassBridgeAudit
open GSTClassicalHodgeVerticalRayMassFactorization
open GSTClassicalHodgeOmniversalGhostBranchClosure
open GSTClassicalHodgeCommonClassPlaneRealization
open GSTClassicalHodgePlaneCompletenessTheorem

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- **STRICT HORIZONTAL FRONTIER EXACT STATUS.**
Once the source side has been independently proved by vertical rays and native
mass factorization, ghost-weight primitive strict closure is equivalent to the
Hodge conclusion. -/
theorem ghostWeightPrimitiveStrictClosure_iff_hodge_of_verticalMass
    (G : GeometricCycleClassSpine V H)
    (F : NativeMassCohomologyFactorization (V := V) (H := H))
    (vertical : ∀ p : Nat, HodgeWeightLive H p →
      ExactVerticalCutRayCertificate V p) :
    GhostWeightPrimitiveStrictClosure G ↔
      BigradedBettiHodgeStatement V H := by
  constructor
  · intro hclose
    exact hodge_of_massFactorization_verticalRays_and_strictClosure
      G F vertical hclose
  · intro hHodge
    exact ghostWeightPrimitiveStrictClosure_of_hodge G hHodge

/-- Common-class ghost closure has the same circular status after the source
side is theoremized. -/
theorem ghostWeightPrimitiveCommonClassClosure_iff_hodge_of_verticalMass
    (G : GeometricCycleClassSpine V H)
    (F : NativeMassCohomologyFactorization (V := V) (H := H))
    (vertical : ∀ p : Nat, HodgeWeightLive H p →
      ExactVerticalCutRayCertificate V p) :
    GhostWeightPrimitiveCommonClassClosure G ↔
      BigradedBettiHodgeStatement V H := by
  constructor
  · intro hplanes
    have hsurvive : GhostWeightNativeSeedSurvival G :=
      ghostWeightNativeSeedSurvival_of_massFactorization_verticalRays
        G F vertical
    exact hodge_of_survival_and_commonClassPlaneClosure G hsurvive hplanes
  · intro hHodge
    exact ghostWeightPrimitiveCommonClassClosure_of_hodge G hHodge

/-- Both ghost-indexed horizontal formulations are conclusion-equivalent once
the vertical source has been constructed.  This is the exact formal reason the
horizontal finale must be proved as an unconditional non-ghost-indexed geometry
theorem instead. -/
theorem horizontal_ghost_closure_circularity_crown
    (G : GeometricCycleClassSpine V H)
    (F : NativeMassCohomologyFactorization (V := V) (H := H))
    (vertical : ∀ p : Nat, HodgeWeightLive H p →
      ExactVerticalCutRayCertificate V p) :
    (GhostWeightPrimitiveStrictClosure G ↔
      BigradedBettiHodgeStatement V H)
    ∧ (GhostWeightPrimitiveCommonClassClosure G ↔
      BigradedBettiHodgeStatement V H) := by
  exact ⟨ghostWeightPrimitiveStrictClosure_iff_hodge_of_verticalMass
      G F vertical,
    ghostWeightPrimitiveCommonClassClosure_iff_hodge_of_verticalMass
      G F vertical⟩

#check ghostWeightPrimitiveStrictClosure_iff_hodge_of_verticalMass
#check ghostWeightPrimitiveCommonClassClosure_iff_hodge_of_verticalMass
#check horizontal_ghost_closure_circularity_crown

#print axioms ghostWeightPrimitiveStrictClosure_iff_hodge_of_verticalMass
#print axioms ghostWeightPrimitiveCommonClassClosure_iff_hodge_of_verticalMass
#print axioms horizontal_ghost_closure_circularity_crown

end GSTClassicalHodgeHorizontalGhostClosureCircularity
