import GSTClassicalHodgeGeneralSpaceSynchronization
import GSTClassicalHodgeExactClayStatement

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeGeneralSpaceDefectExtinction

open GSTGeneralSpace
open GSTProjectiveOverC
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeGeneralSpaceRealization
open GSTClassicalHodgeGeneralSpaceSynchronization
open GSTClassicalHodgeExactClayStatement

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- A genuine Hodge defect is a Hodge state outside the domain of the native
algebraic partial realization. -/
def GeneralSpaceHodgeDefect
    (G : GeometricCycleClassSpine V H)
    (x : (hodgeGeneralSpace G).Point) : Prop :=
  HodgeLocus G x ∧ ¬ NativeLocus G x

/-- A Hodge defect cannot be reached by a genuine synchronized geometric path
from any native state. -/
theorem defect_not_reachable_from_native
    (G : GeometricCycleClassSpine V H)
    {x y : (hodgeGeneralSpace G).Point}
    (hx : NativeLocus G x)
    (hy : GeneralSpaceHodgeDefect G y) :
    ¬ (hodgeGeneralSpace G).Path x y := by
  intro hxy
  exact hy.2 (nativeLocus_of_reachable G hxy hx)

/-- General Space saturation: every Hodge state is reachable from some genuine
native state by a synchronized geometric path.  This is stated as a target,
not assumed inside the ontology. -/
def HodgeNativeSaturation
    (G : GeometricCycleClassSpine V H) : Prop :=
  ∀ y : (hodgeGeneralSpace G).Point,
    HodgeLocus G y →
      ∃ x : (hodgeGeneralSpace G).Point,
        NativeLocus G x ∧ (hodgeGeneralSpace G).Path x y

/-- Saturation extinguishes every General Space Hodge defect. -/
theorem no_defect_of_saturation
    (G : GeometricCycleClassSpine V H)
    (hsat : HodgeNativeSaturation G) :
    ∀ y : (hodgeGeneralSpace G).Point,
      ¬ GeneralSpaceHodgeDefect G y := by
  intro y hy
  rcases hsat y hy.1 with ⟨x, hx, hxy⟩
  exact hy.2 (nativeLocus_of_reachable G hxy hx)

/-- Conversely, extinction of all defects says every Hodge state is native. -/
theorem hodge_native_of_no_defect
    (G : GeometricCycleClassSpine V H)
    (hno : ∀ y : (hodgeGeneralSpace G).Point,
      ¬ GeneralSpaceHodgeDefect G y) :
    ∀ y : (hodgeGeneralSpace G).Point,
      HodgeLocus G y → NativeLocus G y := by
  intro y hy
  by_contra hnative
  exact hno y ⟨hy, hnative⟩

/-- Exact equivalence: General Space native saturation is neither weaker nor
stronger than the elementwise rational Hodge target.  If Hodge already holds,
choose the target itself as the native source and use the identity path. -/
theorem saturation_iff_exactHodge
    (G : GeometricCycleClassSpine V H) :
    HodgeNativeSaturation G ↔
      EveryHodgeClassIsRationalAlgebraic H := by
  constructor
  · intro hsat
    apply (exactHodge_iff_hodgeLocus_le_nativeLocus G).2
    intro y hy
    rcases hsat y hy with ⟨x, hx, hxy⟩
    exact nativeLocus_of_reachable G hxy hx
  · intro hHodge y hy
    have hynative : NativeLocus G y :=
      (exactHodge_iff_hodgeLocus_le_nativeLocus G).1 hHodge y hy
    refine ⟨y, hynative, ?_⟩
    exact (hodgeGeneralSpace G).idPath y

/-- Exact defect-extinction formulation of the rational Hodge conjecture. -/
theorem defectExtinction_iff_exactHodge
    (G : GeometricCycleClassSpine V H) :
    (∀ y : (hodgeGeneralSpace G).Point,
      ¬ GeneralSpaceHodgeDefect G y) ↔
      EveryHodgeClassIsRationalAlgebraic H := by
  constructor
  · intro hno
    apply (exactHodge_iff_hodgeLocus_le_nativeLocus G).2
    exact hodge_native_of_no_defect G hno
  · intro hHodge y hy
    have hynative : NativeLocus G y :=
      (exactHodge_iff_hodgeLocus_le_nativeLocus G).1 hHodge y hy.1
    exact hy.2 hynative

/-- Literal finite-rational-combination endpoint from General Space saturation. -/
theorem finiteRationalCombination_of_saturation
    (G : GeometricCycleClassSpine V H)
    (hsat : HodgeNativeSaturation G) :
    EveryHodgeClassIsFiniteRationalCombination H := by
  have hAlg : EveryHodgeClassIsRationalAlgebraic H :=
    (saturation_iff_exactHodge G).1 hsat
  exact
    (rationalAlgebraic_iff_finiteRationalCombination H).1 hAlg

#check GeneralSpaceHodgeDefect
#check HodgeNativeSaturation
#check defect_not_reachable_from_native
#check no_defect_of_saturation
#check saturation_iff_exactHodge
#check defectExtinction_iff_exactHodge
#check finiteRationalCombination_of_saturation

#print axioms defect_not_reachable_from_native
#print axioms saturation_iff_exactHodge
#print axioms defectExtinction_iff_exactHodge
#print axioms finiteRationalCombination_of_saturation

end GSTClassicalHodgeGeneralSpaceDefectExtinction
