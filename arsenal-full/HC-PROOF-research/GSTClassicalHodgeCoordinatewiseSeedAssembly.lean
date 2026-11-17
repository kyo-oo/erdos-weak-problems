import Mathlib.GroupTheory.CosetCover
import GSTGeometricRealizationStage2D
import GSTClassicalHodgeWeightedCyclicCriterion

/-!
# GST CLASSICAL HODGE — COORDINATEWISE SEED ASSEMBLY

Over the infinite field `ℚ`, one does not need to construct a single atomic
seed touching every live Hodge sheet in one shot.

Fix a finite spectral family and let `A` be the vector space of coefficient
functions whose spectral combination belongs to the algebraic atomic
submodule.  For each selected sheet `i`, failure of the i-th coordinate on
`A` is a linear hyperplane `ker(eval_i)`.

If every sheet is individually visible — for each `i` there is some atomic
spectral combination with nonzero i-th coefficient — then each coordinate
hyperplane is proper.  A vector space over an infinite field cannot be a
finite union of proper subspaces.  Hence `A` contains one coefficient vector
outside every coordinate hyperplane simultaneously.  That vector is the
required cyclic seed with every coordinate nonzero.

This converts a simultaneous seed-construction problem into independent
per-sheet visibility problems, which can be attacked by GST sheet projectors,
Lefschetz tomography, Poincare strands, or any other local mechanism.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000000

noncomputable section

open scoped BigOperators
open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeCyclicSpectralGeneration
open GSTClassicalHodgeCyclicSpectralGeneration.FiniteSpectralFamily
open GSTClassicalHodgeLocalCyclicCriterion
open GSTClassicalHodgeWeightedCyclicCriterion

namespace GSTClassicalHodgeCoordinatewiseSeedAssembly

universe u

variable {M : Type u} [AddCommGroup M] [Module ℚ M]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

end GSTClassicalHodgeCoordinatewiseSeedAssembly

variable {M : Type u} [AddCommGroup M] [Module ℚ M]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace GSTClassicalHodgeCyclicSpectralGeneration.FiniteSpectralFamily

/-- Linearization of the finite spectral-combination operation in its
coefficient vector. -/
noncomputable def spectralCombinationLinear
    (S : FiniteSpectralFamily ι M) :
    (ι → ℚ) →ₗ[ℚ] M where
  toFun := S.spectralCombination
  map_add' := by
    intro a b
    simp [spectralCombination, add_smul, Finset.sum_add_distrib]
  map_smul' := by
    intro q a
    simp [spectralCombination, mul_smul, Finset.smul_sum]

@[simp]
theorem spectralCombinationLinear_apply
    (S : FiniteSpectralFamily ι M) (a : ι → ℚ) :
    S.spectralCombinationLinear a = S.spectralCombination a :=
  rfl

/-- Coefficient vectors whose spectral combination lies in a chosen stable
submodule. -/
noncomputable def admissibleCoefficientSpace
    (S : FiniteSpectralFamily ι M)
    (W : Submodule ℚ M) : Submodule ℚ (ι → ℚ) :=
  W.comap S.spectralCombinationLinear

/-- Evaluate one coordinate on the admissible coefficient space. -/
noncomputable def admissibleCoordinate
    (S : FiniteSpectralFamily ι M)
    (W : Submodule ℚ M)
    (i : ι) :
    S.admissibleCoefficientSpace W →ₗ[ℚ] ℚ where
  toFun := fun a => a.1 i
  map_add' := by
    intro a b
    rfl
  map_smul' := by
    intro q a
    rfl

/-- Individual visibility of coordinate i is exactly nontriviality of its
coordinate functional on the admissible seed space. -/
def CoordinateVisible
    (S : FiniteSpectralFamily ι M)
    (W : Submodule ℚ M)
    (i : ι) : Prop :=
  ∃ a : S.admissibleCoefficientSpace W, a.1 i ≠ 0

/-- Coordinate visibility makes the corresponding zero-coordinate hyperplane
proper. -/
theorem admissibleCoordinate_ker_ne_top
    (S : FiniteSpectralFamily ι M)
    (W : Submodule ℚ M)
    (i : ι)
    (hi : S.CoordinateVisible W i) :
    LinearMap.ker (S.admissibleCoordinate W i) ≠ ⊤ := by
  rintro htop
  rcases hi with ⟨a, ha⟩
  have haKer : a ∈ LinearMap.ker (S.admissibleCoordinate W i) := by
    rw [htop]
    trivial
  exact ha (show a.1 i = 0 from haKer)

/-- **FINITE HYPERPLANE AVOIDANCE FOR CYCLIC SEEDS.**

If every spectral coordinate is individually visible in W, then there exists
one W-valued spectral combination whose every coefficient is nonzero. -/
theorem exists_cyclic_seed_of_coordinatewise_visible
    (S : FiniteSpectralFamily ι M)
    (W : Submodule ℚ M)
    (hvisible : ∀ i, S.CoordinateVisible W i) :
    ∃ a : ι → ℚ,
      (∀ i, a i ≠ 0) ∧ S.spectralCombination a ∈ W := by
  let A := S.admissibleCoefficientSpace W
  let K : ι → Subspace ℚ A :=
    fun i => LinearMap.ker (S.admissibleCoordinate W i)
  have hproper : ∀ i, K i ≠ ⊤ := by
    intro i
    exact S.admissibleCoordinate_ker_ne_top W i (hvisible i)
  have hnotcover : (⋃ i, (K i : Set A)) ≠ Set.univ := by
    intro hcover
    obtain ⟨i, hi⟩ := Subspace.exists_eq_top_of_iUnion_eq_univ hcover
    exact hproper i hi
  obtain ⟨a, ha⟩ : ∃ a : A, a ∉ ⋃ i, (K i : Set A) := by
    by_contra hnone
    push_neg at hnone
    apply hnotcover
    ext a
    constructor
    · intro h
      trivial
    · intro h
      exact hnone a
  refine ⟨a.1, ?_, ?_⟩
  · intro i hai
    apply ha
    simp only [Set.mem_iUnion]
    refine ⟨i, ?_⟩
    exact hai
  · exact a.2

end GSTClassicalHodgeCyclicSpectralGeneration.FiniteSpectralFamily

namespace GSTClassicalHodgeCoordinatewiseSeedAssembly

variable {M : Type u} [AddCommGroup M] [Module ℚ M]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Classical-Hodge specialization: every live sheet is separately visible in
some atomic spectral combination.  Different sheets may use different
combinations; no simultaneous seed is assumed. -/
structure CoordinatewiseVisibleLocalRealization
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (alpha : ClassicalHodgeFiber V H p) where
  spectral :
    ClassicalHodgeSpectralOperator V H p (HodgeSupportIndex alpha)
  spectral_basisIndex :
    spectral.basisIndex = HodgeSupportIndex.include
  visible : ∀ i : HodgeSupportIndex alpha,
    ∃ a : HodgeSupportIndex alpha → ℚ,
      (∑ j : HodgeSupportIndex alpha,
        a j • (classicalHodgeBasis V H p j.1).1) ∈
          pointCycleClassSpan p (H.cycleClass p)
      ∧ a i ≠ 0

namespace CoordinatewiseVisibleLocalRealization

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}
variable {alpha : ClassicalHodgeFiber V H p}

/-- Coordinatewise atomic visibility automatically assembles one weighted
cyclic seed touching every live sheet. -/
noncomputable def toWeightedLocalCyclicRealization
    (R : CoordinatewiseVisibleLocalRealization V H p alpha) :
    WeightedLocalCyclicRealization V H p alpha := by
  have hvec : ∀ i : HodgeSupportIndex alpha,
      R.spectral.toFiniteSpectralFamily.vector i =
        (classicalHodgeBasis V H p i.1).1 := by
    intro i
    simp only [ClassicalHodgeSpectralOperator.toFiniteSpectralFamily,
      R.spectral_basisIndex, HodgeSupportIndex.include]
  have hvisible : ∀ i : HodgeSupportIndex alpha,
      R.spectral.toFiniteSpectralFamily.CoordinateVisible
        (pointCycleClassSpan p (H.cycleClass p)) i := by
    intro i
    rcases R.visible i with ⟨a, haW, hai⟩
    refine ⟨⟨a, ?_⟩, hai⟩
    show R.spectral.toFiniteSpectralFamily.spectralCombination a ∈
        pointCycleClassSpan p (H.cycleClass p)
    rw [show R.spectral.toFiniteSpectralFamily.spectralCombination a =
      ∑ j : HodgeSupportIndex alpha,
        a j • (classicalHodgeBasis V H p j.1).1 from by
      simp only [FiniteSpectralFamily.spectralCombination, hvec]]
    exact haW
  have hseed :=
    R.spectral.toFiniteSpectralFamily.exists_cyclic_seed_of_coordinatewise_visible
      (pointCycleClassSpan p (H.cycleClass p)) hvisible
  have hseedW : ∑ i : HodgeSupportIndex alpha,
      hseed.choose i • (classicalHodgeBasis V H p i.1).1 ∈
      pointCycleClassSpan p (H.cycleClass p) := by
    have h := hseed.choose_spec.2
    rw [show R.spectral.toFiniteSpectralFamily.spectralCombination hseed.choose =
      ∑ i : HodgeSupportIndex alpha,
        hseed.choose i • (classicalHodgeBasis V H p i.1).1 from by
      simp only [FiniteSpectralFamily.spectralCombination, hvec]] at h
    exact h
  refine {
    spectral := R.spectral
    spectral_basisIndex := R.spectral_basisIndex
    coefficient := hseed.choose
    coefficient_ne_zero := hseed.choose_spec.1
    seed_mem_atomic := hseedW
  }

/-- Coordinatewise visibility therefore constructs an exact native cycle for
the original genuine Hodge class. -/
theorem exists_native_cycle
    (R : CoordinatewiseVisibleLocalRealization V H p alpha) :
    ∃ Z : codimensionCycles V.X p,
      H.cycleClass p Z = alpha.1 :=
  (toWeightedLocalCyclicRealization R).exists_native_cycle

end CoordinatewiseVisibleLocalRealization

/-- **COORDINATEWISE-VISIBILITY HODGE CRITERION.**
It is enough to solve the atomic visibility problem independently for each live
sheet of each Hodge class.  Infinite-field hyperplane avoidance assembles the
one cyclic seed automatically. -/
theorem bigradedBettiHodge_of_coordinatewise_visible_realizations
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (hlocal :
      ∀ p : Nat, ∀ alpha : ClassicalHodgeFiber V H p,
        Nonempty (CoordinatewiseVisibleLocalRealization V H p alpha)) :
    BigradedBettiHodgeStatement V H := by
  intro p x hx
  let alpha : ClassicalHodgeFiber V H p := ⟨x, hx⟩
  exact (Classical.choice (hlocal p alpha)).exists_native_cycle

#check FiniteSpectralFamily.spectralCombinationLinear
#check FiniteSpectralFamily.admissibleCoefficientSpace
#check FiniteSpectralFamily.CoordinateVisible
#check FiniteSpectralFamily.admissibleCoordinate_ker_ne_top
#check FiniteSpectralFamily.exists_cyclic_seed_of_coordinatewise_visible
#check CoordinatewiseVisibleLocalRealization
#check CoordinatewiseVisibleLocalRealization.toWeightedLocalCyclicRealization
#check CoordinatewiseVisibleLocalRealization.exists_native_cycle
#check bigradedBettiHodge_of_coordinatewise_visible_realizations

#print axioms FiniteSpectralFamily.exists_cyclic_seed_of_coordinatewise_visible
#print axioms CoordinatewiseVisibleLocalRealization.toWeightedLocalCyclicRealization
#print axioms CoordinatewiseVisibleLocalRealization.exists_native_cycle
#print axioms bigradedBettiHodge_of_coordinatewise_visible_realizations

end GSTClassicalHodgeCoordinatewiseSeedAssembly
