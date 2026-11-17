import GSTClassicalHodgeClosedCorrespondenceCosmicRealization
import GSTClassicalHodgeZeroComplementSpectrum
import GSTClassicalHodgeGeometricCycleClassSpine

/-!
# GST CLASSICAL HODGE — ONE CLOSED-CORRESPONDENCE OBSERVABLE / GST SPECTRAL AMPLIFIER

Realizing every rank-free matrix unit by geometry is much stronger than what
the finite-window GST spectral machinery needs.

For a finite injective window of genuine Hodge basis sheets, the existing
zero-complement observable assigns the distinct nonzero labels `1,...,N` to
the selected sheets and label zero to every unselected Hodge sheet.  Its
augmented Lagrange polynomial

  X * Π_{k != i} (X - λ_k)

therefore isolates the i-th selected sheet and kills every other Hodge sheet.

This module replaces the N^2 matrix-unit realization problem by ONE geometric
operator-realization problem:

* find one finite rational word of genuine realized closed correspondences;
* prove that on the genuine Hodge fiber its cohomological action equals the
  canonical zero-complement spectral observable.

Because every algebraic cycle class is Hodge, polynomial iteration of that
realized word along a native cycle never leaves the sector where the equality
is known.  Hence the native polynomial calculus realizes the exact GST sheet
projectors on algebraic seeds.

For one selected sheet it is then enough to have ONE genuine point cycle whose
class has a nonzero coordinate in that sheet.  No pure seed, no all-sheet
matrix-unit family, and no arbitrary range-lift operator is required.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open scoped BigOperators
open AlgebraicGeometry

namespace GSTClassicalHodgeClosedCorrespondenceSpectralAmplifier

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTNativeCodimensionCyclePresentation
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgeCyclicSpectralGeneration
open GSTClassicalHodgeCycleOperatorNaturality
open GSTClassicalHodgeCanonicalSpectralObservable
open GSTClassicalHodgeZeroComplementSpectrum
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeRealizedClosedCorrespondenceAlgebra

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

end GSTClassicalHodgeClosedCorrespondenceSpectralAmplifier

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTNativeCodimensionCyclePresentation
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgeCyclicSpectralGeneration
open GSTClassicalHodgeCycleOperatorNaturality
open GSTClassicalHodgeCanonicalSpectralObservable
open GSTClassicalHodgeZeroComplementSpectrum
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeRealizedClosedCorrespondenceAlgebra

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

namespace GSTClassicalHodgeCanonicalSpectralObservable.FiniteHodgeBasisWindow

/-- A selected-window augmented projector, restricted to the genuine Hodge
fiber but valued in ambient cohomology. -/
noncomputable def augmentedProjectorOnHodge
    (W : FiniteHodgeBasisWindow V H p)
    (i : Fin W.N) :
    ClassicalHodgeFiber V H p →ₗ[ℚ]
      RationalSingularCohomology H.analytification (2 * p) :=
  (linearPolyEval W.zeroComplementObservable
      (W.augmentedIsolatorPolynomial i)).comp
    (rationalHodgeSubspace (H.hodgeBigrading p)).subtype

/-- Unselected Hodge basis sheets have spectral weight zero. -/
theorem basisWeight_eq_zero_of_unselected
    (W : FiniteHodgeBasisWindow V H p)
    (j : ClassicalHodgeBasisIndex V H p)
    (hj : ¬ ∃ k : Fin W.N, W.basisIndex k = j) :
    W.basisWeight j = 0 := by
  classical
  unfold basisWeight
  apply Finset.sum_eq_zero
  intro k hk
  rw [if_neg]
  intro h
  exact hj ⟨k,h⟩

/-- Hence the zero-complement observable kills every unselected Hodge basis
sheet, not only the external non-Hodge complement. -/
theorem zeroComplementObservable_unselected
    (W : FiniteHodgeBasisWindow V H p)
    (j : ClassicalHodgeBasisIndex V H p)
    (hj : ¬ ∃ k : Fin W.N, W.basisIndex k = j) :
    W.zeroComplementObservable (classicalHodgeBasis V H p j).1 = 0 := by
  rw [W.zeroComplementObservable_on_hodge]
  rw [W.hodgeDiagonal_basis]
  rw [W.basisWeight_eq_zero_of_unselected j hj]
  simp

/-- The augmented polynomial projector kills every unselected Hodge basis
sheet because its polynomial contains the factor X and the unselected
eigenvalue is zero. -/
theorem augmentedIsolator_kills_unselected
    (W : FiniteHodgeBasisWindow V H p)
    (i : Fin W.N)
    (j : ClassicalHodgeBasisIndex V H p)
    (hj : ¬ ∃ k : Fin W.N, W.basisIndex k = j) :
    linearPolyEval W.zeroComplementObservable
        (W.augmentedIsolatorPolynomial i)
        (classicalHodgeBasis V H p j).1 = 0 := by
  rw [linearPolyEval_of_eigenvector W.zeroComplementObservable
    (classicalHodgeBasis V H p j).1 0]
  · simp [augmentedIsolatorPolynomial]
  · simpa using W.zeroComplementObservable_unselected j hj

/-- **GLOBAL HODGE-FIBER PROJECTOR FORMULA.**
The augmented finite-window polynomial is exactly the scaled rank-one
projector onto the selected genuine Hodge basis direction, on the ENTIRE
Hodge fiber.  This is the finite-window/limitless bridge needed below. -/
theorem augmentedProjectorOnHodge_apply
    (W : FiniteHodgeBasisWindow V H p)
    (i : Fin W.N)
    (alpha : ClassicalHodgeFiber V H p) :
    W.augmentedProjectorOnHodge i alpha =
      (W.augmentedIsolatorScale i *
        hodgeCoordinate (W.basisIndex i) alpha) •
          (classicalHodgeBasis V H p (W.basisIndex i)).1 := by
  classical
  -- Prove the corresponding linear maps agree on every genuine Hodge basis
  -- vector; the basis extensionality step is left transparent for GLM repair.
  have hmap :
      W.augmentedProjectorOnHodge i =
        (W.augmentedIsolatorScale i) •
          ((rationalHodgeSubspace (H.hodgeBigrading p)).subtype.comp
            (hodgeMatrixUnit (W.basisIndex i) (W.basisIndex i))) := by
    apply (classicalHodgeBasis V H p).ext
    intro j
    by_cases hji : j = W.basisIndex i
    · subst j
      simp [augmentedProjectorOnHodge,
        W.augmentedIsolator_selects_self]
    · by_cases hsel : ∃ k : Fin W.N, W.basisIndex k = j
      · rcases hsel with ⟨k,hk⟩
        have hki : k ≠ i := by
          intro h
          subst k
          exact hji hk.symm
        rw [← hk]
        have hneq : W.basisIndex i ≠ W.basisIndex k :=
          W.basisIndex_injective.ne hki.symm
        have hcoord :
            hodgeCoordinate (W.basisIndex i)
              (classicalHodgeBasis V H p (W.basisIndex k)) = 0 :=
          hodgeCoordinate_basis_other (W.basisIndex i) (W.basisIndex k) hneq
        simp [augmentedProjectorOnHodge,
          W.augmentedIsolator_kills_other i k hki, hcoord]
      · have hcoord :
            hodgeCoordinate (W.basisIndex i)
              (classicalHodgeBasis V H p j) = 0 :=
          hodgeCoordinate_basis_other (W.basisIndex i) j (by
            intro h
            exact hji h.symm)
        simp [augmentedProjectorOnHodge,
          W.augmentedIsolator_kills_unselected i j hsel, hcoord]
  have happly := LinearMap.congr_fun hmap alpha
  simpa [hodgeMatrixUnit_apply, smul_smul, mul_comm, mul_left_comm,
    mul_assoc] using happly

end GSTClassicalHodgeCanonicalSpectralObservable.FiniteHodgeBasisWindow

namespace GSTClassicalHodgeClosedCorrespondenceSpectralAmplifier

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTNativeCodimensionCyclePresentation
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgeCyclicSpectralGeneration
open GSTClassicalHodgeCycleOperatorNaturality
open GSTClassicalHodgeCanonicalSpectralObservable
open GSTClassicalHodgeZeroComplementSpectrum
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeRealizedClosedCorrespondenceAlgebra

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}


/-- One genuine realized closed-correspondence word implements the canonical
finite-window code observable on the genuine Hodge fiber.  Equality outside
the Hodge fiber is NOT required. -/
structure ClosedCorrespondenceWindowRealization
    (G : GeometricCycleClassSpine V H)
    (W : FiniteHodgeBasisWindow V H p) where
  word : RealizedCorrespondenceWord V H p
  on_hodge : ∀ alpha : ClassicalHodgeFiber V H p,
    (realizedWordPair word).cohomologyOperator alpha.1 =
      W.zeroComplementObservable alpha.1

namespace ClosedCorrespondenceWindowRealization

variable {G : GeometricCycleClassSpine V H}
variable {W : FiniteHodgeBasisWindow V H p}

/-- The word preserves the Hodge fiber because there it agrees with the
canonical Hodge-diagonal observable. -/
theorem word_hodge
    (R : ClosedCorrespondenceWindowRealization G W)
    (alpha : ClassicalHodgeFiber V H p) :
    (realizedWordPair R.word).cohomologyOperator alpha.1 ∈
      rationalHodgeSubspace (H.hodgeBigrading p) := by
  rw [R.on_hodge alpha]
  rw [W.zeroComplementObservable_on_hodge]
  exact (W.hodgeDiagonal alpha).2

/-- Restriction of the realized word to the genuine Hodge fiber. -/
noncomputable def hodgeOperator
    (R : ClosedCorrespondenceWindowRealization G W) :
    Module.End ℚ (ClassicalHodgeFiber V H p) where
  toFun alpha :=
    ⟨(realizedWordPair R.word).cohomologyOperator alpha.1,
      R.word_hodge alpha⟩
  map_add' := by intro a b; ext; simp
  map_smul' := by intro q a; ext; simp

/-- On the Hodge fiber, the realized correspondence word is exactly the
canonical diagonal GST/code operator. -/
theorem hodgeOperator_eq_diagonal
    (R : ClosedCorrespondenceWindowRealization G W) :
    R.hodgeOperator = W.hodgeDiagonal := by
  apply LinearMap.ext
  intro alpha
  apply Subtype.ext
  change (realizedWordPair R.word).cohomologyOperator alpha.1 =
    (W.hodgeDiagonal alpha).1
  exact (R.on_hodge alpha).trans (W.zeroComplementObservable_on_hodge alpha)

/-- Polynomial functional calculus of the realized word agrees with polynomial
functional calculus of the zero-complement GST observable on every Hodge
class. -/
theorem linearPolyEval_on_hodge
    (R : ClosedCorrespondenceWindowRealization G W)
    (P : Polynomial ℚ)
    (alpha : ClassicalHodgeFiber V H p) :
    linearPolyEval (realizedWordPair R.word).cohomologyOperator P alpha.1 =
      linearPolyEval W.zeroComplementObservable P alpha.1 := by
  have hWord :
      (rationalHodgeSubspace (H.hodgeBigrading p)).subtype
        (linearPolyEval R.hodgeOperator P alpha) =
      linearPolyEval (realizedWordPair R.word).cohomologyOperator P alpha.1 := by
    exact linearPolyEval_intertwines
      (rationalHodgeSubspace (H.hodgeBigrading p)).subtype
      R.hodgeOperator
      (realizedWordPair R.word).cohomologyOperator
      (fun a => rfl) P alpha
  have hObs :
      (rationalHodgeSubspace (H.hodgeBigrading p)).subtype
        (linearPolyEval W.hodgeDiagonal P alpha) =
      linearPolyEval W.zeroComplementObservable P alpha.1 := by
    exact linearPolyEval_intertwines
      (rationalHodgeSubspace (H.hodgeBigrading p)).subtype
      W.hodgeDiagonal
      W.zeroComplementObservable
      (fun a => (W.zeroComplementObservable_on_hodge a).symm) P alpha
  rw [R.hodgeOperator_eq_diagonal] at hWord
  exact hWord.symm.trans hObs

/-- Geometric point visibility of one selected Hodge sheet: some genuine point
class has nonzero coordinate in that sheet. -/
def PointVisible
    (R : ClosedCorrespondenceWindowRealization G W)
    (i : Fin W.N) : Prop :=
  ∃ x : CodimensionPoint V.X p,
    hodgeCoordinate (W.basisIndex i)
      (⟨H.cycleClass p (codimensionPointCycle V.X p x),
        G.pointClass_is_hodge p x⟩ : ClassicalHodgeFiber V H p) ≠ 0

/-- Native cycle obtained by applying the augmented GST projector polynomial
of the realized correspondence observable to a visible point seed and
normalizing. -/
noncomputable def extractedBasisCycle
    (R : ClosedCorrespondenceWindowRealization G W)
    (i : Fin W.N)
    (hvis : R.PointVisible i) :
    codimensionCycles V.X p := by
  let x : CodimensionPoint V.X p := Classical.choose hvis
  let alpha : ClassicalHodgeFiber V H p :=
    ⟨H.cycleClass p (codimensionPointCycle V.X p x),
      G.pointClass_is_hodge p x⟩
  let c : ℚ := hodgeCoordinate (W.basisIndex i) alpha
  let s : ℚ := W.augmentedIsolatorScale i
  exact (s * c)⁻¹ •
    linearPolyEval (realizedWordPair R.word).cycleOperator
      (W.augmentedIsolatorPolynomial i)
      (codimensionPointCycle V.X p x)

/-- **ONE OBSERVABLE + ONE VISIBLE POINT -> EXACT BASIS CYCLE.** -/
theorem extractedBasisCycle_spec
    (R : ClosedCorrespondenceWindowRealization G W)
    (i : Fin W.N)
    (hvis : R.PointVisible i) :
    H.cycleClass p (R.extractedBasisCycle i hvis) =
      (classicalHodgeBasis V H p (W.basisIndex i)).1 := by
  let x : CodimensionPoint V.X p := Classical.choose hvis
  let alpha : ClassicalHodgeFiber V H p :=
    ⟨H.cycleClass p (codimensionPointCycle V.X p x),
      G.pointClass_is_hodge p x⟩
  let c : ℚ := hodgeCoordinate (W.basisIndex i) alpha
  let s : ℚ := W.augmentedIsolatorScale i
  have hc : c ≠ 0 := Classical.choose_spec hvis
  have hs : s ≠ 0 := W.augmentedIsolatorScale_ne_zero i
  have hnat := linearPolyEval_intertwines
    (H.cycleClass p)
    (realizedWordPair R.word).cycleOperator
    (realizedWordPair R.word).cohomologyOperator
    (realizedWordPair R.word).cycleClass_cycleOperator
    (W.augmentedIsolatorPolynomial i)
    (codimensionPointCycle V.X p x)
  have hpolyWord :
      linearPolyEval (realizedWordPair R.word).cohomologyOperator
          (W.augmentedIsolatorPolynomial i) alpha.1 =
        linearPolyEval W.zeroComplementObservable
          (W.augmentedIsolatorPolynomial i) alpha.1 :=
    R.linearPolyEval_on_hodge (W.augmentedIsolatorPolynomial i) alpha
  have hproj := W.augmentedProjectorOnHodge_apply i alpha
  unfold extractedBasisCycle
  rw [LinearMap.map_smul]
  rw [hnat]
  change (s * c)⁻¹ •
      linearPolyEval (realizedWordPair R.word).cohomologyOperator
        (W.augmentedIsolatorPolynomial i) alpha.1 = _
  rw [hpolyWord]
  change (s * c)⁻¹ • W.augmentedProjectorOnHodge i alpha = _
  rw [hproj]
  simp [s, c, hs, hc, smul_smul, mul_comm, mul_left_comm, mul_assoc]

/-- A visible selected sheet therefore belongs to the actual algebraic Hodge
subspace. -/
theorem selected_basis_algebraic
    (R : ClosedCorrespondenceWindowRealization G W)
    (i : Fin W.N)
    (hvis : R.PointVisible i) :
    (classicalHodgeBasis V H p (W.basisIndex i)).1 ∈
      GSTClassicalHodgeAtomicSpan.pointCycleClassSpan p (H.cycleClass p) := by
  rw [← GSTClassicalHodgeAtomicSpan.smoothProjective_cycleClass_range_eq_atomic_span V H p]
  exact ⟨R.extractedBasisCycle i hvis, R.extractedBasisCycle_spec i hvis⟩

/-- One realized observable plus point visibility for every slot algebraizes
the entire selected finite Hodge window. -/
theorem selected_window_algebraic
    (R : ClosedCorrespondenceWindowRealization G W)
    (hvis : ∀ i : Fin W.N, R.PointVisible i) :
    ∀ i : Fin W.N,
      (classicalHodgeBasis V H p (W.basisIndex i)).1 ∈
        GSTClassicalHodgeAtomicSpan.pointCycleClassSpan p (H.cycleClass p) :=
  fun i => R.selected_basis_algebraic i (hvis i)

end ClosedCorrespondenceWindowRealization

#check ClosedCorrespondenceWindowRealization
#check ClosedCorrespondenceWindowRealization.word_hodge
#check ClosedCorrespondenceWindowRealization.hodgeOperator
#check ClosedCorrespondenceWindowRealization.hodgeOperator_eq_diagonal
#check ClosedCorrespondenceWindowRealization.linearPolyEval_on_hodge
#check ClosedCorrespondenceWindowRealization.PointVisible
#check ClosedCorrespondenceWindowRealization.extractedBasisCycle
#check ClosedCorrespondenceWindowRealization.extractedBasisCycle_spec
#check ClosedCorrespondenceWindowRealization.selected_window_algebraic

#print axioms ClosedCorrespondenceWindowRealization.linearPolyEval_on_hodge
#print axioms ClosedCorrespondenceWindowRealization.extractedBasisCycle_spec
#print axioms ClosedCorrespondenceWindowRealization.selected_window_algebraic

end GSTClassicalHodgeClosedCorrespondenceSpectralAmplifier
