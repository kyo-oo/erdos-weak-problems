import Mathlib.LinearAlgebra.Projection
import GSTClassicalHodgeCanonicalSpectralObservable
import GSTClassicalHodgeCyclicSpectralGeneration

/-!
# GST CLASSICAL HODGE — ZERO-COMPLEMENT SPECTRUM

The first canonical spectral construction used an arbitrary linear extension
of the Hodge-diagonal operator.  For projector extraction we can do better.
Every rational vector space is complemented, so the genuine rational Hodge
subspace admits an algebraic complement.  We choose one and define the ambient
observable by:

* the canonical diagonal operator on the Hodge subspace;
* zero on the complementary subspace.

Consequently zero is the only complementary eigenvalue.  Multiplying the
ordinary Lagrange isolator by `X` kills the whole complement while preserving
the selected nonzero Hodge eigenvalue.  The resulting polynomial is therefore
an honest ambient sheet projector, not merely a projector inside the selected
finite Hodge span.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000000

noncomputable section

open scoped BigOperators
open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeCyclicSpectralGeneration
open GSTClassicalHodgeSpectralSeparatorCollision
open GSTClassicalHodgeCanonicalSpectralObservable

namespace GSTClassicalHodgeZeroComplementSpectrum

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

abbrev AmbientCohomology :=
  RationalSingularCohomology H.analytification (2 * p)

end GSTClassicalHodgeZeroComplementSpectrum

open GSTClassicalHodgeZeroComplementSpectrum

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

namespace GSTClassicalHodgeCanonicalSpectralObservable.FiniteHodgeBasisWindow

/-- The genuine Hodge subspace in ambient rational singular cohomology. -/
abbrev hodgeSubspace
    (W : FiniteHodgeBasisWindow V H p) :
    Submodule ℚ (AmbientCohomology (H := H) (p := p)) :=
  rationalHodgeSubspace (H.hodgeBigrading p)

/-- Choose an algebraic vector-space complement to the genuine Hodge
subspace.  Existence is automatic over the field `ℚ`. -/
noncomputable def hodgeComplement
    (W : FiniteHodgeBasisWindow V H p) :
    Submodule ℚ (AmbientCohomology (H := H) (p := p)) :=
  Classical.choose (exists_isCompl W.hodgeSubspace)

/-- The chosen complement is genuinely complementary. -/
theorem hodge_isCompl_complement
    (W : FiniteHodgeBasisWindow V H p) :
    IsCompl W.hodgeSubspace W.hodgeComplement :=
  Classical.choose_spec (exists_isCompl W.hodgeSubspace)

/-- Canonical projection from ambient cohomology onto the genuine rational
Hodge fiber along the chosen complement. -/
noncomputable def hodgeProjection
    (W : FiniteHodgeBasisWindow V H p) :
    AmbientCohomology (H := H) (p := p) →ₗ[ℚ]
      ClassicalHodgeFiber V H p :=
  W.hodgeSubspace.projectionOnto W.hodgeComplement
    W.hodge_isCompl_complement

@[simp]
theorem hodgeProjection_on_hodge
    (W : FiniteHodgeBasisWindow V H p)
    (x : ClassicalHodgeFiber V H p) :
    W.hodgeProjection x.1 = x := by
  exact Submodule.projectionOnto_apply_left
    W.hodge_isCompl_complement x

/-- The Hodge projection kills the chosen complementary sector. -/
@[simp]
theorem hodgeProjection_on_complement
    (W : FiniteHodgeBasisWindow V H p)
    (x : W.hodgeComplement) :
    W.hodgeProjection x.1 = 0 := by
  exact Submodule.projectionOnto_apply_right
    W.hodge_isCompl_complement x

/-- Zero-complement ambient observable.  It projects to the genuine Hodge
fiber, applies the canonical diagonal operator there, and includes back into
ambient cohomology. -/
noncomputable def zeroComplementObservable
    (W : FiniteHodgeBasisWindow V H p) :
    AmbientCohomology (H := H) (p := p) →ₗ[ℚ]
      AmbientCohomology (H := H) (p := p) :=
  W.hodgeSubspace.subtype.comp
    (W.hodgeDiagonal.comp W.hodgeProjection)

/-- On every genuine Hodge vector the zero-complement observable is exactly
the canonical Hodge-diagonal operator. -/
theorem zeroComplementObservable_on_hodge
    (W : FiniteHodgeBasisWindow V H p)
    (x : ClassicalHodgeFiber V H p) :
    W.zeroComplementObservable x.1 = (W.hodgeDiagonal x).1 := by
  simp [zeroComplementObservable]

/-- The observable vanishes identically on the complementary sector. -/
theorem zeroComplementObservable_on_complement
    (W : FiniteHodgeBasisWindow V H p)
    (x : W.hodgeComplement) :
    W.zeroComplementObservable x.1 = 0 := by
  simp [zeroComplementObservable]

/-- Selected genuine Hodge basis directions retain their distinct canonical
nonzero eigenvalues. -/
theorem zeroComplementObservable_selected
    (W : FiniteHodgeBasisWindow V H p)
    (i : Fin W.N) :
    W.zeroComplementObservable
        (classicalHodgeBasis V H p (W.basisIndex i)).1 =
      W.eigenvalue i •
        (classicalHodgeBasis V H p (W.basisIndex i)).1 := by
  rw [W.zeroComplementObservable_on_hodge]
  rw [W.hodgeDiagonal_selected]
  rfl

/-- Raw spectral observable with the stronger zero-complement behavior. -/
noncomputable def toZeroComplementRawSpectralObservable
    (W : FiniteHodgeBasisWindow V H p) :
    RawClassicalHodgeSpectralObservable V H p (Fin W.N) where
  basisIndex := W.basisIndex
  basisIndex_injective := W.basisIndex_injective
  observable := W.zeroComplementObservable
  eigenvalue := W.eigenvalue
  eigenvalue_injective := W.eigenvalue_injective
  eigenvector := W.zeroComplementObservable_selected

/-- The extra factor `X` kills the zero-eigenvalue complement. -/
noncomputable def augmentedIsolatorPolynomial
    (W : FiniteHodgeBasisWindow V H p)
    (i : Fin W.N) : Polynomial ℚ :=
  Polynomial.X *
    (W.toZeroComplementRawSpectralObservable.toFiniteSpectralFamily).isolatorPolynomial i

/-- Scalar by which the augmented isolator acts on the selected Hodge sheet. -/
noncomputable def augmentedIsolatorScale
    (W : FiniteHodgeBasisWindow V H p)
    (i : Fin W.N) : ℚ :=
  W.eigenvalue i *
    (W.toZeroComplementRawSpectralObservable.toFiniteSpectralFamily).isolatorScale i

/-- The augmented normalization scalar is nonzero. -/
theorem augmentedIsolatorScale_ne_zero
    (W : FiniteHodgeBasisWindow V H p)
    (i : Fin W.N) :
    W.augmentedIsolatorScale i ≠ 0 := by
  apply mul_ne_zero
  · unfold eigenvalue
    exact ne_of_gt (by positivity)
  · exact
      (W.toZeroComplementRawSpectralObservable.toFiniteSpectralFamily).isolatorScale_ne_zero i

/-- The augmented projector selects its Hodge sheet with the exact nonzero
normalization. -/
theorem augmentedIsolator_selects_self
    (W : FiniteHodgeBasisWindow V H p)
    (i : Fin W.N) :
    linearPolyEval W.zeroComplementObservable
        (W.augmentedIsolatorPolynomial i)
        (classicalHodgeBasis V H p (W.basisIndex i)).1 =
      W.augmentedIsolatorScale i •
        (classicalHodgeBasis V H p (W.basisIndex i)).1 := by
  let F := W.toZeroComplementRawSpectralObservable.toFiniteSpectralFamily
  rw [show W.zeroComplementObservable = F.observable from rfl]
  rw [show (classicalHodgeBasis V H p (W.basisIndex i)).1 = F.vector i from rfl]
  rw [F.linearPolyEval_eigenvector]
  simp [augmentedIsolatorPolynomial, augmentedIsolatorScale,
    FiniteSpectralFamily.isolatorScale]
  rfl

/-- The augmented projector kills every other selected Hodge sheet. -/
theorem augmentedIsolator_kills_other
    (W : FiniteHodgeBasisWindow V H p)
    (i j : Fin W.N)
    (hji : j ≠ i) :
    linearPolyEval W.zeroComplementObservable
        (W.augmentedIsolatorPolynomial i)
        (classicalHodgeBasis V H p (W.basisIndex j)).1 = 0 := by
  let F := W.toZeroComplementRawSpectralObservable.toFiniteSpectralFamily
  rw [show W.zeroComplementObservable = F.observable from rfl]
  rw [show (classicalHodgeBasis V H p (W.basisIndex j)).1 = F.vector j from rfl]
  rw [F.linearPolyEval_eigenvector]
  have hz := F.isolatorPolynomial_eval_other i j hji
  simp [augmentedIsolatorPolynomial, hz]
  exact Or.inl (Or.inr hz)

/-- Every positive-degree polynomial in the zero-complement observable kills
all vectors in the chosen complement.  In particular every augmented sheet
projector kills the entire non-Hodge sector selected by that complement. -/
theorem augmentedIsolator_kills_complement
    (W : FiniteHodgeBasisWindow V H p)
    (i : Fin W.N)
    (x : W.hodgeComplement) :
    linearPolyEval W.zeroComplementObservable
        (W.augmentedIsolatorPolynomial i) x.1 = 0 := by
  have hzero : W.zeroComplementObservable x.1 = 0 :=
    W.zeroComplementObservable_on_complement x
  rw [linearPolyEval_of_eigenvector W.zeroComplementObservable x.1 0
    (by simpa using hzero)]
  simp [augmentedIsolatorPolynomial]

#check hodgeComplement
#check hodgeProjection
#check zeroComplementObservable
#check toZeroComplementRawSpectralObservable
#check augmentedIsolatorPolynomial
#check augmentedIsolatorScale
#check augmentedIsolator_selects_self
#check augmentedIsolator_kills_other
#check augmentedIsolator_kills_complement

#print axioms zeroComplementObservable_selected
#print axioms augmentedIsolator_selects_self
#print axioms augmentedIsolator_kills_other
#print axioms augmentedIsolator_kills_complement

end GSTClassicalHodgeCanonicalSpectralObservable.FiniteHodgeBasisWindow

