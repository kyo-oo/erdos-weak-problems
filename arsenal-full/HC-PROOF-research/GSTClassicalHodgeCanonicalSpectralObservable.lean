import Mathlib.LinearAlgebra.Basis.VectorSpace
import GSTClassicalHodgeGeneratorwiseAtomicStability
import GSTClassicalHodgeFiniteSupportChart

/-!
# GST CLASSICAL HODGE — CANONICAL SPECTRAL OBSERVABLE

The spectral observable used by the microscopic Hodge attack is not extra
geometry.  It can be manufactured from the genuine rational `(p,p)` Hodge
fiber itself.

For any finite injective window of genuine Hodge-basis directions we:

1. assign the distinct rational labels `1,2,...,N`;
2. define the corresponding diagonal endomorphism of the genuine Hodge
   subspace by basis coordinates;
3. include that endomorphism in ambient rational singular cohomology;
4. extend it linearly from the Hodge subspace to all ambient cohomology using
   the vector-space extension theorem.

The resulting ambient operator has exactly the requested Hodge basis vectors
as eigenvectors with pairwise-distinct eigenvalues.  Thus all remaining
geometry in the microscopic certificate is concentrated in cycle naturality
and the projector seed, not in an arbitrary choice of spectral operator.
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
open GSTClassicalHodgeSpectralSeparatorCollision
open GSTClassicalHodgeGeneratorwiseAtomicStability

namespace GSTClassicalHodgeCanonicalSpectralObservable

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- A finite window in the unrestricted genuine Hodge basis. -/
structure FiniteHodgeBasisWindow
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat) where
  N : Nat
  basisIndex : Fin N → ClassicalHodgeBasisIndex V H p
  basisIndex_injective : Function.Injective basisIndex

namespace FiniteHodgeBasisWindow

/-- Canonical nonzero spectral label.  Starting at one is useful later because
zero can be reserved for the complementary/nonselected sector. -/
def eigenvalue
    (W : FiniteHodgeBasisWindow V H p) (i : Fin W.N) : ℚ :=
  (i.1 + 1 : Nat)

/-- Canonical spectral labels are pairwise distinct. -/
theorem eigenvalue_injective
    (W : FiniteHodgeBasisWindow V H p) :
    Function.Injective W.eigenvalue := by
  intro i j hij
  apply Fin.ext
  have h2 : (i.1 + 1 : Nat) = (j.1 + 1 : Nat) := by
    have h3 : ((i.1 + 1 : Nat) : ℚ) = ((j.1 + 1 : Nat) : ℚ) := hij
    exact_mod_cast h3
  omega

/-- Weight attached to an arbitrary genuine Hodge-basis direction.  A live
window direction receives its canonical eigenvalue; every nonselected basis
direction receives zero. -/
noncomputable def basisWeight
    (W : FiniteHodgeBasisWindow V H p)
    (j : ClassicalHodgeBasisIndex V H p) : ℚ :=
  ∑ i : Fin W.N,
    if W.basisIndex i = j then W.eigenvalue i else 0

/-- On a selected sheet the basis weight is exactly its canonical eigenvalue. -/
theorem basisWeight_selected
    (W : FiniteHodgeBasisWindow V H p)
    (i : Fin W.N) :
    W.basisWeight (W.basisIndex i) = W.eigenvalue i := by
  classical
  unfold basisWeight
  rw [Finset.sum_eq_single i]
  · simp
  · intro j hj hji
    have hne : W.basisIndex j ≠ W.basisIndex i :=
      W.basisIndex_injective.ne hji
    simp [hne]
  · simp

/-- Diagonal endomorphism on the genuine rational `(p,p)` Hodge fiber. -/
noncomputable def hodgeDiagonal
    (W : FiniteHodgeBasisWindow V H p) :
    ClassicalHodgeFiber V H p →ₗ[ℚ] ClassicalHodgeFiber V H p :=
  (classicalHodgeBasis V H p).constr ℚ
    (fun j => W.basisWeight j • classicalHodgeBasis V H p j)

@[simp]
theorem hodgeDiagonal_basis
    (W : FiniteHodgeBasisWindow V H p)
    (j : ClassicalHodgeBasisIndex V H p) :
    W.hodgeDiagonal (classicalHodgeBasis V H p j) =
      W.basisWeight j • classicalHodgeBasis V H p j := by
  simp [hodgeDiagonal]

@[simp]
theorem hodgeDiagonal_selected
    (W : FiniteHodgeBasisWindow V H p)
    (i : Fin W.N) :
    W.hodgeDiagonal (classicalHodgeBasis V H p (W.basisIndex i)) =
      W.eigenvalue i • classicalHodgeBasis V H p (W.basisIndex i) := by
  rw [W.hodgeDiagonal_basis, W.basisWeight_selected]

/-- Hodge-diagonal operator viewed as a map from the Hodge subspace into the
ambient rational singular cohomology. -/
noncomputable def hodgeDiagonalIntoAmbient
    (W : FiniteHodgeBasisWindow V H p) :
    ClassicalHodgeFiber V H p →ₗ[ℚ]
      RationalSingularCohomology H.analytification (2 * p) :=
  (rationalHodgeSubspace (H.hodgeBigrading p)).subtype.comp W.hodgeDiagonal

/-- Every Hodge-subspace linear map extends to ambient cohomology.  We choose
one extension of the canonical diagonal map. -/
noncomputable def ambientObservable
    (W : FiniteHodgeBasisWindow V H p) :
    RationalSingularCohomology H.analytification (2 * p) →ₗ[ℚ]
      RationalSingularCohomology H.analytification (2 * p) :=
  Classical.choose (LinearMap.exists_extend W.hodgeDiagonalIntoAmbient)

/-- The chosen ambient extension agrees with the diagonal Hodge operator on
all genuine Hodge classes. -/
theorem ambientObservable_comp_subtype
    (W : FiniteHodgeBasisWindow V H p) :
    W.ambientObservable.comp
        (rationalHodgeSubspace (H.hodgeBigrading p)).subtype =
      W.hodgeDiagonalIntoAmbient := by
  exact Classical.choose_spec
    (LinearMap.exists_extend W.hodgeDiagonalIntoAmbient)

/-- In particular every selected genuine Hodge-basis direction is an exact
eigenvector of the ambient operator. -/
theorem ambientObservable_selected
    (W : FiniteHodgeBasisWindow V H p)
    (i : Fin W.N) :
    W.ambientObservable
        (classicalHodgeBasis V H p (W.basisIndex i)).1 =
      W.eigenvalue i •
        (classicalHodgeBasis V H p (W.basisIndex i)).1 := by
  have h := LinearMap.congr_fun W.ambientObservable_comp_subtype
    (classicalHodgeBasis V H p (W.basisIndex i))
  simpa [hodgeDiagonalIntoAmbient, hodgeDiagonal_selected,
    basisWeight_selected] using h

/-- **CANONICAL RAW SPECTRAL OBSERVABLE.**  No spectral datum is supplied:
it is manufactured from the finite Hodge-basis window. -/
noncomputable def toRawSpectralObservable
    (W : FiniteHodgeBasisWindow V H p) :
    RawClassicalHodgeSpectralObservable V H p (Fin W.N) where
  basisIndex := W.basisIndex
  basisIndex_injective := W.basisIndex_injective
  observable := W.ambientObservable
  eigenvalue := W.eigenvalue
  eigenvalue_injective := W.eigenvalue_injective
  eigenvector := W.ambientObservable_selected

@[simp]
theorem toRawSpectralObservable_basisIndex
    (W : FiniteHodgeBasisWindow V H p) :
    W.toRawSpectralObservable.basisIndex = W.basisIndex := rfl

@[simp]
theorem toRawSpectralObservable_observable
    (W : FiniteHodgeBasisWindow V H p) :
    W.toRawSpectralObservable.observable = W.ambientObservable := rfl

/-- Singleton window centered on one genuine Hodge basis sheet. -/
noncomputable def singleton
    (i : ClassicalHodgeBasisIndex V H p) :
    FiniteHodgeBasisWindow V H p where
  N := 1
  basisIndex := fun _ => i
  basisIndex_injective := by
    intro a b _
    exact Subsingleton.elim a b

@[simp]
theorem singleton_basisIndex
    (i : ClassicalHodgeBasisIndex V H p)
    (j : Fin (singleton i).N) :
    (singleton i).basisIndex j = i := rfl

/-- Spectral data needed for one microscopic basis-sheet attack exists
unconditionally. -/
theorem exists_rawSpectralObservable_targeting
    (i : ClassicalHodgeBasisIndex V H p) :
    ∃ N : Nat,
      ∃ S : RawClassicalHodgeSpectralObservable V H p (Fin N),
      ∃ slot : Fin N, S.basisIndex slot = i := by
  refine ⟨1, (singleton i).toRawSpectralObservable, 0, ?_⟩
  rfl

end FiniteHodgeBasisWindow

#check FiniteHodgeBasisWindow
#check FiniteHodgeBasisWindow.eigenvalue
#check FiniteHodgeBasisWindow.hodgeDiagonal
#check FiniteHodgeBasisWindow.ambientObservable
#check FiniteHodgeBasisWindow.toRawSpectralObservable
#check FiniteHodgeBasisWindow.singleton
#check FiniteHodgeBasisWindow.exists_rawSpectralObservable_targeting

#print axioms FiniteHodgeBasisWindow.ambientObservable_selected
#print axioms FiniteHodgeBasisWindow.toRawSpectralObservable
#print axioms FiniteHodgeBasisWindow.exists_rawSpectralObservable_targeting

end GSTClassicalHodgeCanonicalSpectralObservable
