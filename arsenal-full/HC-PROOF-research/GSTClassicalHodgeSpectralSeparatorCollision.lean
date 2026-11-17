import GSTClassicalHodgeCoordinatewiseSeedAssembly
import GSTClassicalHodgeSingleSheetCrown

/-!
# GST CLASSICAL HODGE — SPECTRAL/SEPARATOR COLLISION

This module isolates the contradiction engine independently of any particular
GST observable.

Let W be the genuine atomic cycle-class submodule.  Suppose a finite family of
Hodge sheets is diagonal for an observable with distinct eigenvalues and W
contains one cyclic seed with every selected coordinate nonzero.  If an
atomic separator detects one selected sheet while annihilating W, then the
observable cannot preserve W.

Reason: if W were invariant, Lagrange functional calculus would isolate the
detected sheet from the cyclic seed while remaining inside W.  The separator
would then have to both vanish and not vanish on that sheet.

Thus the final operator attack can be divided cleanly:

1. produce a GST/Lefschetz spectral observable and a cyclic atomic seed;
2. prove the observable is natural on genuine algebraic cycle classes;
3. every microscopic Hodge separator becomes impossible.
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
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeAtomicAnnihilator
open GSTClassicalHodgeSingleSheetCrown
open GSTClassicalHodgeCyclicSpectralGeneration

namespace GSTClassicalHodgeSpectralSeparatorCollision

universe u

variable {M : Type u} [AddCommGroup M] [Module ℚ M]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **ABSTRACT SPECTRAL-SEPARATOR COLLISION.**
A detector annihilating W but detecting one spectral direction forces any
observable admitting a W-valued cyclic seed to fail W-invariance. -/
theorem separator_forces_observable_instability
    (S : FiniteSpectralFamily ι M)
    (W : Submodule ℚ M)
    (ell : M →ₗ[ℚ] ℚ)
    (hann : W ≤ LinearMap.ker ell)
    (i : ι)
    (hdetect : ell (S.vector i) ≠ 0)
    (a : ι → ℚ)
    (ha : ∀ j, a j ≠ 0)
    (hseed : S.spectralCombination a ∈ W) :
    ¬ (∀ x : M, x ∈ W → S.observable x ∈ W) := by
  intro hstable
  have hiW : S.vector i ∈ W :=
    S.every_vector_mem_of_cyclic_seed W hstable a ha hseed i
  exact hdetect (hann hiW)

/-- Equivalent positive form: W-invariance plus a cyclic seed rules out every
functional that annihilates W and detects a selected eigendirection. -/
theorem no_separator_of_stable_cyclic_seed
    (S : FiniteSpectralFamily ι M)
    (W : Submodule ℚ M)
    (hstable : ∀ x : M, x ∈ W → S.observable x ∈ W)
    (a : ι → ℚ)
    (ha : ∀ j, a j ≠ 0)
    (hseed : S.spectralCombination a ∈ W)
    (i : ι)
    (ell : M →ₗ[ℚ] ℚ)
    (hann : W ≤ LinearMap.ker ell) :
    ell (S.vector i) = 0 := by
  have hiW : S.vector i ∈ W :=
    S.every_vector_mem_of_cyclic_seed W hstable a ha hseed i
  exact hann hiW

/-! ## Classical Hodge specialization without hiding stability -/

/-- A raw spectral observable on selected genuine Hodge basis directions.
Unlike `ClassicalHodgeSpectralOperator`, this structure deliberately does NOT
assume preservation of the atomic algebraic span. -/
structure RawClassicalHodgeSpectralObservable
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (ι : Type*) [Fintype ι] [DecidableEq ι] where
  basisIndex : ι → ClassicalHodgeBasisIndex V H p
  basisIndex_injective : Function.Injective basisIndex
  observable :
    RationalSingularCohomology H.analytification (2 * p) →ₗ[ℚ]
      RationalSingularCohomology H.analytification (2 * p)
  eigenvalue : ι → ℚ
  eigenvalue_injective : Function.Injective eigenvalue
  eigenvector : ∀ i,
    observable (classicalHodgeBasis V H p (basisIndex i)).1 =
      eigenvalue i • (classicalHodgeBasis V H p (basisIndex i)).1

namespace RawClassicalHodgeSpectralObservable

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- Underlying finite spectral family of a raw classical observable. -/
noncomputable def toFiniteSpectralFamily
    (S : RawClassicalHodgeSpectralObservable V H p ι) :
    FiniteSpectralFamily ι
      (RationalSingularCohomology H.analytification (2 * p)) where
  observable := S.observable
  vector := fun i => (classicalHodgeBasis V H p (S.basisIndex i)).1
  eigenvalue := S.eigenvalue
  eigenvector := S.eigenvector
  eigenvalue_injective := S.eigenvalue_injective

/-- Genuine atomic-span preservation, separated from the raw spectral data. -/
def AtomicStable
    (S : RawClassicalHodgeSpectralObservable V H p ι) : Prop :=
  ∀ x,
    x ∈ pointCycleClassSpan p (H.cycleClass p) →
      S.observable x ∈ pointCycleClassSpan p (H.cycleClass p)

/-- Add atomic stability to recover the previous geometry-ready spectral
operator. -/
noncomputable def toClassicalHodgeSpectralOperator
    (S : RawClassicalHodgeSpectralObservable V H p ι)
    (hstable : S.AtomicStable) :
    ClassicalHodgeSpectralOperator V H p ι where
  basisIndex := S.basisIndex
  basisIndex_injective := S.basisIndex_injective
  observable := S.observable
  eigenvalue := S.eigenvalue
  eigenvalue_injective := S.eigenvalue_injective
  eigenvector := S.eigenvector
  atomic_stable := hstable

/-- **MICROSCOPIC CLASSICAL COLLISION.**
If one selected Hodge sheet carries an atomic separator and a weighted atomic
cyclic seed touches every selected sheet, then the raw observable is forced to
break atomic-span invariance. -/
theorem basisSeparator_forces_not_atomicStable
    (S : RawClassicalHodgeSpectralObservable V H p ι)
    (i : ι)
    (Sep : BasisAtomicSeparator V H p (S.basisIndex i))
    (a : ι → ℚ)
    (ha : ∀ j, a j ≠ 0)
    (hseed :
      ∑ j : ι,
        a j • (classicalHodgeBasis V H p (S.basisIndex j)).1 ∈
          pointCycleClassSpan p (H.cycleClass p)) :
    ¬ S.AtomicStable := by
  let F := S.toFiniteSpectralFamily
  have hann :
      pointCycleClassSpan p (H.cycleClass p) ≤
        LinearMap.ker Sep.detector :=
    (annihilatesPointCycles_iff_atomicSpan_le_ker
      p (H.cycleClass p) Sep.detector).mp Sep.annihilates_atoms
  apply separator_forces_observable_instability F
    (pointCycleClassSpan p (H.cycleClass p))
    Sep.detector hann i
    (by simpa [F, RawClassicalHodgeSpectralObservable.toFiniteSpectralFamily] using
      Sep.detects_basis)
    a
    ha
    (by simpa [F, FiniteSpectralFamily.spectralCombination,
      RawClassicalHodgeSpectralObservable.toFiniteSpectralFamily] using hseed)

/-- Positive contradiction form: atomic stability and one cyclic seed eliminate
any basis separator on every selected sheet. -/
theorem isEmpty_basisAtomicSeparator_of_stable_seed
    (S : RawClassicalHodgeSpectralObservable V H p ι)
    (hstable : S.AtomicStable)
    (a : ι → ℚ)
    (ha : ∀ j, a j ≠ 0)
    (hseed :
      ∑ j : ι,
        a j • (classicalHodgeBasis V H p (S.basisIndex j)).1 ∈
          pointCycleClassSpan p (H.cycleClass p))
    (i : ι) :
    IsEmpty (BasisAtomicSeparator V H p (S.basisIndex i)) := by
  refine ⟨?_⟩
  intro Sep
  exact (S.basisSeparator_forces_not_atomicStable i Sep a ha hseed) hstable

end RawClassicalHodgeSpectralObservable

#check separator_forces_observable_instability
#check no_separator_of_stable_cyclic_seed
#check RawClassicalHodgeSpectralObservable
#check RawClassicalHodgeSpectralObservable.AtomicStable
#check RawClassicalHodgeSpectralObservable.toClassicalHodgeSpectralOperator
#check RawClassicalHodgeSpectralObservable.basisSeparator_forces_not_atomicStable
#check RawClassicalHodgeSpectralObservable.isEmpty_basisAtomicSeparator_of_stable_seed

#print axioms separator_forces_observable_instability
#print axioms no_separator_of_stable_cyclic_seed
#print axioms RawClassicalHodgeSpectralObservable.basisSeparator_forces_not_atomicStable
#print axioms RawClassicalHodgeSpectralObservable.isEmpty_basisAtomicSeparator_of_stable_seed

end GSTClassicalHodgeSpectralSeparatorCollision
