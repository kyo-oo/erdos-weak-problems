import GSTClassicalHodgeProjectiveWordOrbit
import GSTClassicalHodgeNativeGeneratorNaturality
import GSTClassicalHodgeCoordinatewiseSeedAssembly
import GSTClassicalHodgeGeneratorwiseAtomicStability
import GSTNativeCodimensionCyclePresentation

/-!
# GST CLASSICAL HODGE — ONE PROJECTIVE WORD / FINITE SPECTRAL COVER

The previous projective-word crown allowed one independently chosen geometric
word for each target basis sheet.  This file compresses that interface again.

A single finite noncommutative projective word already acts on native cycles.
Hence its canonical cohomological realization has a native lift on every
codimension-p point generator: simply apply the same word to that point cycle.
On a smooth projective carrier, native generatorwise lifts imply atomic-span
stability.  Thus algebraicity preservation of the observable is now a theorem,
not an input.

If that one geometric word is spectral with distinct rational eigenvalues on a
finite family of genuine Hodge basis directions, only coordinatewise atomic
visibility remains.  Different coordinates may be witnessed by different
algebraic combinations.  Infinite-field hyperplane avoidance assembles one
cyclic algebraic seed, and the existing Lagrange-isolator calculus extracts
every selected sheet.

For one concrete Hodge class it is enough that the finite spectral family
covers its live support.  Therefore the per-class geometric burden becomes:

  one genuine projective operator word
+ finite spectral laws for that word
+ weak coordinate visibility on a finite cover
= one exact native algebraic cycle for the Hodge class.

No matrix unit, no exact target word, no whole-fiber operator realization and
no separately assumed atomic stability occurs in this crown.
-/

set_option maxHeartbeats 90000000
set_option maxRecDepth 1000000

noncomputable section

open scoped BigOperators
open AlgebraicGeometry

namespace GSTClassicalHodgeProjectiveSpectralCover

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeGeneratorwiseAtomicStability
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeLocalCyclicCriterion
open GSTClassicalHodgeCyclicSpectralGeneration
open GSTClassicalHodgeCoordinatewiseSeedAssembly
open GSTClassicalHodgeNativeGeneratorNaturality
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeProjectiveWordOrbit

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

namespace ProjectiveOperatorWord

/-- Every genuine projective word has native generatorwise lifts for its
canonical cohomological realization. -/
theorem hasNativePointLifts
    (G : GeometricCycleClassSpine V H)
    (W : ProjectiveOperatorWord V p) :
    HasNativePointLifts
      (p := p) (cl := H.cycleClass p)
      (W.operatorPair G).cohomologyOperator := by
  intro x
  refine ⟨W.eval (GSTNativeCodimensionCyclePresentation.codimensionPointCycle V.X p x), ?_⟩
  exact W.cycleClass_eval G (GSTNativeCodimensionCyclePresentation.codimensionPointCycle V.X p x)

/-- Consequently the cohomological face of every projective word preserves the
actual atomic cycle-class span.  This is derived from geometric action on point
generators rather than supplied as an external invariant. -/
theorem cohomologyOperator_atomicStable
    (G : GeometricCycleClassSpine V H)
    (W : ProjectiveOperatorWord V p) :
    AtomicSpanStable
      (p := p) (cl := H.cycleClass p)
      (W.operatorPair G).cohomologyOperator := by
  exact (smoothProjective_atomicStable_iff_nativePointLifts
    (V := V) (H := H) (p := p)
    (W.operatorPair G).cohomologyOperator).2
      (hasNativePointLifts G W)

end ProjectiveOperatorWord

/-- One projective word together with a finite diagonal Hodge chart for its
canonical cohomological action.  Algebraic-span stability is deliberately not
a field: it is proved from the geometric word. -/
structure ProjectiveWordSpectralFamily
    (G : GeometricCycleClassSpine V H)
    (ι : Type*) [Fintype ι] [DecidableEq ι] where
  word : ProjectiveOperatorWord V p
  basisIndex : ι → ClassicalHodgeBasisIndex V H p
  basisIndex_injective : Function.Injective basisIndex
  eigenvalue : ι → ℚ
  eigenvalue_injective : Function.Injective eigenvalue
  eigenvector : ∀ i,
    (word.operatorPair G).cohomologyOperator
        (classicalHodgeBasis V H p (basisIndex i)).1 =
      eigenvalue i • (classicalHodgeBasis V H p (basisIndex i)).1

namespace ProjectiveWordSpectralFamily

variable {G : GeometricCycleClassSpine V H}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Forget the geometric construction only after using it to discharge atomic
stability. -/
noncomputable def toClassicalHodgeSpectralOperator
    (S : ProjectiveWordSpectralFamily (V := V) (H := H) (p := p) G ι) :
    ClassicalHodgeSpectralOperator V H p ι where
  basisIndex := S.basisIndex
  basisIndex_injective := S.basisIndex_injective
  observable := (S.word.operatorPair G).cohomologyOperator
  eigenvalue := S.eigenvalue
  eigenvalue_injective := S.eigenvalue_injective
  eigenvector := S.eigenvector
  atomic_stable :=
    (ProjectiveOperatorWord.cohomologyOperator_atomicStable G S.word)

/-- Weak visibility of one selected spectral coordinate.  The witnessing
algebraic vector may mix all selected sheets; only the requested coefficient
must be nonzero. -/
def CoordinateVisible
    (S : ProjectiveWordSpectralFamily (V := V) (H := H) (p := p) G ι)
    (i : ι) : Prop :=
  ∃ a : ι → ℚ,
    (∑ j : ι,
      a j • (classicalHodgeBasis V H p (S.basisIndex j)).1) ∈
        pointCycleClassSpan p (H.cycleClass p)
    ∧ a i ≠ 0

/-- Coordinatewise visibility for the projective spectral family assembles one
algebraic cyclic seed with every selected coefficient nonzero. -/
theorem exists_cyclic_atomic_seed
    (S : ProjectiveWordSpectralFamily (V := V) (H := H) (p := p) G ι)
    (hvisible : ∀ i, S.CoordinateVisible i) :
    ∃ a : ι → ℚ,
      (∀ i, a i ≠ 0) ∧
      (∑ i : ι,
        a i • (classicalHodgeBasis V H p (S.basisIndex i)).1) ∈
          pointCycleClassSpan p (H.cycleClass p) := by
  let C := S.toClassicalHodgeSpectralOperator
  let F := C.toFiniteSpectralFamily
  let W := pointCycleClassSpan p (H.cycleClass p)
  have hvis : ∀ i, F.CoordinateVisible W i := by
    intro i
    rcases hvisible i with ⟨a, haW, hai⟩
    let aa : F.admissibleCoefficientSpace W := ⟨a, ?_⟩
    · exact ⟨aa, hai⟩
    · simpa [F, C, W,
        ClassicalHodgeSpectralOperator.toFiniteSpectralFamily,
        FiniteSpectralFamily.admissibleCoefficientSpace,
        FiniteSpectralFamily.spectralCombinationLinear,
        FiniteSpectralFamily.spectralCombination,
        ProjectiveWordSpectralFamily.toClassicalHodgeSpectralOperator]
        using haW
  obtain ⟨a, haNZ, haW⟩ :=
    F.exists_cyclic_seed_of_coordinatewise_visible W hvis
  refine ⟨a, haNZ, ?_⟩
  simpa [F, C, W,
    ClassicalHodgeSpectralOperator.toFiniteSpectralFamily,
    FiniteSpectralFamily.spectralCombination,
    ProjectiveWordSpectralFamily.toClassicalHodgeSpectralOperator]
    using haW

/-- **ONE-WORD SPECTRAL EXTRACTION.**  A single genuine projective word plus
coordinatewise visibility forces every selected Hodge basis sheet to be
algebraic. -/
theorem selected_basis_algebraic
    (S : ProjectiveWordSpectralFamily (V := V) (H := H) (p := p) G ι)
    (hvisible : ∀ i, S.CoordinateVisible i) :
    ∀ i : ι,
      (classicalHodgeBasis V H p (S.basisIndex i)).1 ∈
        pointCycleClassSpan p (H.cycleClass p) := by
  obtain ⟨a, haNZ, haW⟩ := S.exists_cyclic_atomic_seed hvisible
  exact S.toClassicalHodgeSpectralOperator.selected_basis_algebraic_of_cyclic_seed
    a haNZ haW

end ProjectiveWordSpectralFamily

/-- Finite geometric spectral cover for one concrete Hodge class.  The cover
may contain extra sheets; it only has to contain every live sheet of `alpha`.
Visibility is required on the finite cover, never on the unrestricted Hodge
basis. -/
structure FiniteProjectiveSpectralCover
    (G : GeometricCycleClassSpine V H)
    (alpha : ClassicalHodgeFiber V H p) where
  rank : Nat
  spectral :
    ProjectiveWordSpectralFamily
      (V := V) (H := H) (p := p) G (Fin rank)
  covers_live_support :
    ∀ i : HodgeSupportIndex alpha,
      ∃ k : Fin rank, spectral.basisIndex k = i.1
  visible : ∀ k : Fin rank, spectral.CoordinateVisible k

namespace FiniteProjectiveSpectralCover

variable {G : GeometricCycleClassSpine V H}
variable {alpha : ClassicalHodgeFiber V H p}

/-- Every live basis direction of the requested Hodge class is algebraic. -/
theorem live_basis_algebraic
    (C : FiniteProjectiveSpectralCover G alpha)
    (i : HodgeSupportIndex alpha) :
    (classicalHodgeBasis V H p i.1).1 ∈
      pointCycleClassSpan p (H.cycleClass p) := by
  rcases C.covers_live_support i with ⟨k, hk⟩
  rw [← hk]
  exact C.spectral.selected_basis_algebraic C.visible k

/-- The original Hodge class lies in the actual atomic cycle-class span. -/
theorem class_mem_atomicSpan
    (C : FiniteProjectiveSpectralCover G alpha) :
    alpha.1 ∈ pointCycleClassSpan p (H.cycleClass p) := by
  rw [hodgeClass_eq_support_sum alpha]
  apply Submodule.sum_mem
  intro i hi
  exact (pointCycleClassSpan p (H.cycleClass p)).smul_mem
    ((classicalHodgeBasis V H p).repr alpha i.1)
    (C.live_basis_algebraic i)

/-- **FINITE PROJECTIVE SPECTRAL COVER LANDING.**  The class is represented by
an actual native codimension-p algebraic cycle. -/
theorem exists_native_cycle
    (C : FiniteProjectiveSpectralCover G alpha) :
    ∃ Z : codimensionCycles V.X p,
      H.cycleClass p Z = alpha.1 := by
  exact pointCycleClassSpan_le_cycleClass_range
    p (H.cycleClass p) C.class_mem_atomicSpan

end FiniteProjectiveSpectralCover

/-- **ONE PROJECTIVE WORD PER FINITE COVER — STAGE-2G CROWN.**
For every nonzero concrete Hodge class, one finite projective spectral cover
suffices.  The zero class is represented by the zero native cycle and requests
no spectral data. -/
theorem bigradedBettiHodge_of_finite_projective_spectral_covers
    (G : GeometricCycleClassSpine V H)
    (C : ∀ p : Nat,
      ∀ alpha : ClassicalHodgeFiber V H p,
        alpha ≠ 0 → Nonempty (FiniteProjectiveSpectralCover G alpha)) :
    BigradedBettiHodgeStatement V H := by
  intro p x hx
  let alpha : ClassicalHodgeFiber V H p := ⟨x, hx⟩
  by_cases halpha : alpha = 0
  · have hx0 : x = 0 := congrArg Subtype.val halpha
    subst x
    exact ⟨0, by simp⟩
  · exact (Classical.choice (C p alpha halpha)).exists_native_cycle

/-- Elementwise form of the spectral-cover crown. -/
theorem every_hodge_class_has_native_cycle_of_finite_projective_spectral_covers
    (G : GeometricCycleClassSpine V H)
    (C : ∀ q : Nat,
      ∀ beta : ClassicalHodgeFiber V H q,
        beta ≠ 0 → Nonempty (FiniteProjectiveSpectralCover G beta))
    (alpha : ClassicalHodgeFiber V H p) :
    ∃ Z : codimensionCycles V.X p,
      H.cycleClass p Z = alpha.1 := by
  by_cases halpha : alpha = 0
  · refine ⟨0, ?_⟩
    rw [halpha]
    simp
  · exact (Classical.choice (C p alpha halpha)).exists_native_cycle

#check ProjectiveOperatorWord.hasNativePointLifts
#check ProjectiveOperatorWord.cohomologyOperator_atomicStable
#check ProjectiveWordSpectralFamily
#check ProjectiveWordSpectralFamily.exists_cyclic_atomic_seed
#check ProjectiveWordSpectralFamily.selected_basis_algebraic
#check FiniteProjectiveSpectralCover
#check FiniteProjectiveSpectralCover.live_basis_algebraic
#check FiniteProjectiveSpectralCover.class_mem_atomicSpan
#check FiniteProjectiveSpectralCover.exists_native_cycle
#check bigradedBettiHodge_of_finite_projective_spectral_covers
#check every_hodge_class_has_native_cycle_of_finite_projective_spectral_covers

#print axioms ProjectiveOperatorWord.hasNativePointLifts
#print axioms ProjectiveOperatorWord.cohomologyOperator_atomicStable
#print axioms ProjectiveWordSpectralFamily.selected_basis_algebraic
#print axioms FiniteProjectiveSpectralCover.exists_native_cycle
#print axioms bigradedBettiHodge_of_finite_projective_spectral_covers

end GSTClassicalHodgeProjectiveSpectralCover