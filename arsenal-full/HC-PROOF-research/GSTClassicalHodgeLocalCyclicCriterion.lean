import GSTClassicalHodgeCyclicSpectralGeneration

/-!
# GST CLASSICAL HODGE — LOCAL CYCLIC CRITERION

The genuine rational `(p,p)` Hodge fiber need not have finite rank for this
proof architecture.  Every individual vector has finite support in the chosen
basis.  Therefore cyclic spectral generation is needed only on the finite set
of basis directions actually used by the class under consideration.

For one Hodge class alpha, let SupportIndex(alpha) be the subtype of basis
indices occurring with nonzero coefficient in `Basis.repr alpha`.  A local
cyclic realization consists of:

* one ambient rational observable whose eigenvalues are distinct on those live
  directions;
* stability of the genuine atomic algebraic span under that observable;
* one algebraic seed equal to the sum of the live basis directions.

Lagrange projectors then extract every live basis vector.  Since alpha is a
finite linear combination of exactly those live vectors, alpha is algebraic.

This removes every global finite-dimensionality or countability hypothesis.
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
open GSTClassicalHodgeCyclicSpectralGeneration

namespace GSTClassicalHodgeLocalCyclicCriterion

/-- Live basis indices of one genuine rational Hodge class. -/
abbrev HodgeSupportIndex
    {V : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    {p : Nat}
    (alpha : ClassicalHodgeFiber V H p) :=
  {i : ClassicalHodgeBasisIndex V H p //
    i ∈ ((classicalHodgeBasis V H p).repr alpha).support}

/-- Inclusion of a live support index back into the full Hodge-basis index. -/
def HodgeSupportIndex.include
    {V : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    {p : Nat}
    {alpha : ClassicalHodgeFiber V H p} :
    HodgeSupportIndex alpha → ClassicalHodgeBasisIndex V H p :=
  fun i => i.1

/-- The support inclusion is injective. -/
theorem HodgeSupportIndex.include_injective
    {V : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    {p : Nat}
    {alpha : ClassicalHodgeFiber V H p} :
    Function.Injective (@HodgeSupportIndex.include V H p alpha) := by
  intro i j h
  exact Subtype.ext h

/-- Every live support coefficient is nonzero by construction. -/
theorem support_coefficient_ne_zero
    {V : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    {p : Nat}
    (alpha : ClassicalHodgeFiber V H p)
    (i : HodgeSupportIndex alpha) :
    (classicalHodgeBasis V H p).repr alpha i.1 ≠ 0 := by
  exact Finsupp.mem_support_iff.mp i.2

/-- The actual class is exactly the sum over its live support subtype. -/
theorem hodgeClass_eq_support_sum
    {V : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    {p : Nat}
    (alpha : ClassicalHodgeFiber V H p) :
    alpha.1 =
      ∑ i : HodgeSupportIndex alpha,
        ((classicalHodgeBasis V H p).repr alpha i.1) •
          (classicalHodgeBasis V H p i.1).1 := by
  have hcomb : Finsupp.linearCombination ℚ (classicalHodgeBasis V H p)
      ((classicalHodgeBasis V H p).repr alpha) = alpha :=
    (classicalHodgeBasis V H p).linearCombination_repr alpha
  have hpush : (ClassicalHodgeFiber V H p).subtype
      (((classicalHodgeBasis V H p).repr alpha).sum
        (fun i c => c • (classicalHodgeBasis V H p i)))
      = ∑ i ∈ ((classicalHodgeBasis V H p).repr alpha).support,
          ((classicalHodgeBasis V H p).repr alpha i) •
            (classicalHodgeBasis V H p i).1 := by
    rw [map_finsuppSum]
    simp only [Finsupp.sum]
    exact Finset.sum_congr rfl fun i _ =>
      map_smul (ClassicalHodgeFiber V H p).subtype _ _
  calc alpha.1
      = (Finsupp.linearCombination ℚ (classicalHodgeBasis V H p)
          ((classicalHodgeBasis V H p).repr alpha)).1 := by
        rw [hcomb]
    _ = (((classicalHodgeBasis V H p).repr alpha).sum
        (fun i c => c • (classicalHodgeBasis V H p i))).1 := by
        rw [Finsupp.linearCombination_apply]
    _ = ∑ i ∈ ((classicalHodgeBasis V H p).repr alpha).support,
        ((classicalHodgeBasis V H p).repr alpha i) •
          (classicalHodgeBasis V H p i).1 := hpush
    _ = ∑ i : HodgeSupportIndex alpha,
        ((classicalHodgeBasis V H p).repr alpha i.1) •
          (classicalHodgeBasis V H p i.1).1 :=
      (Finset.sum_coe_sort
        (s := ((classicalHodgeBasis V H p).repr alpha).support)
        (f := fun j => ((classicalHodgeBasis V H p).repr alpha j) •
          (classicalHodgeBasis V H p j).1)).symm

/-- A local cyclic realization of precisely the live support of one Hodge
class.  No algebraicity of the class itself or of any individual basis vector
is assumed. -/
structure LocalCyclicRealization
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (alpha : ClassicalHodgeFiber V H p) where
  spectral :
    ClassicalHodgeSpectralOperator V H p (HodgeSupportIndex alpha)
  spectral_basisIndex :
    spectral.basisIndex = HodgeSupportIndex.include
  seed_mem_atomic :
    (∑ i : HodgeSupportIndex alpha,
      (classicalHodgeBasis V H p i.1).1) ∈
        pointCycleClassSpan p (H.cycleClass p)

namespace LocalCyclicRealization

/-- Every live basis direction of the class is algebraic.  One seed with all
coefficients equal to one is enough because all seed coefficients are
nonzero. -/
theorem live_basis_mem_atomic
    {V : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    {p : Nat}
    {alpha : ClassicalHodgeFiber V H p}
    (R : LocalCyclicRealization V H p alpha) :
    ∀ i : HodgeSupportIndex alpha,
      (classicalHodgeBasis V H p i.1).1 ∈
        pointCycleClassSpan p (H.cycleClass p) := by
  have h := R.spectral.selected_basis_algebraic_of_cyclic_seed
    (fun _ : HodgeSupportIndex alpha => (1 : ℚ))
    (by intro i; norm_num)
  have hseed :
      (∑ i : HodgeSupportIndex alpha,
        (1 : ℚ) •
          (classicalHodgeBasis V H p
            (R.spectral.basisIndex i)).1) ∈
        pointCycleClassSpan p (H.cycleClass p) := by
    simp only [one_smul]
    rw [R.spectral_basisIndex]
    exact R.seed_mem_atomic
  intro i
  have hi := h hseed i
  rw [R.spectral_basisIndex] at hi
  exact hi

/-- **LOCAL CYCLIC ALGEBRAICITY.**  A Hodge class admitting a local cyclic
realization is already in the genuine atomic algebraic span. -/
theorem class_mem_atomic
    {V : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    {p : Nat}
    {alpha : ClassicalHodgeFiber V H p}
    (R : LocalCyclicRealization V H p alpha) :
    alpha.1 ∈ pointCycleClassSpan p (H.cycleClass p) := by
  rw [hodgeClass_eq_support_sum alpha]
  apply Submodule.sum_mem
  intro i hi
  exact Submodule.smul_mem _ _ (R.live_basis_mem_atomic i)

end LocalCyclicRealization

/-- **ARBITRARY-MULTIPLICITY LOCAL CYCLIC CRITERION.**

If every individual rational `(p,p)` Hodge class admits a local cyclic
realization of its own finite support, then the full Stage-2G Hodge statement
holds.  No finite-rank, countability, or global enumeration hypothesis is
required. -/
theorem bigradedBettiHodge_of_local_cyclic_realizations
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (hlocal :
      ∀ p : Nat, ∀ alpha : ClassicalHodgeFiber V H p,
        Nonempty (LocalCyclicRealization V H p alpha)) :
    BigradedBettiHodgeStatement V H := by
  apply (bigradedBettiHodgeStatement_iff_atomic_span V H).mpr
  intro p x hx
  let alpha : ClassicalHodgeFiber V H p := ⟨x,hx⟩
  exact (Classical.choice (hlocal p alpha)).class_mem_atomic

/-- Exact equivalence version: the full Hodge target is equivalent to the
existence, for every class, of some finite support certificate whose selected
basis directions are all atomic-algebraic.  The cyclic spectral package is a
strictly stronger constructive way to produce such a certificate. -/
def SupportAlgebraicityCertificate
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (alpha : ClassicalHodgeFiber V H p) : Prop :=
  ∀ i : HodgeSupportIndex alpha,
    (classicalHodgeBasis V H p i.1).1 ∈
      pointCycleClassSpan p (H.cycleClass p)

/-- Local cyclic realization implies the minimal support algebraicity
certificate. -/
theorem supportCertificate_of_localCyclic
    {V : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    {p : Nat}
    {alpha : ClassicalHodgeFiber V H p}
    (R : LocalCyclicRealization V H p alpha) :
    SupportAlgebraicityCertificate V H p alpha :=
  R.live_basis_mem_atomic

/-- A support certificate reconstructs the whole class algebraically. -/
theorem class_mem_atomic_of_supportCertificate
    {V : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    {p : Nat}
    {alpha : ClassicalHodgeFiber V H p}
    (h : SupportAlgebraicityCertificate V H p alpha) :
    alpha.1 ∈ pointCycleClassSpan p (H.cycleClass p) := by
  rw [hodgeClass_eq_support_sum alpha]
  apply Submodule.sum_mem
  intro i hi
  exact Submodule.smul_mem _ _ (h i)

/-- Full target in finite-support local form. -/
theorem bigradedBettiHodgeStatement_iff_supportCertificates
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V) :
    BigradedBettiHodgeStatement V H ↔
      ∀ p : Nat, ∀ alpha : ClassicalHodgeFiber V H p,
        SupportAlgebraicityCertificate V H p alpha := by
  constructor
  · intro h p alpha i
    exact (bigradedBettiHodgeStatement_iff_atomic_span V H).mp h p
      (classicalHodgeBasis V H p i.1).2
  · intro h
    apply (bigradedBettiHodgeStatement_iff_atomic_span V H).mpr
    intro p x hx
    let alpha : ClassicalHodgeFiber V H p := ⟨x,hx⟩
    exact class_mem_atomic_of_supportCertificate (h p alpha)

#check HodgeSupportIndex
#check HodgeSupportIndex.include
#check support_coefficient_ne_zero
#check hodgeClass_eq_support_sum
#check LocalCyclicRealization
#check LocalCyclicRealization.live_basis_mem_atomic
#check LocalCyclicRealization.class_mem_atomic
#check bigradedBettiHodge_of_local_cyclic_realizations
#check SupportAlgebraicityCertificate
#check supportCertificate_of_localCyclic
#check class_mem_atomic_of_supportCertificate
#check bigradedBettiHodgeStatement_iff_supportCertificates

#print axioms LocalCyclicRealization.live_basis_mem_atomic
#print axioms LocalCyclicRealization.class_mem_atomic
#print axioms bigradedBettiHodge_of_local_cyclic_realizations
#print axioms bigradedBettiHodgeStatement_iff_supportCertificates

end GSTClassicalHodgeLocalCyclicCriterion
