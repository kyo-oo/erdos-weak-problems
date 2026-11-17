import GSTClassicalHodgeLocalCyclicCriterion
import GSTClassicalHodgePointNormalForm

/-!
# GST CLASSICAL HODGE — CYCLE-OPERATOR NATURALITY

The cyclic spectral criterion becomes fully constructive when the spectral
observable on cohomology is induced by an actual linear operator on native
codimension-p algebraic cycles.

Assume a commuting square

            cycleOperator
  Cycles --------------------> Cycles
    |                            |
    | cycleClass                 | cycleClass
    v                            v
  Cohomology ----------------> Cohomology
           cohomologyOperator

Then every polynomial in the cycle operator intertwines with the same
polynomial in the cohomology operator.  Starting from one seed cycle whose
class has nonzero component in every selected Hodge eigendirection, the
Lagrange isolator polynomial produces an explicit native cycle representing
each individual direction.

Thus the realization problem is reduced from many independent cycle witnesses
to one cyclic seed cycle plus one natural operator correspondence.
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
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeCyclicSpectralGeneration

namespace GSTClassicalHodgeCycleOperatorNaturality

/-- A native cycle operator together with its cohomological realization and
exact cycle-class naturality square. -/
structure CycleClassOperatorPair
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat) where
  cycleOperator :
    codimensionCycles V.X p →ₗ[ℚ] codimensionCycles V.X p
  cohomologyOperator :
    RationalSingularCohomology H.analytification (2 * p) →ₗ[ℚ]
      RationalSingularCohomology H.analytification (2 * p)
  cycleClass_natural :
    (H.cycleClass p).comp cycleOperator =
      cohomologyOperator.comp (H.cycleClass p)

namespace CycleClassOperatorPair

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

@[simp]
theorem cycleClass_cycleOperator
    (T : CycleClassOperatorPair V H p)
    (Z : codimensionCycles V.X p) :
    H.cycleClass p (T.cycleOperator Z) =
      T.cohomologyOperator (H.cycleClass p Z) := by
  have h := LinearMap.congr_fun T.cycleClass_natural Z
  exact h

/-- The full native cycle-class range is automatically stable under the
cohomology operator. -/
theorem cycleClass_range_stable
    (T : CycleClassOperatorPair V H p) :
    ∀ x,
      x ∈ LinearMap.range (H.cycleClass p) →
        T.cohomologyOperator x ∈ LinearMap.range (H.cycleClass p) := by
  rintro x ⟨Z,rfl⟩
  exact ⟨T.cycleOperator Z, T.cycleClass_cycleOperator Z⟩

/-- On a smooth projective carrier the atomic point-cycle span equals the full
native cycle-class range, so naturality implies atomic-span stability. -/
theorem atomicSpan_stable
    (T : CycleClassOperatorPair V H p) :
    ∀ x,
      x ∈ pointCycleClassSpan p (H.cycleClass p) →
        T.cohomologyOperator x ∈
          pointCycleClassSpan p (H.cycleClass p) := by
  intro x hx
  rw [← smoothProjective_cycleClass_range_eq_atomic_span V H p] at hx ⊢
  exact T.cycleClass_range_stable x hx

end CycleClassOperatorPair

/-- A spectral cycle operator on one finite family of genuine classical Hodge
directions.  No basis vector is assumed algebraic. -/
structure SpectralCycleOperator
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (ι : Type*) [Fintype ι] [DecidableEq ι] where
  operatorPair : CycleClassOperatorPair V H p
  basisIndex : ι → ClassicalHodgeBasisIndex V H p
  basisIndex_injective : Function.Injective basisIndex
  eigenvalue : ι → ℚ
  eigenvalue_injective : Function.Injective eigenvalue
  eigenvector : ∀ i,
    operatorPair.cohomologyOperator
        (classicalHodgeBasis V H p (basisIndex i)).1 =
      eigenvalue i • (classicalHodgeBasis V H p (basisIndex i)).1

namespace SpectralCycleOperator

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The corresponding cohomological spectral package used by the cyclic
criterion. -/
noncomputable def toClassicalHodgeSpectralOperator
    (S : SpectralCycleOperator V H p ι) :
    ClassicalHodgeSpectralOperator V H p ι where
  basisIndex := S.basisIndex
  basisIndex_injective := S.basisIndex_injective
  observable := S.operatorPair.cohomologyOperator
  eigenvalue := S.eigenvalue
  eigenvalue_injective := S.eigenvalue_injective
  eigenvector := S.eigenvector
  atomic_stable := S.operatorPair.atomicSpan_stable

/-- Underlying finite spectral family on cohomology. -/
noncomputable def cohomologyFamily
    (S : SpectralCycleOperator V H p ι) :=
  S.toClassicalHodgeSpectralOperator.toFiniteSpectralFamily

/-- Polynomial functional calculus on the native cycle operator. -/
noncomputable def cyclePolyEval
    (S : SpectralCycleOperator V H p ι)
    (P : Polynomial ℚ) :
    codimensionCycles V.X p →ₗ[ℚ] codimensionCycles V.X p :=
  linearPolyEval S.operatorPair.cycleOperator P

/-- Polynomial naturality: the cycle-class square commutes not only for the
basic observable but for every rational polynomial in it. -/
theorem cycleClass_cyclePolyEval
    (S : SpectralCycleOperator V H p ι)
    (P : Polynomial ℚ)
    (Z : codimensionCycles V.X p) :
    H.cycleClass p (S.cyclePolyEval P Z) =
      linearPolyEval S.operatorPair.cohomologyOperator P
        (H.cycleClass p Z) := by
  exact linearPolyEval_intertwines (H.cycleClass p)
    S.operatorPair.cycleOperator S.operatorPair.cohomologyOperator
    S.operatorPair.cycleClass_cycleOperator P Z

/-- One native cyclic seed cycle with prescribed nonzero components in every
selected Hodge eigendirection.  This is a single cycle witness, not one cycle
per basis vector. -/
structure CyclicSeed
    (S : SpectralCycleOperator V H p ι) where
  cycle : codimensionCycles V.X p
  coefficient : ι → ℚ
  coefficient_ne_zero : ∀ i, coefficient i ≠ 0
  class_eq :
    H.cycleClass p cycle =
      ∑ i : ι,
        coefficient i •
          (classicalHodgeBasis V H p (S.basisIndex i)).1

/-- Explicit native cycle extracted for one selected Hodge sheet by applying
its Lagrange isolator to the seed cycle and normalizing. -/
noncomputable def extractedBasisCycle
    (S : SpectralCycleOperator V H p ι)
    (seed : CyclicSeed S)
    (i : ι) : codimensionCycles V.X p :=
  let F := S.cohomologyFamily
  let c := seed.coefficient i * F.isolatorScale i
  c⁻¹ • S.cyclePolyEval (F.isolatorPolynomial i) seed.cycle

/-- **EXPLICIT SHEET EXTRACTION.**  The extracted native cycle has cycle
class exactly the chosen genuine Hodge basis direction. -/
theorem extractedBasisCycle_spec
    (S : SpectralCycleOperator V H p ι)
    (seed : CyclicSeed S)
    (i : ι) :
    H.cycleClass p (S.extractedBasisCycle seed i) =
      (classicalHodgeBasis V H p (S.basisIndex i)).1 := by
  let F := S.cohomologyFamily
  have hc :
      H.cycleClass p
        (S.cyclePolyEval (F.isolatorPolynomial i) seed.cycle) =
      (seed.coefficient i * F.isolatorScale i) •
        (classicalHodgeBasis V H p (S.basisIndex i)).1 := by
    rw [S.cycleClass_cyclePolyEval]
    rw [seed.class_eq]
    change linearPolyEval F.observable (F.isolatorPolynomial i)
      (F.spectralCombination seed.coefficient) = _
    exact F.isolator_on_combination seed.coefficient i
  unfold extractedBasisCycle
  rw [LinearMap.map_smul, hc]
  have hnonzero : seed.coefficient i * F.isolatorScale i ≠ 0 :=
    mul_ne_zero (seed.coefficient_ne_zero i) (F.isolatorScale_ne_zero i)
  exact inv_smul_smul₀ hnonzero _

/-- The selected finite Hodge family therefore has an actual native
basis-cycle bridge, constructed from one seed cycle. -/
noncomputable def extractedBasisCycleBridge
    (S : SpectralCycleOperator V H p ι)
    (seed : CyclicSeed S) :
    ∀ i : ι,
      {Z : codimensionCycles V.X p //
        H.cycleClass p Z =
          (classicalHodgeBasis V H p (S.basisIndex i)).1} :=
  fun i => ⟨S.extractedBasisCycle seed i,
    S.extractedBasisCycle_spec seed i⟩

/-- Algebraicity of every selected direction, now with explicit native cycle
witnesses rather than mere span membership. -/
theorem selected_basis_has_native_cycles
    (S : SpectralCycleOperator V H p ι)
    (seed : CyclicSeed S) :
    ∀ i : ι,
      ∃ Z : codimensionCycles V.X p,
        H.cycleClass p Z =
          (classicalHodgeBasis V H p (S.basisIndex i)).1 := by
  intro i
  exact ⟨S.extractedBasisCycle seed i,
    S.extractedBasisCycle_spec seed i⟩

end SpectralCycleOperator

/-- **CYCLE-OPERATOR CROWN.**
A finite genuine Hodge family is algebraic once one supplies:
(1) a natural spectral operator pair on cycles/cohomology and
(2) one cyclic native seed cycle with nonzero component in every direction.
All individual basis cycles are then constructed by Lagrange polynomial
functional calculus on the cycle operator. -/
theorem finite_hodge_family_from_one_seed
    {V : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    {p : Nat}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : SpectralCycleOperator V H p ι)
    (seed : S.CyclicSeed) :
    ∀ i : ι,
      ∃ Z : codimensionCycles V.X p,
        H.cycleClass p Z =
          (classicalHodgeBasis V H p (S.basisIndex i)).1 :=
  S.selected_basis_has_native_cycles seed

#check CycleClassOperatorPair
#check CycleClassOperatorPair.cycleClass_range_stable
#check CycleClassOperatorPair.atomicSpan_stable
#check SpectralCycleOperator
#check SpectralCycleOperator.toClassicalHodgeSpectralOperator
#check SpectralCycleOperator.CyclicSeed
#check SpectralCycleOperator.extractedBasisCycle
#check SpectralCycleOperator.extractedBasisCycle_spec
#check SpectralCycleOperator.selected_basis_has_native_cycles
#check finite_hodge_family_from_one_seed

#print axioms CycleClassOperatorPair.atomicSpan_stable
#print axioms SpectralCycleOperator.cycleClass_cyclePolyEval
#print axioms SpectralCycleOperator.extractedBasisCycle_spec
#print axioms SpectralCycleOperator.selected_basis_has_native_cycles
#print axioms finite_hodge_family_from_one_seed

end GSTClassicalHodgeCycleOperatorNaturality
