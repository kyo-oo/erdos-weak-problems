import GSTClassicalHodgeCyclicSpectralGeneration
import GSTClassicalHodgeRealizedClosedCorrespondenceAlgebra
import GSTClassicalHodgeExactClayStatement

/-!
# GST CLASSICAL HODGE — REALIZED-CORRESPONDENCE CYCLIC SPECTRAL FINALE

This file removes one synthetic layer from the cyclic spectral attack.

The observable is no longer an arbitrary linear endomorphism equipped with an
`atomic_stable` field.  It is the cohomological action of one ACTUAL realized
closed-correspondence word.  Stability of the algebraic cycle-class range is
therefore derived from the correspondence commuting square.

At one weight p the remaining certificate is now finite and explicit:

* one genuine realized closed-correspondence word;
* a simple rational spectrum on the full genuine Hodge basis;
* one actual native codimension-p cycle whose class is a linear combination of
  all those eigendirections with every coefficient nonzero.

Polynomial functional calculus in the realized correspondence then extracts
every Hodge basis direction as an algebraic cycle class.  No matrix-unit family,
no per-basis cycle witness, no arbitrary stable observable, and no Hodge
surjectivity premise occurs in this package.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open scoped BigOperators
open AlgebraicGeometry

namespace GSTClassicalHodgeRealizedCorrespondenceCyclicSpectralFinale

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeCyclicSpectralGeneration
open GSTClassicalHodgeRealizedClosedCorrespondenceAlgebra
open GSTClassicalHodgeExactClayStatement

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- One actual closed-correspondence observable with simple spectrum on the
entire genuine Hodge basis, together with one genuine algebraic cyclic seed.

`seedClass_spec` is a direct equality for an already-existing native cycle; it
does not supply basis cycles or any target Hodge representative individually. -/
structure RealizedCyclicSpectralCertificate
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat) where
  [basisIndex_fintype : Fintype (ClassicalHodgeBasisIndex V H p)]
  [basisIndex_decidableEq : DecidableEq (ClassicalHodgeBasisIndex V H p)]
  word : RealizedCorrespondenceWord V H p
  eigenvalue : ClassicalHodgeBasisIndex V H p → ℚ
  eigenvalue_injective : Function.Injective eigenvalue
  eigenvector : ∀ i : ClassicalHodgeBasisIndex V H p,
    (realizedWordPair word).cohomologyOperator
        (classicalHodgeBasis V H p i).1 =
      eigenvalue i • (classicalHodgeBasis V H p i).1
  coefficient : ClassicalHodgeBasisIndex V H p → ℚ
  coefficient_ne_zero : ∀ i, coefficient i ≠ 0
  seedCycle : codimensionCycles V.X p
  seedClass_spec :
    H.cycleClass p seedCycle =
      ∑ i : ClassicalHodgeBasisIndex V H p,
        coefficient i • (classicalHodgeBasis V H p i).1

namespace RealizedCyclicSpectralCertificate

/-- The cohomological action of the actual correspondence is a geometric
spectral operator.  Atomic-span stability is DERIVED from genuine
cycle-class naturality of the realized word.  The certificate's own
basis-index instances are passed explicitly so every declaration below
elaborates against exactly the data the certificate carries. -/
noncomputable def spectralOperator
    (C : RealizedCyclicSpectralCertificate V H p) :
    @ClassicalHodgeSpectralOperator V H p
      (ClassicalHodgeBasisIndex V H p)
      C.basisIndex_fintype C.basisIndex_decidableEq :=
  @ClassicalHodgeSpectralOperator.mk V H p
    (ClassicalHodgeBasisIndex V H p)
    C.basisIndex_fintype C.basisIndex_decidableEq
    (fun i => i)
    (fun _ _ h => h)
    ((realizedWordPair C.word).cohomologyOperator)
    C.eigenvalue
    C.eigenvalue_injective
    C.eigenvector
    (by
      intro x hx
      rw [← smoothProjective_cycleClass_range_eq_atomic_span V H p] at hx ⊢
      exact realizedWord_range_stable C.word x hx)

/-- The supplied native cyclic seed really lies in the algebraic atomic span. -/
theorem cyclic_seed_mem_atomic
    (C : RealizedCyclicSpectralCertificate V H p) :
    Finset.sum
      (@Finset.univ (ClassicalHodgeBasisIndex V H p) C.basisIndex_fintype)
      (fun i => C.coefficient i • (classicalHodgeBasis V H p i).1) ∈
        pointCycleClassSpan p (H.cycleClass p) := by
  rw [← C.seedClass_spec]
  rw [← smoothProjective_cycleClass_range_eq_atomic_span V H p]
  exact ⟨C.seedCycle, rfl⟩

/-- **ONE ACTUAL CORRESPONDENCE + ONE ACTUAL CYCLIC CYCLE SATURATES THE WEIGHT.** -/
theorem weight_hodge
    (C : RealizedCyclicSpectralCertificate V H p) :
    rationalHodgeSubspace (H.hodgeBigrading p) ≤
      pointCycleClassSpan p (H.cycleClass p) := by
  exact @GSTClassicalHodgeCyclicSpectralGeneration.ClassicalHodgeSpectralOperator.weight_hodge_of_cyclic_spectral_generation
    V H p (ClassicalHodgeBasisIndex V H p) C.basisIndex_fintype
    C.basisIndex_decidableEq C.spectralOperator
    (fun j => ⟨j, rfl⟩)
    C.coefficient
    C.coefficient_ne_zero
    C.cyclic_seed_mem_atomic

/-- Every genuine Hodge class in this weight therefore has an actual native
codimension-p algebraic cycle representative. -/
theorem exists_cycle
    (C : RealizedCyclicSpectralCertificate V H p)
    (alpha : RationalSingularCohomology H.analytification (2 * p))
    (halpha : alpha ∈ rationalHodgeSubspace (H.hodgeBigrading p)) :
    ∃ Z : codimensionCycles V.X p,
      H.cycleClass p Z = alpha := by
  have hatomic := C.weight_hodge halpha
  rw [← smoothProjective_cycleClass_range_eq_atomic_span V H p] at hatomic
  exact hatomic

end RealizedCyclicSpectralCertificate

/-- **GLOBAL ACTUAL-CORRESPONDENCE CYCLIC-SPECTRAL FINALE.**
A certificate in every weight proves the literal rational Hodge statement. -/
theorem exactHodge_of_realizedCyclicSpectralCertificates
    (hcert : ∀ q : Nat,
      Nonempty (RealizedCyclicSpectralCertificate V H q)) :
    EveryHodgeClassIsRationalAlgebraic H := by
  intro q alpha halpha
  exact (Classical.choice (hcert q)).exists_cycle alpha halpha

/-- Literal finite rational-combination wording of the same theorem. -/
theorem finiteCombination_of_realizedCyclicSpectralCertificates
    (hcert : ∀ q : Nat,
      Nonempty (RealizedCyclicSpectralCertificate V H q)) :
    EveryHodgeClassIsFiniteRationalCombination H := by
  rw [← rationalAlgebraic_iff_finiteRationalCombination]
  exact exactHodge_of_realizedCyclicSpectralCertificates hcert

#check RealizedCyclicSpectralCertificate
#check RealizedCyclicSpectralCertificate.spectralOperator
#check RealizedCyclicSpectralCertificate.cyclic_seed_mem_atomic
#check RealizedCyclicSpectralCertificate.weight_hodge
#check RealizedCyclicSpectralCertificate.exists_cycle
#check exactHodge_of_realizedCyclicSpectralCertificates
#check finiteCombination_of_realizedCyclicSpectralCertificates

#print axioms RealizedCyclicSpectralCertificate.weight_hodge
#print axioms RealizedCyclicSpectralCertificate.exists_cycle
#print axioms exactHodge_of_realizedCyclicSpectralCertificates
#print axioms finiteCombination_of_realizedCyclicSpectralCertificates

end GSTClassicalHodgeRealizedCorrespondenceCyclicSpectralFinale
