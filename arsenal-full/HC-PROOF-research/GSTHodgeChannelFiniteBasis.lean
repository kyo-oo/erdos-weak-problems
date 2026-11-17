import Mathlib
import GSTMathlibFiniteBasis
import GSTHodgeChannelQuotient

/-!
# GST HODGE CHANNEL FINITE BASIS ALGEBRAIZATION

This layer removes the channel quotient itself from the geometric obligation.
A finite basis of the rational Hodge sector canonically supplies all channel
geometry:

* N basis vectors -> the standard Wave-II N-shape;
* Basis.repr -> channel coordinates;
* finite basis superposition -> the channel decoder;
* basis reconstruction -> decoder surjectivity.

Therefore the only algebraic input that remains is one codimension-p cycle
whose cycle class equals each basis vector.

The second half chooses Mathlib's canonical `FiniteDimensional.finBasis` when
a finite-dimensional instance is available.  In that form even the choice of
basis disappears: the sole remaining datum is a cycle for each canonical
finite-dimensional basis vector.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000000

noncomputable section

open GSTMathlibFiniteBasis
open GSTNCohomology
open GSTMultiChannelHodgeCosmology
open GSTHodgeChannelQuotient
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G

namespace GSTHodgeChannelFiniteBasis

/-- Algebraicity data on a finite basis of one rational Hodge sector. -/
structure FiniteBasisAlgebraization
    (N p : Nat)
    (Coh CycleQ : Type*)
    [AddCommGroup Coh] [Module ℚ Coh]
    [AddCommGroup CycleQ] [Module ℚ CycleQ]
    (hodge : Submodule ℚ Coh)
    (cycleClass : CycleQ →ₗ[ℚ] Coh) where
  basis : Module.Basis (Fin N) ℚ hodge
  basisCycle : Fin N → CycleQ
  basisCycle_class :
    ∀ i : Fin N,
      cycleClass (basisCycle i) = (basis i).1

variable {N p : Nat}
variable {Coh CycleQ : Type*}
variable [AddCommGroup Coh] [Module ℚ Coh]
variable [AddCommGroup CycleQ] [Module ℚ CycleQ]
variable {hodge : Submodule ℚ Coh}
variable {cycleClass : CycleQ →ₗ[ℚ] Coh}

/-- A finite Hodge basis canonically becomes a Wave-II channel quotient.
No extra encode/decode/retract data is supplied. -/
noncomputable def FiniteBasisAlgebraization.toChannelQuotient
    (A : FiniteBasisAlgebraization N p Coh CycleQ hodge cycleClass) :
    ChannelHodgeQuotient p Coh CycleQ hodge cycleClass where
  shape := standardChannelShape N
  decode := basisDecode A.basis
  decode_surjective := basisDecode_surjective A.basis
  channelCycle := A.basisCycle
  channelCycle_decodes := by
    intro i
    rw [A.basisCycle_class i]
    congr 1
    exact (basisDecode_kronecker A.basis i).symm

/-- Basis algebraicity already implies the complete Hodge sector lies in the
cycle-class range. -/
theorem finite_basis_hodge_le_cycleClass_range
    (A : FiniteBasisAlgebraization N p Coh CycleQ hodge cycleClass) :
    hodge ≤ LinearMap.range cycleClass := by
  exact quotient_hodge_le_cycleClass_range A.toChannelQuotient

/-- Constructive cycle attached to one Hodge class through its finite-basis
coordinates and the supplied basis cycles. -/
noncomputable def finiteBasisCycleWitness
    (A : FiniteBasisAlgebraization N p Coh CycleQ hodge cycleClass)
    (alpha : hodge) : CycleQ :=
  quotientCycleWitness A.toChannelQuotient alpha

/-- The finite-basis cycle witness realizes alpha exactly. -/
theorem finiteBasisCycleWitness_spec
    (A : FiniteBasisAlgebraization N p Coh CycleQ hodge cycleClass)
    (alpha : hodge) :
    cycleClass (finiteBasisCycleWitness A alpha) = alpha.1 :=
  quotientCycleWitness_spec A.toChannelQuotient alpha

/-- Stage-2G basis algebraization package.  The basis rank is allowed to vary
with X and p. -/
structure Stage2GFiniteBasisAlgebraization
    (V : GSTProjectiveOverC.SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat) where
  N : Nat
  basis :
    Module.Basis (Fin N) ℚ (rationalHodgeSubspace (H.hodgeBigrading p))
  basisCycle : Fin N → codimensionCycles V.X p
  basisCycle_class :
    ∀ i : Fin N,
      H.cycleClass p (basisCycle i) = (basis i).1

/-- Forget the Stage-2G packaging and obtain the generic finite-basis datum. -/
noncomputable def Stage2GFiniteBasisAlgebraization.toGeneric
    {V : GSTProjectiveOverC.SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    {p : Nat}
    (A : Stage2GFiniteBasisAlgebraization V H p) :
    FiniteBasisAlgebraization
      A.N p
      (RationalSingularCohomology H.analytification (2 * p))
      (codimensionCycles V.X p)
      (rationalHodgeSubspace (H.hodgeBigrading p))
      (H.cycleClass p) where
  basis := A.basis
  basisCycle := A.basisCycle
  basisCycle_class := A.basisCycle_class

/-- Every finite basis algebraization canonically generates the minimal
Stage-2G channel quotient. -/
noncomputable def Stage2GFiniteBasisAlgebraization.toChannelQuotient
    {V : GSTProjectiveOverC.SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    {p : Nat}
    (A : Stage2GFiniteBasisAlgebraization V H p) :
    Stage2GChannelQuotient V H p :=
  A.toGeneric.toChannelQuotient

/-- One finite basis algebraization realizes every rational (p,p) class. -/
theorem hodge_class_has_finite_basis_cycle
    (V : GSTProjectiveOverC.SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    {p : Nat}
    (A : Stage2GFiniteBasisAlgebraization V H p)
    (alpha : RationalSingularCohomology H.analytification (2 * p))
    (halpha : alpha ∈ rationalHodgeSubspace (H.hodgeBigrading p)) :
    ∃ Z : codimensionCycles V.X p,
      H.cycleClass p Z = alpha := by
  exact hodge_class_has_stage2g_quotient_cycle
    V H A.toChannelQuotient alpha halpha

/-- **FINITE-BASIS STAGE-2G LANDING.** -/
theorem bigraded_betti_hodge_of_finite_basis_family
    (V : GSTProjectiveOverC.SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (A : ∀ p : Nat, Stage2GFiniteBasisAlgebraization V H p) :
    BigradedBettiHodgeStatement V H := by
  apply bigraded_betti_hodge_of_channel_quotient_family V H
  intro p
  exact (A p).toChannelQuotient

/-- The geometric obligation after all Wave-II coordinate architecture has
been derived: every p has a finite Hodge basis and each basis vector is the
class of one native codimension-p cycle. -/
def Stage2GFiniteBasisAlgebraizationObligation
    (V : GSTProjectiveOverC.SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V) : Prop :=
  ∀ p : Nat, Nonempty (Stage2GFiniteBasisAlgebraization V H p)

/-- The finite-basis obligation closes the full Stage-2G Hodge target. -/
theorem bigraded_betti_hodge_of_finite_basis_obligation
    (V : GSTProjectiveOverC.SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (hA : Stage2GFiniteBasisAlgebraizationObligation V H) :
    BigradedBettiHodgeStatement V H := by
  exact bigraded_betti_hodge_of_finite_basis_family
    V H (fun p => (hA p).some)

/-! ## Canonical finite-dimensional basis form -/

/-- Once the rational Hodge sector is known finite-dimensional, Mathlib's
canonical finBasis removes the choice of basis.  This structure asks only for
algebraic cycles realizing those canonical basis vectors. -/
structure CanonicalBasisCycleSupply
    (V : GSTProjectiveOverC.SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    [FiniteDimensional ℚ (rationalHodgeSubspace (H.hodgeBigrading p))] where
  basisCycle :
    Fin (Module.finrank ℚ
      (rationalHodgeSubspace (H.hodgeBigrading p))) →
      codimensionCycles V.X p
  basisCycle_class :
    ∀ i,
      H.cycleClass p (basisCycle i) =
        ((Module.finBasis ℚ
          (rationalHodgeSubspace (H.hodgeBigrading p))) i).1

/-- Canonical basis-cycle supply becomes a full finite-basis algebraization. -/
noncomputable def CanonicalBasisCycleSupply.toFiniteBasisAlgebraization
    {V : GSTProjectiveOverC.SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    {p : Nat}
    [FiniteDimensional ℚ (rationalHodgeSubspace (H.hodgeBigrading p))]
    (A : CanonicalBasisCycleSupply V H p) :
    Stage2GFiniteBasisAlgebraization V H p where
  N := Module.finrank ℚ
    (rationalHodgeSubspace (H.hodgeBigrading p))
  basis := Module.finBasis ℚ
    (rationalHodgeSubspace (H.hodgeBigrading p))
  basisCycle := A.basisCycle
  basisCycle_class := A.basisCycle_class

/-- At a finite-dimensional Hodge fiber, algebraicity of the canonical
Mathlib basis alone gives every Hodge class. -/
theorem hodge_class_has_canonical_basis_cycle
    (V : GSTProjectiveOverC.SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    {p : Nat}
    [FiniteDimensional ℚ (rationalHodgeSubspace (H.hodgeBigrading p))]
    (A : CanonicalBasisCycleSupply V H p)
    (alpha : RationalSingularCohomology H.analytification (2 * p))
    (halpha : alpha ∈ rationalHodgeSubspace (H.hodgeBigrading p)) :
    ∃ Z : codimensionCycles V.X p,
      H.cycleClass p Z = alpha := by
  exact hodge_class_has_finite_basis_cycle
    V H A.toFiniteBasisAlgebraization alpha halpha

/-- Finite-basis algebraization crown. -/
theorem finite_basis_algebraization_crown
    (V : GSTProjectiveOverC.SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V) :
    Stage2GFiniteBasisAlgebraizationObligation V H →
      BigradedBettiHodgeStatement V H :=
  bigraded_betti_hodge_of_finite_basis_obligation V H

#check FiniteBasisAlgebraization
#check FiniteBasisAlgebraization.toChannelQuotient
#check finiteBasisCycleWitness
#check finiteBasisCycleWitness_spec
#check Stage2GFiniteBasisAlgebraization
#check Stage2GFiniteBasisAlgebraization.toChannelQuotient
#check hodge_class_has_finite_basis_cycle
#check bigraded_betti_hodge_of_finite_basis_family
#check Stage2GFiniteBasisAlgebraizationObligation
#check CanonicalBasisCycleSupply
#check CanonicalBasisCycleSupply.toFiniteBasisAlgebraization
#check hodge_class_has_canonical_basis_cycle
#check finite_basis_algebraization_crown

#print axioms finiteBasisCycleWitness_spec
#print axioms bigraded_betti_hodge_of_finite_basis_family
#print axioms hodge_class_has_canonical_basis_cycle
#print axioms finite_basis_algebraization_crown

end GSTHodgeChannelFiniteBasis
