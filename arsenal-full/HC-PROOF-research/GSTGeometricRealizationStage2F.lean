import Mathlib
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.CategoryTheory.Abelian.Ext
import GSTGeometricRealizationStage2E

/-!
# STAGE 2F — ANALYTIFICATION AND NATIVE RATIONAL BETTI COHOMOLOGY

Stage 2E made the classical Hodge target explicit but still allowed the
rational cohomology carrier to be supplied as semantic data.

Stage 2F removes that freedom.

For an actual smooth projective complex scheme V:

* ComplexPoint V is the actual type of C-valued scheme points over Spec(C);
* AnalytificationData supplies only the missing analytic topology, packaged
  as a TopCat whose underlying points are equivalent to ComplexPoint V;
* rationalSingularChains is Mathlib's actual singular chain complex;
* rationalSingularCochains is the Q-linear dual cochain complex built with
  ChainComplex.linearYonedaObj;
* rationalSingularCohomology is the actual homology object of that cochain
  complex.

Thus the Betti cohomology carrier is no longer arbitrary data.

The remaining classical inputs are deliberately visible:
1. the genuine analytification topology;
2. the genuine rational (p,p) Hodge subspace inside H^(2p);
3. the genuine algebraic cycle-class map into H^(2p).

No surjectivity/algebraicity assumption is included in those inputs.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000000

noncomputable section

open CategoryTheory
open AlgebraicGeometry
open AlgebraicTopology
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2E

namespace GSTGeometricRealizationStage2F

/-- Actual C-valued points of a complex scheme, with the point required to
lie over the identity point of Spec(C). -/
abbrev ComplexPoint (V : SmoothProjectiveComplexScheme) :=
  { f : complexBase ⟶ V.X //
      f ≫ V.structureMap = 𝟙 complexBase }

/-- The only genuinely new analytic datum Stage 2F must receive:
a topological analytification whose underlying point set is identified with
the actual C-valued scheme points.

No cohomology group is supplied here. -/
structure AnalytificationData
    (V : SmoothProjectiveComplexScheme) where
  space : TopCat
  pointsEquiv : ComplexPoint V ≃ space

/-- Rational coefficient object in the category of Q-modules. -/
abbrev rationalCoefficient : ModuleCat ℚ :=
  ModuleCat.of ℚ ℚ

/-- Mathlib's genuine rational singular chain complex of the supplied
analytification. -/
noncomputable def rationalSingularChains
    {V : SmoothProjectiveComplexScheme}
    (A : AnalytificationData V) :
    ChainComplex (ModuleCat ℚ) ℕ :=
  ((singularChainComplexFunctor (ModuleCat ℚ)).obj rationalCoefficient).obj A.space

/-- Genuine rational singular cochains: the Q-linear dual of the singular
chain complex. -/
noncomputable def rationalSingularCochains
    {V : SmoothProjectiveComplexScheme}
    (A : AnalytificationData V) :
    CochainComplex (ModuleCat ℚ) ℕ :=
  (rationalSingularChains A).linearYonedaObj
    ℚ rationalCoefficient

/-- The n-th rational singular cohomology object of the analytification.
This is computed as homology of the singular cochain complex, not supplied
as an arbitrary vector space. -/
noncomputable def rationalSingularCohomologyObj
    {V : SmoothProjectiveComplexScheme}
    (A : AnalytificationData V) (n : Nat) :
    ModuleCat ℚ :=
  (rationalSingularCochains A).homology n

/-- The underlying rational vector space of native singular cohomology. -/
abbrev RationalSingularCohomology
    {V : SmoothProjectiveComplexScheme}
    (A : AnalytificationData V) (n : Nat) : Type :=
  rationalSingularCohomologyObj A n

instance
    {V : SmoothProjectiveComplexScheme}
    (A : AnalytificationData V) (n : Nat) :
    AddCommGroup (RationalSingularCohomology A n) :=
  inferInstance

instance
    {V : SmoothProjectiveComplexScheme}
    (A : AnalytificationData V) (n : Nat) :
    Module ℚ (RationalSingularCohomology A n) :=
  inferInstance

/-- Package native rational singular cohomology in the Stage-2E vector-space
wrapper. -/
noncomputable def bettiVectorSpace
    {V : SmoothProjectiveComplexScheme}
    (A : AnalytificationData V) (n : Nat) :
    RationalVectorSpace where
  carrier := RationalSingularCohomology A n
  addCommGroup := inferInstance
  moduleQ := inferInstance

/-- Hodge semantic data after the Betti carrier has been made native.

Unlike Stage 2E, there is no field selecting the cohomology vector spaces:
degree 2p cohomology is definitionally the rational singular cohomology of
the supplied analytification.

The two remaining fields are exactly the still-missing classical geometry:
the rational (p,p) subspace and the genuine cycle-class map. -/
structure BettiHodgeData
    (V : SmoothProjectiveComplexScheme) where
  analytification : AnalytificationData V
  hodgePP :
    ∀ p : Nat,
      Submodule ℚ
        (RationalSingularCohomology analytification (2 * p))
  cycleClass :
    ∀ p : Nat,
      codimensionCycles V.X p →ₗ[ℚ]
        RationalSingularCohomology analytification (2 * p)

/-- Stage 2F embeds canonically into the Stage-2E semantic interface by
choosing the already-constructed Betti cohomology spaces. -/
noncomputable def BettiHodgeData.toClassicalHodgeData
    {V : SmoothProjectiveComplexScheme}
    (H : BettiHodgeData V) :
    ClassicalHodgeData V where
  cohomology := fun p =>
    bettiVectorSpace H.analytification (2 * p)
  hodgePP := H.hodgePP
  cycleClass := H.cycleClass

/-- Exact Hodge target with genuine rational singular cohomology as carrier. -/
def BettiHodgeStatement
    (V : SmoothProjectiveComplexScheme)
    (H : BettiHodgeData V) : Prop :=
  ∀ p : Nat,
    H.hodgePP p ≤ LinearMap.range (H.cycleClass p)

/-- Stage-2F's direct target agrees with the Stage-2E target after canonical
Betti specialization. -/
theorem bettiHodgeStatement_iff_stage2e
    (V : SmoothProjectiveComplexScheme)
    (H : BettiHodgeData V) :
    BettiHodgeStatement V H ↔
      ClassicalHodgeStatement V H.toClassicalHodgeData :=
  Iff.rfl

/-- A Stage-2F realization certificate is exactly a Stage-2E certificate
after the cohomology carrier has been fixed to native singular cohomology. -/
abbrev Stage2FClassRealization
    (V : SmoothProjectiveComplexScheme)
    (H : BettiHodgeData V)
    (p N : Nat) :=
  Stage2EClassRealization
    V H.toClassicalHodgeData p N

/-- A Stage-2F realization gives an actual codimension-p algebraic cycle
representing every rational (p,p) class in native singular cohomology. -/
theorem hodge_class_has_betti_cycle
    (V : SmoothProjectiveComplexScheme)
    (H : BettiHodgeData V)
    {p N : Nat}
    (R : Stage2FClassRealization V H p N)
    (alpha :
      RationalSingularCohomology H.analytification (2 * p))
    (halpha : alpha ∈ H.hodgePP p) :
    ∃ Z : codimensionCycles V.X p,
      H.cycleClass p Z = alpha := by
  exact hodge_class_has_classical_cycle
    V H.toClassicalHodgeData R alpha halpha

/-- Explicit algebraic-cycle selector for one native Betti-Hodge
realization certificate. -/
noncomputable def bettiCycleSelector
    (V : SmoothProjectiveComplexScheme)
    (H : BettiHodgeData V)
    {p N : Nat}
    (R : Stage2FClassRealization V H p N)
    (alpha : H.hodgePP p) :
    codimensionCycles V.X p :=
  classicalCycleSelector V H.toClassicalHodgeData R alpha

/-- The Betti selector is a verified right inverse of the native Betti
cycle-class map on the intended Hodge sector. -/
theorem bettiCycleSelector_spec
    (V : SmoothProjectiveComplexScheme)
    (H : BettiHodgeData V)
    {p N : Nat}
    (R : Stage2FClassRealization V H p N)
    (alpha : H.hodgePP p) :
    H.cycleClass p (bettiCycleSelector V H R alpha) = alpha.1 := by
  exact classicalCycleSelector_spec V H.toClassicalHodgeData R alpha

/-- **STAGE-2F BETTI LANDING THEOREM.**

Once every degree admits an explicit finite realization certificate, the
Hodge target follows with Mathlib-constructed rational singular cohomology
as the cohomology carrier. -/
theorem betti_hodge_of_stage2f_family
    (V : SmoothProjectiveComplexScheme)
    (H : BettiHodgeData V)
    (N : Nat -> Nat)
    (R : ∀ p : Nat, Stage2FClassRealization V H p (N p)) :
    BettiHodgeStatement V H := by
  intro p alpha halpha
  exact hodge_class_has_betti_cycle
    V H (R p) alpha halpha

/-- The precise Stage-2F realization obligation. -/
def Stage2FRealizationObligation
    (V : SmoothProjectiveComplexScheme)
    (H : BettiHodgeData V) : Prop :=
  ∃ N : Nat -> Nat,
    ∀ p : Nat,
      Nonempty (Stage2FClassRealization V H p (N p))

/-- Stage 2F changes the cohomology carrier to native singular cohomology but
does not change the realization obligation itself: the Betti obligation is
definitionally the Stage-2E obligation for the induced classical package. -/
theorem stage2F_obligation_iff_stage2E
    (V : SmoothProjectiveComplexScheme)
    (H : BettiHodgeData V) :
    Stage2FRealizationObligation V H ↔
      Stage2ERealizationObligation V H.toClassicalHodgeData :=
  Iff.rfl

theorem betti_hodge_of_stage2f_obligation
    (V : SmoothProjectiveComplexScheme)
    (H : BettiHodgeData V)
    (hR : Stage2FRealizationObligation V H) :
    BettiHodgeStatement V H := by
  rcases hR with ⟨N, hN⟩
  exact betti_hodge_of_stage2f_family
    V H N (fun p => (hN p).some)

/-! ## Rank-free compact Stage-2F route -/

abbrev Stage2FCompactRealization
    (V : SmoothProjectiveComplexScheme)
    (H : BettiHodgeData V)
    (p : Nat) :=
  Stage2ECompactRealization V H.toClassicalHodgeData p

/-- Native Betti cohomology now inherits the same countable finite-support
realization route, with no global coordinate rank. -/
theorem hodge_class_has_betti_cycle_compact
    (V : SmoothProjectiveComplexScheme)
    (H : BettiHodgeData V)
    {p : Nat}
    (R : Stage2FCompactRealization V H p)
    (alpha : RationalSingularCohomology H.analytification (2 * p))
    (halpha : alpha ∈ H.hodgePP p) :
    ∃ Z : codimensionCycles V.X p,
      H.cycleClass p Z = alpha := by
  exact hodge_class_has_classical_cycle_compact
    V H.toClassicalHodgeData R alpha halpha

/-- **RANK-FREE STAGE-2F BETTI LANDING.** -/
theorem betti_hodge_of_stage2f_compact_family
    (V : SmoothProjectiveComplexScheme)
    (H : BettiHodgeData V)
    (R : ∀ p : Nat, Stage2FCompactRealization V H p) :
    BettiHodgeStatement V H := by
  intro p alpha halpha
  exact hodge_class_has_betti_cycle_compact
    V H (R p) alpha halpha

def Stage2FCompactRealizationObligation
    (V : SmoothProjectiveComplexScheme)
    (H : BettiHodgeData V) : Prop :=
  ∀ p : Nat, Nonempty (Stage2FCompactRealization V H p)

theorem stage2F_compact_obligation_iff_stage2E_compact
    (V : SmoothProjectiveComplexScheme)
    (H : BettiHodgeData V) :
    Stage2FCompactRealizationObligation V H ↔
      Stage2ECompactRealizationObligation V H.toClassicalHodgeData :=
  Iff.rfl

theorem betti_hodge_of_stage2f_compact_obligation
    (V : SmoothProjectiveComplexScheme)
    (H : BettiHodgeData V)
    (hR : Stage2FCompactRealizationObligation V H) :
    BettiHodgeStatement V H := by
  exact betti_hodge_of_stage2f_compact_family
    V H (fun p => (hR p).some)

#check ComplexPoint
#check AnalytificationData
#check rationalCoefficient
#check rationalSingularChains
#check rationalSingularCochains
#check rationalSingularCohomologyObj
#check RationalSingularCohomology
#check bettiVectorSpace
#check BettiHodgeData
#check BettiHodgeData.toClassicalHodgeData
#check BettiHodgeStatement
#check bettiHodgeStatement_iff_stage2e
#check Stage2FClassRealization
#check hodge_class_has_betti_cycle
#check bettiCycleSelector
#check bettiCycleSelector_spec
#check betti_hodge_of_stage2f_family
#check Stage2FRealizationObligation
#check stage2F_obligation_iff_stage2E
#check betti_hodge_of_stage2f_obligation

#print axioms bettiHodgeStatement_iff_stage2e
#print axioms hodge_class_has_betti_cycle
#print axioms bettiCycleSelector_spec
#print axioms stage2F_obligation_iff_stage2E
#print axioms betti_hodge_of_stage2f_family
#print axioms betti_hodge_of_stage2f_obligation

end GSTGeometricRealizationStage2F
