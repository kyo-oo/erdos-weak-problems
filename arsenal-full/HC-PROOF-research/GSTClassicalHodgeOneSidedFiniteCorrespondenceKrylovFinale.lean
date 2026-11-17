import GSTClassicalHodgeFiniteClosedCorrespondenceOperator
import GSTClassicalHodgeRankFreeArsenalIrreducibility
import GSTClassicalHodgeExactClayStatement
import GSTClassicalHodgeAtomicSpan

/-!
# GST CLASSICAL HODGE — ONE-SIDED FINITE-CORRESPONDENCE KRYLOV FINALE

This removes an unnecessary geometric restriction from the cyclic attack.
The correspondence carrier is required to be finite only over the SOURCE
projection, exactly as in `FiniteClosedCorrespondence`.  No finiteness of the
right projection, transpose, or correspondence-word algebra is needed.

At a fixed weight p, one genuine closed correspondence K, one genuine
cohomological realization T of K on point cycles, one genuine algebraic Hodge
seed Z, and cyclicity of the T-orbit of cl(Z) are enough.

The native orbit is obtained by iterating K.nativeOperator.  The exact
cycle-class identity along every iterate follows by induction from the already
proved pointwise-correspondence-to-full-naturality theorem.  Thus every Krylov
orbit vector has an explicit native cycle representative.

This is strictly weaker than the bi-finite realized-word criterion and avoids
needing transpose/composition at the scheme-carrier level.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeOneSidedFiniteCorrespondenceKrylovFinale

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeFiniteClosedCorrespondence
open GSTClassicalHodgeFiniteClosedCorrespondenceOperator
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgeExactClayStatement

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- One actual left-finite closed correspondence with an independently proved
cohomological action and one actual algebraic Hodge seed. -/
structure OneSidedKrylovCertificate
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat) where
  correspondence : FiniteClosedCorrespondence V
  cohomologyOperator :
    RationalSingularCohomology H.analytification (2 * p) →ₗ[ℚ]
      RationalSingularCohomology H.analytification (2 * p)
  realizesOnPoints :
    correspondence.RealizesAmbientOnPoints (H := H) cohomologyOperator
  preservesHodge : ∀ alpha : ClassicalHodgeFiber V H p,
    cohomologyOperator alpha.1 ∈
      rationalHodgeSubspace (H.hodgeBigrading p)
  seedCycle : codimensionCycles V.X p
  seedHodge :
    H.cycleClass p seedCycle ∈
      rationalHodgeSubspace (H.hodgeBigrading p)

namespace OneSidedKrylovCertificate

/-- Restriction of the independently realized correspondence action to the
weight-p rational Hodge fiber. -/
noncomputable def hodgeOperator
    (C : OneSidedKrylovCertificate V H p) :
    Module.End ℚ (ClassicalHodgeFiber V H p) where
  toFun alpha := ⟨C.cohomologyOperator alpha.1, C.preservesHodge alpha⟩
  map_add' := by intro a b; ext; simp
  map_smul' := by intro q a; ext; simp

/-- Genuine Hodge seed supplied by the actual native cycle. -/
noncomputable def seed
    (C : OneSidedKrylovCertificate V H p) :
    ClassicalHodgeFiber V H p :=
  ⟨H.cycleClass p C.seedCycle, C.seedHodge⟩

/-- Native Krylov orbit under repeated application of the same genuine
left-finite correspondence. -/
noncomputable def nativeOrbit
    (C : OneSidedKrylovCertificate V H p) :
    Nat → codimensionCycles V.X p
  | 0 => C.seedCycle
  | n + 1 => C.correspondence.nativeOperator p (C.nativeOrbit n)

/-- Hodge Krylov orbit under the matching cohomological operator. -/
noncomputable def hodgeOrbit
    (C : OneSidedKrylovCertificate V H p) :
    Nat → ClassicalHodgeFiber V H p
  | 0 => C.seed
  | n + 1 => C.hodgeOperator (C.hodgeOrbit n)

/-- Exact native/Betti synchronization along every iterate of the one-sided
correspondence. -/
theorem nativeOrbit_cycleClass
    (C : OneSidedKrylovCertificate V H p) :
    ∀ n : Nat,
      H.cycleClass p (C.nativeOrbit n) = (C.hodgeOrbit n).1 := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      change H.cycleClass p
          (C.correspondence.nativeOperator p (C.nativeOrbit n)) =
        C.cohomologyOperator (C.hodgeOrbit n).1
      rw [C.correspondence.cycleClass_nativeOperator
        C.cohomologyOperator C.realizesOnPoints (C.nativeOrbit n), ih]

/-- Every vector in the orbit has an explicit native algebraic-cycle
representative. -/
theorem hodgeOrbit_algebraic
    (C : OneSidedKrylovCertificate V H p)
    (n : Nat) :
    C.hodgeOrbit n ∈ AlgebraicHodgeSubspace V H p := by
  rw [mem_AlgebraicHodgeSubspace_iff,
    ← smoothProjective_cycleClass_range_eq_atomic_span V H p]
  exact ⟨C.nativeOrbit n, C.nativeOrbit_cycleClass n⟩

/-- The only representation-theoretic finishing condition: one genuine
correspondence orbit spans the entire weight-p Hodge fiber. -/
def IsKrylovCyclic
    (C : OneSidedKrylovCertificate V H p) : Prop :=
  Submodule.span ℚ (Set.range C.hodgeOrbit) = ⊤

/-- A cyclic one-sided finite correspondence saturates the algebraic Hodge
subspace in this weight. -/
theorem algebraicHodgeSubspace_eq_top
    (C : OneSidedKrylovCertificate V H p)
    (hcyc : C.IsKrylovCyclic) :
    AlgebraicHodgeSubspace V H p = ⊤ := by
  apply top_unique
  rw [← hcyc]
  apply Submodule.span_le.mpr
  rintro x ⟨n, rfl⟩
  exact C.hodgeOrbit_algebraic n

/-- Exact cycle representative for any rational Hodge class in this weight. -/
theorem exists_cycle
    (C : OneSidedKrylovCertificate V H p)
    (hcyc : C.IsKrylovCyclic)
    (alpha : RationalSingularCohomology H.analytification (2 * p))
    (halpha : alpha ∈ rationalHodgeSubspace (H.hodgeBigrading p)) :
    ∃ Z : codimensionCycles V.X p,
      H.cycleClass p Z = alpha := by
  let a : ClassicalHodgeFiber V H p := ⟨alpha, halpha⟩
  have htop := C.algebraicHodgeSubspace_eq_top hcyc
  have ha : a ∈ AlgebraicHodgeSubspace V H p := by
    rw [htop]
    trivial
  rw [mem_AlgebraicHodgeSubspace_iff] at ha
  rw [← smoothProjective_cycleClass_range_eq_atomic_span V H p] at ha
  exact ha

end OneSidedKrylovCertificate

/-- **GLOBAL ONE-SIDED CORRESPONDENCE FINALE.** -/
theorem exactHodge_of_oneSidedFiniteCorrespondenceKrylov
    (C : ∀ q : Nat, OneSidedKrylovCertificate V H q)
    (hcyc : ∀ q : Nat, (C q).IsKrylovCyclic) :
    EveryHodgeClassIsRationalAlgebraic H := by
  intro q alpha halpha
  exact (C q).exists_cycle (hcyc q) alpha halpha

/-- Literal finite rational-combination wording. -/
theorem finiteCombination_of_oneSidedFiniteCorrespondenceKrylov
    (C : ∀ q : Nat, OneSidedKrylovCertificate V H q)
    (hcyc : ∀ q : Nat, (C q).IsKrylovCyclic) :
    EveryHodgeClassIsFiniteRationalCombination H := by
  rw [← rationalAlgebraic_iff_finiteRationalCombination]
  exact exactHodge_of_oneSidedFiniteCorrespondenceKrylov C hcyc

#check OneSidedKrylovCertificate
#check OneSidedKrylovCertificate.hodgeOperator
#check OneSidedKrylovCertificate.nativeOrbit
#check OneSidedKrylovCertificate.nativeOrbit_cycleClass
#check OneSidedKrylovCertificate.IsKrylovCyclic
#check OneSidedKrylovCertificate.exists_cycle
#check exactHodge_of_oneSidedFiniteCorrespondenceKrylov
#check finiteCombination_of_oneSidedFiniteCorrespondenceKrylov

#print axioms OneSidedKrylovCertificate.nativeOrbit_cycleClass
#print axioms OneSidedKrylovCertificate.algebraicHodgeSubspace_eq_top
#print axioms exactHodge_of_oneSidedFiniteCorrespondenceKrylov
#print axioms finiteCombination_of_oneSidedFiniteCorrespondenceKrylov

end GSTClassicalHodgeOneSidedFiniteCorrespondenceKrylovFinale
