import GSTClassicalHodgeRealizedClosedCorrespondenceAlgebra
import GSTClassicalHodgeAtomicSpan
import GSTClassicalHodgeExactClayStatement
open GSTClassicalHodgeAtomicSpan

/-!
# GST CLASSICAL HODGE — REALIZED-CORRESPONDENCE KRYLOV FINALE

This is the basis-free cyclic reduction of the actual correspondence attack.

At a fixed weight p, it is enough to have:

* one ACTUAL realized closed-correspondence word T;
* T preserves the genuine rational Hodge fiber;
* one ACTUAL native codimension-p cycle Z whose cycle class is Hodge;
* the Hodge-fiber orbit of cl(Z) under repeated application of T spans the
  whole Hodge fiber.

Every orbit vector has an explicit native representative obtained by iterating
the native cycle operator of the same realized correspondence word.  Therefore
if the orbit spans, every Hodge class is algebraic.

No spectrum, eigenbasis, matrix-unit family, per-target correspondence word,
point-visibility family, or arbitrary operator-stability hypothesis is used.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeRealizedCorrespondenceKrylovFinale

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgeRealizedClosedCorrespondenceAlgebra
open GSTClassicalHodgeExactClayStatement

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- One genuine correspondence word with one genuine algebraic seed whose
Krylov orbit spans the whole weight-p Hodge fiber. -/
structure RealizedCorrespondenceKrylovCertificate
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat) where
  word : RealizedCorrespondenceWord V H p
  word_hodge : ∀ alpha : ClassicalHodgeFiber V H p,
    (realizedWordPair word).cohomologyOperator alpha.1 ∈
      rationalHodgeSubspace (H.hodgeBigrading p)
  seedCycle : codimensionCycles V.X p
  seed_hodge :
    H.cycleClass p seedCycle ∈
      rationalHodgeSubspace (H.hodgeBigrading p)

namespace RealizedCorrespondenceKrylovCertificate

/-- Restriction of the genuine correspondence action to the genuine Hodge
fiber. -/
noncomputable def hodgeOperator
    (C : RealizedCorrespondenceKrylovCertificate V H p) :
    Module.End ℚ (ClassicalHodgeFiber V H p) where
  toFun alpha :=
    ⟨(realizedWordPair C.word).cohomologyOperator alpha.1,
      C.word_hodge alpha⟩
  map_add' := by intro a b; ext; simp
  map_smul' := by intro q a; ext; simp

/-- Genuine Hodge seed coming from the actual native cycle. -/
noncomputable def seed
    (C : RealizedCorrespondenceKrylovCertificate V H p) :
    ClassicalHodgeFiber V H p :=
  ⟨H.cycleClass p C.seedCycle, C.seed_hodge⟩

/-- Native orbit under repeated application of the actual correspondence. -/
noncomputable def nativeOrbit
    (C : RealizedCorrespondenceKrylovCertificate V H p) :
    Nat → codimensionCycles V.X p
  | 0 => C.seedCycle
  | n + 1 =>
      (realizedWordPair C.word).cycleOperator (C.nativeOrbit n)

/-- Hodge orbit under the matching cohomological correspondence action. -/
noncomputable def hodgeOrbit
    (C : RealizedCorrespondenceKrylovCertificate V H p) :
    Nat → ClassicalHodgeFiber V H p
  | 0 => C.seed
  | n + 1 => C.hodgeOperator (C.hodgeOrbit n)

/-- Exact commuting-square identity along the entire Krylov orbit. -/
theorem nativeOrbit_cycleClass
    (C : RealizedCorrespondenceKrylovCertificate V H p) :
    ∀ n : Nat,
      H.cycleClass p (C.nativeOrbit n) = (C.hodgeOrbit n).1 := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      change H.cycleClass p
          ((realizedWordPair C.word).cycleOperator (C.nativeOrbit n)) =
        (realizedWordPair C.word).cohomologyOperator (C.hodgeOrbit n).1
      rw [(realizedWordPair C.word).cycleClass_cycleOperator, ih]

/-- Every vector in the genuine correspondence orbit is already algebraic. -/
theorem hodgeOrbit_algebraic
    (C : RealizedCorrespondenceKrylovCertificate V H p)
    (n : Nat) :
    C.hodgeOrbit n ∈ AlgebraicHodgeSubspace V H p := by
  rw [mem_AlgebraicHodgeSubspace_iff,
    ← smoothProjective_cycleClass_range_eq_atomic_span V H p]
  exact ⟨C.nativeOrbit n, C.nativeOrbit_cycleClass n⟩

/-- Basis-free cyclicity condition: the linear span of the single genuine
correspondence orbit is the whole Hodge fiber. -/
def IsKrylovCyclic
    (C : RealizedCorrespondenceKrylovCertificate V H p) : Prop :=
  Submodule.span ℚ (Set.range C.hodgeOrbit) = ⊤

/-- **ONE ACTUAL CORRESPONDENCE ORBIT SATURATES ONE HODGE WEIGHT.** -/
theorem algebraicHodgeSubspace_eq_top
    (C : RealizedCorrespondenceKrylovCertificate V H p)
    (hcyc : C.IsKrylovCyclic) :
    AlgebraicHodgeSubspace V H p = ⊤ := by
  apply top_unique
  rw [← hcyc]
  apply Submodule.span_le.mpr
  rintro x ⟨n, rfl⟩
  exact C.hodgeOrbit_algebraic n

/-- Every rational Hodge class in the weight has an actual native cycle
representative once the single realized correspondence orbit is cyclic. -/
theorem exists_cycle
    (C : RealizedCorrespondenceKrylovCertificate V H p)
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
  rcases ha with ⟨Z, hZ⟩
  exact ⟨Z, hZ⟩

end RealizedCorrespondenceKrylovCertificate

/-- **GLOBAL KRYLOV FINALE.**
One actual cyclic closed-correspondence orbit in every weight proves the
literal rational Hodge statement. -/
theorem exactHodge_of_realizedCorrespondenceKrylov
    (C : ∀ q : Nat,
      RealizedCorrespondenceKrylovCertificate V H q)
    (hcyc : ∀ q : Nat, (C q).IsKrylovCyclic) :
    EveryHodgeClassIsRationalAlgebraic H := by
  intro q alpha halpha
  exact (C q).exists_cycle (hcyc q) alpha halpha

/-- Literal finite rational-combination wording. -/
theorem finiteCombination_of_realizedCorrespondenceKrylov
    (C : ∀ q : Nat,
      RealizedCorrespondenceKrylovCertificate V H q)
    (hcyc : ∀ q : Nat, (C q).IsKrylovCyclic) :
    EveryHodgeClassIsFiniteRationalCombination H := by
  rw [← rationalAlgebraic_iff_finiteRationalCombination]
  exact exactHodge_of_realizedCorrespondenceKrylov C hcyc

#check RealizedCorrespondenceKrylovCertificate
#check RealizedCorrespondenceKrylovCertificate.hodgeOperator
#check RealizedCorrespondenceKrylovCertificate.nativeOrbit
#check RealizedCorrespondenceKrylovCertificate.hodgeOrbit
#check RealizedCorrespondenceKrylovCertificate.nativeOrbit_cycleClass
#check RealizedCorrespondenceKrylovCertificate.IsKrylovCyclic
#check RealizedCorrespondenceKrylovCertificate.algebraicHodgeSubspace_eq_top
#check RealizedCorrespondenceKrylovCertificate.exists_cycle
#check exactHodge_of_realizedCorrespondenceKrylov
#check finiteCombination_of_realizedCorrespondenceKrylov

#print axioms RealizedCorrespondenceKrylovCertificate.nativeOrbit_cycleClass
#print axioms RealizedCorrespondenceKrylovCertificate.algebraicHodgeSubspace_eq_top
#print axioms exactHodge_of_realizedCorrespondenceKrylov
#print axioms finiteCombination_of_realizedCorrespondenceKrylov

end GSTClassicalHodgeRealizedCorrespondenceKrylovFinale
