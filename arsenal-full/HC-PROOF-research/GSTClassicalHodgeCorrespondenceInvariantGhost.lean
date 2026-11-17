import GSTClassicalHodgeRealizedCorrespondenceExpressionAlgebra
import GSTClassicalHodgeAtomicSpan
import GSTClassicalHodgeRankFreeArsenalIrreducibility
import GSTClassicalHodgeExactClayStatement
open GSTClassicalHodgeAtomicSpan

/-!
# GST CLASSICAL HODGE — CORRESPONDENCE-INVARIANT GHOST

The full compositional algebra of genuine realized correspondences preserves
the actual cycle-class range.  When one such expression also preserves the
rational `(p,p)` Hodge fiber, it must therefore preserve the algebraic Hodge
subspace.

Consequently a failure of the Hodge conjecture at weight p produces one very
rigid object: a proper Hodge submodule which is invariant under EVERY genuine
Hodge-compatible realized-correspondence expression.

This is the correct target for the GST irreducibility artillery.  To kill the
failure it is enough to prove that the actual geometric correspondence algebra
acts irreducibly on every nonzero genuine Hodge fiber.  Zero Hodge fibers are
handled directly and require no artificial nonvanishing seed.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeCorrespondenceInvariantGhost

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgeRealizedCorrespondenceExpressionAlgebra
open GSTClassicalHodgeRealizedCorrespondenceExpressionAlgebra.RealizedCorrespondenceExpr
open GSTClassicalHodgeExactClayStatement

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- A genuine correspondence expression is Hodge-compatible when its actual
cohomological action preserves the derived rational `(p,p)` subspace. -/
def HodgeCompatible
    (E : RealizedCorrespondenceExpr V H p) : Prop :=
  ∀ alpha : ClassicalHodgeFiber V H p,
    E.cohomologyOperator alpha.1 ∈
      rationalHodgeSubspace (H.hodgeBigrading p)

/-- Restriction of a Hodge-compatible genuine correspondence expression to the
actual Hodge fiber. -/
noncomputable def hodgeOperator
    (E : RealizedCorrespondenceExpr V H p)
    (hE : HodgeCompatible E) :
    Module.End ℚ (ClassicalHodgeFiber V H p) where
  toFun alpha := ⟨E.cohomologyOperator alpha.1, hE alpha⟩
  map_add' := by intro a b; ext; simp [RealizedCorrespondenceExpr.cohomologyOperator]
  map_smul' := by intro q a; ext; simp [RealizedCorrespondenceExpr.cohomologyOperator]

/-- **ACTUAL GEOMETRY PRESERVES THE ALGEBRAIC HODGE SUBSPACE.** -/
theorem maps_algebraicHodgeSubspace
    (E : RealizedCorrespondenceExpr V H p)
    (hE : HodgeCompatible E)
    (alpha : ClassicalHodgeFiber V H p)
    (halpha : alpha ∈ AlgebraicHodgeSubspace V H p) :
    hodgeOperator E hE alpha ∈ AlgebraicHodgeSubspace V H p := by
  rw [mem_AlgebraicHodgeSubspace_iff] at halpha
  rw [← smoothProjective_cycleClass_range_eq_atomic_span V H p] at halpha
  rcases halpha with ⟨Z, hZ⟩
  rw [mem_AlgebraicHodgeSubspace_iff]
  rw [← smoothProjective_cycleClass_range_eq_atomic_span V H p]
  refine ⟨E.cycleOperator Z, ?_⟩
  change H.cycleClass p (E.cycleOperator Z) = E.cohomologyOperator alpha.1
  rw [E.cycleClass_natural, hZ]

/-- Invariance of a Hodge submodule under every genuine Hodge-compatible
correspondence expression. -/
def CorrespondenceInvariant
    (S : Submodule ℚ (ClassicalHodgeFiber V H p)) : Prop :=
  ∀ (E : RealizedCorrespondenceExpr V H p)
    (hE : HodgeCompatible E)
    (alpha : ClassicalHodgeFiber V H p),
      alpha ∈ S → hodgeOperator E hE alpha ∈ S

/-- The actual algebraic Hodge subspace is automatically correspondence
invariant. -/
theorem algebraicHodgeSubspace_correspondenceInvariant :
    CorrespondenceInvariant (V := V) (H := H) (p := p)
      (AlgebraicHodgeSubspace V H p) := by
  intro E hE alpha halpha
  exact maps_algebraicHodgeSubspace E hE alpha halpha

/-- One-weight failure is exactly properness of the actual algebraic Hodge
subspace. -/
def WeightFailure : Prop :=
  AlgebraicHodgeSubspace V H p ≠ ⊤

/-- A Hodge failure therefore produces a proper correspondence-invariant
submodule, with no choice of basis or separator. -/
theorem failure_gives_proper_invariant_ghost
    (hfail : WeightFailure (V := V) (H := H) (p := p)) :
    AlgebraicHodgeSubspace V H p ≠ ⊤ ∧
      CorrespondenceInvariant (V := V) (H := H) (p := p)
        (AlgebraicHodgeSubspace V H p) :=
  ⟨hfail, algebraicHodgeSubspace_correspondenceInvariant⟩

/-- Geometric irreducibility statement needed to kill every possible ghost.
It quantifies over submodules, but only invariance under ACTUAL realized
Hodge-compatible correspondence expressions. -/
def ActualCorrespondenceIrreducible : Prop :=
  ∀ S : Submodule ℚ (ClassicalHodgeFiber V H p),
    CorrespondenceInvariant (V := V) (H := H) (p := p) S →
    S ≠ ⊥ → S = ⊤

/-- **IRREDUCIBILITY + ONE NONZERO ALGEBRAIC SEED CLOSES ONE WEIGHT.** -/
theorem algebraicHodgeSubspace_eq_top_of_actualCorrespondenceIrreducible
    (hirr : ActualCorrespondenceIrreducible (V := V) (H := H) (p := p))
    (hne : AlgebraicHodgeSubspace V H p ≠ ⊥) :
    AlgebraicHodgeSubspace V H p = ⊤ :=
  hirr (AlgebraicHodgeSubspace V H p)
    algebraicHodgeSubspace_correspondenceInvariant hne

/-- The source condition required in one weight: either the whole Hodge fiber
is zero, or there is at least one nonzero genuine algebraic Hodge class. -/
def ZeroFiberOrAlgebraicSeed : Prop :=
  (∀ alpha : ClassicalHodgeFiber V H p, alpha = 0) ∨
    AlgebraicHodgeSubspace V H p ≠ ⊥

/-- **EXACT HODGE FROM ACTUAL-CORRESPONDENCE IRREDUCIBILITY.**
Zero Hodge weights are discharged by the zero cycle; every nonzero weight only
needs one nonzero algebraic seed plus irreducibility of the genuine
correspondence action. -/
theorem exactHodge_of_actualCorrespondenceIrreducible
    (hirr : ∀ q : Nat,
      ActualCorrespondenceIrreducible (V := V) (H := H) (p := q))
    (hseed : ∀ q : Nat,
      ZeroFiberOrAlgebraicSeed (V := V) (H := H) (p := q)) :
    EveryHodgeClassIsRationalAlgebraic H := by
  rw [everyHodgeClassIsRationalAlgebraic_iff_stage2G]
  intro q alpha halpha
  let a : ClassicalHodgeFiber V H q := ⟨alpha, halpha⟩
  rcases hseed q with hzero | hne
  · have ha0 : a = 0 := hzero a
    refine ⟨0, ?_⟩
    have hval : alpha = 0 := congrArg Subtype.val ha0
    simpa [hval]
  · have htop :=
      algebraicHodgeSubspace_eq_top_of_actualCorrespondenceIrreducible
        (hirr q) hne
    have ha : a ∈ AlgebraicHodgeSubspace V H q := by
      rw [htop]
      trivial
    rw [mem_AlgebraicHodgeSubspace_iff] at ha
    rw [← smoothProjective_cycleClass_range_eq_atomic_span V H q] at ha
    rcases ha with ⟨Z,hZ⟩
    exact ⟨Z,hZ⟩

/-- Literal finite rational-combination form under the same sharp criterion. -/
theorem finiteCombination_of_actualCorrespondenceIrreducible
    (hirr : ∀ q : Nat,
      ActualCorrespondenceIrreducible (V := V) (H := H) (p := q))
    (hseed : ∀ q : Nat,
      ZeroFiberOrAlgebraicSeed (V := V) (H := H) (p := q)) :
    EveryHodgeClassIsFiniteRationalCombination H := by
  rw [← rationalAlgebraic_iff_finiteRationalCombination]
  exact exactHodge_of_actualCorrespondenceIrreducible hirr hseed

#check HodgeCompatible
#check hodgeOperator
#check maps_algebraicHodgeSubspace
#check CorrespondenceInvariant
#check algebraicHodgeSubspace_correspondenceInvariant
#check failure_gives_proper_invariant_ghost
#check ActualCorrespondenceIrreducible
#check ZeroFiberOrAlgebraicSeed
#check algebraicHodgeSubspace_eq_top_of_actualCorrespondenceIrreducible
#check exactHodge_of_actualCorrespondenceIrreducible
#check finiteCombination_of_actualCorrespondenceIrreducible

#print axioms maps_algebraicHodgeSubspace
#print axioms algebraicHodgeSubspace_correspondenceInvariant
#print axioms failure_gives_proper_invariant_ghost
#print axioms exactHodge_of_actualCorrespondenceIrreducible
#print axioms finiteCombination_of_actualCorrespondenceIrreducible

end GSTClassicalHodgeCorrespondenceInvariantGhost
