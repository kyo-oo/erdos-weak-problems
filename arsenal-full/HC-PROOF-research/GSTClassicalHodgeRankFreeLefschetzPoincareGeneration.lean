import GSTClassicalHodgeLefschetzPoincareMatrixGeneration
import GSTClassicalHodgeRankFreePrimitiveGeneration

/-!
# GST CLASSICAL HODGE — RANK-FREE LEFSCHETZ/POINCARE GENERATION

The finite pure-window theorem shows that Lefschetz and Poincare alone
generate every matrix unit.  This module transports that exact identity into
an arbitrary genuine classical Hodge fiber through finite coordinate
localization.

The theorem is deliberately an operator identity, not yet a claim that the
coordinate localization is algebraic.  The latter is the geometric theorem
to be derived on the native-cycle side.
-/

set_option maxHeartbeats 30000000
set_option maxRecDepth 1000000

noncomputable section

open GSTProjectiveOverC
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeFullArsenalIrreducibility
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgeRankFreePrimitiveGeneration
open GSTClassicalHodgeLefschetzPoincareMatrixGeneration

namespace GSTClassicalHodgeRankFreeLefschetzPoincareGeneration

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- Lift of the finite Lefschetz/Poincare word associated to two local slots. -/
noncomputable def liftedLefschetzPoincareWord
    {N : Nat}
    (e : Fin N → ClassicalHodgeBasisIndex V H p)
    (r s : Fin N) :
    Module.End ℚ (ClassicalHodgeFiber V H p) :=
  liftFiniteHodgeOperator e (lefschetzPoincareMatrixWord r s)

/-- Exact finite-to-rank-free conjugation of the LP word. -/
theorem liftedLefschetzPoincareWord_eq_matrixUnit
    {N : Nat}
    (e : Fin N → ClassicalHodgeBasisIndex V H p)
    (r s : Fin N) :
    liftedLefschetzPoincareWord e r s =
      hodgeMatrixUnit (e r) (e s) := by
  unfold liftedLefschetzPoincareWord
  rw [lefschetzPoincareMatrixWord_eq]
  exact liftFiniteHodgeOperator_matrixUnit e r s

/-- Every global matrix unit is the two-slot lift of an operator word built
only from the native GST Lefschetz and Poincare primitives. -/
theorem rankFreeMatrixUnit_eq_twoSlot_LP_word
    (i j : ClassicalHodgeBasisIndex V H p) :
    hodgeMatrixUnit i j =
      liftedLefschetzPoincareWord
        (pairBasisIndex i j) sourceSlot targetSlot := by
  symm
  simpa using
    liftedLefschetzPoincareWord_eq_matrixUnit
      (pairBasisIndex i j) sourceSlot targetSlot

/-- In the universal 2-slot chart, the LP word equals the normalized
one-step Lefschetz shift; Poincare is needed for general finite words but not
for this ordered local source-target chart. -/
theorem universalTwoSlot_LP_word_eq_forwardShift :
    lefschetzPoincareMatrixWord sourceSlot targetSlot =
      pureForwardShift 2 := by
  rw [lefschetzPoincareMatrixWord_eq]
  apply LinearMap.ext
  intro a
  rw [rationalPureWindow_eq_sum_basis a]
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro r _
  fin_cases r
  · simp [pureMatrixUnit_basis_source, pureForwardShift_basis,
      sourceSlot, targetSlot]
  · simp [pureMatrixUnit_basis_other, pureForwardShift_basis,
      sourceSlot, targetSlot]

/-- **UNIVERSAL TWO-SLOT LEFSCHETZ FORMULA.**  Every rank-free matrix unit is
the finite localization of the same normalized `L^2` operator. -/
theorem rankFreeMatrixUnit_eq_twoSlot_Lefschetz
    (i j : ClassicalHodgeBasisIndex V H p) :
    hodgeMatrixUnit i j =
      liftFiniteHodgeOperator (pairBasisIndex i j)
        (pureForwardShift 2) := by
  rw [rankFreeMatrixUnit_eq_twoSlot_LP_word,
    liftedLefschetzPoincareWord,
    universalTwoSlot_LP_word_eq_forwardShift]

/-- Rank-free Lefschetz/Poincare generation crown. -/
theorem rank_free_lefschetz_poincare_generation_crown :
    ∀ i j : ClassicalHodgeBasisIndex V H p,
      hodgeMatrixUnit i j =
        liftFiniteHodgeOperator (pairBasisIndex i j)
          (pureForwardShift 2) :=
  rankFreeMatrixUnit_eq_twoSlot_Lefschetz

/-! ## ACTUAL GEOMETRIC LEFSCHETZ VS ABSTRACT TWO-SLOT SHIFT

The preceding rank-free two-slot operator is a formal coordinate
localization. It must NOT be equated with words in actual cup-L
and its lowering operator Lambda without a theorem realizing that
localization by a genuine algebraic correspondence.

Here is an exact all-module test. On any primitive middle vector
annihilated by both genuine L and Lambda, every NONEMPTY word
in those two operators annihilates the vector; an arbitrary finite
rational combination of words only produces a scalar multiple of
the original vector. Therefore such words alone cannot rotate one
independent primitive direction into another.

This is not a counterexample to Hodge; it discriminates the missing
geometric-source operator needed in the unrestricted GST assembly. -/

section GenuineGeometricLPObstruction

variable {A : Type*} [AddCommGroup A] [Module ℚ A]

/-- Evaluate a word in two actual ℚ-linear graded operators on a
chosen vector. True means raising, false lowering; [] is identity. -/
def geometricLPWordApply
    (L D : Module.End ℚ A) (v : A) : List Bool → A
  | [] => v
  | true :: t => L (geometricLPWordApply L D v t)
  | false :: t => D (geometricLPWordApply L D v t)

/-- Every nonempty geometric Lefschetz/lowering word kills a vector
annihilated by BOTH primitives, independently of noncommutativity. -/
theorem geometricLPWord_nonempty_kills_joint_primitive
    (L D : Module.End ℚ A) (v : A)
    (hL : L v = 0) (hD : D v = 0) :
    ∀ w : List Bool, w ≠ [] →
      geometricLPWordApply L D v w = 0 := by
  intro w
  induction w with
  | nil =>
      intro hn
      exact (hn rfl).elim
  | cons b rest ih =>
      intro _
      cases rest with
      | nil =>
          cases b <;>
            simp [geometricLPWordApply, hL, hD]
      | cons b' rest' =>
          have hz :
              geometricLPWordApply L D v (b' :: rest') = 0 :=
            ih (by simp)
          cases b <;>
            simp [geometricLPWordApply, hz]

/-- Finite rational combinations of any finite words in geometric
raising/lowering. No assumptions about a coordinate basis or about
algebraicity of any unknown Hodge target. -/
def geometricLPFiniteCombination
    (L D : Module.End ℚ A) (v : A)
    (words : List (ℚ × List Bool)) : A :=
  words.foldr (fun q acc =>
    q.1 • geometricLPWordApply L D v q.2 + acc) 0

/-- FULL ALL-RANK NO-ROTATION LAW. Given L v=Lambda v=0,
every finite polynomial in genuine L and Lambda maps v into
the original one-dimensional rational span of v. -/
theorem geometricLPFiniteCombination_mem_source_line
    (L D : Module.End ℚ A) (v : A)
    (hL : L v = 0) (hD : D v = 0)
    (words : List (ℚ × List Bool)) :
    geometricLPFiniteCombination L D v words ∈
      Submodule.span ℚ ({v} : Set A) := by
  let W : Submodule ℚ A := Submodule.span ℚ ({v} : Set A)
  have hv : v ∈ W := Submodule.subset_span (by simp)
  have hword : ∀ w : List Bool,
      geometricLPWordApply L D v w ∈ W := by
    intro w
    by_cases he : w = []
    · subst w
      simpa [geometricLPWordApply] using hv
    · have hz := geometricLPWord_nonempty_kills_joint_primitive
        L D v hL hD w he
      rw [hz]
      exact W.zero_mem
  induction words with
  | nil =>
      simp only [geometricLPFiniteCombination, List.foldr_nil]
      exact W.zero_mem
  | cons q tail ih =>
      change q.1 • geometricLPWordApply L D v q.2 +
          geometricLPFiniteCombination L D v tail ∈ W
      exact W.add_mem (W.smul_mem q.1 (hword q.2)) ih

/-- A missing independent primitive direction is unreachable
by every finite expression in actual L and Lambda
alone, even if the abstract GST two-slot matrix unit reaches it. -/
theorem geometricLPFiniteCombination_cannot_hit_missing_direction
    (L D : Module.End ℚ A) (v target : A)
    (hL : L v = 0) (hD : D v = 0)
    (hIndependent : target ∉ Submodule.span ℚ ({v} : Set A))
    (words : List (ℚ × List Bool)) :
    geometricLPFiniteCombination L D v words ≠ target := by
  intro heq
  apply hIndependent
  rw [← heq]
  exact geometricLPFiniteCombination_mem_source_line
    L D v hL hD words

/-! ## ORIGINAL-X PRIMITIVE DEGREE MOMENT BLINDNESS

On genuine middle primitive cohomology the ordinary projective
degree trace factors through cup by the ample class:
trace(alpha) = integral(alpha * h^p) =
integral((h*alpha) * h^(p-1)), whenever p >= 1.
Thus trace annihilates the primitive kernel L alpha=0.

More generally ANY actual algebraic correspondence preserving that
primitive kernel has a completely zero projective-degree Hankel
moment matrix on a primitive seed. A nonzero geometric source and
a genuine correspondence are therefore insufficient to make the
projective-degree moment determinant positive on such a sector.
Primitive pairing functionals, not ordinary degree alone, are
mathematically necessary for target-sensitive detection. -/

/-- Iterated action of any degree-preserving geometric operator. -/
def geometricPrimitiveOrbit
    (T : Module.End ℚ A) (v : A) : ℕ → A
  | 0 => v
  | n + 1 => T (geometricPrimitiveOrbit T v n)

/-- Native primitive stability is preserved through every iterate,
when the underlying actual correspondence preserves ker(L). -/
theorem geometricPrimitiveOrbit_stays_primitive
    (L T : Module.End ℚ A)
    (hStable : ∀ z : A, L z = 0 → L (T z) = 0)
    (v : A) (hv : L v = 0) :
    ∀ n : ℕ, L (geometricPrimitiveOrbit T v n) = 0 := by
  intro n
  induction n with
  | zero => exact hv
  | succ n ih =>
      exact hStable (geometricPrimitiveOrbit T v n) ih

/-- The natural degree trace factors through hyperplane cup, so
it is zero on every iterate in the true primitive kernel. -/
theorem geometricPrimitiveOrbit_degree_trace_zero
    (L T : Module.End ℚ A)
    (hStable : ∀ z : A, L z = 0 → L (T z) = 0)
    (v : A) (hv : L v = 0)
    (trace : A →ₗ[ℚ] ℚ) (factor : A →ₗ[ℚ] ℚ)
    (hTrace : ∀ z : A, trace z = factor (L z)) :
    ∀ n : ℕ, trace (geometricPrimitiveOrbit T v n) = 0 := by
  intro n
  rw [hTrace]
  rw [geometricPrimitiveOrbit_stays_primitive L T hStable v hv n]
  exact map_zero factor

/-- Every entry of the corresponding degree-trace Hankel matrix
vanishes, for ALL finite ranks; even if the actual primitive
orbit itself contains several independent nonzero vectors. -/
theorem geometricPrimitiveDegreeHankel_eq_zero
    (L T : Module.End ℚ A)
    (hStable : ∀ z : A, L z = 0 → L (T z) = 0)
    (v : A) (hv : L v = 0)
    (trace : A →ₗ[ℚ] ℚ) (factor : A →ₗ[ℚ] ℚ)
    (hTrace : ∀ z : A, trace z = factor (L z))
    (r : ℕ) :
    (fun i j : Fin r =>
      trace (geometricPrimitiveOrbit T v (i.val + j.val))) =
        (0 : Matrix (Fin r) (Fin r) ℚ) := by
  ext i j
  exact geometricPrimitiveOrbit_degree_trace_zero
    L T hStable v hv trace factor hTrace (i.val + j.val)

#check geometricPrimitiveOrbit_stays_primitive
#check geometricPrimitiveOrbit_degree_trace_zero
#check geometricPrimitiveDegreeHankel_eq_zero
#print axioms geometricPrimitiveDegreeHankel_eq_zero

end GenuineGeometricLPObstruction

#check geometricLPWord_nonempty_kills_joint_primitive
#check geometricLPFiniteCombination_mem_source_line
#check geometricLPFiniteCombination_cannot_hit_missing_direction
#print axioms geometricLPFiniteCombination_cannot_hit_missing_direction

#check liftedLefschetzPoincareWord
#check liftedLefschetzPoincareWord_eq_matrixUnit
#check rankFreeMatrixUnit_eq_twoSlot_LP_word
#check universalTwoSlot_LP_word_eq_forwardShift
#check rankFreeMatrixUnit_eq_twoSlot_Lefschetz

#print axioms liftedLefschetzPoincareWord_eq_matrixUnit
#print axioms rankFreeMatrixUnit_eq_twoSlot_LP_word
#print axioms universalTwoSlot_LP_word_eq_forwardShift
#print axioms rankFreeMatrixUnit_eq_twoSlot_Lefschetz

end GSTClassicalHodgeRankFreeLefschetzPoincareGeneration
