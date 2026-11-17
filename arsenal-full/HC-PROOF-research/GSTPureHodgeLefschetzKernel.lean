import Mathlib
import GSTUniversalLefschetzKernel
import GSTGlobalPureHodgeCosmology

/-!
# GST PURE-HODGE LEFSCHETZ KERNEL

The universal transition kernel classifies every source/target matrix entry of
every Lefschetz power.  The global pure-Hodge cosmology supplies the canonical
diagonal cells.

Combining them produces a closed Hodge/Lefschetz propagation law:

* a pure diagonal cell of weight p can reach a pure diagonal cell of weight q
  only when p <= q;
* the unique live propagation time is 2(q-p);
* the exact coefficient is the central binomial number choose(2(q-p), q-p).

Thus the diagonal-to-diagonal part of universal Lefschetz evolution is a
dimension-free central-binomial kernel, with the historical finite HC world
appearing only as one bounded chart.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000000

namespace GSTPureHodgeLefschetzKernel

open GSTWorldCosmology
open GSTWorldPoincareDuality
open GSTDimensionFreeHodgeDiagonal
open GSTGlobalPureHodgeCosmology
open GSTTruncatedWorldCohomologyRing
open GSTUniversalLefschetzKernel

/-- Distance between two canonical pure-Hodge weights. -/
def pureWeightGap
    {A B : Nat}
    (p q : Fin (min A B)) : Nat :=
  q.1 - p.1

/-- A forward pure-Hodge jump by r has unique Lefschetz time 2r and exact
central-binomial multiplicity. -/
theorem pure_diagonal_lefschetz_forward_exact
    {A B : Nat}
    (p q : Fin (min A B))
    (hpq : p.1 ≤ q.1) :
    worldAct A B
        ((L A B)^(2 * pureWeightGap p q))
        (worldBasis (pureDiagonalState p))
        (pureDiagonalState q) =
      ((2 * pureWeightGap p q).choose
        (pureWeightGap p q) : ℤ) := by
  apply worldAct_L_pow_basis_exact
  · unfold worldForward pureDiagonalState diagonalState
    exact ⟨hpq, hpq⟩
  · unfold worldCausalDistance carryDistance digitDistance
    unfold pureWeightGap pureDiagonalState diagonalState
    simp only
    omega

/-- Inside the forward Hodge cone, every time other than 2(q-p) vanishes. -/
theorem pure_diagonal_lefschetz_wrong_time_zero
    {A B n : Nat}
    (p q : Fin (min A B))
    (hpq : p.1 ≤ q.1)
    (htime : n ≠ 2 * pureWeightGap p q) :
    worldAct A B
        ((L A B)^n)
        (worldBasis (pureDiagonalState p))
        (pureDiagonalState q) = 0 := by
  apply worldAct_L_pow_basis_wrong_time_zero
  · unfold worldForward pureDiagonalState diagonalState
    exact ⟨hpq, hpq⟩
  · unfold worldCausalDistance carryDistance digitDistance
    unfold pureDiagonalState diagonalState
    unfold pureWeightGap at htime
    simp only
    omega

/-- Pure-Hodge propagation is strictly forward in weight. -/
theorem pure_diagonal_lefschetz_backward_zero
    {A B n : Nat}
    (p q : Fin (min A B))
    (hback : q.1 < p.1) :
    worldAct A B
        ((L A B)^n)
        (worldBasis (pureDiagonalState p))
        (pureDiagonalState q) = 0 := by
  apply worldAct_L_pow_basis_outside_future_zero
  unfold worldForward pureDiagonalState diagonalState
  simp only
  omega

/-- **UNIVERSAL PURE-HODGE LEFSCHETZ KERNEL.**

The complete diagonal-to-diagonal matrix coefficient is central-binomial at
one unique forward time and zero everywhere else. -/
theorem pure_diagonal_lefschetz_kernel
    {A B n : Nat}
    (p q : Fin (min A B)) :
    worldAct A B
        ((L A B)^n)
        (worldBasis (pureDiagonalState p))
        (pureDiagonalState q) =
      if hpq : p.1 ≤ q.1 then
        if htime : n = 2 * pureWeightGap p q then
          (n.choose (pureWeightGap p q) : ℤ)
        else 0
      else 0 := by
  by_cases hpq : p.1 ≤ q.1
  · rw [dif_pos hpq]
    by_cases htime : n = 2 * pureWeightGap p q
    · rw [dif_pos htime]
      subst n
      exact pure_diagonal_lefschetz_forward_exact p q hpq
    · rw [dif_neg htime]
      exact pure_diagonal_lefschetz_wrong_time_zero p q hpq htime
  · rw [dif_neg hpq]
    exact pure_diagonal_lefschetz_backward_zero
      (n:=n) p q (by omega)

/-- In the historical 4 x 3 chart, diagonal weight 0 reaches diagonal weight
2 after four Lefschetz steps with multiplicity choose(4,2)=6. -/
theorem hc_pure_zero_to_two_kernel :
    worldAct 4 3
        ((L 4 3)^4)
        (worldBasis
          (pureDiagonalState
            (A:=4) (B:=3) (⟨0, by decide⟩ : Fin (min 4 3))))
        (pureDiagonalState
          (A:=4) (B:=3) (⟨2, by decide⟩ : Fin (min 4 3))) = 6 := by
  simpa [pureWeightGap, show (Nat.choose 4 2 : ℤ) = 6 from by decide] using
    (pure_diagonal_lefschetz_forward_exact
      (A:=4) (B:=3)
      (⟨0, by decide⟩ : Fin (min 4 3))
      (⟨2, by decide⟩ : Fin (min 4 3))
      (by decide))

/-- Capstone joining global Hodge coordinates to the exact universal
Lefschetz transition kernel. -/
theorem pure_hodge_lefschetz_kernel_crown :
    (∀ A B n (p q : Fin (min A B)),
      worldAct A B
          ((L A B)^n)
          (worldBasis (pureDiagonalState p))
          (pureDiagonalState q) =
        if hpq : p.1 ≤ q.1 then
          if htime : n = 2 * pureWeightGap p q then
            (n.choose (pureWeightGap p q) : ℤ)
          else 0
        else 0)
    ∧ worldAct 4 3
        ((L 4 3)^4)
        (worldBasis
          (pureDiagonalState
            (A:=4) (B:=3) (⟨0, by decide⟩ : Fin (min 4 3))))
        (pureDiagonalState
          (A:=4) (B:=3) (⟨2, by decide⟩ : Fin (min 4 3))) = 6 := by
  exact ⟨
    fun A B n p q => pure_diagonal_lefschetz_kernel p q,
    hc_pure_zero_to_two_kernel⟩

#check pureWeightGap
#check pure_diagonal_lefschetz_forward_exact
#check pure_diagonal_lefschetz_wrong_time_zero
#check pure_diagonal_lefschetz_backward_zero
#check pure_diagonal_lefschetz_kernel
#check hc_pure_zero_to_two_kernel
#check pure_hodge_lefschetz_kernel_crown

#print axioms pure_diagonal_lefschetz_forward_exact
#print axioms pure_diagonal_lefschetz_kernel
#print axioms hc_pure_zero_to_two_kernel
#print axioms pure_hodge_lefschetz_kernel_crown

end GSTPureHodgeLefschetzKernel
