import Mathlib
import GSTUniversalLefschetzCausalGeometry

/-!
# GST LEFSCHETZ--POINCARE RECIPROCITY

The universal Lefschetz kernel gives the exact forward transition amplitude
between any two world cells.  Dimension-free Poincare duality gives the
canonical complementary cell involution.

These two structures are not independent.

Poincare complement reverses the native causal order, preserves both exact
axis distances after reversing source and target, and therefore preserves the
entire Lefschetz transition kernel:

    K_n(s,t) = K_n(s^*, t^*) with the causal arrow reversed,

more precisely

    K_n(s,t) = K_n(worldDual t, worldDual s).

Thus every finite GST world carries an exact time-reversal reciprocity between
its Lefschetz propagation law and its Poincare involution.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000000

namespace GSTLefschetzPoincareReciprocity

open GSTWorldCosmology
open GSTGradedWorldAlgebra
open GSTTruncatedWorldCohomologyRing
open GSTWorldPoincareDuality
open GSTUniversalLefschetzKernel
open GSTUniversalLefschetzCausalGeometry

/-- Poincare complement reverses the native forward relation exactly. -/
theorem worldForward_dual_iff
    {A B : Nat} (s t : WorldCell A B) :
    worldForward s t ↔
      worldForward (worldDual t) (worldDual s) := by
  rcases s with ⟨⟨Cs,hCs⟩,⟨ds,hds⟩⟩
  rcases t with ⟨⟨Ct,hCt⟩,⟨dt,hdt⟩⟩
  unfold worldForward worldDual complementFin
  simp only
  constructor
  · rintro ⟨hC,hd⟩
    constructor <;> omega
  · rintro ⟨hC,hd⟩
    constructor <;> omega

/-- Carry distance is invariant under Poincare reversal. -/
theorem carryDistance_dual_reverse
    {A B : Nat} (s t : WorldCell A B) :
    carryDistance (worldDual t) (worldDual s) =
      carryDistance s t := by
  rcases s with ⟨⟨Cs,hCs⟩,⟨ds,hds⟩⟩
  rcases t with ⟨⟨Ct,hCt⟩,⟨dt,hdt⟩⟩
  unfold carryDistance worldDual complementFin
  simp only
  omega

/-- Digit distance is invariant under Poincare reversal. -/
theorem digitDistance_dual_reverse
    {A B : Nat} (s t : WorldCell A B) :
    digitDistance (worldDual t) (worldDual s) =
      digitDistance s t := by
  rcases s with ⟨⟨Cs,hCs⟩,⟨ds,hds⟩⟩
  rcases t with ⟨⟨Ct,hCt⟩,⟨dt,hdt⟩⟩
  unfold digitDistance worldDual complementFin
  simp only
  omega

/-- Total causal distance is invariant under Poincare reversal. -/
theorem worldCausalDistance_dual_reverse
    {A B : Nat} (s t : WorldCell A B) :
    worldCausalDistance (worldDual t) (worldDual s) =
      worldCausalDistance s t := by
  unfold worldCausalDistance
  rw [carryDistance_dual_reverse, digitDistance_dual_reverse]

/-- **UNIVERSAL LEFSCHETZ--POINCARE RECIPROCITY.**

Every n-step transition amplitude equals the amplitude of the
Poincare-complemented transition with its causal arrow reversed. -/
theorem lefschetz_kernel_poincare_reciprocity
    {A B n : Nat} (s t : WorldCell A B) :
    worldAct A B ((L A B)^n) (worldBasis s) t =
      worldAct A B ((L A B)^n)
        (worldBasis (worldDual t)) (worldDual s) := by
  rw [worldAct_L_pow_basis_kernel, worldAct_L_pow_basis_kernel]
  by_cases hforward : worldForward s t
  · have hdual :
        worldForward (worldDual t) (worldDual s) :=
      (worldForward_dual_iff s t).mp hforward
    simp only [hforward, hdual]
    rw [worldCausalDistance_dual_reverse,
        digitDistance_dual_reverse]
  · have hdual :
        ¬ worldForward (worldDual t) (worldDual s) := by
      intro h
      exact hforward ((worldForward_dual_iff s t).mpr h)
    simp only [hforward, hdual]
    rfl

/-- Nonzero propagation is exactly invariant under Poincare reversal. -/
theorem nonzero_transition_dual_iff
    {A B n : Nat} (s t : WorldCell A B) :
    (worldAct A B ((L A B)^n) (worldBasis s) t ≠ 0) ↔
      (worldAct A B ((L A B)^n)
        (worldBasis (worldDual t)) (worldDual s) ≠ 0) := by
  rw [lefschetz_kernel_poincare_reciprocity]

/-- The unique transition time is therefore the same on a causal arrow and
its Poincare-reversed arrow. -/
theorem dual_transition_time_exact
    {A B n : Nat} (s t : WorldCell A B)
    (hne :
      worldAct A B ((L A B)^n) (worldBasis s) t ≠ 0) :
    n = worldCausalDistance (worldDual t) (worldDual s) := by
  have htime :=
    (nonzero_lefschetz_transition_forces_causality s t hne).2
  rw [worldCausalDistance_dual_reverse]
  exact htime

/-- Poincare reversal exchanges the source and target degrees around the same
top degree while retaining the exact propagation time. -/
theorem dual_transition_degree_balance
    {A B n : Nat} (s t : WorldCell A B)
    (hne :
      worldAct A B ((L A B)^n) (worldBasis s) t ≠ 0) :
    worldDegree (worldDual s) =
      worldDegree (worldDual t) + n := by
  have hdeg := nonzero_transition_degree_exact s t hne
  have hs := worldDegree_dual_sum s
  have ht := worldDegree_dual_sum t
  omega

/-- Capstone joining the exact transition kernel, causal geometry and
Poincare involution into one reciprocity law. -/
theorem lefschetz_poincare_reciprocity_crown :
    (∀ A B (s t : WorldCell A B),
      worldForward s t ↔
        worldForward (worldDual t) (worldDual s))
    ∧ (∀ A B (s t : WorldCell A B),
      worldCausalDistance (worldDual t) (worldDual s) =
        worldCausalDistance s t)
    ∧ (∀ A B n (s t : WorldCell A B),
      worldAct A B ((L A B)^n) (worldBasis s) t =
        worldAct A B ((L A B)^n)
          (worldBasis (worldDual t)) (worldDual s))
    ∧ (∀ A B n (s t : WorldCell A B),
      worldAct A B ((L A B)^n) (worldBasis s) t ≠ 0 →
        worldDegree (worldDual s) =
          worldDegree (worldDual t) + n) := by
  exact ⟨
    fun A B s t => worldForward_dual_iff s t,
    fun A B s t => worldCausalDistance_dual_reverse s t,
    fun A B n s t => lefschetz_kernel_poincare_reciprocity s t,
    fun A B n s t h =>
      dual_transition_degree_balance s t h⟩

#check worldForward_dual_iff
#check carryDistance_dual_reverse
#check digitDistance_dual_reverse
#check worldCausalDistance_dual_reverse
#check lefschetz_kernel_poincare_reciprocity
#check nonzero_transition_dual_iff
#check dual_transition_time_exact
#check dual_transition_degree_balance
#check lefschetz_poincare_reciprocity_crown

#print axioms worldForward_dual_iff
#print axioms worldCausalDistance_dual_reverse
#print axioms lefschetz_kernel_poincare_reciprocity
#print axioms dual_transition_degree_balance
#print axioms lefschetz_poincare_reciprocity_crown

end GSTLefschetzPoincareReciprocity
