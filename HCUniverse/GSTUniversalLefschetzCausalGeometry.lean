import Mathlib
import HCUniverse.GSTUniversalLefschetzKernel

/-!
# GST UNIVERSAL LEFSCHETZ CAUSAL GEOMETRY

The exact universal transition kernel carries more structure than a closed
matrix formula.  Its nonzero entries define an intrinsic causal order on every
finite GST world.

This file extracts that geometry directly from the already-proven kernel:

* every nonzero transition moves forward on both native axes;
* its time is uniquely the intrinsic causal distance;
* total world degree advances by exactly the transition time;
* two different times can never connect the same ordered pair;
* positive-time return to the same cell is impossible;
* bidirectional nonzero propagation is necessarily the trivial zero-time loop;
* every nonzero transition time is bounded by the remaining world depth.

No new carrier and no external geometric model is introduced.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000000

namespace GSTUniversalLefschetzCausalGeometry

open GSTWorldCosmology
open GSTGradedWorldAlgebra
open GSTTruncatedWorldCohomologyRing
open GSTWorldPoincareDuality
open GSTUniversalLefschetzKernel

/-- The native forward relation is reflexive. -/
theorem worldForward_refl
    {A B : Nat} (s : WorldCell A B) :
    worldForward s s := by
  exact ⟨le_rfl, le_rfl⟩

/-- The native forward relation is transitive. -/
theorem worldForward_trans
    {A B : Nat} {r s t : WorldCell A B}
    (hrs : worldForward r s)
    (hst : worldForward s t) :
    worldForward r t := by
  exact ⟨le_trans hrs.1 hst.1, le_trans hrs.2 hst.2⟩

/-- The native forward relation is antisymmetric, hence it is an exact
partial order on GST cells. -/
theorem worldForward_antisymm
    {A B : Nat} {s t : WorldCell A B}
    (hst : worldForward s t)
    (hts : worldForward t s) :
    s = t := by
  rcases s with ⟨⟨Cs,hCs⟩,⟨ds,hds⟩⟩
  rcases t with ⟨⟨Ct,hCt⟩,⟨dt,hdt⟩⟩
  unfold worldForward at hst hts
  apply Prod.ext
  · apply Fin.ext
    omega
  · apply Fin.ext
    omega

/-- Causal distance from a cell to itself is zero. -/
@[simp]
theorem worldCausalDistance_self
    {A B : Nat} (s : WorldCell A B) :
    worldCausalDistance s s = 0 := by
  simp [worldCausalDistance, carryDistance, digitDistance]

/-- Causal distance is additive along an ordered chain. -/
theorem worldCausalDistance_add
    {A B : Nat} {r s t : WorldCell A B}
    (hrs : worldForward r s)
    (hst : worldForward s t) :
    worldCausalDistance r t =
      worldCausalDistance r s + worldCausalDistance s t := by
  rcases r with ⟨⟨Cr,hCr⟩,⟨dr,hdr⟩⟩
  rcases s with ⟨⟨Cs,hCs⟩,⟨ds,hds⟩⟩
  rcases t with ⟨⟨Ct,hCt⟩,⟨dt,hdt⟩⟩
  unfold worldForward at hrs hst
  unfold worldCausalDistance carryDistance digitDistance
  omega

/-- **EXACT DEGREE ADVANCE.**
Every nonzero n-step Lefschetz transition advances total world degree by
exactly n. -/
theorem nonzero_transition_degree_exact
    {A B n : Nat} (s t : WorldCell A B)
    (hne :
      worldAct A B ((L A B)^n) (worldBasis s) t ≠ 0) :
    worldDegree t = worldDegree s + n := by
  obtain ⟨hforward, htime⟩ :=
    nonzero_lefschetz_transition_forces_causality s t hne
  rcases s with ⟨⟨Cs,hCs⟩,⟨ds,hds⟩⟩
  rcases t with ⟨⟨Ct,hCt⟩,⟨dt,hdt⟩⟩
  unfold worldForward at hforward
  unfold worldCausalDistance carryDistance digitDistance at htime
  unfold worldDegree
  omega

/-- **UNIQUE TRANSITION TIME.**
The same ordered source/target pair cannot carry nonzero Lefschetz
coefficients at two different times. -/
theorem nonzero_transition_time_unique
    {A B m n : Nat} (s t : WorldCell A B)
    (hm :
      worldAct A B ((L A B)^m) (worldBasis s) t ≠ 0)
    (hn :
      worldAct A B ((L A B)^n) (worldBasis s) t ≠ 0) :
    m = n := by
  have hm' :=
    (nonzero_lefschetz_transition_forces_causality s t hm).2
  have hn' :=
    (nonzero_lefschetz_transition_forces_causality s t hn).2
  omega

/-- Exact return kernel: the only self-transition is the identity at time 0. -/
theorem lefschetz_self_transition_kernel
    {A B n : Nat} (s : WorldCell A B) :
    worldAct A B ((L A B)^n) (worldBasis s) s =
      if n = 0 then 1 else 0 := by
  rw [worldAct_L_pow_basis_kernel]
  simp [worldForward_refl, worldCausalDistance_self,
    digitDistance, carryDistance]

/-- Positive-time recurrence to the same cell is impossible. -/
theorem positive_time_no_return
    {A B n : Nat} (s : WorldCell A B)
    (hn : 0 < n) :
    worldAct A B ((L A B)^n) (worldBasis s) s = 0 := by
  rw [lefschetz_self_transition_kernel]
  simp [show n ≠ 0 by omega]

/-- **NO NONTRIVIAL CAUSAL CYCLES.**
If there are nonzero transitions in both directions, both cells coincide and
both transition times are zero. -/
theorem bidirectional_nonzero_transition_trivial
    {A B m n : Nat} (s t : WorldCell A B)
    (hst :
      worldAct A B ((L A B)^m) (worldBasis s) t ≠ 0)
    (hts :
      worldAct A B ((L A B)^n) (worldBasis t) s ≠ 0) :
    s = t ∧ m = 0 ∧ n = 0 := by
  have hst' :=
    nonzero_lefschetz_transition_forces_causality s t hst
  have hts' :=
    nonzero_lefschetz_transition_forces_causality t s hts
  have heq : s = t :=
    worldForward_antisymm hst'.1 hts'.1
  subst t
  simp only [worldCausalDistance_self] at hst' hts'
  exact ⟨rfl, hst'.2, hts'.2⟩

/-- Transition times add along any composable nonzero causal chain. -/
theorem nonzero_chain_degree_add
    {A B m n : Nat} (r s t : WorldCell A B)
    (hrs :
      worldAct A B ((L A B)^m) (worldBasis r) s ≠ 0)
    (hst :
      worldAct A B ((L A B)^n) (worldBasis s) t ≠ 0) :
    worldDegree t = worldDegree r + (m+n) := by
  have h1 := nonzero_transition_degree_exact r s hrs
  have h2 := nonzero_transition_degree_exact s t hst
  omega

/-- Every live transition time is bounded by the remaining total depth of
its source cell. -/
theorem nonzero_transition_time_bounded
    {A B n : Nat} (s t : WorldCell A B)
    (hne :
      worldAct A B ((L A B)^n) (worldBasis s) t ≠ 0) :
    n ≤ A+B-2 - worldDegree s := by
  have hdeg := nonzero_transition_degree_exact s t hne
  have htop := worldDegree_le_top t
  omega

/-- Capstone: the exact kernel induces a graded acyclic causal geometry on
every rectangular GST world. -/
theorem universal_lefschetz_causal_crown :
    (∀ A B n (s t : WorldCell A B),
      worldAct A B ((L A B)^n) (worldBasis s) t ≠ 0 →
        worldDegree t = worldDegree s + n)
    ∧ (∀ A B m n (s t : WorldCell A B),
      worldAct A B ((L A B)^m) (worldBasis s) t ≠ 0 →
      worldAct A B ((L A B)^n) (worldBasis s) t ≠ 0 →
        m = n)
    ∧ (∀ A B n (s : WorldCell A B), 0 < n →
      worldAct A B ((L A B)^n) (worldBasis s) s = 0)
    ∧ (∀ A B m n (s t : WorldCell A B),
      worldAct A B ((L A B)^m) (worldBasis s) t ≠ 0 →
      worldAct A B ((L A B)^n) (worldBasis t) s ≠ 0 →
        s = t ∧ m = 0 ∧ n = 0) := by
  exact ⟨
    fun A B n s t h =>
      nonzero_transition_degree_exact s t h,
    fun A B m n s t hm hn =>
      nonzero_transition_time_unique s t hm hn,
    fun A B n s hn =>
      positive_time_no_return s hn,
    fun A B m n s t hst hts =>
      bidirectional_nonzero_transition_trivial s t hst hts⟩

#check worldForward_refl
#check worldForward_trans
#check worldForward_antisymm
#check worldCausalDistance_self
#check worldCausalDistance_add
#check nonzero_transition_degree_exact
#check nonzero_transition_time_unique
#check lefschetz_self_transition_kernel
#check positive_time_no_return
#check bidirectional_nonzero_transition_trivial
#check nonzero_chain_degree_add
#check nonzero_transition_time_bounded
#check universal_lefschetz_causal_crown

#print axioms worldForward_antisymm
#print axioms worldCausalDistance_add
#print axioms nonzero_transition_degree_exact
#print axioms bidirectional_nonzero_transition_trivial
#print axioms nonzero_transition_time_bounded
#print axioms universal_lefschetz_causal_crown

end GSTUniversalLefschetzCausalGeometry
