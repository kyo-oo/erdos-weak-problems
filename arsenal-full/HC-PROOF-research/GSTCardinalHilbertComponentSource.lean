import GSTCardinalSimultaneousOriginalXCompiler
import Mathlib

/-!
# GST connected cardinal topology: actual-cycle parameter-component compression

The user's cardinal/topological sources must live on the SAME original X.

Pure-algebra compiler inputs:
I = true algebraic-source parameter set (Hilbert points in geometry);
C = topological connected components of those parameter spaces;
A = actual rational Chow classes of the original X;
B = rational Hodge classes of X;
cycleClass = canonical rational Betti class map.

The input class_constant is the geometric theorem: members of the same
connected flat Hilbert-family component have identical Betti cycle classes.
This Lean module checks logical consequences, not that external theorem.

No Hodge surjectivity, target Chow inverse, or untyped infinite Chow sum.
-/

set_option maxHeartbeats 1500000
noncomputable section

namespace GSTCardinalHilbertComponentSource

universe u v w z
variable {I : Type u} {C : Type v} {A : Type w} {B : Type z}
variable [AddCommGroup A] [Module ℚ A]
variable [AddCommGroup B] [Module ℚ B]

structure ParameterSource (I : Type u) (C : Type v)
    (A : Type w) (B : Type z)
    [AddCommGroup A] [Module ℚ A]
    [AddCommGroup B] [Module ℚ B] where
  cycleClass : A →ₗ[ℚ] B
  nativeCycle : I → A
  component : I → C
  representative : C → I
  representative_component : ∀ c : C, component (representative c) = c
  class_constant :
    ∀ i j : I, component i = component j →
      cycleClass (nativeCycle i) = cycleClass (nativeCycle j)

namespace ParameterSource

variable (P : ParameterSource I C A B)

def sourceClass (i : I) : B := P.cycleClass (P.nativeCycle i)

theorem class_of_component (i : I) :
    P.sourceClass i =
      P.sourceClass (P.representative (P.component i)) := by
  exact P.class_constant i (P.representative (P.component i))
    (P.representative_component (P.component i)).symm

/-- Even arbitrary-cardinal many algebraic-source parameters have exactly
the same rational Hodge CLASS SPAN as one representative from each
connected Hilbert component. This does not assume universal Hodge. -/
theorem parameter_span_eq_component_span :
    Submodule.span ℚ (Set.range P.sourceClass) =
    Submodule.span ℚ
      (Set.range (fun c : C => P.sourceClass (P.representative c))) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro y ⟨i, rfl⟩
    rw [P.class_of_component i]
    exact Submodule.subset_span
      (Set.mem_range_self (P.component i))
  · apply Submodule.span_le.mpr
    rintro y ⟨c, rfl⟩
    exact Submodule.subset_span
      (Set.mem_range_self (P.representative c))

/-- Pure topological navigation inside one connected Hilbert component
cannot generate a new original-X rational Hodge class. -/
theorem no_new_class_inside_component
    (i j : I) (h : P.component i = P.component j) :
    P.sourceClass i = P.sourceClass j :=
  P.class_constant i j h

/-- A genuinely fresh algebraic Hodge source cannot lie in one of the
previously exhausted topological source components. -/
theorem fresh_requires_new_component
    (old : Set C) (L : Submodule ℚ B)
    (hOld : ∀ c ∈ old,
      P.sourceClass (P.representative c) ∈ L)
    (i : I) (hFresh : P.sourceClass i ∉ L) :
    P.component i ∉ old := by
  intro hi
  apply hFresh
  rw [P.class_of_component i]
  exact hOld (P.component i) hi

end ParameterSource

#check ParameterSource.parameter_span_eq_component_span
#check ParameterSource.no_new_class_inside_component
#check ParameterSource.fresh_requires_new_component
#print axioms ParameterSource.parameter_span_eq_component_span
#print axioms ParameterSource.no_new_class_inside_component
#print axioms ParameterSource.fresh_requires_new_component

end GSTCardinalHilbertComponentSource
