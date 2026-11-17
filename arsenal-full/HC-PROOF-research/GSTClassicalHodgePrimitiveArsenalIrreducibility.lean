import GSTClassicalHodgeExplicitArsenalGeneration

/-!
# GST CLASSICAL HODGE — PRIMITIVE ARSENAL IRREDUCIBILITY

The full matrix-unit invariance condition is stronger than the geometric
input we actually need.  The previous module proves every matrix unit is an
explicit word in three primitive GST operations:

* sheet projector;
* universal Lefschetz power;
* square-world Poincare reversal.

This module proves that invariance under those primitive operators already
implies full matrix-unit invariance and therefore irreducibility.  The
classical externalization problem is reduced to naturality of the genuine GST
primitive arsenal, rather than naturality of arbitrary coordinate operators.
-/

set_option maxHeartbeats 30000000
set_option maxRecDepth 1000000

noncomputable section

open GSTClassicalHodgeFullArsenalIrreducibility
open GSTClassicalHodgeExplicitArsenalGeneration

namespace GSTClassicalHodgePrimitiveArsenalIrreducibility

/-- Stability under the actual primitive finite-window GST operators. -/
def PrimitiveArsenalInvariant
    {N : Nat} (S : Submodule ℚ (RationalPureWindow N)) : Prop :=
  (∀ p : Fin N, ∀ a ∈ S, sheetProjectorQ p a ∈ S)
  ∧ (∀ t : Nat, ∀ a ∈ S, diagonalLefschetzQ N t a ∈ S)
  ∧ (∀ a ∈ S, poincareReverseQ N a ∈ S)

namespace PrimitiveArsenalInvariant

variable {N : Nat} {S : Submodule ℚ (RationalPureWindow N)}

/-- Stability is closed under composition of two operators that preserve S. -/
theorem comp_mem
    {A B : Module.End ℚ (RationalPureWindow N)}
    (hA : ∀ a ∈ S, A a ∈ S)
    (hB : ∀ a ∈ S, B a ∈ S) :
    ∀ a ∈ S, (A.comp B) a ∈ S := by
  intro a ha
  exact hA (B a) (hB a ha)

/-- Rational rescaling of a preserving operator still preserves S. -/
theorem smul_mem
    {A : Module.End ℚ (RationalPureWindow N)}
    (hA : ∀ a ∈ S, A a ∈ S)
    (c : ℚ) :
    ∀ a ∈ S, (c • A) a ∈ S := by
  intro a ha
  exact S.smul_mem c (hA a ha)

/-- Every raw forward GST word preserves a primitive-arsenal invariant
submodule. -/
theorem rawForwardWord_mem
    (h : PrimitiveArsenalInvariant S)
    (p q : Fin N) :
    ∀ a ∈ S, rawForwardWord p q a ∈ S := by
  rcases h with ⟨hproj, hL, hP⟩
  intro a ha
  unfold rawForwardWord
  exact comp_mem (hproj q)
    (comp_mem (hL (2 * GSTPureHodgeLefschetzKernel.pureWeightGap
      (Fin.castLE (show N ≤ min N N by omega) p)
      (Fin.castLE (show N ≤ min N N by omega) q))) (hproj p)) a ha

/-- Every normalized forward word preserves S. -/
theorem forwardArsenalWord_mem
    (h : PrimitiveArsenalInvariant S)
    (p q : Fin N) :
    ∀ a ∈ S, forwardArsenalWord p q a ∈ S := by
  exact smul_mem (rawForwardWord_mem h p q) (forwardScalar p q : ℚ)⁻¹

/-- Poincare conjugation preserves S whenever the middle operator does. -/
theorem poincareConjugate_mem
    (h : PrimitiveArsenalInvariant S)
    {T : Module.End ℚ (RationalPureWindow N)}
    (hT : ∀ a ∈ S, T a ∈ S) :
    ∀ a ∈ S, poincareConjugate T a ∈ S := by
  rcases h with ⟨_, _, hP⟩
  intro a ha
  exact hP _ (hT _ (hP a ha))

/-- Every backward GST word preserves S. -/
theorem backwardArsenalWord_mem
    (h : PrimitiveArsenalInvariant S)
    (p q : Fin N) :
    ∀ a ∈ S, backwardArsenalWord p q a ∈ S := by
  exact poincareConjugate_mem h
    (forwardArsenalWord_mem h (mirrorFin p) (mirrorFin q))

/-- **PRIMITIVE ARSENAL ⇒ FULL MATRIX-UNIT ARSENAL.** -/
theorem fullArsenalInvariant
    (h : PrimitiveArsenalInvariant S) :
    FullArsenalInvariant S := by
  intro p q a ha
  rcases matrixUnit_generated_by_GST_arsenal p q with hforward | hback
  · rcases hforward with ⟨hpq, hEq⟩
    rw [← hEq]
    exact forwardArsenalWord_mem h p q a ha
  · rcases hback with ⟨hqp, hEq⟩
    rw [← hEq]
    exact backwardArsenalWord_mem h p q a ha

end PrimitiveArsenalInvariant

/-- **PRIMITIVE GST ARSENAL IRREDUCIBILITY.**
A nonzero submodule stable only under projector/Lefschetz/Poincare is already
the full finite pure-Hodge window. -/
theorem primitiveArsenalInvariant_eq_top
    {N : Nat}
    (S : Submodule ℚ (RationalPureWindow N))
    (hprimitive : PrimitiveArsenalInvariant S)
    (hne : S ≠ ⊥) :
    S = ⊤ :=
  fullArsenalInvariant_eq_top S hprimitive.fullArsenalInvariant hne

/-- Primitive-arena zero-or-top dichotomy. -/
theorem primitiveArsenalInvariant_bot_or_top
    {N : Nat}
    (S : Submodule ℚ (RationalPureWindow N))
    (hprimitive : PrimitiveArsenalInvariant S) :
    S = ⊥ ∨ S = ⊤ :=
  fullArsenalInvariant_bot_or_top S hprimitive.fullArsenalInvariant

/-- One nonzero primitive-stable seed generates every finite pure sheet. -/
theorem every_basis_from_primitive_seed
    {N : Nat}
    (S : Submodule ℚ (RationalPureWindow N))
    (hprimitive : PrimitiveArsenalInvariant S)
    {a : RationalPureWindow N}
    (haS : a ∈ S) (ha0 : a ≠ 0) :
    ∀ q : Fin N, rationalPureBasis q ∈ S :=
  every_basis_from_nonzero_seed S hprimitive.fullArsenalInvariant haS ha0

/-- Crown: finite Hodge irreducibility is driven by the three primitive GST
operators, with matrix units derived rather than postulated. -/
theorem primitive_arsenal_irreducibility_crown :
    ∀ N (S : Submodule ℚ (RationalPureWindow N)),
      PrimitiveArsenalInvariant S → S ≠ ⊥ → S = ⊤ :=
  fun _ S hs hn => primitiveArsenalInvariant_eq_top S hs hn

#check PrimitiveArsenalInvariant
#check PrimitiveArsenalInvariant.fullArsenalInvariant
#check primitiveArsenalInvariant_eq_top
#check every_basis_from_primitive_seed
#check primitive_arsenal_irreducibility_crown

#print axioms PrimitiveArsenalInvariant.fullArsenalInvariant
#print axioms primitiveArsenalInvariant_eq_top
#print axioms every_basis_from_primitive_seed
#print axioms primitive_arsenal_irreducibility_crown

end GSTClassicalHodgePrimitiveArsenalIrreducibility
