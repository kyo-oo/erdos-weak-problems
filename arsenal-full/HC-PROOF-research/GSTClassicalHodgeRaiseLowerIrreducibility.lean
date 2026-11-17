import GSTClassicalHodgeTwoGeneratorLefschetzPoincareGeneration

/-!
# GST CLASSICAL HODGE — RAISE/LOWER IRREDUCIBILITY

The finite pure-Hodge matrix algebra does not need Poincare reversal as a
primitive geometric operator.  Once the normalized Lefschetz raising shift
`U` and the exact lowering shift `D` both preserve a submodule, the endpoint
projector

  Pi_0 = I - U D

also preserves it.  Hence every matrix unit

  E_ij = U^j Pi_0 D^i

preserves it.  A nonzero raise/lower-stable submodule is therefore the whole
pure-Hodge window.

This is the form needed for genuine correspondence geometry: one can realize
`U` by a projective incidence action and `D` by its genuine algebraic
transpose, without first externalizing Poincare reversal itself.
-/

set_option maxHeartbeats 60000000
set_option maxRecDepth 1000000

noncomputable section

open GSTGlobalPureHodgeCosmology
open GSTClassicalHodgeFullArsenalIrreducibility
open GSTClassicalHodgeTwoGeneratorLefschetzPoincareGeneration

namespace GSTClassicalHodgeRaiseLowerIrreducibility

/-- Stability under the two one-step operators themselves. -/
def RaiseLowerInvariant
    {N : Nat} (S : Submodule ℚ (RationalPureWindow N)) : Prop :=
  (∀ a ∈ S, raiseQ N a ∈ S) ∧
    (∀ a ∈ S, lowerQ N a ∈ S)

/-- Raise/lower stability supplies every finite pure-Hodge matrix unit. -/
theorem fullArsenalInvariant_of_raiseLower
    {N : Nat} (S : Submodule ℚ (RationalPureWindow N))
    (h : RaiseLowerInvariant S) :
    FullArsenalInvariant S := by
  rcases h with ⟨hU, hD⟩
  have hiterU : ∀ n a, a ∈ S → iterEnd (raiseQ N) n a ∈ S := by
    intro n
    induction n with
    | zero => intro a ha; simpa using ha
    | succ n ih => intro a ha; exact hU _ (ih a ha)
  have hiterD : ∀ n a, a ∈ S → iterEnd (lowerQ N) n a ∈ S := by
    intro n
    induction n with
    | zero => intro a ha; simpa using ha
    | succ n ih => intro a ha; exact hD _ (ih a ha)
  have hPi0 : ∀ a ∈ S, bottomProjectorFromLP N a ∈ S := by
    intro a ha
    unfold bottomProjectorFromLP
    exact S.sub_mem ha (hU _ (hD a ha))
  intro i j a ha
  rw [← twoGeneratorMatrixUnit_eq i j]
  unfold twoGeneratorMatrixUnit
  exact hiterU j.1 _ (hPi0 _ (hiterD i.1 a ha))

/-- **RAISE/LOWER IRREDUCIBILITY.**
A nonzero submodule stable under the exact raising and lowering shifts is the
entire rational pure-Hodge window. -/
theorem raiseLowerInvariant_eq_top
    {N : Nat} (S : Submodule ℚ (RationalPureWindow N))
    (h : RaiseLowerInvariant S)
    (hne : S ≠ ⊥) :
    S = ⊤ :=
  fullArsenalInvariant_eq_top S
    (fullArsenalInvariant_of_raiseLower S h) hne

/-- Compact crown used by the geometric realization layer. -/
theorem raise_lower_irreducibility_crown :
    ∀ N (S : Submodule ℚ (RationalPureWindow N)),
      RaiseLowerInvariant S → S ≠ ⊥ → S = ⊤ :=
  fun _ S hS hne => raiseLowerInvariant_eq_top S hS hne

#check RaiseLowerInvariant
#check fullArsenalInvariant_of_raiseLower
#check raiseLowerInvariant_eq_top
#check raise_lower_irreducibility_crown

#print axioms fullArsenalInvariant_of_raiseLower
#print axioms raiseLowerInvariant_eq_top
#print axioms raise_lower_irreducibility_crown

end GSTClassicalHodgeRaiseLowerIrreducibility
