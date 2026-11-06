import Arsenal.ErdosTernary2.Basic
import Arsenal.CardinalWorlds
import Arsenal.CardinalWorldsV2

/-! ## THE ARSENAL BRIDGE (BOSS's mathematics, applied to #1056's witness
numbers). erdosternary2's digit predicates on the frontier prime's own
ternary digits: 52163 = (2211221222)₃ least-significant first. -/
theorem erdos1056_digits_52163 :
    [52163 % 3, (52163/3) % 3, (52163/9) % 3, (52163/27) % 3,
     (52163/81) % 3, (52163/243) % 3, (52163/729) % 3, (52163/2187) % 3,
     (52163/6561) % 3, (52163/19683) % 3] = [2, 2, 2, 2, 1, 1, 2, 2, 1, 2] := by
  decide

theorem erdos1056_arsenal_digit_validity :
    [2, 2, 2, 2, 1, 1, 2, 2, 1, 2].all (fun d => ErdosTernary2.isTernaryDigit d) := by
  decide

/-- The k = 11 first cut point 3924 routes through the arsenal's
residue trichotomy (`lt_three_cases`). -/
theorem erdos1056_ternary_routing (m : Nat) (h : m % 3 < 3) :
    m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 :=
  ErdosTernary2.lt_three_cases (m % 3) h

theorem erdos1056_cut3924_residue : 3924 % 3 = 0 := by
  have h : 3924 % 3 < 3 := by decide
  cases erdos1056_ternary_routing 3924 h with
  | inl h0 => exact h0
  | inr h => cases h with
    | inl h1 => exact absurd h1 (by decide)
    | inr h2 => exact absurd h2 (by decide)

/-- HC-PROOF's ternary-carry bound on the witness numbers: every carry
position of 3924 and 52161 under the ×4 ternary dynamics stays below 4. -/
theorem erdos1056_carry_bound_witness :
    carryAtPos 3924 1 < 4 ∧ carryAtPos 3924 2 < 4 ∧ carryAtPos 52161 1 < 4
      ∧ carryAtPos 52161 2 < 4 ∧ carryAtPos 52161 3 < 4 :=
  ⟨carryAtPos_bound 3924 1, carryAtPos_bound 3924 2, carryAtPos_bound 52161 1,
    carryAtPos_bound 52161 2, carryAtPos_bound 52161 3⟩

/-- HC-PROOF's dyadic scaling on the chain's own numbers: 52161 = 3·17387
and 7290 = 3·2430 leave their 2-adic profiles invariant. -/
theorem erdos1056_v2r_scaling : v2r 52161 = v2r 17387 ∧ v2r 7290 = v2r 2430 :=
  ⟨CardinalWorldsV2.v2r_ternary_scaling 1 17387,
    CardinalWorldsV2.v2r_ternary_scaling 1 2430⟩

#eval "FI_BRIDGE_GREEN"
#eval v2r 52161
#print axioms erdos1056_digits_52163
#print axioms erdos1056_carry_bound_witness
#print axioms erdos1056_v2r_scaling
