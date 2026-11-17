import GSTFourPowerDirectResidue

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
# Exact GST direct-hGate repair guard: dyadic multiplicity is not source purity

This isolates a FALSE upgrade of the stalled 3-step collision:
"if an integer R is highly divisible by 4, and R has a Happy gate
at p>=3, then 64*R also has a Happy gate at some row p>=3."

The original physical source is E=4^K (odd multiplier literally 1),
which is far stronger than 4^12 | E. Therefore the counterexample here
does not refute the genuine hGate theorem. It proves that any
repaired proof must actually exploit the exact 4^K source.
-/

namespace GSTProblem406DyadicShortcutNoGo

open GSTFourPowerDirectResidue

def nonPureSource : Nat := 4^12 * 100

/-- The synthetic source is in the correct mod-3 unit class
and divisible by a high power of 4; it is not a pure power. -/
theorem has_high_dyadic_source : 4^12 ∣ nonPureSource ∧
    nonPureSource % 3 = 1 := by
  constructor
  · exact ⟨100, rfl⟩
  · decide

/-- A real same-row two exists for (R,4R) at row 11. -/
theorem synthetic_child_happy :
    digit3 nonPureSource 11 = 2 ∧
    digit3 (4*nonPureSource) 11 = 2 := by
  decide

/-- But the triple-wave parent (64R,256R) never fires at any row >= 3,
including its entire finite terminal suffix. -/
theorem synthetic_parent_has_no_high_gate
    (p : Nat) (hp : 3 ≤ p) :
    ¬ (digit3 (64*nonPureSource) p = 2 ∧
       digit3 (256*nonPureSource) p = 2) := by
  by_cases hlow : p < 24
  · have hfinite : ∀ q : Fin 24,
        ¬ (digit3 (64*nonPureSource) q.val = 2 ∧
           digit3 (256*nonPureSource) q.val = 2) := by decide
    exact hfinite ⟨p, hlow⟩
  · have hsize : 64*nonPureSource < 3^24 := by decide
    have hpn : 24 ≤ p := by omega
    have hpow : 3^24 ≤ 3^p :=
      Nat.pow_le_pow_of_le (by decide : 1 < 3) hpn
    have hlt : 64*nonPureSource < 3^p := lt_of_lt_of_le hsize hpow
    have hz : digit3 (64*nonPureSource) p = 0 := by
      unfold digit3
      rw [Nat.div_eq_of_lt hlt]
    intro h
    omega

/-- Counterexample to a tempting but invalid replacement of the
missing source-specific 3-step GST collision. -/
theorem no_high_dyadic_only_propagation :
    ¬ (∀ R : Nat, 4^12 ∣ R → R%3=1 →
        (∃ p, 3 ≤ p ∧ digit3 R p=2 ∧ digit3 (4*R) p=2) →
        (∃ p, 3 ≤ p ∧ digit3 (64*R) p=2 ∧
            digit3 (256*R) p=2)) := by
  intro h
  have hsrc := has_high_dyadic_source
  obtain ⟨p, hp, hs, hn⟩ :=
    h nonPureSource hsrc.1 hsrc.2
      ⟨11, by decide, synthetic_child_happy.1,
       synthetic_child_happy.2⟩
  exact synthetic_parent_has_no_high_gate p hp ⟨hs,hn⟩

#print axioms has_high_dyadic_source
#print axioms synthetic_child_happy
#print axioms synthetic_parent_has_no_high_gate
#print axioms no_high_dyadic_only_propagation

end GSTProblem406DyadicShortcutNoGo
