import GSTFourPowerDirectResidue

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
# GST exact ternary exponent-child permutation

The GST LTE digit-lift implies that the three children of any exponent
prefix have different next ternary digits in 4^K. This is a local
unconditional, proof-relevant step behind the exact 2^L Cantor dust tree.
It is not the missing terminal theorem about eventually-zero K.
-/

namespace GSTWorldtraceFiniteDust

open GSTFourPowerDirectResidue

/-- The next-row digit distinguishes all three exponent-trit children. -/
theorem child_top_trit_injective
    (p r a b : Nat) (ha : a < 3) (hb : b < 3) :
    (digit3 (4^(r+a*3^p)) (p+1) =
      digit3 (4^(r+b*3^p)) (p+1)) ↔ a = b := by
  rw [pow4_exponent_trit_lift_digit p r a ha,
      pow4_exponent_trit_lift_digit p r b hb]
  have hd : digit3 (4^r) (p+1) < 3 := by
    unfold digit3
    exact Nat.mod_lt _ (by decide)
  constructor
  · intro h
    omega
  · intro h
    rw [h]

/-- At every node exactly one exponent-trit child has a top digit two. -/
theorem exactly_one_dead_child (p r : Nat) :
    ∃ a : Nat, a < 3 ∧
      digit3 (4^(r+a*3^p)) (p+1) = 2 ∧
      ∀ b : Nat, b < 3 →
        digit3 (4^(r+b*3^p)) (p+1) = 2 → b = a := by
  let d := digit3 (4^r) (p+1)
  have hd : d < 3 := by
    dsimp [d, digit3]
    exact Nat.mod_lt _ (by decide)
  let a := (5-d)%3
  have ha : a < 3 := by
    dsimp [a]
    exact Nat.mod_lt _ (by decide)
  have hval : (d+a)%3=2 := by
    dsimp [a]
    omega
  have hcert : digit3 (4^(r+a*3^p)) (p+1) = 2 := by
    rw [pow4_exponent_trit_lift_digit p r a ha]
    exact hval
  refine ⟨a, ha, hcert, ?_⟩
  intro b hb hbcert
  exact (child_top_trit_injective p r b a hb ha).1 (by
    rw [hbcert, hcert])

#print axioms child_top_trit_injective
#print axioms exactly_one_dead_child

end GSTWorldtraceFiniteDust
