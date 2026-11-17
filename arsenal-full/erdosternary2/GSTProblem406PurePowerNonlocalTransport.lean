import GSTFourPowerDirectResidue
import Mathlib

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
# GST 406: exact pure-power three-step transport, all finite horizons

The universal global target is NOT modified. This file derives a new
non-circular structural constraint on attempts to close the missing
`power_three_step_collision` by a bounded observation window.

The actual pure-power child 4^8 has a Happy row 4. The actual
parent 4^11 is BAD on rows 1..9. The exact GST exponent-trit
lift permits arbitrarily extending the *parent's* BAD prefix
while keeping the child's row-4 Happy.

The mechanism is entirely symbolic: for any p, the exponent
trit a∈{0,1,2} can make the physical source digit at p+1 zero,
while leaving all earlier physical digits unchanged. Thus
NO uniformly bounded observation window after a Child Happy
can force a Parent Happy, even when the source is exactly 4^K.

This does NOT refute the original all-depth proposition, and
does NOT assert a true perfect-power parent remains BAD forever.
It isolates the genuinely nonlocal, source-specific arithmetic
requirement that must close the old Lean `sorryAx` proof seam.
-/

namespace GSTProblem406PurePowerNonlocalTransport

open GSTFourPowerDirectResidue

def ChildHappyAtFour (K : Nat) : Prop :=
  digit3 (4^K) 4 = 2 ∧
  digit3 (4^(K+1)) 4 = 2

def ParentBadThrough (K H : Nat) : Prop :=
  ∀ j : Nat, 1 ≤ j → j ≤ H →
    ¬ (digit3 (4^(K+3)) j = 2 ∧
       digit3 (4^((K+3)+1)) j = 2)

/-- An exact exponent shift at scale 3^p does not alter ANY
physical ternary digit below or at row p. -/
theorem exponent_trit_preserves_lower_rows
    (p K a j : Nat) (hj : j ≤ p) :
    digit3 (4^(K + a*3^p)) j = digit3 (4^K) j := by
  have hpow : 3^p = 3^j * 3^(p-j) := by
    conv_lhs => rw [show p = j+(p-j) by omega]
    rw [pow_add]
  have hExp : K + a*3^p =
      K + 3^j*(3^(p-j)*a) := by
    rw [hpow]
    ring
  rw [hExp]
  exact pow4_digit_period j K (3^(p-j)*a)

/-- At any exponent and any row p+1, one of the three
exponent trits makes the physical SOURCE digit equal ZERO.
This excludes a simultaneous (2,2) at that row exactly. -/
theorem choose_exponent_trit_source_zero
    (p K : Nat) :
    ∃ a : Nat, a < 3 ∧
      digit3 (4^(K+a*3^p)) (p+1) = 0 := by
  let d := digit3 (4^K) (p+1)
  let a := (3-d) % 3
  have hd : d < 3 := by
    dsimp [d, digit3]
    exact Nat.mod_lt _ (by decide)
  have ha : a < 3 := Nat.mod_lt _ (by decide)
  refine ⟨a, ha, ?_⟩
  rw [pow4_exponent_trit_lift_digit p K a ha]
  dsimp [a]
  omega

/-- Base of the genuine 3-step source-neighbor audit:
4^8 has a physical Happy row at p=4, while 4^11
and 4^12 have no same-row two at any p≤9. -/
theorem true_child_eight_parent_eleven_seed :
    ChildHappyAtFour 8 ∧ ParentBadThrough 8 9 := by
  constructor
  · unfold ChildHappyAtFour
    decide
  · intro j hj hBound
    have hfinite : ∀ j : Fin 10, 1 ≤ j.val →
      ¬ (digit3 (4^(8+3)) j.val = 2 ∧
         digit3 (4^((8+3)+1)) j.val = 2) := by decide
    exact hfinite ⟨j, by omega⟩ hj

/-- One exact GST exponent-trit extension. Preserves a real
child Happy at p=4, all earlier parent BAD rows, and forces
the next parent row to be BAD by making its source digit zero. -/
theorem extend_pure_power_bad_parent
    (p K : Nat) (hp : 9 ≤ p)
    (hchild : ChildHappyAtFour K)
    (hbad : ParentBadThrough K p) :
    ∃ K' : Nat, K ≤ K' ∧
      ChildHappyAtFour K' ∧
      ParentBadThrough K' (p+1) := by
  obtain ⟨a, ha, hzero⟩ :=
    choose_exponent_trit_source_zero p (K+3)
  let K' := K + a*3^p
  have hChild0 :
      digit3 (4^K') 4 = digit3 (4^K) 4 := by
    dsimp [K']
    exact exponent_trit_preserves_lower_rows p K a 4 (by omega)
  have hChild1 :
      digit3 (4^(K'+1)) 4 = digit3 (4^(K+1)) 4 := by
    have he : K'+1 = (K+1)+a*3^p := by dsimp [K']; omega
    rw [he]
    exact exponent_trit_preserves_lower_rows p (K+1) a 4 (by omega)
  have hRight0 (j : Nat) (hj : j ≤ p) :
      digit3 (4^(K'+3)) j = digit3 (4^(K+3)) j := by
    have he : K'+3=(K+3)+a*3^p := by dsimp [K']; omega
    rw [he]
    exact exponent_trit_preserves_lower_rows p (K+3) a j hj
  have hRight1 (j : Nat) (hj : j ≤ p) :
      digit3 (4^((K'+3)+1)) j =
        digit3 (4^((K+3)+1)) j := by
    have he : (K'+3)+1=((K+3)+1)+a*3^p := by dsimp [K']; omega
    rw [he]
    exact exponent_trit_preserves_lower_rows p ((K+3)+1) a j hj
  have hzeroRight :
      digit3 (4^(K'+3)) (p+1)=0 := by
    have he : K'+3=(K+3)+a*3^p := by dsimp [K']; omega
    rw [he]
    exact hzero
  refine ⟨K', by dsimp [K']; omega,
    ⟨hChild0.trans hchild.1, hChild1.trans hchild.2⟩, ?_⟩
  intro j hj hmax hpair
  by_cases hlow : j ≤ p
  · have hBadOld := hbad j hj hlow
    apply hBadOld
    exact ⟨(hRight0 j hlow).symm.trans hpair.1,
      (hRight1 j hlow).symm.trans hpair.2⟩
  · have hjTop : j=p+1 := by omega
    rw [hjTop] at hpair
    omega

/-- Arbitrarily long BAD parent prefixes remain possible for
literal positive powers 4^K, even with a fixed child
Happy row p=4. This is an ALL-H exact induction. -/
theorem arbitrary_pure_power_parent_bad_prefix
    (H : Nat) (hH : 9 ≤ H) :
    ∃ K : Nat, 8 ≤ K ∧
      ChildHappyAtFour K ∧ ParentBadThrough K H := by
  have hN : ∀ n : Nat,
      ∃ K : Nat, 8 ≤ K ∧ ChildHappyAtFour K ∧
        ParentBadThrough K (9+n) := by
    intro n
    induction n with
    | zero =>
        refine ⟨8, by decide, ?_, ?_⟩
        · exact true_child_eight_parent_eleven_seed.1
        · simpa using true_child_eight_parent_eleven_seed.2
    | succ n ih =>
        obtain ⟨K, hK, hc, hb⟩ := ih
        obtain ⟨K', hKK', hc', hb'⟩ :=
          extend_pure_power_bad_parent (9+n) K (by omega) hc hb
        refine ⟨K', by omega, hc', ?_⟩
        simpa [Nat.add_assoc] using hb'
  obtain ⟨K, hK, hc, hb⟩ := hN (H-9)
  have hident : 9+(H-9)=H := by omega
  refine ⟨K,hK,hc,?_⟩
  simpa only [hident] using hb

/-- No UNIFORM finite future window can prove the three-step
collision on a true 4^K source from the child row-4 event.
Any valid source-specific contradiction must use more information
than a fixed-size local GST window. -/
theorem no_uniform_bounded_three_step_reappearance :
    ¬ (∃ B : Nat, ∀ K : Nat, 8 ≤ K →
      ChildHappyAtFour K →
        ∃ j : Nat, 1 ≤ j ∧ j ≤ B+9 ∧
          digit3 (4^(K+3)) j=2 ∧
          digit3 (4^((K+3)+1)) j=2) := by
  rintro ⟨B, hB⟩
  obtain ⟨K,hK,hchild,hbad⟩ :=
    arbitrary_pure_power_parent_bad_prefix (B+9) (by omega)
  obtain ⟨j,hj,hbound,hsrc,hnbr⟩ := hB K hK hchild
  exact hbad j hj hbound ⟨hsrc,hnbr⟩

#print axioms exponent_trit_preserves_lower_rows
#print axioms choose_exponent_trit_source_zero
#print axioms true_child_eight_parent_eleven_seed
#print axioms extend_pure_power_bad_parent
#print axioms arbitrary_pure_power_parent_bad_prefix
#print axioms no_uniform_bounded_three_step_reappearance

end GSTProblem406PurePowerNonlocalTransport
