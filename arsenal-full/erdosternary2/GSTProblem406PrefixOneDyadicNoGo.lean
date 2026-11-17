import GSTGraphV2InfiniteControl
import Mathlib

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
# Mathbox: exact 3-step collision countermodel with prefix ONE and high dyadic order

This attacks ONLY a false auxiliary claim, not the original theorem.
The exact-power source E=4^K has odd cofactor 1.

Here E = 4339*2^24:
 E mod 27 = 1, 2^24 | E,
 a true child Happy at ternary row 3,
 and its literal width-three parent 64*E is BAD at EVERY row.

This disproves deriving the final 3-step contradiction from
prefix-one + high v2 + GST local/terminal conservation alone,
without the exact cofactor-one pure-power origin.
-/

namespace GSTProblem406PrefixOneDyadicNoGo

open GSTCanonicalSevenAxisBridge
open GSTU2DEventTransport
open GSTGraphV2InfiniteControl

def sourceE : Nat := 4339 * 2^24
def badParent : Nat := 64 * sourceE

theorem exact_source_fingerprint :
    sourceE = 72796340224 ∧
    badParent = 4658965774336 ∧
    sourceE % 27 = 1 ∧
    (2:Nat)^24 ∣ sourceE ∧
    0 < badParent ∧ badParent < 3^30 := by
  constructor
  · decide
  constructor
  · decide
  constructor
  · decide
  constructor
  · refine ⟨4339, ?_⟩
    norm_num [sourceE]
  · decide

/-- Physical child at row 3 is a genuine shared-two Happy cell. -/
theorem genuine_child_happy :
    HappyCell (graph sourceE 0 3).seven.carry
      (graph sourceE 0 3).seven.digit := by
  unfold HappyCell
  decide

/-- The 64-multiple is BAD at every row, including all heights
above its full finite ternary expansion. -/
theorem bad_parent_at_every_row (p : Nat) :
    ¬ HappyCell (graph sourceE 3 p).seven.carry
        (graph sourceE 3 p).seven.digit := by
  by_cases hp : p < 30
  · have hfinite : ∀ q : Fin 30,
      ¬ HappyCell (graph sourceE 3 q.val).seven.carry
          (graph sourceE 3 q.val).seven.digit := by
        unfold HappyCell
        decide
    exact hfinite ⟨p, hp⟩
  · have hbound : badParent < 3^p :=
      lt_of_lt_of_le exact_source_fingerprint.2.2.2.2.2
        (Nat.pow_le_pow_of_le (by decide : 1 < (3:Nat)) (by omega))
    have hzero : GSTCanonicalSevenAxisBridge.digit3 badParent p=0 := by
      unfold GSTCanonicalSevenAxisBridge.digit3
      rw [Nat.div_eq_of_lt hbound]
    have hparent :
      (graph sourceE 3 p).seven.digit =
        GSTCanonicalSevenAxisBridge.digit3 badParent p := by
      simp [graph, cell, GSTCanonicalSevenAxisBridge.vertex,
        badParent, show (4:Nat)^3=64 by decide]
    intro hhappy
    have htwo : (graph sourceE 3 p).seven.digit=2 := hhappy.1
    rw [hparent,hzero] at htwo
    omega

/-- High dyadic order and prefix-one do not force the width-three
collision. The exact odd cofactor one must be used. -/
theorem prefix_one_high_dyadic_does_not_force_collision :
    ¬ (∀ E : Nat,
         E%27=1 → (2:Nat)^24 ∣ E →
         HappyCell (graph E 0 3).seven.carry
           (graph E 0 3).seven.digit →
         ∃ p : Nat, HappyCell (graph E 3 p).seven.carry
           (graph E 3 p).seven.digit) := by
  intro h
  obtain ⟨p,hp⟩ := h sourceE
    exact_source_fingerprint.2.2.1
    exact_source_fingerprint.2.2.2.1
    genuine_child_happy
  exact bad_parent_at_every_row p hp

#print axioms exact_source_fingerprint
#print axioms genuine_child_happy
#print axioms bad_parent_at_every_row
#print axioms prefix_one_high_dyadic_does_not_force_collision

end GSTProblem406PrefixOneDyadicNoGo
