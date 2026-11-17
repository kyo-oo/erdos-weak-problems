import GSTU2DAtomicBridge

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace GSTU2DEventTransport

open GST2DMixedEmergence

/-- The two physical x4 Happy orientations. -/
def HappyCell (C d : Nat) : Prop :=
  d = 2 ∧ (C = 0 ∨ C = 3)

/-- A small nonnegative carry potential selected by the physical event table. -/
def eventCarryPotential (C : Nat) : Int :=
  if C = 0 then 3 else if C = 1 then 1 else 0

/-- Local event divergence.  It keeps the hidden NULL midpoint through
`surviveI`, while its sign detects whether a physical x4 cell is Happy. -/
def eventDensity (C d : Nat) : Int :=
  twoI (outDigit C d) - twoI d +
    eventCarryPotential C - 3 * eventCarryPotential (nextCarry C d) +
    surviveI C d

/-- Complete physical table of the event divergence. -/
theorem eventDensity_physical_table :
    eventDensity 0 0 = -6 ∧ eventDensity 0 1 = 0 ∧ eventDensity 0 2 = 3 ∧
    eventDensity 1 0 = -8 ∧ eventDensity 1 1 = 0 ∧ eventDensity 1 2 = 0 ∧
    eventDensity 2 0 = -8 ∧ eventDensity 2 1 = 0 ∧ eventDensity 2 2 = 0 ∧
    eventDensity 3 0 = -3 ∧ eventDensity 3 1 = 0 ∧ eventDensity 3 2 = 2 := by
  decide

/-- Every physical event has density at least -8. -/
theorem eventDensity_ge_neg_eight
    (C d : Nat) (hC : C < 4) (hd : d < 3) :
    (-8 : Int) ≤ eventDensity C d := by
  have hCc : C = 0 ∨ C = 1 ∨ C = 2 ∨ C = 3 := by omega
  have hdc : d = 0 ∨ d = 1 ∨ d = 2 := by omega
  rcases hCc with rfl | rfl | rfl | rfl <;>
    rcases hdc with rfl | rfl | rfl <;>
    norm_num [eventDensity, eventCarryPotential, twoI, outDigit, nextCarry,
      surviveI, midDigit, finalMicroDigit, microOutput, highBit, lowBit]

/-- At input BIG2 the density is never negative, for any physical carry. -/
theorem eventDensity_big2_nonnegative
    (C : Nat) (hC : C < 4) :
    0 ≤ eventDensity C 2 := by
  have hCc : C = 0 ∨ C = 1 ∨ C = 2 ∨ C = 3 := by omega
  rcases hCc with rfl | rfl | rfl | rfl <;>
    norm_num [eventDensity, eventCarryPotential, twoI, outDigit, nextCarry,
      surviveI, midDigit, finalMicroDigit, microOutput, highBit, lowBit]

/-- Both NULL and GST+ Happy cells inject strictly positive density and emit
BIG2 again. -/
theorem happyCell_positive_and_preserves_big2
    (C d : Nat) (h : HappyCell C d) :
    2 ≤ eventDensity C d ∧ outDigit C d = 2 := by
  rcases h with ⟨rfl, h0 | h3⟩
  · subst C
    norm_num [eventDensity, eventCarryPotential, twoI, outDigit, nextCarry,
      surviveI, midDigit, finalMicroDigit, microOutput, highBit, lowBit]
  · subst C
    norm_num [eventDensity, eventCarryPotential, twoI, outDigit, nextCarry,
      surviveI, midDigit, finalMicroDigit, microOutput, highBit, lowBit]

/-- Reverse-base-four accumulation of one horizontal event row.  Earlier
horizontal cells receive larger powers of four, matching the physical carry
word orientation of Equation III. -/
def reverseEventCode (C d : Nat → Nat) : Nat → Int
  | 0 => 0
  | N+1 => 4 * reverseEventCode C d N + eventDensity (C N) (d N)

/-- **Horizontal no-erasure theorem.**

If the first x4 cell of a physical horizontal chain is Happy, then after two
or more cells its reverse-base-four event code is at least eight.  The proof is
uniform in the horizontal length.  It uses only the exact local x4 transition,
not a terminal height or a finite-support hypothesis.

The key mechanism is rigid: a Happy cell emits BIG2, so the second event is
nonnegative; after that every possible physical event is at worst -8 while the
existing code is multiplied by four at each new column. -/
theorem reverseEventCode_ge_eight_of_leading_happy
    (C d : Nat → Nat)
    (hfirst : HappyCell (C 0) (d 0)) :
    ∀ N : Nat,
      2 ≤ N →
      (∀ t, t < N → C t < 4) →
      (∀ t, t < N → d t < 3) →
      (∀ t, t < N → outDigit (C t) (d t) = d (t+1)) →
      8 ≤ reverseEventCode C d N := by
  intro N
  induction N with
  | zero =>
      intro hN
      omega
  | succ N ih =>
      intro hN hC hd hstep
      by_cases hN1 : N = 1
      · subst N
        have hlead := happyCell_positive_and_preserves_big2
          (C 0) (d 0) hfirst
        have hstep0 := hstep 0 (by omega)
        have hd1 : d 1 = 2 := by
          rw [← hstep0]
          exact hlead.2
        have hsecond : 0 ≤ eventDensity (C 1) (d 1) := by
          rw [hd1]
          exact eventDensity_big2_nonnegative (C 1) (hC 1 (by omega))
        simp only [reverseEventCode]
        omega
      · have hN2 : 2 ≤ N := by omega
        have ih' : 8 ≤ reverseEventCode C d N :=
          ih hN2
            (fun t ht => hC t (by omega))
            (fun t ht => hd t (by omega))
            (fun t ht => hstep t (by omega))
        have hlast : (-8 : Int) ≤ eventDensity (C N) (d N) :=
          eventDensity_ge_neg_eight (C N) (d N)
            (hC N (by omega)) (hd N (by omega))
        rw [reverseEventCode]
        omega

/-- One-cell form, useful when the physical horizontal width has not yet been
expanded. -/
theorem reverseEventCode_positive_one
    (C d : Nat → Nat)
    (hfirst : HappyCell (C 0) (d 0)) :
    0 < reverseEventCode C d 1 := by
  have h := happyCell_positive_and_preserves_big2 (C 0) (d 0) hfirst
  simp only [reverseEventCode]
  omega

#check eventDensity_physical_table
#check eventDensity_ge_neg_eight
#check happyCell_positive_and_preserves_big2
#check reverseEventCode_ge_eight_of_leading_happy
#print axioms reverseEventCode_ge_eight_of_leading_happy

end GSTU2DEventTransport
