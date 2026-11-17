import GSTGraphV2InfiniteControl

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace GSTGraphV2NonlocalCascade

open GSTCanonicalSevenAxisBridge
open GST2DMixedEmergence
open GSTU2DEventTransport
open GSTGraphV2InfiniteControl

/-- The exact ontological output of one horizontal x4 wave.  A physical Happy
cell either stays physically Happy in the next column, or its digit-two
information is retained as an ALT-minus latent packet whose next vertical
carry is exactly three.  No claim about the next digit is inserted. -/
theorem graph_happy_lifts_or_latent
    (E t p : Nat)
    (hHappy : HappyCell
      (graph E t p).seven.carry
      (graph E t p).seven.digit) :
    HappyCell
        (graph E (t+1) p).seven.carry
        (graph E (t+1) p).seven.digit ∨
      ((graph E (t+1) p).seven.digit = 2 ∧
        ((graph E (t+1) p).seven.carry = 1 ∨
         (graph E (t+1) p).seven.carry = 2) ∧
        (graph E (t+1) (p+1)).seven.carry = 3) := by
  have hcell := graph_cell_exact E t p
  have hRightDigit : (graph E (t+1) p).seven.digit = 2 := by
    rw [← hcell.1]
    rcases hHappy with ⟨hd, h0 | h3⟩
    · rw [hd, h0]
      decide
    · rw [hd, h3]
      decide
  have hRightCarry := graph_carry_lt_four E (t+1) p
  have hCases :
      (graph E (t+1) p).seven.carry = 0 ∨
      (graph E (t+1) p).seven.carry = 1 ∨
      (graph E (t+1) p).seven.carry = 2 ∨
      (graph E (t+1) p).seven.carry = 3 := by
    omega
  rcases hCases with h0 | h1 | h2 | h3
  · exact Or.inl ⟨hRightDigit, Or.inl h0⟩
  · right
    refine ⟨hRightDigit, Or.inl h1, ?_⟩
    have hstep := (graph_cell_exact E (t+1) p).2
    rw [h1, hRightDigit] at hstep
    norm_num [nextCarry] at hstep
    exact hstep.symm
  · right
    refine ⟨hRightDigit, Or.inr h2, ?_⟩
    have hstep := (graph_cell_exact E (t+1) p).2
    rw [h2, hRightDigit] at hstep
    norm_num [nextCarry] at hstep
    exact hstep.symm
  · exact Or.inl ⟨hRightDigit, Or.inr h3⟩

/-- Canonical unit-sheet specialization.  This is the exact induction packet
for the transition from `4^K` to `4^(K+1)`. -/
theorem four_power_happy_lifts_or_latent
    (K p : Nat)
    (hHappy : HappyCell
      (graph 1 K p).seven.carry
      (graph 1 K p).seven.digit) :
    HappyCell
        (graph 1 (K+1) p).seven.carry
        (graph 1 (K+1) p).seven.digit ∨
      ((graph 1 (K+1) p).seven.digit = 2 ∧
        ((graph 1 (K+1) p).seven.carry = 1 ∨
         (graph 1 (K+1) p).seven.carry = 2) ∧
        (graph 1 (K+1) (p+1)).seven.carry = 3) := by
  exact graph_happy_lifts_or_latent 1 K p hHappy


/-! ## Exact latent-sector extraction -/

/-- If a Happy source fails to remain Happy one horizontal wave later, then
the entire latent packet is forced: digit two survives, the new carry lies in
the ALT-minus sector {1,2}, and the next vertical carry is exactly three. -/
theorem graph_happy_forces_latent_of_next_bad
    (E t p : Nat)
    (hHappy : HappyCell
      (graph E t p).seven.carry
      (graph E t p).seven.digit)
    (hBad : ¬ HappyCell
      (graph E (t+1) p).seven.carry
      (graph E (t+1) p).seven.digit) :
    (graph E (t+1) p).seven.digit = 2 ∧
      ((graph E (t+1) p).seven.carry = 1 ∨
       (graph E (t+1) p).seven.carry = 2) ∧
      (graph E (t+1) (p+1)).seven.carry = 3 := by
  rcases graph_happy_lifts_or_latent E t p hHappy with hStay | hLatent
  · exact False.elim (hBad hStay)
  · exact hLatent

/-- Conversely, a Happy source has exactly two mutually exhaustive outcomes:
persistent Happy transport or forced latent transport. -/
theorem graph_happy_transport_dichotomy
    (E t p : Nat)
    (hHappy : HappyCell
      (graph E t p).seven.carry
      (graph E t p).seven.digit) :
    (HappyCell
        (graph E (t+1) p).seven.carry
        (graph E (t+1) p).seven.digit)
      ∨
    ((¬ HappyCell
        (graph E (t+1) p).seven.carry
        (graph E (t+1) p).seven.digit) ∧
      (graph E (t+1) p).seven.digit = 2 ∧
      ((graph E (t+1) p).seven.carry = 1 ∨
       (graph E (t+1) p).seven.carry = 2) ∧
      (graph E (t+1) (p+1)).seven.carry = 3) := by
  by_cases hStay : HappyCell
      (graph E (t+1) p).seven.carry
      (graph E (t+1) p).seven.digit
  · exact Or.inl hStay
  · exact Or.inr ⟨hStay,
      graph_happy_forces_latent_of_next_bad E t p hHappy hStay⟩


#check graph_happy_lifts_or_latent
#check four_power_happy_lifts_or_latent
#check graph_happy_forces_latent_of_next_bad
#check graph_happy_transport_dichotomy
#print axioms graph_happy_lifts_or_latent
#print axioms four_power_happy_lifts_or_latent
#print axioms graph_happy_transport_dichotomy

end GSTGraphV2NonlocalCascade
