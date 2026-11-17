import GSTFourPowerDirectResidue

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
# GST Problem 406 — sharpness of the generic seven-step physical-pair theorem

The new universal positive-source theorem proves that for every positive A
there is a shift j <= 7 such that A*4^j and 4*(A*4^j) share a ternary 2
at one positive row.

A=3829 is an exact, finite, nonzero counterexample to improving this
uniform statement to j <= 6 for arbitrary A. Its first successful shift
is j=7, with simultaneous digit 2 at row p=2.

This counterexample does NOT refute the original fixed-exponent theorem,
because 3829 is not a power of four. It shows that any attempt to
convert the generic bounded-shift result into a fixed-K original hGate
must use the actual perfect-power origin A=4^K.

The proof includes a finite Fin 7 x Fin 17 kernel decision and an
independent global row cutoff. It makes no custom axiom or universal
CommonTwo assumption.
-/

namespace GSTProblem406SevenStepSharpness

open GSTFourPowerDirectResidue

/-- Exhaustive finite calculation for all seven earlier orbit shifts
and every row below 17. All arithmetic is exact. -/
private theorem finite_seven_shift_survival :
    ∀ j : Fin 7, ∀ p : Fin 17,
      ¬ (digit3 (3829 * 4^j.val) p.val = 2 ∧
         digit3 (4 * (3829 * 4^j.val)) p.val = 2) := by
  decide

/-- Extend finite certification to every natural ternary row using
the exact size bound on the largest tested integer. -/
theorem source_3829_no_pair_before_shift_seven
    (j p : Nat) (hj : j < 7) :
    ¬ (digit3 (3829 * 4^j) p = 2 ∧
       digit3 (4 * (3829 * 4^j)) p = 2) := by
  by_cases hp : p < 17
  · exact finite_seven_shift_survival ⟨j,hj⟩ ⟨p,hp⟩
  · intro hPair
    have hpow : (4 : Nat)^j ≤ 4^6 := by
      gcongr <;> omega
    have hbounded : 4 * (3829 * 4^j) ≤ 4 * (3829 * 4^6) :=
      Nat.mul_le_mul_left 4 (Nat.mul_le_mul_left 3829 hpow)
    have hsmall : 4 * (3829 * 4^6) < 3^17 := by decide
    have hpowp : (3 : Nat)^17 ≤ 3^p := by
      gcongr <;> omega
    have hlt : 4 * (3829 * 4^j) < 3^p :=
      lt_of_lt_of_le (lt_of_le_of_lt hbounded hsmall) hpowp
    have hzero : digit3 (4 * (3829 * 4^j)) p = 0 := by
      unfold digit3
      rw [Nat.div_eq_of_lt hlt]
    omega

/-- The next orbit shift DOES contain a simultaneous physical
ternary 2 at positive row two, and so seven is exactly sharp. -/
theorem source_3829_pair_at_seven :
    digit3 (3829 * 4^7) 2 = 2 ∧
    digit3 (4 * (3829 * 4^7)) 2 = 2 := by
  constructor <;> norm_num [digit3]

/-- A full unconditional optimality theorem for the positive-source
seven-step claim; this does not assert the original fixed-K hGate. -/
theorem generic_seven_step_bound_is_sharp :
    (∀ j : Nat, j ≤ 6 →
      ¬ ∃ p : Nat, 1 ≤ p ∧
        digit3 (3829 * 4^j) p = 2 ∧
        digit3 (4 * (3829 * 4^j)) p = 2) ∧
    (∃ p : Nat, 1 ≤ p ∧
        digit3 (3829 * 4^7) p = 2 ∧
        digit3 (4 * (3829 * 4^7)) p = 2) := by
  constructor
  · intro j hj ⟨p, _, hSource, hNeighbor⟩
    exact (source_3829_no_pair_before_shift_seven j p (by omega))
      ⟨hSource,hNeighbor⟩
  · exact ⟨2, by decide, source_3829_pair_at_seven.1,
      source_3829_pair_at_seven.2⟩

#print axioms source_3829_no_pair_before_shift_seven
#print axioms source_3829_pair_at_seven
#print axioms generic_seven_step_bound_is_sharp

end GSTProblem406SevenStepSharpness
