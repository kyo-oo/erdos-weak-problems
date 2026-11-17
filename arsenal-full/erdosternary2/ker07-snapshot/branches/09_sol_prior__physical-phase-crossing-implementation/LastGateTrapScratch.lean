/- ======================================================================
/- CHRONOLOGICAL LABEL -- #0347 / 1132
/-    Path         : branches/sol_physical-phase-crossing-implementation/LastGateTrapScratch.lean
/-    Ref          : origin/sol/physical-phase-crossing-implementation
/-    First-commit : 2026-08-15 17:18:10 +0530  (6c56a4c)
/-    Last-commit  : 2026-08-15 17:24:37 +0530  (a199940)
/-    Total commits: 2
/- ======================================================================
/- GIT HISTORY (chronological, oldest first)
/- ======================================================================
/- [01/2] 2026-08-15 17:18:10 +0530  6c56a4c  (ker07-dev)
/-        Formalize last-gate seeded bad suffix trap
/- [02/2] 2026-08-15 17:24:37 +0530  a199940  (ker07-dev)
/-        Repair last-gate ceiling proof seams
/- ====================================================================== -/

import InformationIterationScratch
import FiniteSupportScratch

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

/-- A Happy Gate in a seed-retaining child wave. -/
def GSTSeededHappyS (D X j : Nat) : Prop :=
  gstDigitS X j = 2 ∧
    (gstAffineMulCarryS 4 D X j = 0 ∨
     gstAffineMulCarryS 4 D X j = 3)

/-- Any nonempty finite interval of seeded gates has a last gate. -/
theorem gst_exists_last_seeded_gate_belowS
    (D X N : Nat)
    (hex : ∃ j, j < N ∧ GSTSeededHappyS D X j) :
    ∃ q, q < N ∧ GSTSeededHappyS D X q ∧
      ∀ r, q < r → r < N → ¬ GSTSeededHappyS D X r := by
  induction N with
  | zero =>
      obtain ⟨j, hj, _⟩ := hex
      omega
  | succ N ih =>
      by_cases hN : GSTSeededHappyS D X N
      · refine ⟨N, Nat.lt_succ_self N, hN, ?_⟩
        intro r hNr hr
        omega
      · have hexN : ∃ j, j < N ∧ GSTSeededHappyS D X j := by
          obtain ⟨j, hj, hjgate⟩ := hex
          by_cases heq : j = N
          · subst j
            exact False.elim (hN hjgate)
          · have hjN : j < N := by omega
            exact ⟨j, hjN, hjgate⟩
        obtain ⟨q, hqN, hqgate, hlast⟩ := ih hexN
        refine ⟨q, by omega, hqgate, ?_⟩
        intro r hqr hr
        by_cases heq : r = N
        · subst r
          exact hN
        · have hrN : r < N := by omega
          exact hlast r hqr hrN

/-- Above the explicit natural ceiling every ternary digit is zero. -/
theorem gst_digit_zero_above_self_ceilingS
    (X j : Nat) (hj : X + 1 ≤ j) :
    gstDigitS X j = 0 := by
  have hbase : X < 3^(X+1) := three_pow_succ_gt_selfS X
  have hpow : 3^(X+1) ≤ 3^j :=
    Nat.pow_le_pow_of_le (by decide : 1 < 3) hj
  have hlt : X < 3^j := lt_of_lt_of_le hbase hpow
  unfold gstDigitS
  rw [Nat.div_eq_of_lt hlt]

/-- Seeded gates are therefore confined below the same finite natural ceiling;
    this bounds only the location of a gate, not the GST wave itself. -/
theorem gst_no_seeded_gate_above_self_ceilingS
    (D X j : Nat) (hj : X + 1 ≤ j) :
    ¬ GSTSeededHappyS D X j := by
  intro hgate
  have hd0 : gstDigitS X j = 0 :=
    gst_digit_zero_above_self_ceilingS X j hj
  have hd2 : gstDigitS X j = 2 := hgate.1
  omega

/-- Every seeded witness in a natural child has a globally last Happy Gate. -/
theorem gst_exists_global_last_seeded_gateS
    (D X : Nat)
    (hex : ∃ j, GSTSeededHappyS D X j) :
    ∃ q, GSTSeededHappyS D X q ∧
      ∀ r, q < r → ¬ GSTSeededHappyS D X r := by
  obtain ⟨j, hjgate⟩ := hex
  have hjlt : j < X + 1 := by
    by_contra hnot
    have hj : X + 1 ≤ j := by omega
    exact gst_no_seeded_gate_above_self_ceilingS D X j hj hjgate
  obtain ⟨q, hq, hqgate, hlast⟩ :=
    gst_exists_last_seeded_gate_belowS D X (X+1) ⟨j, hjlt, hjgate⟩
  refine ⟨q, hqgate, ?_⟩
  intro r hqr
  by_cases hr : r < X + 1
  · exact hlast r hqr hr
  · have hceil : X + 1 ≤ r := by omega
    exact gst_no_seeded_gate_above_self_ceilingS D X r hceil

/-- Once we cut immediately after the globally last child gate, the remaining
    child wave is a complete seeded bad trace.  The gate is not declared
    terminal: its carry is retained exactly as the incoming suffix seed. -/
theorem gst_suffix_after_last_gate_is_badS
    (D X q : Nat)
    (hq : GSTSeededHappyS D X q)
    (hlast : ∀ r, q < r → ¬ GSTSeededHappyS D X r) :
    let Dq := gstAffineMulCarryS 4 D X q
    let Dnext := gstStepCarryS Dq 2
    let Xnext := X / 3^(q+1)
    GSTSeededBadTraceS Dnext Xnext := by
  dsimp only
  have hstep := gstAffineS_forward_exact_all D X q
  have hDnext :
      gstAffineMulCarryS 4 D X (q+1) =
        gstStepCarryS (gstAffineMulCarryS 4 D X q) 2 := by
    rw [hstep, hq.1]
  intro j
  have hno := hlast (q+1+j) (by omega)
  intro hgate
  apply hno
  constructor
  · rw [gst_seeded_affine_digit_shiftS X (q+1) j]
    exact hgate.1
  · rw [gst_seeded_affine_carry_semigroupS D X (q+1) j,
        hDnext]
    exact hgate.2
