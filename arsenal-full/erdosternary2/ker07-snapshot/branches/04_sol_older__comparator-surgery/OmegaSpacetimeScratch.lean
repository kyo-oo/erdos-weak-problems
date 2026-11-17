/- ======================================================================
/- CHRONOLOGICAL LABEL -- #0446 / 1132
/-    Path         : branches/sol_comparator-surgery/OmegaSpacetimeScratch.lean
/-    Ref          : origin/sol/comparator-surgery
/-    First-commit : 2026-08-15 23:08:39 +0530  (d994046)
/-    Last-commit  : 2026-08-16 03:08:50 +0530  (ebbdf18)
/-    Total commits: 3
/- ======================================================================
/- GIT HISTORY (chronological, oldest first)
/- ======================================================================
/- [01/3] 2026-08-15 23:08:39 +0530  d994046  (ker07-dev)
/-        Kernelize infinite-wave phase sandwich endpoints
/- [02/3] 2026-08-16 03:01:26 +0530  047bdd2  (ker07-dev)
/-        add infinite Omega energy-pressure consumer
/- [03/3] 2026-08-16 03:08:50 +0530  ebbdf18  (ker07-dev)
/-        fix Omega pressure radix split
/- ====================================================================== -/

import PurePowerBadAxisScratch
import OriginTransducerScratch

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

/-!
Spacetime endpoint facts for the prefix-one GST surgery.

This file deliberately does NOT use a terminal zero tail, finite-support cutoff,
or origin exhaustion. It identifies the BIG2-bearing phase boundaries of the
same canonical power orbit and the fixed-energy pressure law for arbitrarily
high re-realisations.
-/

/-- A child Happy Gate is an actual BIG2/SURVIVE vertex of the full phase-zero
perfect-power energy after the forced low prefix is crossed. -/
theorem gst_child_gate_embeds_phase_zero_energyS
    (s T q : Nat) (hs : 1 ≤ s)
    (hgate : gstDigitS T q = 2 ∧
      (gstCarryS T q = 0 ∨ gstCarryS T q = 3)) :
    let E0 := 1 + 3^(s+2) * T
    gstDigitS E0 (s+2+q) = 2 ∧
      (gstCarryS E0 (s+2+q) = 0 ∨
       gstCarryS E0 (s+2+q) = 3) := by
  dsimp only
  have hstate := gst_child_energy_stateS s T q hs
  dsimp only at hstate
  constructor
  · rw [hstate.1]
    exact hgate.1
  · rw [hstate.2]
    exact hgate.2

/-- Any exact phase-two energy

      E2 = 1 + 2*3^(s+1) + 3^(s+2)*H

carries an unconditional BIG2/SURVIVE vertex at the phase boundary `s+1`:
digit two with NULL carry. This is a phase boundary statement, not a
terminal-NULL statement. -/
theorem gst_phase_two_energy_boundary_gateS
    (s H : Nat) (hs : 1 ≤ s) :
    let E2 := 1 + 2*3^(s+1) + 3^(s+2)*H
    gstDigitS E2 (s+1) = 2 ∧
      gstCarryS E2 (s+1) = 0 := by
  dsimp only
  let D := 3^(s+1)
  have hD9 : 9 ≤ D := by
    dsimp [D]
    rw [show (9:Nat) = 3^2 by decide]
    exact Nat.pow_le_pow_of_le (by decide : 1 < 3) (by omega)
  have hDpos : 0 < D := by omega
  have hpow : 3^(s+2) = 3*D := by
    dsimp [D]
    rw [show s+2 = (s+1)+1 by omega, Nat.pow_succ]
    ac_rfl
  have hshape :
      1 + 2*3^(s+1) + 3^(s+2)*H =
        1 + D * (2 + 3*H) := by
    rw [show 3^(s+1) = D by rfl, hpow]
    ring
  rw [hshape]
  constructor
  · have htail : (1 + D * (2 + 3*H)) / D = 2 + 3*H := by
      rw [Nat.add_mul_div_left 1 (2+3*H) hDpos]
      rw [Nat.div_eq_of_lt (by omega : 1 < D)]
      simp
    unfold gstDigitS
    rw [show 3^(s+1) = D by rfl, htail]
    omega
  · unfold gstCarryS
    rw [show 3^(s+1) = D by rfl]
    have hmod : (1 + D * (2 + 3*H)) % D = 1 := by
      rw [Nat.add_mod, Nat.mul_mod]
      simp [Nat.mod_eq_of_lt (by omega : 1 < D)]
    rw [hmod]
    exact Nat.div_eq_of_lt (by omega : 4 < D)

/-- The exact three-phase power orbit: phase zero -> phase one is multiplication
by `A`, and phase one -> phase two is another multiplication by the same `A`.
This is the horizontal GST spacetime axis; no finite endpoint is introduced. -/
theorem gst_three_phase_energy_orbitS
    (A D c z T H2 n : Nat)
    (hDN : ∃ N, D = 3*N)
    (hA : A = 1 + D*c)
    (hc : c = 1 + 3*z)
    (h0 : A^(3*n) = 1 + 3*D*T)
    (h2 : A^(3*n + 2) = 1 + 2*D + 3*D*H2) :
    let H1 := z + A*T
    A^(3*n + 1) = 1 + D + 3*D*H1 ∧
      A^(3*n + 2) = 1 + 2*D + 3*D*H2 := by
  dsimp only
  constructor
  · exact gst_phase_one_exactS A D c z T n hA hc h0
  · exact h2

/-!
## Infinite Omega pressure

The following subsystem is deliberately independent of terminal support. It
says only that a BIG2 realisation at ternary height `j` carries an explicit
positive packet `3^(t+1+j) * digit(T,j)`, and every such packet is bounded by
one fixed conserved origin energy `1 + 3^(t+1)*T`.
-/

def gstOmegaPressureEnergyS (t T : Nat) : Nat :=
  1 + 3^(t+1) * T

def gstOmegaPressureTransferS (t T j : Nat) : Nat :=
  3^(t+1+j) * gstDigitS T j

/-- Exact radix split underlying the pressure bound. -/
theorem gst_omega_pressure_energy_splitS
    (t T j : Nat) :
    gstOmegaPressureEnergyS t T =
      1 + 3^(t+1+j) * (T / 3^j) +
        3^(t+1) * (T % 3^j) := by
  unfold gstOmegaPressureEnergyS
  have hT : T = 3^j * (T / 3^j) + T % 3^j :=
    (Nat.div_add_mod T (3^j)).symm
  have hscaled :
      3^(t+1) * T =
        3^(t+1+j) * (T / 3^j) +
          3^(t+1) * (T % 3^j) := by
    calc
      3^(t+1) * T =
          3^(t+1) * (3^j * (T / 3^j) + T % 3^j) := by rw [← hT]
      _ = (3^(t+1) * 3^j) * (T / 3^j) +
          3^(t+1) * (T % 3^j) := by ring
      _ = 3^(t+1+j) * (T / 3^j) +
          3^(t+1) * (T % 3^j) := by rw [← Nat.pow_add]
  omega

/-- Every realised information packet is bounded by the same fixed Omega
origin energy. -/
theorem gst_omega_pressure_transfer_le_energyS
    (t T j : Nat) :
    gstOmegaPressureTransferS t T j ≤ gstOmegaPressureEnergyS t T := by
  have hsplit := gst_omega_pressure_energy_splitS t T j
  have hmod : gstDigitS T j ≤ T / 3^j := by
    unfold gstDigitS
    exact Nat.mod_le _ _
  have hmul :
      3^(t+1+j) * gstDigitS T j ≤
        3^(t+1+j) * (T / 3^j) :=
    Nat.mul_le_mul_left _ hmod
  unfold gstOmegaPressureTransferS
  omega

/-- Elementary pressure growth, stated internally so the Omega argument does
not appeal to a terminal-support theorem. -/
theorem gst_three_pow_succ_gt_pressureS (m : Nat) :
    m < 3^(m+1) := by
  induction m with
  | zero => decide
  | succ m ih =>
      have hp : 0 < 3^(m+1) := Nat.pow_pos (by decide)
      have hle : m+1 ≤ 3^(m+1) := by omega
      rw [Nat.pow_succ]
      omega

/-- A digit-two re-realisation at a height at least the fixed energy already
requires a transfer packet strictly larger than that entire energy. -/
theorem gst_omega_pressure_two_above_energyS
    (t T j : Nat)
    (hj : gstOmegaPressureEnergyS t T ≤ j)
    (hd : gstDigitS T j = 2) :
    gstOmegaPressureEnergyS t T < gstOmegaPressureTransferS t T j := by
  let E := gstOmegaPressureEnergyS t T
  have hbase : E < 3^(E+1) := gst_three_pow_succ_gt_pressureS E
  have hexp : E+1 ≤ t+1+j := by
    dsimp [E] at hj ⊢
    omega
  have hpow : 3^(E+1) ≤ 3^(t+1+j) :=
    Nat.pow_le_pow_of_le (by decide : 1 < 3) hexp
  unfold gstOmegaPressureTransferS
  rw [hd]
  have hpos : 0 < 3^(t+1+j) := Nat.pow_pos (by decide)
  omega

/-- Fixed Omega energy forbids digit-two information from re-realising at
arbitrarily high ternary heights. This is an energy-pressure contradiction,
not a terminal-NULL or last-gate argument. -/
theorem gst_omega_pressure_no_unbounded_twoS
    (t T : Nat)
    (hunbounded : ∀ M, ∃ j, M ≤ j ∧ gstDigitS T j = 2) :
    False := by
  let E := gstOmegaPressureEnergyS t T
  obtain ⟨j, hj, hd⟩ := hunbounded E
  have hlarge : E < gstOmegaPressureTransferS t T j :=
    gst_omega_pressure_two_above_energyS t T j hj hd
  have hbound : gstOmegaPressureTransferS t T j ≤ E := by
    dsimp [E]
    exact gst_omega_pressure_transfer_le_energyS t T j
  omega
