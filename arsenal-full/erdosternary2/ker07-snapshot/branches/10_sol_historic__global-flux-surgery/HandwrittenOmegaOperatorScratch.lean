/- ======================================================================
/- CHRONOLOGICAL LABEL -- #0876 / 1132
/-    Path         : branches/sol_global-flux-surgery/HandwrittenOmegaOperatorScratch.lean
/-    Ref          : origin/sol/global-flux-surgery
/-    First-commit : 2026-08-17 07:35:45 +0530  (ecd3e30)
/-    Last-commit  : 2026-08-17 08:13:30 +0530  (1d1b844)
/-    Total commits: 4
/- ======================================================================
/- GIT HISTORY (chronological, oldest first)
/- ======================================================================
/- [01/4] 2026-08-17 07:35:45 +0530  ecd3e30  (ker07-dev)
/-        Add exact natural-index Omega transfer budget
/- [02/4] 2026-08-17 07:50:10 +0530  678e5c5  (ker07-dev)
/-        Add exact future-past Omega transfer balance
/- [03/4] 2026-08-17 08:04:09 +0530  e21cc70  (ker07-dev)
/-        Add exact natural-origin Pi constructor
/- [04/4] 2026-08-17 08:13:30 +0530  1d1b844  (ker07-dev)
/-        Realize handwritten simultaneous multiply-divide as exact origin energy transfer
/- ====================================================================== -/

import OmegaSpacetimeScratch
import CanonicalPrefixScratch

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

/-!
# Handwritten Ω / U / Navigation operator — exact arithmetic core

This scratch formalizes the parts of Boss's handwritten operator that can be
stated without any new forcing axiom.
-/

def gstOmegaNaturalTransferS (t T i : Nat) : Nat :=
  3^(t+1+i) * gstDigitS T i

theorem gst_omega_natural_transfer_prefixS
    (t T K : Nat) :
    (∑ i in Finset.range K, gstOmegaNaturalTransferS t T i) =
      3^(t+1) * (T % 3^K) := by
  induction K with
  | zero => simp [gstOmegaNaturalTransferS]
  | succ K ih =>
      rw [Finset.sum_range_succ, ih]
      have hstep :
          T % 3^(K+1) = T % 3^K + 3^K * gstDigitS T K := by
        unfold gstDigitS
        rw [Nat.pow_succ, Nat.mod_mul]
      rw [hstep]
      have hpow : 3^(t+1+K) = 3^(t+1) * 3^K := Nat.pow_add 3 (t+1) K
      rw [gstOmegaNaturalTransferS, hpow]
      ring

theorem gst_omega_natural_transfer_totalS
    (t T : Nat) :
    (∑ i in Finset.range (T+1), gstOmegaNaturalTransferS t T i) =
      3^(t+1) * T := by
  rw [gst_omega_natural_transfer_prefixS]
  have hlt : T < 3^(T+1) := gst_three_pow_succ_gt_pressureS T
  rw [Nat.mod_eq_of_lt hlt]

theorem gst_omega_natural_transfer_is_energyS
    (t T : Nat) :
    1 + (∑ i in Finset.range (T+1), gstOmegaNaturalTransferS t T i) =
      gstOmegaPressureEnergyS t T := by
  rw [gst_omega_natural_transfer_totalS]
  rfl

theorem gst_handwritten_navigation_omega_budgetS
    (Q : Nat → Nat → Nat)
    (hQ : GSTCanonicalOriginEnergyS Q)
    (t n : Nat) (ht : 1 ≤ t) :
    1 +
        (∑ i in Finset.range (Q t n + 1),
          gstOmegaNaturalTransferS t (Q t n) i) =
      4^(3^t * n) := by
  rw [gst_omega_natural_transfer_totalS]
  exact (hQ t n ht).symm

theorem gst_handwritten_prefix_one_omega_budgetS
    (Q : Nat → Nat → Nat)
    (hQ : GSTCanonicalOriginEnergyS Q)
    (s n : Nat) (hs : 1 ≤ s) :
    1 +
        (∑ i in Finset.range (Q (s+1) n + 1),
          gstOmegaNaturalTransferS (s+1) (Q (s+1) n) i) =
      4^(3^(s+1) * n) := by
  exact gst_handwritten_navigation_omega_budgetS Q hQ (s+1) n (by omega)

theorem gst_omega_natural_transfer_pos_of_big2S
    (t T i : Nat) (hd : gstDigitS T i = 2) :
    0 < gstOmegaNaturalTransferS t T i := by
  unfold gstOmegaNaturalTransferS
  rw [hd]
  have hp : 0 < 3^(t+1+i) := Nat.pow_pos (by decide)
  omega

theorem gst_omega_natural_transfer_zero_above_ceilingS
    (t T i : Nat) (hi : T+1 ≤ i) :
    gstOmegaNaturalTransferS t T i = 0 := by
  unfold gstOmegaNaturalTransferS
  have hbase : T < 3^(T+1) := gst_three_pow_succ_gt_pressureS T
  have hpow : 3^(T+1) ≤ 3^i :=
    Nat.pow_le_pow_of_le (by decide : 1 < 3) hi
  have hlt : T < 3^i := lt_of_lt_of_le hbase hpow
  have hdiv : T / 3^i = 0 := Nat.div_eq_of_lt hlt
  simp [gstDigitS, hdiv]

theorem gst_handwritten_child_gate_packet_and_energyS
    (s T i : Nat) (hs : 1 ≤ s)
    (hgate : gstDigitS T i = 2 ∧
      (gstCarryS T i = 0 ∨ gstCarryS T i = 3)) :
    0 < gstOmegaNaturalTransferS (s+1) T i ∧
      (let U := 1 + 3^(s+2) * T
       gstDigitS U (s+2+i) = 2 ∧
         (gstCarryS U (s+2+i) = 0 ∨
          gstCarryS U (s+2+i) = 3)) := by
  constructor
  · exact gst_omega_natural_transfer_pos_of_big2S (s+1) T i hgate.1
  · exact gst_child_gate_embeds_phase_zero_energyS s T i hs hgate

/-! ## Exact future/past simultaneous transfer -/

def gstOmegaNaturalFutureS (t T i : Nat) : Nat :=
  3^(t+1+i) * (T / 3^i)

def gstOmegaNaturalPastS (t T i : Nat) : Nat :=
  3^(t+1) * (T % 3^i)

theorem gst_omega_natural_energy_splitS
    (t T i : Nat) :
    gstOmegaPressureEnergyS t T =
      1 + gstOmegaNaturalFutureS t T i + gstOmegaNaturalPastS t T i := by
  have hsplit := gst_omega_pressure_energy_splitS t T i
  simpa [gstOmegaNaturalFutureS, gstOmegaNaturalPastS] using hsplit

theorem gst_omega_natural_future_transferS
    (t T i : Nat) :
    gstOmegaNaturalFutureS t T i =
      gstOmegaNaturalFutureS t T (i+1) + gstOmegaNaturalTransferS t T i := by
  unfold gstOmegaNaturalFutureS gstOmegaNaturalTransferS
  have hsplit : T / 3^i = 3 * (T / 3^(i+1)) + gstDigitS T i := by
    unfold gstDigitS
    have h := Nat.mod_add_div (T / 3^i) 3
    have hq : T / 3^i / 3 = T / 3^(i+1) := by
      rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul]
    rw [hq] at h
    omega
  conv_lhs => rw [hsplit]
  rw [Nat.mul_add]
  have hpow : 3^(t+1+i) * 3 = 3^(t+1+(i+1)) := by
    rw [show t+1+(i+1) = (t+1+i)+1 by omega, Nat.pow_succ]
  rw [show
      3^(t+1+i) * (3 * (T / 3^(i+1))) =
        (3^(t+1+i) * 3) * (T / 3^(i+1)) by ac_rfl,
      hpow]

theorem gst_omega_natural_past_transferS
    (t T i : Nat) :
    gstOmegaNaturalPastS t T (i+1) =
      gstOmegaNaturalPastS t T i + gstOmegaNaturalTransferS t T i := by
  unfold gstOmegaNaturalPastS gstOmegaNaturalTransferS
  have hstep : T % 3^(i+1) = T % 3^i + 3^i * gstDigitS T i := by
    unfold gstDigitS
    rw [Nat.pow_succ, Nat.mod_mul]
  rw [hstep, Nat.mul_add]
  have hpow :
      3^(t+1) * (3^i * gstDigitS T i) =
        3^(t+1+i) * gstDigitS T i := by
    rw [← Nat.mul_assoc, ← Nat.pow_add]
  rw [hpow]

theorem gst_omega_natural_simultaneous_transferS
    (t T i : Nat) :
    gstOmegaNaturalFutureS t T i =
        gstOmegaNaturalFutureS t T (i+1) + gstOmegaNaturalTransferS t T i ∧
      gstOmegaNaturalPastS t T (i+1) =
        gstOmegaNaturalPastS t T i + gstOmegaNaturalTransferS t T i := by
  exact ⟨gst_omega_natural_future_transferS t T i,
    gst_omega_natural_past_transferS t T i⟩

/-! ## Exact Pi natural-origin constructor -/

def gstOriginNaturalTritS (n t : Nat) : Nat := n / 3^t % 3

theorem gst_origin_phase_prefixS
    (s n K : Nat) :
    (∑ t in Finset.range K, 3^(s+t) * gstOriginNaturalTritS n t) =
      3^s * (n % 3^K) := by
  induction K with
  | zero => simp [gstOriginNaturalTritS]
  | succ K ih =>
      rw [Finset.sum_range_succ, ih]
      have hstep :
          n % 3^(K+1) = n % 3^K + 3^K * gstOriginNaturalTritS n K := by
        unfold gstOriginNaturalTritS
        rw [Nat.pow_succ, Nat.mod_mul]
      rw [hstep, Nat.mul_add]
      have hpow : 3^s * 3^K = 3^(s+K) := by rw [← Nat.pow_add]
      rw [hpow]
      ring

theorem gst_origin_phase_totalS
    (s n : Nat) :
    (∑ t in Finset.range (n+1),
      3^(s+t) * gstOriginNaturalTritS n t) = 3^s * n := by
  rw [gst_origin_phase_prefixS]
  have hlt : n < 3^(n+1) := gst_three_pow_succ_gt_pressureS n
  rw [Nat.mod_eq_of_lt hlt]

theorem gst_origin_phase_reconstructs_energyS
    (s n : Nat) :
    4^(∑ t in Finset.range (n+1),
      3^(s+t) * gstOriginNaturalTritS n t) = 4^(3^s * n) := by
  rw [gst_origin_phase_totalS]

/-!
## Exact multiplicative realization of the handwritten simultaneous glyph

At one origin step the remaining perfect-power U factor is divided by the
phase selected by the consumed trit, while the affine information multiplier
is multiplied by exactly that phase.  Their product is invariant.
-/

def gstOriginRemainingUS (t n : Nat) : Nat := 4^(3^t * n)

def gstOriginConsumedPhaseS (t n : Nat) : Nat :=
  4^(3^t * (n % 3))

def gstOriginMultiplierStepS (M t n : Nat) : Nat :=
  M * gstOriginConsumedPhaseS t n

/-- One-step exact multiply/divide conservation. -/
theorem gst_origin_simultaneous_mul_divS
    (M t n : Nat) :
    M * gstOriginRemainingUS t n =
      gstOriginMultiplierStepS M t n *
        gstOriginRemainingUS (t+1) (n/3) := by
  unfold gstOriginRemainingUS gstOriginMultiplierStepS gstOriginConsumedPhaseS
  rw [gst_pure_power_origin_splitS t n]
  ac_rfl

/-- The consumed prefix energy after K origin trits. -/
def gstOriginConsumedPrefixUS (t n K : Nat) : Nat :=
  4^(3^t * (n % 3^K))

/-- Exact factorization after K natural-origin steps: the consumed U factor
multiplied by the remaining U factor is the original U. -/
theorem gst_origin_prefix_remaining_U_conservationS
    (t n K : Nat) :
    gstOriginConsumedPrefixUS t n K *
      gstOriginRemainingUS (t+K) (n / 3^K) =
      gstOriginRemainingUS t n := by
  unfold gstOriginConsumedPrefixUS gstOriginRemainingUS
  have hn : n = n % 3^K + 3^K * (n / 3^K) := by
    have h := Nat.mod_add_div n (3^K)
    omega
  have hexp :
      3^t * n =
        3^t * (n % 3^K) + 3^(t+K) * (n / 3^K) := by
    calc
      3^t*n = 3^t * (n % 3^K + 3^K*(n/3^K)) := by rw [hn]
      _ = 3^t*(n%3^K) + 3^t*3^K*(n/3^K) := by ring
      _ = 3^t*(n%3^K) + 3^(t+K)*(n/3^K) := by rw [← Nat.pow_add]
  rw [hexp, Nat.pow_add]

/-- At the explicit natural ceiling the remaining U factor is one, so the
consumed phase product has absorbed the entire original perfect-power energy. -/
theorem gst_origin_total_U_absorbedS
    (t n : Nat) :
    gstOriginConsumedPrefixUS t n (n+1) = gstOriginRemainingUS t n := by
  unfold gstOriginConsumedPrefixUS gstOriginRemainingUS
  have hlt : n < 3^(n+1) := gst_three_pow_succ_gt_pressureS n
  rw [Nat.mod_eq_of_lt hlt]
