/- ======================================================================
/- CHRONOLOGICAL LABEL -- #0500 / 1132
/-    Path         : branches/sol_right-chord-firepower-base/PurePowerResidueGraphScratch.lean
/-    Ref          : origin/sol/right-chord-firepower-base
/-    First-commit : 2026-08-16 00:57:35 +0530  (d98cfa4)
/-    Last-commit  : 2026-08-16 05:04:46 +0530  (6d65c16)
/-    Total commits: 9
/- ======================================================================
/- GIT HISTORY (chronological, oldest first)
/- ======================================================================
/- [01/9] 2026-08-16 00:57:35 +0530  d98cfa4  (ker07-dev)
/-        Add pure-power residue tower to GST Graph V2
/- [02/9] 2026-08-16 02:25:28 +0530  080ac16  (ker07-dev)
/-        Wire exponent-lift graph into pure-power residue tower
/- [03/9] 2026-08-16 02:38:33 +0530  9979ea4  (ker07-dev)
/-        identify residue strips with actual power GST rows
/- [04/9] 2026-08-16 02:48:08 +0530  16651a1  (ker07-dev)
/-        add exact GST power rectangle conservation
/- [05/9] 2026-08-16 02:59:32 +0530  d79cd62  (ker07-dev)
/-        lift block echo to physical power channels
/- [06/9] 2026-08-16 03:23:02 +0530  b5d8bac  (ker07-dev)
/-        fix power rectangle normalization
/- [07/9] 2026-08-16 03:30:56 +0530  295b919  (ker07-dev)
/-        normalize block carrier before physical substitution
/- [08/9] 2026-08-16 04:44:15 +0530  ece717f  (ker07-dev)
/-        fix physical block-channel carrier normalization
/- [09/9] 2026-08-16 05:04:46 +0530  6d65c16  (ker07-dev)
/-        fix final pure-power rectangle tactic noise
/- ====================================================================== -/

import GSTGraphV2Scratch
import GSTExponentLiftScratch
import InformationCarryWordBridgeScratch
import PurePowerTailReductionScratch
import StripConservationScratch
import GSTGraphV2BlockScratch

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

/-!
# Pure-power residue tower view of GST Graph V2

The canonical child is represented only through residues of the exact power of
four. No finite cutoff or terminal NULL interpretation appears here.
-/

def gstResidueTowerModulusS (D q : Nat) : Nat := 3*D*3^q

/-- The aligned residue tower grows by exactly one child ternary digit. -/
theorem gst_residue_tower_stepS
    (D T q : Nat) :
    1 + 3*D*(T % 3^(q+1)) =
      (1 + 3*D*(T % 3^q)) +
        gstResidueTowerModulusS D q * gstDigitS T q := by
  unfold gstResidueTowerModulusS gstDigitS
  rw [Nat.pow_succ, Nat.mod_mul]
  ring

/-- For an exact pure-power energy the q-th aligned residue is precisely the
canonical child prefix residue. -/
theorem gst_pure_power_residue_tower_exactS
    (D T E K q : Nat)
    (hD : 1 ≤ D)
    (hE : E = 1 + 3*D*T)
    (hPow : E = 4^K) :
    4^K % gstResidueTowerModulusS D q =
      1 + 3*D*(T % 3^q) := by
  unfold gstResidueTowerModulusS
  exact gst_pure_power_strip_input_residueS D T E K q hD hE hPow

/-- For the canonical prefix-one scale D=3^(s+1), the q-th residue-tower
modulus is exactly the absolute ternary row s+2+q. -/
theorem gst_residue_tower_modulus_canonicalS
    (s q : Nat) :
    gstResidueTowerModulusS (3^(s+1)) q = 3^(s+2+q) := by
  unfold gstResidueTowerModulusS
  calc
    3 * 3^(s+1) * 3^q = 3^1 * 3^(s+1) * 3^q := by norm_num
    _ = 3^(1+(s+1)) * 3^q := by rw [← Nat.pow_add]
    _ = 3^((1+(s+1))+q) := by rw [← Nat.pow_add]
    _ = 3^(s+2+q) := by congr 1 <;> omega

/-- V2 power-grid bridge. Once the strip input is the exact residue of 4^K,
every horizontal carry coordinate is literally the ordinary GST carry of the
actual consecutive power column 4^(K+i) at the aligned ternary row. -/
theorem gst_residue_strip_carry_is_exact_power_carryS
    (s K q i : Nat) :
    gstStripCarryS
        (4^K % gstResidueTowerModulusS (3^(s+1)) q)
        (gstResidueTowerModulusS (3^(s+1)) q) i =
      gstCarryS (4^(K+i)) (s+2+q) := by
  have hM := gst_residue_tower_modulus_canonicalS s q
  unfold gstStripCarryS gstCarryS
  rw [hM]
  have hres :
      (4^i * (4^K % 3^(s+2+q))) % 3^(s+2+q) =
        (4^i * 4^K) % 3^(s+2+q) := by
    simp [Nat.mul_mod]
  rw [hres]
  have hpow : 4^i * 4^K = 4^(K+i) := by
    calc
      4^i * 4^K = 4^(i+K) := (Nat.pow_add 4 i K).symm
      _ = 4^(K+i) := by rw [Nat.add_comm]
  rw [hpow]

/-- The final strip quotient is the wide carry across the same exact rectangle
of consecutive power columns. -/
theorem gst_residue_strip_quotient_is_exact_power_wide_carryS
    (s K q width : Nat) :
    gstStripQuotientS
        (4^K % gstResidueTowerModulusS (3^(s+1)) q)
        (gstResidueTowerModulusS (3^(s+1)) q) width =
      (4^width * (4^K % 3^(s+2+q))) / 3^(s+2+q) := by
  unfold gstStripQuotientS
  rw [gst_residue_tower_modulus_canonicalS]

/-- The whole shared GST information carrier is the horizontal carry quotient
of the exact pure-power residue tower. -/
theorem gst_shared_state_is_pure_power_residue_stripS
    (N D c z T E K q : Nat)
    (hD3 : 3 ≤ D)
    (hD1 : 1 ≤ D)
    (hA : 4^N = 1 + D*c)
    (hc : c = 1 + 3*z)
    (hE : E = 1 + 3*D*T)
    (hPow : E = 4^K) :
    gstStripQuotientS
        (4^K % gstResidueTowerModulusS D q)
        (gstResidueTowerModulusS D q)
        (N+1) =
      gstAffineMulCarryS 4 1 (z + 4^N*T) q +
        4 * gstAffineMulCarryS (4^N) z T q := by
  have hr := gst_pure_power_residue_tower_exactS D T E K q hD1 hE hPow
  unfold gstResidueTowerModulusS at hr ⊢
  rw [hr]
  exact gst_shared_information_is_carry_wordS N D c z T q hD3 hA hc

/-- Canonical rectangle identification. The shared information word is exactly
the wide carry generated by the actual power rectangle 4^K -> 4^(K+N+1). -/
theorem gst_shared_state_is_exact_power_rectangleS
    (s N c z T E K q : Nat)
    (hs : 1 ≤ s)
    (hA : 4^N = 1 + 3^(s+1)*c)
    (hc : c = 1 + 3*z)
    (hE : E = 1 + 3*3^(s+1)*T)
    (hPow : E = 4^K) :
    gstWideCarryS (4^(N+1)) (4^K) (s+2+q) =
      gstAffineMulCarryS 4 1 (z + 4^N*T) q +
        4 * gstAffineMulCarryS (4^N) z T q := by
  have hD3 : 3 ≤ 3^(s+1) := by
    have h9 : 9 ≤ 3^(s+1) := by
      rw [show (9:Nat) = 3^2 by decide]
      exact Nat.pow_le_pow_of_le (by decide : 1 < 3) (by omega)
    omega
  have hDpos : 0 < 3^(s+1) := Nat.pow_pos (by decide)
  have hD1 : 1 ≤ 3^(s+1) := by omega
  have hstrip := gst_shared_state_is_pure_power_residue_stripS
    N (3^(s+1)) c z T E K q hD3 hD1 hA hc hE hPow
  have hrect := gst_residue_strip_quotient_is_exact_power_wide_carryS
    s K q (N+1)
  have hwide :
      gstStripQuotientS
          (4^K % gstResidueTowerModulusS (3^(s+1)) q)
          (gstResidueTowerModulusS (3^(s+1)) q) (N+1) =
        gstWideCarryS (4^(N+1)) (4^K) (s+2+q) := by
    rw [hrect]
    rfl
  exact hwide.symm.trans hstrip

/-- The physical wide carry and the affine shared carrier are the same integer. -/
theorem gst_exact_power_rectangle_is_shared_carrierS
    (s N c z T E K q : Nat)
    (hs : 1 ≤ s)
    (hA : 4^N = 1 + 3^(s+1)*c)
    (hc : c = 1 + 3*z)
    (hE : E = 1 + 3*3^(s+1)*T)
    (hPow : E = 4^K) :
    gstWideCarryS (4^(N+1)) (4^K) (s+2+q) =
      gstAffineMulCarryS (4*(4^N)) (1 + 4*z) T q := by
  have hwide := gst_shared_state_is_exact_power_rectangleS
    s N c z T E K q hs hA hc hE hPow
  have hstate := gst_shared_information_state_exactS (4^N) z T q
  exact hwide.trans hstate.symm

/-- Exact channel equation in physical power-grid coordinates. Sampling the
seven-axis GST rectangle every k=s+1 ternary rows gives the nonlinear block
echo without an abstract endpoint replacement. -/
theorem gst_exact_power_block_channel_echoS
    (s N c z T E K q : Nat)
    (hs : 1 ≤ s)
    (hA : 4^N = 1 + 3^(s+1)*c)
    (hc : c = 1 + 3*z)
    (hE : E = 1 + 3*3^(s+1)*T)
    (hPow : E = 4^K) :
    let U := (T / 3^q) % 3^(s+1)
    gstWideCarryS (4^(N+1)) (4^K) (s+2+(q+(s+1))) =
      4*c*U +
        (gstWideCarryS (4^(N+1)) (4^K) (s+2+q) + 4*U) / 3^(s+1) := by
  dsimp only
  have hq := gst_exact_power_rectangle_is_shared_carrierS
    s N c z T E K q hs hA hc hE hPow
  have hqk := gst_exact_power_rectangle_is_shared_carrierS
    s N c z T E K (q+(s+1)) hs hA hc hE hPow
  have hblock := gst_shared_information_block_echoV2S
    (4^N) c (3^(s+1)) z T q (s+1) rfl hA
  dsimp only at hblock
  have hmul : 4 * 4^N = 4^(N+1) := by
    rw [Nat.pow_succ]
    ac_rfl
  have hq' :
      gstWideCarryS (4^(N+1)) (4^K) (s+2+q) =
        gstAffineMulCarryS (4^(N+1)) (1 + 4*z) T q := by
    simpa [hmul] using hq
  have hqk' :
      gstWideCarryS (4^(N+1)) (4^K) (s+2+(q+(s+1))) =
        gstAffineMulCarryS (4^(N+1)) (1 + 4*z) T (q+(s+1)) := by
    simpa [hmul] using hqk
  rw [hmul] at hblock
  rw [← hq', ← hqk'] at hblock
  exact hblock

/-- Exact conservation across one physical GST power rectangle. -/
theorem gst_exact_power_rectangle_conservationS
    (s N K q : Nat) :
    4^(N+1) * gstDigitS (4^K) (s+2+q) +
        gstWideCarryS (4^(N+1)) (4^K) (s+2+q) =
      gstDigitS (4^(K+N+1)) (s+2+q) +
        3 * gstWideCarryS (4^(N+1)) (4^K) ((s+2+q)+1) := by
  have h := gst_strip_conservation_exactS
    (4^(N+1)) (4^K) (s+2+q)
  have hpow : 4^(N+1) * 4^K = 4^(K+N+1) := by
    calc
      4^(N+1) * 4^K = 4^((N+1)+K) := (Nat.pow_add 4 (N+1) K).symm
      _ = 4^(K+N+1) := by congr 1 <;> omega
  simpa [gstWideDigitS, gstDigitS, hpow] using h

/-- Parent badness is a forbidden-sector statement about one quotient of an
exact power-of-four residue. -/
theorem gst_pure_power_parent_bad_forbids_residue_sectorS
    (N D c z T E K q : Nat)
    (hD3 : 3 ≤ D)
    (hD1 : 1 ≤ D)
    (hA : 4^N = 1 + D*c)
    (hc : c = 1 + 3*z)
    (hE : E = 1 + 3*D*T)
    (hPow : E = 4^K)
    (hbad : GSTBadPairS
      (gstAffineMulCarryS 4 1 (z + 4^N*T) q)
      ((gstAffineMulCarryS (4^N) z T q + gstDigitS T q) % 3)) :
    let S := gstStripQuotientS
      (4^K % gstResidueTowerModulusS D q)
      (gstResidueTowerModulusS D q) (N+1)
    ¬ GSTParentHappyResidue12S S (gstDigitS T q) := by
  dsimp only
  have hS := gst_shared_state_is_pure_power_residue_stripS
    N D c z T E K q hD3 hD1 hA hc hE hPow
  let P := gstAffineMulCarryS 4 1 (z + 4^N*T) q
  let Z := gstAffineMulCarryS (4^N) z T q
  let r := gstDigitS T q
  have hP : P < 4 := by
    dsimp [P]
    exact gst_affine_carry_lt_multiplierS 4 1 (z + 4^N*T) q (by decide) (by decide)
  have hr : r < 3 := by
    dsimp [r, gstDigitS]
    exact Nat.mod_lt _ (by decide)
  have hshape :
      gstStripQuotientS
          (4^K % gstResidueTowerModulusS D q)
          (gstResidueTowerModulusS D q) (N+1) = P + 4*Z := by
    simpa [P, Z] using hS
  have hiff := gst_parent_bad_iff_avoids_shared_residue12S
    (gstStripQuotientS
      (4^K % gstResidueTowerModulusS D q)
      (gstResidueTowerModulusS D q) (N+1)) P Z r hP hr hshape
  apply hiff.mp
  simpa [P, Z, r] using hbad
