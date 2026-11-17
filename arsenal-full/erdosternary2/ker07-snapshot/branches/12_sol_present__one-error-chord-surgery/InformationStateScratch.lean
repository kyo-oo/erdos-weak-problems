/- ======================================================================
/- CHRONOLOGICAL LABEL -- #0238 / 1132
/-    Path         : branches/sol_one-error-chord-surgery/InformationStateScratch.lean
/-    Ref          : origin/sol/one-error-chord-surgery
/-    First-commit : 2026-08-15 11:26:46 +0530  (ada5717)
/-    Last-commit  : 2026-08-15 14:26:37 +0530  (c5ca346)
/-    Total commits: 2
/- ======================================================================
/- GIT HISTORY (chronological, oldest first)
/- ======================================================================
/- [01/2] 2026-08-15 11:26:46 +0530  ada5717  (ker07-dev)
/-        Add single shared information-state normalization
/- [02/2] 2026-08-15 14:26:37 +0530  c5ca346  (ker07-dev)
/-        Fix shared information state proof seams
/- ====================================================================== -/

import InformationDescentScratch
import InformationGeometryScratch

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

/-- The bottom decomposition D + 4 Z is itself one seeded affine information
    carry with multiplier 4*A. -/
theorem gst_shared_information_state_exactS
    (A z T q : Nat) :
    gstAffineMulCarryS (4*A) (1 + 4*z) T q =
      gstAffineMulCarryS 4 1 (z + A*T) q +
        4 * gstAffineMulCarryS A z T q := by
  let M := 3^q
  have hM : 0 < M := by
    dsimp [M]
    exact Nat.pow_pos (by decide)
  let Y := z + A*(T % M)
  have hmodY : Y % M = (z + A*T) % M := by
    dsimp [Y, M]
    simp [Nat.add_mod, Nat.mul_mod]
  have hdiv := gst_affine_tail_div_decompositionS 1 4 Y q
  have hYdiv : Y / M = gstAffineMulCarryS A z T q := by
    dsimp [Y, M, gstAffineMulCarryS]
  have hparent :
      gstAffineMulCarryS 4 1 Y q =
        gstAffineMulCarryS 4 1 (z + A*T) q := by
    unfold gstAffineMulCarryS
    dsimp [M] at hmodY
    rw [hmodY]
  calc
    gstAffineMulCarryS (4*A) (1 + 4*z) T q =
        (1 + 4*Y) / 3^q := by
          unfold gstAffineMulCarryS
          dsimp [Y, M]
          congr 1
          ring
    _ = gstAffineMulCarryS 4 1 Y q + 4 * (Y / 3^q) := hdiv
    _ = gstAffineMulCarryS 4 1 (z + A*T) q +
          4 * gstAffineMulCarryS A z T q := by
          dsimp [M] at hYdiv
          rw [hparent, hYdiv]

/-- One shared information state obeys the exact ternary vertical recurrence. -/
theorem gst_shared_information_state_forwardS
    (A z T q : Nat) :
    gstAffineMulCarryS (4*A) (1 + 4*z) T (q+1) =
      (gstAffineMulCarryS (4*A) (1 + 4*z) T q +
        (4*A) * gstDigitS T q) / 3 := by
  simp only [gstAffineMulCarryS, gstDigitS, Nat.pow_succ]
  have hp : 0 < 3^q := Nat.pow_pos (by decide)
  have hsplit : T % (3^q * 3) =
      T % 3^q + 3^q * (T / 3^q % 3) := by
    rw [Nat.mod_mul]
  rw [hsplit, Nat.mul_add]
  rw [show (4*A) * (3^q * (T / 3^q % 3)) =
      3^q * ((4*A) * (T / 3^q % 3)) by ac_rfl]
  rw [show
      1 + 4*z + ((4*A) * (T % 3^q) +
        3^q * ((4*A) * (T / 3^q % 3))) =
      (1 + 4*z + (4*A) * (T % 3^q)) +
        3^q * ((4*A) * (T / 3^q % 3)) by ring]
  rw [← Nat.div_div_eq_div_mul]
  rw [Nat.add_mul_div_left _ _ hp]

/-- The parent seeded carry and vertical affine carry are exactly the bottom
    base-4 digit and quotient of the shared information state. -/
theorem gst_shared_information_bottom_coordinatesS
    (A z T q : Nat)
    (hD : gstAffineMulCarryS 4 1 (z + A*T) q < 4) :
    let S := gstAffineMulCarryS (4*A) (1 + 4*z) T q
    let D := gstAffineMulCarryS 4 1 (z + A*T) q
    let Z := gstAffineMulCarryS A z T q
    S % 4 = D ∧ S / 4 = Z := by
  dsimp only
  have hS := gst_shared_information_state_exactS A z T q
  exact gst_information_low_coordinatesS
    _ _ _ hD hS

/-- The child carry is the top base-4 coordinate of the same information word. -/
theorem gst_shared_information_top_coordinateS
    (A z T q N : Nat)
    (hA : A = 4^N)
    (hApos : 0 < A)
    (hz1 : 1 + 4*z < A) :
    let S := gstAffineMulCarryS (4*A) (1 + 4*z) T q
    let C := gstCarryS T q
    S / A = C := by
  dsimp only
  have hEq := gst_shared_information_carry_equationS A z T q
  have hW : gstAffineMulCarryS A (1 + 4*z) (4*T) q < A :=
    gst_affine_carry_lt_multiplierS A (1 + 4*z) (4*T) q hApos hz1
  have hShared := gst_shared_information_state_exactS A z T q
  rw [hShared]
  rw [← hEq]
  have hcoord := gst_information_high_coordinatesS
    (gstAffineMulCarryS A (1 + 4*z) (4*T) q + A * gstCarryS T q)
    (gstAffineMulCarryS A (1 + 4*z) (4*T) q)
    A (gstCarryS T q) hApos hW rfl
  exact hcoord.2

/-- If A ≡ 1 (mod 3), the parent digit is read from the vertical information
    quotient Z together with the current child digit. -/
theorem gst_parent_digit_from_informationS
    (A z T q : Nat) (hA3 : A % 3 = 1) :
    gstDigitS (z + A*T) q =
      (gstAffineMulCarryS A z T q + gstDigitS T q) % 3 := by
  have htail := gst_affine_tail_div_decompositionS z A T q
  unfold gstDigitS
  rw [htail]
  have hmul : (A * (T / 3^q)) % 3 = gstDigitS T q := by
    unfold gstDigitS
    calc
      (A * (T / 3^q)) % 3 =
          ((A % 3) * ((T / 3^q) % 3)) % 3 := Nat.mul_mod A (T / 3^q) 3
      _ = (T / 3^q) % 3 := by simp [hA3]
  rw [Nat.add_mod, hmul]
  simpa [gstDigitS] using
    (Nat.add_mod
      (gstAffineMulCarryS A z T q)
      (T / 3^q % 3) 3).symm
