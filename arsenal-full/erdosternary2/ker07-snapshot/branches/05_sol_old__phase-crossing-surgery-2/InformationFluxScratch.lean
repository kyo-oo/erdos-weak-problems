/- ======================================================================
/- CHRONOLOGICAL LABEL -- #0255 / 1132
/-    Path         : branches/sol_phase-crossing-surgery-2/InformationFluxScratch.lean
/-    Ref          : origin/sol/phase-crossing-surgery-2
/-    First-commit : 2026-08-15 14:29:36 +0530  (f8e139c)
/-    Last-commit  : 2026-08-15 14:54:06 +0530  (db9648e)
/-    Total commits: 2
/- ======================================================================
/- GIT HISTORY (chronological, oldest first)
/- ======================================================================
/- [01/2] 2026-08-15 14:29:36 +0530  f8e139c  (ker07-dev)
/-        Formalize shared information strip coordinates
/- [02/2] 2026-08-15 14:54:06 +0530  db9648e  (ker07-dev)
/-        Normalize right shared-information endpoint
/- ====================================================================== -/

import InformationCarryWordBridgeScratch
import InformationStateScratch

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

/-- Every horizontal GST carry across the canonical phase strip is literally
    one base-4 coordinate of the same shared information state. -/
theorem gst_shared_information_horizontal_coordinateS
    (N D c z T q i : Nat)
    (hi : i ≤ N)
    (hD : 3 ≤ D)
    (hA : 4^N = 1 + D*c)
    (hc : c = 1 + 3*z) :
    let r := 1 + 3*D*(T % 3^q)
    let M := 3*D*3^q
    let S := gstAffineMulCarryS (4*(4^N)) (1 + 4*z) T q
    gstInformationCarryAtS S (N-i) = gstStripCarryS r M i := by
  dsimp only
  have hDpos : 0 < D := by omega
  have hM : 0 < 3*D*3^q := by
    exact Nat.mul_pos (Nat.mul_pos (by decide) hDpos) (Nat.pow_pos (by decide))
  have hbridge :=
    gst_shared_information_is_carry_wordS N D c z T q hD hA hc
  have hstate := gst_shared_information_state_exactS (4^N) z T q
  have hfinal :
      gstStripQuotientS
          (1 + 3*D*(T % 3^q))
          (3*D*3^q)
          (N+1) =
        gstAffineMulCarryS (4*(4^N)) (1 + 4*z) T q := by
    exact hbridge.trans hstate.symm
  have hcoord :=
    gst_strip_carry_is_information_digitS
      (1 + 3*D*(T % 3^q)) (3*D*3^q) i (N-i) hM
  have hidx : i + (N-i) + 1 = N+1 := by omega
  rw [hidx, hfinal] at hcoord
  simpa [gstInformationCarryAtS] using hcoord

/-- The left boundary carry of the horizontal strip is exactly the child GST
    carry.  This is the top coordinate of the shared information word. -/
theorem gst_shared_information_left_endpointS
    (N D c z T q : Nat)
    (hD : 9 ≤ D)
    (hA : 4^N = 1 + D*c)
    (hc : c = 1 + 3*z) :
    gstStripCarryS
        (1 + 3*D*(T % 3^q))
        (3*D*3^q) 0 = gstCarryS T q := by
  have hD3 : 3 ≤ D := by omega
  have hcoord :=
    gst_shared_information_horizontal_coordinateS
      N D c z T q 0 (by omega) hD3 hA hc
  dsimp only at hcoord
  have hcpos : 1 ≤ c := by omega
  have hzdiv : c / 3 = z := by
    rw [hc, Nat.add_mul_div_left 1 z (by decide : 0 < 3)]
    norm_num
  have hoff := gst_gst_offsets_lt_multiplierS D c hD hcpos
  have hz1 : 1 + 4*z < 4^N := by
    rw [← hzdiv, hA]
    exact hoff.2
  have hApos : 0 < 4^N := Nat.pow_pos (by decide)
  have htop :=
    gst_shared_information_top_coordinateS
      (4^N) z T q N rfl hApos hz1
  dsimp only at htop
  have hC : gstCarryS T q < 4 := by
    have h := gst_affine_carry_lt_multiplierS 4 0 T q (by decide) (by decide)
    simpa [gstCarryS, gstAffineMulCarryS] using h
  have hinfo :
      gstInformationCarryAtS
          (gstAffineMulCarryS (4*(4^N)) (1 + 4*z) T q) N =
        gstCarryS T q := by
    unfold gstInformationCarryAtS
    rw [htop]
    exact Nat.mod_eq_of_lt hC
  exact hcoord.symm.trans hinfo

/-- The right boundary carry of the horizontal strip is exactly the seed-one
    parent GST carry.  This is the bottom coordinate of the same information
    word. -/
theorem gst_shared_information_right_endpointS
    (N D c z T q : Nat)
    (hD : 3 ≤ D)
    (hA : 4^N = 1 + D*c)
    (hc : c = 1 + 3*z) :
    gstStripCarryS
        (1 + 3*D*(T % 3^q))
        (3*D*3^q) N =
      gstAffineMulCarryS 4 1 (z + 4^N*T) q := by
  have hcoord :=
    gst_shared_information_horizontal_coordinateS
      N D c z T q N (by omega) hD hA hc
  dsimp only at hcoord
  have hcoord0 :
      gstStripCarryS
          (1 + 3*D*(T % 3^q))
          (3*D*3^q) N =
        gstInformationCarryAtS
          (gstAffineMulCarryS (4*(4^N)) (1 + 4*z) T q) 0 := by
    simpa using hcoord.symm
  have hp : gstAffineMulCarryS 4 1 (z + 4^N*T) q < 4 :=
    gst_affine_carry_lt_multiplierS 4 1 (z + 4^N*T) q (by decide) (by decide)
  have hbottom :=
    gst_shared_information_bottom_coordinatesS (4^N) z T q hp
  dsimp only at hbottom
  calc
    gstStripCarryS
        (1 + 3*D*(T % 3^q))
        (3*D*3^q) N =
      gstInformationCarryAtS
        (gstAffineMulCarryS (4*(4^N)) (1 + 4*z) T q) 0 := hcoord0
    _ = gstAffineMulCarryS 4 1 (z + 4^N*T) q := by
      simpa [gstInformationCarryAtS] using hbottom.1
