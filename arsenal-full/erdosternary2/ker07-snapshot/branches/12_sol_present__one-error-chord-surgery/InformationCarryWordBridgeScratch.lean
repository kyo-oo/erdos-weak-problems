/- ======================================================================
/- CHRONOLOGICAL LABEL -- #0223 / 1132
/-    Path         : branches/sol_one-error-chord-surgery/InformationCarryWordBridgeScratch.lean
/-    Ref          : origin/sol/one-error-chord-surgery
/-    First-commit : 2026-08-15 11:10:44 +0530  (ee551f5)
/-    Last-commit  : 2026-08-15 14:47:01 +0530  (c5bba4f)
/-    Total commits: 5
/- ======================================================================
/- GIT HISTORY (chronological, oldest first)
/- ======================================================================
/- [01/5] 2026-08-15 11:10:44 +0530  ee551f5  (ker07-dev)
/-        Kernel-check shared information carry-word bridge
/- [02/5] 2026-08-15 11:36:23 +0530  4fb251d  (ker07-dev)
/-        Close carry-word bridge quotient rewrite
/- [03/5] 2026-08-15 14:26:18 +0530  67d258f  (ker07-dev)
/-        Fix information carry-word bridge normalization
/- [04/5] 2026-08-15 14:40:24 +0530  adce651  (ker07-dev)
/-        Close carry-word quotient identity explicitly
/- [05/5] 2026-08-15 14:47:01 +0530  c5bba4f  (ker07-dev)
/-        Confine carry-word quotient decomposition rewrite
/- ====================================================================== -/

import InformationDescentScratch
import CarryWordScratch

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

/-- The commuting-square shared-information integer is literally the horizontal
    GST carry word across the corresponding power-of-four strip. -/
theorem gst_shared_information_is_carry_wordS
    (N D c z T q : Nat)
    (hD : 3 ≤ D)
    (hA : 4^N = 1 + D*c)
    (hc : c = 1 + 3*z) :
    gstStripQuotientS
        (1 + 3*D*(T % 3^q))
        (3*D*3^q)
        (N+1) =
      gstAffineMulCarryS 4 1 (z + 4^N*T) q +
        4 * gstAffineMulCarryS (4^N) z T q := by
  let M : Nat := 3^q
  let K : Nat := 1 + 4*(z + 4^N*(T % M))
  have hM : 0 < M := by
    dsimp [M]
    exact Nat.pow_pos (by decide)
  have hDpos : 0 < D := by omega
  have h3Dpos : 0 < 3*D := Nat.mul_pos (by decide) hDpos
  have hDen : 0 < 3*D*M := Nat.mul_pos h3Dpos hM

  have hnum :
      4^(N+1) * (1 + 3*D*(T % M)) =
        (D+4) + 3*D*K := by
    dsimp [K]
    rw [Nat.pow_succ, hA, hc]
    ring

  have hKsplit : K = M*(K/M) + K%M := by
    have h := Nat.mod_add_div K M
    omega

  have hr : K % M < M := Nat.mod_lt _ hM
  have hsmall : D + 4 < 3*D := by omega
  have hrsucc : K % M + 1 ≤ M := Nat.succ_le_of_lt hr
  have hmul : 3*D*(K % M + 1) ≤ 3*D*M :=
    Nat.mul_le_mul_left (3*D) hrsucc
  have hres : (D+4) + 3*D*(K%M) < 3*D*M := by
    have hlt : (D+4) + 3*D*(K%M) < 3*D + 3*D*(K%M) := by
      omega
    have hshape : 3*D + 3*D*(K%M) = 3*D*(K%M + 1) := by ring
    rw [hshape] at hlt
    exact lt_of_lt_of_le hlt hmul

  have hword :
      gstStripQuotientS
          (1 + 3*D*(T % M))
          (3*D*M)
          (N+1) = K/M := by
    unfold gstStripQuotientS
    rw [hnum]
    have hshape0 :
        (D+4) + 3*D*K =
          (D+4) + 3*D*(M*(K/M) + K%M) :=
      congrArg (fun x => (D+4) + 3*D*x) hKsplit
    have hshape :
        (D + 4) + 3 * D * K =
          ((D+4) + 3*D*(K%M)) + (3*D*M)*(K/M) := by
      calc
        (D+4) + 3*D*K =
            (D+4) + 3*D*(M*(K/M) + K%M) := hshape0
        _ = ((D+4) + 3*D*(K%M)) + (3*D*M)*(K/M) := by ring
    rw [hshape, Nat.add_mul_div_left _ _ hDen]
    rw [Nat.div_eq_of_lt hres]
    simp

  have hmod :
      (z + 4^N*(T % M)) % M = (z + 4^N*T) % M := by
    simp [Nat.add_mod, Nat.mul_mod]

  have hparent :
      gstAffineMulCarryS 4 1 (z + 4^N*(T % M)) q =
        gstAffineMulCarryS 4 1 (z + 4^N*T) q := by
    unfold gstAffineMulCarryS
    dsimp [M] at hmod
    rw [hmod]

  have hdecomp :=
    gst_affine_tail_div_decompositionS 1 4 (z + 4^N*(T % M)) q
  have hshared :
      K/M =
        gstAffineMulCarryS 4 1 (z + 4^N*T) q +
          4 * gstAffineMulCarryS (4^N) z T q := by
    dsimp [K, M]
    dsimp [M] at hparent hdecomp
    rw [hdecomp, hparent]
    rfl

  dsimp [M] at hword
  exact hword.trans hshared
