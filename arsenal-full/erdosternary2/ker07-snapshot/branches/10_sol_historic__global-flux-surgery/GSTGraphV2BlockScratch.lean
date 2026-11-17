/- ======================================================================
/- CHRONOLOGICAL LABEL -- #0522 / 1132
/-    Path         : branches/sol_global-flux-surgery/GSTGraphV2BlockScratch.lean
/-    Ref          : origin/sol/global-flux-surgery
/-    First-commit : 2026-08-16 02:02:40 +0530  (6271946)
/-    Last-commit  : 2026-08-16 02:16:33 +0530  (16e59bc)
/-    Total commits: 2
/- ======================================================================
/- GIT HISTORY (chronological, oldest first)
/- ======================================================================
/- [01/2] 2026-08-16 02:02:40 +0530  6271946  (ker07-dev)
/-        Add GST Graph V2 block echo recurrence
/- [02/2] 2026-08-16 02:16:33 +0530  16e59bc  (ker07-dev)
/-        Wire GST Graph V2 flux sectors into block graph
/- ====================================================================== -/

import GSTGraphV2FluxScratch

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

/-!
Block-scale GST Graph V2 laws.
The vertical Omega graph is sampled every k ternary rows without introducing a
terminal cutoff.  The whole k-trit child block is retained as one exact radix
coordinate.
-/

/-- Generic affine carry sampled across a block of `k` ternary rows. -/
theorem gst_affine_block_step_exactV2S
    (B z T q k : Nat) :
    gstAffineMulCarryS B z T (q+k) =
      (gstAffineMulCarryS B z T q +
        B * ((T / 3^q) % 3^k)) / 3^k := by
  simp only [gstAffineMulCarryS]
  rw [Nat.pow_add, Nat.mod_mul]
  have hqpos : 0 < 3^q := Nat.pow_pos (by decide)
  have hshape :
      z + B * (T % 3^q + 3^q * (T / 3^q % 3^k)) =
        (z + B * (T % 3^q)) +
          3^q * (B * (T / 3^q % 3^k)) := by
    rw [Nat.mul_add]
    ac_rfl
  rw [hshape, ← Nat.div_div_eq_div_mul,
      Nat.add_mul_div_left _ _ hqpos]

/-- Exact block echo of the shared information carrier.

With block width `k`, `D = 3^k`, and GST multiplier `A = 1 + D*c`, write

  S_q = affineCarry(4A,1+4z,T,q)
  U_q = (T/3^q) mod D.

Then one whole block advance is

  S_(q+k) = 4*c*U_q + floor((S_q + 4*U_q)/D).

The term `4*c*U_q` is the explicit shifted information echo; the second term
is the retained residual carrier. -/
theorem gst_shared_information_block_echoV2S
    (A c D z T q k : Nat)
    (hD : D = 3^k)
    (hA : A = 1 + D*c) :
    let S := gstAffineMulCarryS (4*A) (1 + 4*z) T q
    let U := (T / 3^q) % D
    gstAffineMulCarryS (4*A) (1 + 4*z) T (q+k) =
      4*c*U + (S + 4*U) / D := by
  dsimp only
  have hstep :=
    gst_affine_block_step_exactV2S (4*A) (1 + 4*z) T q k
  have hDpos : 0 < D := by
    rw [hD]
    exact Nat.pow_pos (by decide)
  rw [← hD] at hstep
  calc
    gstAffineMulCarryS (4*A) (1 + 4*z) T (q+k) =
        (gstAffineMulCarryS (4*A) (1 + 4*z) T q +
          (4*A) * ((T / 3^q) % D)) / D := hstep
    _ = ((gstAffineMulCarryS (4*A) (1 + 4*z) T q +
          4 * ((T / 3^q) % D)) +
          D * (4*c*((T / 3^q) % D))) / D := by
          rw [hA]
          congr 1
          ring
    _ = (gstAffineMulCarryS (4*A) (1 + 4*z) T q +
          4 * ((T / 3^q) % D)) / D +
          4*c*((T / 3^q) % D) := by
          rw [Nat.add_mul_div_left _ _ hDpos]
    _ = 4*c*((T / 3^q) % D) +
          (gstAffineMulCarryS (4*A) (1 + 4*z) T q +
            4 * ((T / 3^q) % D)) / D := by ac_rfl
