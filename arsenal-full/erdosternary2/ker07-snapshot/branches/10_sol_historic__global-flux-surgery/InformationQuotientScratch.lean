/- ======================================================================
/- CHRONOLOGICAL LABEL -- #0387 / 1132
/-    Path         : branches/sol_global-flux-surgery/InformationQuotientScratch.lean
/-    Ref          : origin/sol/global-flux-surgery
/-    First-commit : 2026-08-15 19:46:39 +0530  (93fd090)
/-    Last-commit  : 2026-08-15 19:46:39 +0530  (93fd090)
/-    Total commits: 1
/- ======================================================================
/- GIT HISTORY (chronological, oldest first)
/- ======================================================================
/- [01/1] 2026-08-15 19:46:39 +0530  93fd090  (ker07-dev)
/-        Add exact shared-information quotient invariants
/- ====================================================================== -/

import InformationDescentScratch

/-!
Exact consequences of the kernel-green shared-information equation.
No universal Erdős claim is made here.
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

/-- The child GST carry is literally the base-A quotient of the shared
    information state `p + 4*a0`. -/
theorem gst_shared_information_childCarry_is_quotientS
    (A z T q : Nat) (hA : 0 < A) (hz1 : 1 + 4*z < A) :
    gstCarryS T q =
      (gstAffineMulCarryS 4 1 (z + A*T) q +
        4 * gstAffineMulCarryS A z T q) / A := by
  have hEq := gst_shared_information_carry_equationS A z T q
  have ha1 : gstAffineMulCarryS A (1 + 4*z) (4*T) q < A :=
    gst_affine_carry_lt_multiplierS A (1 + 4*z) (4*T) q hA hz1
  have hdecomp :
      gstAffineMulCarryS 4 1 (z + A*T) q +
          4 * gstAffineMulCarryS A z T q =
        A * gstCarryS T q +
          gstAffineMulCarryS A (1 + 4*z) (4*T) q := by
    omega
  rw [hdecomp]
  exact (Nat.mul_add_div A (gstCarryS T q)
    (gstAffineMulCarryS A (1 + 4*z) (4*T) q)).trans (by
      rw [Nat.div_eq_of_lt ha1]
      simp [hA])

/-- The complementary affine carry is literally the base-A remainder of the
    same shared information state. -/
theorem gst_shared_information_affineCarry_is_remainderS
    (A z T q : Nat) (hA : 0 < A) (hz1 : 1 + 4*z < A) :
    gstAffineMulCarryS A (1 + 4*z) (4*T) q =
      (gstAffineMulCarryS 4 1 (z + A*T) q +
        4 * gstAffineMulCarryS A z T q) % A := by
  have hEq := gst_shared_information_carry_equationS A z T q
  have ha1 : gstAffineMulCarryS A (1 + 4*z) (4*T) q < A :=
    gst_affine_carry_lt_multiplierS A (1 + 4*z) (4*T) q hA hz1
  have hdecomp :
      gstAffineMulCarryS 4 1 (z + A*T) q +
          4 * gstAffineMulCarryS A z T q =
        A * gstCarryS T q +
          gstAffineMulCarryS A (1 + 4*z) (4*T) q := by
    omega
  rw [hdecomp, Nat.add_mod]
  simp [Nat.mod_eq_of_lt ha1, hA]

/-- The perfect-power energy of the child and the prefix multiplier combine
    exactly to the prefix-one parent perfect power. -/
theorem gst_prefix_one_perfect_power_energy_factorS (s n : Nat) :
    4^(3^s) * 4^(3^(s+1) * n) = 4^(3^s * (1 + 3*n)) := by
  rw [← Nat.pow_add]
  congr 1
  rw [Nat.pow_succ]
  ring
