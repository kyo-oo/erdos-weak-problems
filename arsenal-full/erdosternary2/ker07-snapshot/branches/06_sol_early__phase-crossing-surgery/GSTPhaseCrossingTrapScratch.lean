/- ======================================================================
/- CHRONOLOGICAL LABEL -- #0694 / 1132
/-    Path         : branches/sol_phase-crossing-surgery/GSTPhaseCrossingTrapScratch.lean
/-    Ref          : origin/sol/phase-crossing-surgery
/-    First-commit : 2026-08-17 00:30:32 +0530  (4b65951)
/-    Last-commit  : 2026-08-17 00:30:32 +0530  (4b65951)
/-    Total commits: 1
/- ======================================================================
/- GIT HISTORY (chronological, oldest first)
/- ======================================================================
/- [01/1] 2026-08-17 00:30:32 +0530  4b65951  (ker07-dev)
/-        Reduce canonical phase crossing failure to exact two-boundary trap
/- ====================================================================== -/

import GSTPhaseCrossingScratch
import CanonicalTrapScratch
import PurePowerBadAxisScratch

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

/-!
# Canonical phase-crossing trap reduction

This is a reduction lemma only.  It assumes that the phase-one double jump
never occurs and packages the resulting canonical state after the globally last
phase-zero Happy Gate.  No residual Omega theorem, global mirror principle,
terminal NULL interpretation, or universal Erdos statement is used.
-/

/-- Failure of canonical phase crossing traps the conserved information between
    two complete seeded-bad boundaries after the globally last child gate.
    The resulting equation is the exact finite target for the next surgery:

      Dq + 4*Zq = Wq + A*Cq,

    with Cq in {2,3} and Wq < A. -/
theorem gst_canonical_phase_crossing_failure_trapsS
    (s n c z T H E0 E1 q0 : Nat)
    (hs : 1 ≤ s) (hn : 1 ≤ n)
    (hA : 4^(3^s) = 1 + 3^(s+1)*c)
    (hc : c = 1 + 3*z)
    (hT : E0 = 1 + 3*3^(s+1)*T)
    (hH : H = z + 4^(3^s)*T)
    (hE0 : E0 = 4^(3^(s+1)*n))
    (hE1 : E1 = 4^(3^s*(1+3*n)))
    (hchild : GSTDoubleJumpS (3*3^(s+1)) E0 q0)
    (hnoParent : ∀ q, ¬ GSTDoubleJumpS (3*3^(s+1)) E1 q) :
    ∃ q,
      let Dq := gstAffineMulCarryS 4 1 (z + 4^(3^s)*T) (q+1)
      let Zq := gstAffineMulCarryS (4^(3^s)) z T (q+1)
      let Wq := gstAffineMulCarryS (4^(3^s)) (1 + 4*z) (4*T) (q+1)
      let Cq := gstAffineMulCarryS 4 0 T (q+1)
      let Y := T / 3^(q+1)
      GSTSeededBadTraceS Dq (Zq + 4^(3^s)*Y) ∧
      GSTSeededBadTraceS Cq Y ∧
      (Cq = 2 ∨ Cq = 3) ∧
      Dq + 4*Zq = Wq + 4^(3^s)*Cq ∧
      Wq < 4^(3^s) := by
  let D := 3^(s+1)
  let A := 4^(3^s)

  have hD9 : 9 ≤ D := by
    dsimp [D]
    rw [show (9 : Nat) = 3^2 by decide]
    exact Nat.pow_le_pow_of_le (by decide : 1 < 3) (by omega)
  have hD3 : 3 ≤ D := by omega
  have hApos : 0 < A := by
    dsimp [A]
    exact Nat.pow_pos (by decide)
  have hcpos : 1 ≤ c := by omega
  have hcz : c / 3 = z := by
    rw [hc, Nat.add_mul_div_left 1 z (by decide : 0 < 3)]
    decide
  have hz1 : 1 + 4*z < A := by
    have hoff := gst_gst_offsets_lt_multiplierS D c hD9 hcpos
    dsimp [A, D]
    rw [hA]
    simpa [hcz] using hoff.2

  have hchildGate :
      gstDigitS T q0 = 2 ∧
        (gstAffineMulCarryS 4 0 T q0 = 0 ∨
         gstAffineMulCarryS 4 0 T q0 = 3) := by
    have hiff := gst_phase0_seeded_happy_iff_double_jumpS
      D T E0 q0 hD3
        (by simpa [D, Nat.mul_assoc] using hT)
    exact hiff.mpr (by simpa [D, Nat.mul_assoc] using hchild)

  have hphase : E1 = A * E0 := by
    dsimp [A]
    rw [hE1, hE0]
    have hexp : 3^s * (1 + 3*n) = 3^s + 3^(s+1)*n := by
      rw [Nat.pow_succ]
      ring
    rw [hexp, Nat.pow_add]

  have hA' : A = 1 + D*c := by
    simpa [A, D] using hA
  have hT' : E0 = 1 + 3*D*T := by
    simpa [D, Nat.mul_assoc] using hT
  have haxis := gst_prefix_one_pure_power_axisS A D c z T E0 hA' hc hT'
  have hE1shape : E1 = 1 + D + 3*D*H := by
    rw [hphase]
    rw [← haxis]
    rw [hH]
    dsimp [A]
    ring

  have hparentBad : GSTSeededBadTraceS 1 H := by
    exact (gst_phase1_seeded_bad_iff_no_double_jumpS
      D H E1 hD3 hE1shape).2
        (by simpa [D, Nat.mul_assoc] using hnoParent)
  rw [hH] at hparentBad

  have htrap := gst_canonical_two_boundary_trapS
    A z T hApos hz1 hparentBad ⟨q0, hchildGate⟩
  simpa [A] using htrap
