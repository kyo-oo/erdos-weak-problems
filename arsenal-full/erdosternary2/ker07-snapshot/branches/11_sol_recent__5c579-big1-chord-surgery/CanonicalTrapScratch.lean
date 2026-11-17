/- ======================================================================
/- CHRONOLOGICAL LABEL -- #0352 / 1132
/-    Path         : branches/sol_5c579-big1-chord-surgery/CanonicalTrapScratch.lean
/-    Ref          : origin/sol/5c579-big1-chord-surgery
/-    First-commit : 2026-08-15 17:25:33 +0530  (c11d099)
/-    Last-commit  : 2026-08-15 20:19:31 +0530  (9daa91d)
/-    Total commits: 2
/- ======================================================================
/- GIT HISTORY (chronological, oldest first)
/- ======================================================================
/- [01/2] 2026-08-15 17:25:33 +0530  c11d099  (ker07-dev)
/-        Package canonical two-boundary information trap
/- [02/2] 2026-08-15 20:19:31 +0530  9daa91d  (ker07-dev)
/-        Kernel-check canonical prefix recurrence in active frontier
/- ====================================================================== -/

import LastGateTrapScratch
import InformationStateScratch
import CanonicalPrefixScratch

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

/-- After the globally last child Happy Gate, a hypothetical completely bad
    prefix-one parent traps the regenerated information between two complete
    seeded bad boundaries.  This is a packaging theorem only: it asserts no
    final separation principle.

    D = regenerated parent carry seed
    Z = regenerated low affine quotient
    W = regenerated high latent remainder
    C = regenerated child carry seed (2 or 3)
    Y = remaining child ternary suffix

    The exact shared-information equation D + 4 Z = W + A C is retained. -/
theorem gst_canonical_two_boundary_trapS
    (A z T : Nat)
    (hA : 0 < A)
    (hz1 : 1 + 4*z < A)
    (hparent : GSTSeededBadTraceS 1 (z + A*T))
    (hchild : ∃ j, GSTSeededHappyS 0 T j) :
    ∃ q,
      let D := gstAffineMulCarryS 4 1 (z + A*T) (q+1)
      let Z := gstAffineMulCarryS A z T (q+1)
      let W := gstAffineMulCarryS A (1 + 4*z) (4*T) (q+1)
      let C := gstAffineMulCarryS 4 0 T (q+1)
      let Y := T / 3^(q+1)
      GSTSeededBadTraceS D (Z + A*Y) ∧
      GSTSeededBadTraceS C Y ∧
      (C = 2 ∨ C = 3) ∧
      D + 4*Z = W + A*C ∧
      W < A := by
  obtain ⟨q, hq, hlast⟩ :=
    gst_exists_global_last_seeded_gateS 0 T hchild
  refine ⟨q, ?_⟩
  dsimp only

  have hparentSuffix :=
    gst_seeded_bad_trace_suffixS 1 (z + A*T) (q+1) hparent
  have hparentShape := gst_relative_affine_suffixS A z T (q+1)
  rw [hparentShape] at hparentSuffix

  have hchildSuffix :=
    gst_suffix_after_last_gate_is_badS 0 T q hq hlast
  dsimp only at hchildSuffix
  have hchildStep := gstAffineS_forward_exact_all 0 T q
  have hCeq :
      gstAffineMulCarryS 4 0 T (q+1) =
        gstStepCarryS (gstAffineMulCarryS 4 0 T q) 2 := by
    rw [hchildStep, hq.1]
  rw [← hCeq] at hchildSuffix

  have hlatent0 := gst_child_gate_high_realisationS
    (gstAffineMulCarryS 4 0 T q) hq.2
  have hlatent :
      gstAffineMulCarryS 4 0 T (q+1) = 2 ∨
      gstAffineMulCarryS 4 0 T (q+1) = 3 := by
    rw [hCeq]
    exact hlatent0.2

  have hEq := gst_shared_information_carry_equationS A z T (q+1)
  have hcarryEq :
      gstCarryS T (q+1) = gstAffineMulCarryS 4 0 T (q+1) := by
    simp [gstCarryS, gstAffineMulCarryS]
  rw [hcarryEq] at hEq
  have hshared :
      gstAffineMulCarryS 4 1 (z + A*T) (q+1) +
          4 * gstAffineMulCarryS A z T (q+1) =
        gstAffineMulCarryS A (1 + 4*z) (4*T) (q+1) +
          A * gstAffineMulCarryS 4 0 T (q+1) := hEq.symm

  have hW : gstAffineMulCarryS A (1 + 4*z) (4*T) (q+1) < A :=
    gst_affine_carry_lt_multiplierS A (1 + 4*z) (4*T) (q+1) hA hz1

  exact ⟨hparentSuffix, hchildSuffix, hlatent, hshared, hW⟩
