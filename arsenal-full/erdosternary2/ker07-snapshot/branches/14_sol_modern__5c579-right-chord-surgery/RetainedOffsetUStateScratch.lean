/- ======================================================================
/- CHRONOLOGICAL LABEL -- #1007 / 1132
/-    Path         : branches/sol_5c579-right-chord-surgery/RetainedOffsetUStateScratch.lean
/-    Ref          : origin/sol/5c579-right-chord-surgery
/-    First-commit : 2026-08-17 11:02:14 +0530  (fd54c6b)
/-    Last-commit  : 2026-08-17 11:02:14 +0530  (fd54c6b)
/-    Total commits: 1
/- ======================================================================
/- GIT HISTORY (chronological, oldest first)
/- ======================================================================
/- [01/1] 2026-08-17 11:02:14 +0530  fd54c6b  (ker07-dev)
/-        Add retained-offset canonical U-state step
/- ====================================================================== -/

import ResidualNullTerminalScratch
import HandwrittenOmegaOriginCommutingSquareScratch

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

/-!
# Retained-offset canonical U-state

This is the generic natural-origin step needed after the first residual NULL
regeneration.  The finite offset and multiplier are never discarded.
-/

/-- One exact retained-offset natural-origin step. -/
theorem gst_retained_offset_u_state_stepS
    (Q : Nat → Nat → Nat)
    (hQ : GSTCanonicalOriginEnergyS Q)
    (t n offset mul seed : Nat) (ht : 1 ≤ t)
    (hbad : GSTSeededBadTraceS seed (offset + mul * Q t n)) :
    let originA := 4^(3^t)
    let E := offset + mul * Q t (n % 3)
    let r := E % 3
    let offset' := E / 3
    let mul' := mul * originA^(n % 3)
    let X' := offset' + mul' * Q (t+1) (n/3)
    let seed' := gstStepCarryS seed r
    offset + mul * Q t n = r + 3*X' ∧
      GSTSeededBadTraceS seed' X' ∧
      mul * gstOriginRemainingUS t n =
        mul' * gstOriginRemainingUS (t+1) (n/3) := by
  dsimp only
  let originA := 4^(3^t)
  let E := offset + mul * Q t (n % 3)
  let r := E % 3
  let offset' := E / 3
  let mul' := mul * originA^(n % 3)
  let X' := offset' + mul' * Q (t+1) (n/3)

  have hrec0 := gst_canonical_natural_origin_recurrenceS Q hQ t n ht
  have hn : n = 3*(n/3) + n%3 := by
    have h := Nat.mod_add_div n 3
    omega
  have hrec :
      Q t (3*(n/3) + n%3) =
        Q t (n%3) +
          3 * (4^(3^t))^(n%3) * Q (t+1) (n/3) := by
    rw [← hn]
    exact hrec0

  have hsplit0 := affine_natural_origin_stepS
    Q t n offset mul (4^(3^t)) hrec
  dsimp only at hsplit0
  have hsplit : offset + mul * Q t n = r + 3*X' := by
    simpa [originA, E, r, offset', mul', X'] using hsplit0

  have hrlt : r < 3 := by
    dsimp [r, E]
    exact Nat.mod_lt _ (by decide)
  have hxdiv : (offset + mul * Q t n) / 3 = X' := by
    rw [hsplit]
    rw [Nat.add_mul_div_left r X' (by decide : 0 < 3)]
    rw [Nat.div_eq_of_lt hrlt]
    simp
  have hxmod : (offset + mul * Q t n) % 3 = r := by
    rw [hsplit, Nat.add_mod, Nat.mul_mod]
    simp [Nat.mod_eq_of_lt hrlt]

  have hbadTail := gst_seeded_bad_trace_regenerates_tailS
    seed (offset + mul * Q t n) hbad
  have hseed :
      gstAffineMulCarryS 4 seed (offset + mul * Q t n) 1 =
        gstStepCarryS seed r := by
    rw [gst_parent_seed_after_regenerationS, hxmod]
  rw [hseed, hxdiv] at hbadTail

  have hU := gst_origin_simultaneous_mul_divS mul t n
  have hU' :
      mul * gstOriginRemainingUS t n =
        mul' * gstOriginRemainingUS (t+1) (n/3) := by
    simpa [mul', originA, gstOriginMultiplierStepS,
      gstOriginConsumedPhaseS, Nat.pow_mul] using hU

  exact ⟨hsplit, hbadTail, hU'⟩

/-- Positive retained origins remain a well-founded natural descent. -/
theorem gst_retained_offset_origin_strictS
    (n : Nat) (hn : 1 ≤ n) : n/3 < n := by
  exact Nat.div_lt_self (by omega) (by decide : 1 < 3)

/-- The first residual NULL state expands into the retained-offset normal form
for all subsequent origin steps. -/
theorem gst_residual_null_retained_state_shapeS
    (s u : Nat) :
    (gstCanonicalPrefixOffsetS s + GSTCanonicalBlockS s) / 3 +
        GSTCanonicalBlockS s *
          GSTHardPrefixOneTailS
            gstNavigationConstant gstCanonicalPrefixOffsetS (s+1) u =
      ((gstCanonicalPrefixOffsetS s + GSTCanonicalBlockS s) / 3 +
        GSTCanonicalBlockS s * gstCanonicalPrefixOffsetS (s+1)) +
      (GSTCanonicalBlockS s * GSTCanonicalBlockS (s+1)) *
        gstNavigationConstant (s+2) u := by
  unfold GSTHardPrefixOneTailS
  ring
