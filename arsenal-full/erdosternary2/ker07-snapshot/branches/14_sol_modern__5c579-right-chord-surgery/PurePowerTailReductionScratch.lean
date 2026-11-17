/- ======================================================================
/- CHRONOLOGICAL LABEL -- #0430 / 1132
/-    Path         : branches/sol_5c579-right-chord-surgery/PurePowerTailReductionScratch.lean
/-    Ref          : origin/sol/5c579-right-chord-surgery
/-    First-commit : 2026-08-15 22:19:40 +0530  (8e6e5e6)
/-    Last-commit  : 2026-08-16 11:40:00 +0530  (efdacc6)
/-    Total commits: 5
/- ======================================================================
/- GIT HISTORY (chronological, oldest first)
/- ======================================================================
/- [01/5] 2026-08-15 22:19:40 +0530  8e6e5e6  (ker07-dev)
/-        Reduce information descent to pure-power high-tail transfer
/- [02/5] 2026-08-15 22:28:39 +0530  7de30b2  (ker07-dev)
/-        Expose canonical power residue at every GST cut
/- [03/5] 2026-08-15 23:24:09 +0530  498f240  (ker07-dev)
/-        Repair exact pure-power strip residue decomposition
/- [04/5] 2026-08-15 23:43:47 +0530  c19fe98  (ker07-dev)
/-        Close pure-power strip double modulus
/- [05/5] 2026-08-16 11:40:00 +0530  efdacc6  (ker07-dev)
/-        Compile bad-language magnitude axis through tail reduction
/- ====================================================================== -/

import PurePowerBadAxisScratch
import InformationRegenerationScratch
import BadLanguageMagnitudeScratch

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

/-!
Arithmetic reduction of the prefix-one information-descent seam.
No new forcing principle is assumed here.  The purpose of this file is to
remove Omega/event language and expose the exact remaining pure-power tail
implication.
-/

def GSTHighBadTraceS (R cut : Nat) : Prop :=
  ∀ q, GSTBadPairS (gstCarryS R (cut+q)) (gstDigitS R (cut+q))

/-- The seed-zero child bad trace is exactly badness of the high tail of its
    canonical energy representation `1 + 3^(s+2) T`. -/
theorem gst_child_bad_iff_energy_high_badS
    (s T : Nat) (hs : 1 ≤ s) :
    GSTSeededBadTraceS 0 T ↔
      GSTHighBadTraceS (1 + 3^(s+2) * T) (s+2) := by
  constructor
  · intro hbad q
    have hstate := gst_child_energy_stateS s T q hs
    dsimp only at hstate
    rw [hstate.1, hstate.2]
    simpa [gstAffineMulCarryS, gstCarryS] using hbad q
  · intro hbad q
    have hstate := gst_child_energy_stateS s T q hs
    dsimp only at hstate
    have hq := hbad q
    rw [hstate.1, hstate.2] at hq
    simpa [gstAffineMulCarryS, gstCarryS] using hq

/-- The seed-one parent bad trace is exactly badness of the high tail after
    stripping the forced prefix `1 + 3^(s+1)`. -/
theorem gst_parent_bad_iff_energy_high_badS
    (s X : Nat) (hs : 1 ≤ s) :
    GSTSeededBadTraceS 1 X ↔
      GSTHighBadTraceS
        ((1 + 3^(s+1)) + 3^(s+2) * X) (s+2) := by
  constructor
  · intro hbad q
    have hstate := gst_parent_energy_stateS s X q hs
    dsimp only at hstate
    rw [hstate.1, hstate.2]
    exact hbad q
  · intro hbad q
    have hstate := gst_parent_energy_stateS s X q hs
    dsimp only at hstate
    have hq := hbad q
    rw [hstate.1, hstate.2] at hq
    exact hq

/-- Exact logical reduction: the original seed-one -> seed-zero information
    descent is neither more nor less than high-tail badness transfer between
    the two forced-prefix energies. -/
theorem gst_information_descent_iff_high_tail_transferS
    (s T X : Nat) (hs : 1 ≤ s) :
    (GSTSeededBadTraceS 1 X → GSTSeededBadTraceS 0 T) ↔
      (GSTHighBadTraceS
          ((1 + 3^(s+1)) + 3^(s+2) * X) (s+2) →
       GSTHighBadTraceS (1 + 3^(s+2) * T) (s+2)) := by
  constructor
  · intro h hparent
    have hp : GSTSeededBadTraceS 1 X :=
      (gst_parent_bad_iff_energy_high_badS s X hs).2 hparent
    have hc : GSTSeededBadTraceS 0 T := h hp
    exact (gst_child_bad_iff_energy_high_badS s T hs).1 hc
  · intro h hparent
    have hp : GSTHighBadTraceS
        ((1 + 3^(s+1)) + 3^(s+2) * X) (s+2) :=
      (gst_parent_bad_iff_energy_high_badS s X hs).1 hparent
    have hc : GSTHighBadTraceS (1 + 3^(s+2) * T) (s+2) := h hp
    exact (gst_child_bad_iff_energy_high_badS s T hs).2 hc

/-- At every vertical cut the horizontal strip input is not an arbitrary
    residue: for a canonical energy `E = 4^K = 1 + 3*D*T` it is literally the
    residue of that exact power of four modulo the aligned ternary modulus. -/
theorem gst_pure_power_strip_input_residueS
    (D T E K q : Nat)
    (hD : 1 ≤ D)
    (hE : E = 1 + 3*D*T)
    (hPow : E = 4^K) :
    4^K % (3*D*3^q) = 1 + 3*D*(T % 3^q) := by
  have hqpos : 0 < 3^q := Nat.pow_pos (by decide)
  have hMpos : 0 < 3*D*3^q := by positivity
  have hrlt : 1 + 3*D*(T % 3^q) < 3*D*3^q := by
    have hr : T % 3^q < 3^q := Nat.mod_lt _ hqpos
    have h3D : 1 < 3*D := by omega
    have hmul : 3*D*(T % 3^q + 1) ≤ 3*D*3^q :=
      Nat.mul_le_mul_left (3*D) (Nat.succ_le_of_lt hr)
    have hstep : 1 + 3*D*(T % 3^q) < 3*D*(T % 3^q + 1) := by
      rw [Nat.mul_add, Nat.mul_one]
      omega
    exact lt_of_lt_of_le hstep hmul
  have hT : T = 3^q * (T / 3^q) + T % 3^q :=
    (Nat.div_add_mod T (3^q)).symm
  have hdecomp :
      E = (1 + 3*D*(T % 3^q)) + (3*D*3^q) * (T / 3^q) := by
    rw [hE]
    conv_lhs => rw [hT]
    ring
  have hmulmod :
      ((3*D*3^q) * (T / 3^q)) % (3*D*3^q) = 0 :=
    Nat.mod_eq_zero_of_dvd (Nat.dvd_mul_right _ _)
  rw [← hPow, hdecomp, Nat.add_mod, hmulmod, Nat.add_zero, Nat.mod_mod]
  exact Nat.mod_eq_of_lt hrlt
