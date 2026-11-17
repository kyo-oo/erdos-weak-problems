/- ======================================================================
/- CHRONOLOGICAL LABEL -- #0294 / 1132
/-    Path         : branches/sol_5c579-final-bigN-right-chord-atomic/PurePowerCarrierScratch.lean
/-    Ref          : origin/sol/5c579-final-bigN-right-chord-atomic
/-    First-commit : 2026-08-15 15:34:01 +0530  (9ad31b8)
/-    Last-commit  : 2026-08-15 16:46:00 +0530  (06d7623)
/-    Total commits: 3
/- ======================================================================
/- GIT HISTORY (chronological, oldest first)
/- ======================================================================
/- [01/3] 2026-08-15 15:34:01 +0530  9ad31b8  (ker07-dev)
/-        Formalize canonical pure-power carrier energy
/- [02/3] 2026-08-15 15:40:12 +0530  343fa82  (ker07-dev)
/-        Stabilize pure-power origin split proof
/- [03/3] 2026-08-15 16:46:00 +0530  06d7623  (ker07-dev)
/-        Stabilize pure-power origin split rewrite
/- ====================================================================== -/

import OriginTransducerScratch

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

/-- Abstract certificate that Q is the canonical perfect-power Navigation map. -/
def GSTCanonicalOriginEnergyS (Q : Nat → Nat → Nat) : Prop :=
  ∀ t n, 1 ≤ t →
    4^(3^t*n) = 1 + 3^(t+1) * Q t n

/-- The perfect-power origin splits exactly into its current ternary trit and
    the deeper origin.  This is the energy-side regeneration law. -/
theorem gst_pure_power_origin_splitS (t n : Nat) :
    4^(3^t*n) =
      4^(3^t*(n%3)) * 4^(3^(t+1)*(n/3)) := by
  have hn : n = n % 3 + 3 * (n / 3) := by
    have h := Nat.mod_add_div n 3
    omega
  have hexp : 3^t*n = 3^t*(n%3) + 3^(t+1)*(n/3) := by
    calc
      3^t*n = 3^t*(n % 3 + 3*(n/3)) :=
        congrArg (fun x : Nat => 3^t * x) hn
      _ = 3^t*(n%3) + 3^(t+1)*(n/3) := by
        rw [Nat.pow_succ]
        ring
  rw [hexp, Nat.pow_add]

/-- For a canonical Navigation map, the exact origin energy survives one
    natural-origin descent as a pure power-of-four factor times the deeper
    canonical energy. -/
theorem gst_canonical_origin_energy_regeneratesS
    (Q : Nat → Nat → Nat)
    (hQ : GSTCanonicalOriginEnergyS Q)
    (t n : Nat) (ht : 1 ≤ t) :
    1 + 3^(t+1) * Q t n =
      4^(3^t*(n%3)) *
        (1 + 3^(t+2) * Q (t+1) (n/3)) := by
  have htop := hQ t n ht
  have hdeep := hQ (t+1) (n/3) (by omega)
  rw [← htop, gst_pure_power_origin_splitS t n, hdeep]

/-- At a zero remaining origin the canonical energy is exactly one. -/
theorem gst_canonical_origin_energy_zeroS
    (Q : Nat → Nat → Nat)
    (hQ : GSTCanonicalOriginEnergyS Q)
    (t : Nat) (ht : 1 ≤ t) :
    1 + 3^(t+1) * Q t 0 = 1 := by
  have h := hQ t 0 ht
  simpa using h.symm

/-- Every nonzero natural origin strictly descends under the same n -> n/3
    regeneration axis. -/
theorem gst_canonical_origin_strict_descentS
    (n : Nat) (hn : 0 < n) : n/3 < n := by
  exact Nat.div_lt_self hn (by decide)
