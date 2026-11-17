/- ======================================================================
/- CHRONOLOGICAL LABEL -- #0901 / 1132
/-    Path         : branches/sol_physical-phase-crossing-implementation/PrefixOneOriginPhaseRecursionScratch.lean
/-    Ref          : origin/sol/physical-phase-crossing-implementation
/-    First-commit : 2026-08-17 08:04:37 +0530  (348a846)
/-    Last-commit  : 2026-08-17 08:19:01 +0530  (1ea49db)
/-    Total commits: 4
/- ======================================================================
/- GIT HISTORY (chronological, oldest first)
/- ======================================================================
/- [01/4] 2026-08-17 08:04:37 +0530  348a846  (ker07-dev)
/-        Add exact hard-tail origin phase recursion
/- [02/4] 2026-08-17 08:05:04 +0530  fa64ff0  (ker07-dev)
/-        Remove unproved regeneration draft from origin recursion scratch
/- [03/4] 2026-08-17 08:05:57 +0530  d13ca9e  (ker07-dev)
/-        Add exact bad-trace regeneration for true origin trits
/- [04/4] 2026-08-17 08:19:01 +0530  1ea49db  (ker07-dev)
/-        Add exact parent Navigation and binary fixed-point quotient
/- ====================================================================== -/

import CanonicalOriginModulusScratch
import InformationRegenerationScratch

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

/-!
# Exact origin-phase recursion of the hard prefix-one tail
-/

def GSTHardPrefixOneTailS
    (Q : Nat → Nat → Nat) (z : Nat → Nat) (t n : Nat) : Nat :=
  z t + 4^(3^t) * Q (t+1) n

def GSTCanonicalBlockS (t : Nat) : Nat := 4^(3^t)

/-- The hard tail is exactly the forced-one suffix of the parent Navigation
constant. -/
theorem gst_hard_tail_parent_navigationS
    (Q : Nat → Nat → Nat)
    (hQ : GSTCanonicalOriginEnergyS Q)
    (z : Nat → Nat)
    (hunit : ∀ t, 1 ≤ t → Q t 1 = 1 + 3*z t)
    (t n : Nat) (ht : 1 ≤ t) :
    Q t (1+3*n) = 1 + 3 * GSTHardPrefixOneTailS Q z t n := by
  have hrec := gst_canonical_prefix_recurrenceS Q hQ t 1 1 n ht
  norm_num at hrec
  rw [hrec, hunit t ht]
  unfold GSTHardPrefixOneTailS GSTCanonicalBlockS
  ring

/-- Origin trit one: exact 3-affine copy of the same hard object one level
deeper. -/
theorem gst_hard_tail_origin_one_recursionS
    (Q : Nat → Nat → Nat)
    (hQ : GSTCanonicalOriginEnergyS Q)
    (z : Nat → Nat)
    (hunit : ∀ t, 1 ≤ t → Q t 1 = 1 + 3*z t)
    (t u : Nat) (ht : 1 ≤ t) :
    GSTHardPrefixOneTailS Q z t (3*u + 1) =
      z t + GSTCanonicalBlockS t +
        3 * GSTCanonicalBlockS t *
          GSTHardPrefixOneTailS Q z (t+1) u := by
  unfold GSTHardPrefixOneTailS GSTCanonicalBlockS
  have hrec := gst_canonical_prefix_recurrenceS Q hQ (t+1) 1 1 u (by omega)
  norm_num at hrec
  have hunitNext := hunit (t+1) (by omega)
  rw [show 3*u+1 = 1+3*u by omega, hrec, hunitNext]
  ring

/-- The two-origin block Q_t(2) is the exact repunit Q_t(1)*(1+A_t). -/
theorem gst_canonical_origin_two_repunitS
    (Q : Nat → Nat → Nat)
    (hQ : GSTCanonicalOriginEnergyS Q)
    (t : Nat) (ht : 1 ≤ t) :
    Q t 2 = Q t 1 + 4^(3^t) * Q t 1 := by
  have hrec := gst_canonical_prefix_recurrenceS Q hQ t 1 0 1 ht
  norm_num at hrec
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hrec

/-- Origin trit two: exact 3-affine copy with phase-two multiplier. -/
theorem gst_hard_tail_origin_two_recursionS
    (Q : Nat → Nat → Nat)
    (hQ : GSTCanonicalOriginEnergyS Q)
    (z : Nat → Nat)
    (hunit : ∀ t, 1 ≤ t → Q t 1 = 1 + 3*z t)
    (t u : Nat) (ht : 1 ≤ t) :
    GSTHardPrefixOneTailS Q z t (3*u + 2) =
      z t +
        GSTCanonicalBlockS t * Q (t+1) 1 +
        GSTCanonicalBlockS t * GSTCanonicalBlockS (t+1) +
        3 * GSTCanonicalBlockS t * GSTCanonicalBlockS (t+1) *
          GSTHardPrefixOneTailS Q z (t+1) u := by
  unfold GSTHardPrefixOneTailS GSTCanonicalBlockS
  have hrec := gst_canonical_prefix_recurrenceS Q hQ (t+1) 2 1 u (by omega)
  norm_num at hrec
  have hQ2 := gst_canonical_origin_two_repunitS Q hQ (t+1) (by omega)
  have hunitNext := hunit (t+1) (by omega)
  rw [show 3*u+2 = 2+3*u by omega, hrec, hQ2, hunitNext]
  ring

/-- Stable unit-tail residue: origin-one exposes digit zero. -/
theorem gst_hard_tail_origin_one_mod3S
    (Q : Nat → Nat → Nat)
    (hQ : GSTCanonicalOriginEnergyS Q)
    (z : Nat → Nat)
    (hunit : ∀ t, 1 ≤ t → Q t 1 = 1 + 3*z t)
    (hz3 : ∀ t, 1 ≤ t → z t % 3 = 2)
    (t u : Nat) (ht : 1 ≤ t) :
    GSTHardPrefixOneTailS Q z t (3*u+1) % 3 = 0 := by
  rw [gst_hard_tail_origin_one_recursionS Q hQ z hunit t u ht]
  unfold GSTCanonicalBlockS
  have hA3 : 4^(3^t) % 3 = 1 := by norm_num [Nat.pow_mod]
  simp [Nat.add_mod, Nat.mul_mod, hz3 t ht, hA3]

/-- Stable unit-tail residue: origin-two exposes digit one. -/
theorem gst_hard_tail_origin_two_mod3S
    (Q : Nat → Nat → Nat)
    (hQ : GSTCanonicalOriginEnergyS Q)
    (z : Nat → Nat)
    (hunit : ∀ t, 1 ≤ t → Q t 1 = 1 + 3*z t)
    (hz3 : ∀ t, 1 ≤ t → z t % 3 = 2)
    (t u : Nat) (ht : 1 ≤ t) :
    GSTHardPrefixOneTailS Q z t (3*u+2) % 3 = 1 := by
  rw [gst_hard_tail_origin_two_recursionS Q hQ z hunit t u ht]
  unfold GSTCanonicalBlockS
  have hA3 : 4^(3^t) % 3 = 1 := by norm_num [Nat.pow_mod]
  have hAn3 : 4^(3^(t+1)) % 3 = 1 := by norm_num [Nat.pow_mod]
  have hQ13 : Q (t+1) 1 % 3 = 1 := by
    rw [hunit (t+1) (by omega)]
    simp [Nat.add_mod, Nat.mul_mod]
  simp [Nat.add_mod, Nat.mul_mod, hz3 t ht, hA3, hAn3, hQ13]

/-- Exact first-row quotient in origin-one. -/
theorem gst_hard_tail_origin_one_div3S
    (Q : Nat → Nat → Nat)
    (hQ : GSTCanonicalOriginEnergyS Q)
    (z : Nat → Nat)
    (hunit : ∀ t, 1 ≤ t → Q t 1 = 1 + 3*z t)
    (t u : Nat) (ht : 1 ≤ t) :
    GSTHardPrefixOneTailS Q z t (3*u+1) / 3 =
      (z t + GSTCanonicalBlockS t) / 3 +
        GSTCanonicalBlockS t * GSTHardPrefixOneTailS Q z (t+1) u := by
  rw [gst_hard_tail_origin_one_recursionS Q hQ z hunit t u ht]
  have h3 : 0 < (3:Nat) := by decide
  have hshape :
      z t + GSTCanonicalBlockS t +
          3 * GSTCanonicalBlockS t * GSTHardPrefixOneTailS Q z (t+1) u =
        (z t + GSTCanonicalBlockS t) +
          3 * (GSTCanonicalBlockS t * GSTHardPrefixOneTailS Q z (t+1) u) := by ring
  rw [hshape, Nat.add_mul_div_left _ _ h3]

/-- Exact first-row quotient in origin-two. -/
theorem gst_hard_tail_origin_two_div3S
    (Q : Nat → Nat → Nat)
    (hQ : GSTCanonicalOriginEnergyS Q)
    (z : Nat → Nat)
    (hunit : ∀ t, 1 ≤ t → Q t 1 = 1 + 3*z t)
    (t u : Nat) (ht : 1 ≤ t) :
    GSTHardPrefixOneTailS Q z t (3*u+2) / 3 =
      (z t + GSTCanonicalBlockS t * Q (t+1) 1 +
        GSTCanonicalBlockS t * GSTCanonicalBlockS (t+1)) / 3 +
      GSTCanonicalBlockS t * GSTCanonicalBlockS (t+1) *
        GSTHardPrefixOneTailS Q z (t+1) u := by
  rw [gst_hard_tail_origin_two_recursionS Q hQ z hunit t u ht]
  have h3 : 0 < (3:Nat) := by decide
  have hshape :
      z t + GSTCanonicalBlockS t * Q (t+1) 1 +
          GSTCanonicalBlockS t * GSTCanonicalBlockS (t+1) +
          3 * GSTCanonicalBlockS t * GSTCanonicalBlockS (t+1) *
            GSTHardPrefixOneTailS Q z (t+1) u =
        (z t + GSTCanonicalBlockS t * Q (t+1) 1 +
          GSTCanonicalBlockS t * GSTCanonicalBlockS (t+1)) +
        3 * (GSTCanonicalBlockS t * GSTCanonicalBlockS (t+1) *
          GSTHardPrefixOneTailS Q z (t+1) u) := by ring
  rw [hshape, Nat.add_mul_div_left _ _ h3]

/-- Complete badness regenerates on the origin-one branch. -/
theorem gst_bad_hard_tail_origin_one_regeneratesS
    (Q : Nat → Nat → Nat)
    (hQ : GSTCanonicalOriginEnergyS Q)
    (z : Nat → Nat)
    (hunit : ∀ t, 1 ≤ t → Q t 1 = 1 + 3*z t)
    (hz3 : ∀ t, 1 ≤ t → z t % 3 = 2)
    (t u : Nat) (ht : 1 ≤ t)
    (hbad : GSTSeededBadTraceS 1 (GSTHardPrefixOneTailS Q z t (3*u+1))) :
    GSTSeededBadTraceS 0
      ((z t + GSTCanonicalBlockS t) / 3 +
        GSTCanonicalBlockS t * GSTHardPrefixOneTailS Q z (t+1) u) := by
  have hsuffix := gst_seeded_bad_trace_regenerates_tailS
    1 (GSTHardPrefixOneTailS Q z t (3*u+1)) hbad
  have hd0 := gst_hard_tail_origin_one_mod3S Q hQ z hunit hz3 t u ht
  have hseed :
      gstAffineMulCarryS 4 1 (GSTHardPrefixOneTailS Q z t (3*u+1)) 1 = 0 := by
    rw [gst_parent_seed_after_regenerationS, hd0]
    decide
  rw [hseed, gst_hard_tail_origin_one_div3S Q hQ z hunit t u ht] at hsuffix
  exact hsuffix

/-- Complete badness regenerates on the origin-two branch. -/
theorem gst_bad_hard_tail_origin_two_regeneratesS
    (Q : Nat → Nat → Nat)
    (hQ : GSTCanonicalOriginEnergyS Q)
    (z : Nat → Nat)
    (hunit : ∀ t, 1 ≤ t → Q t 1 = 1 + 3*z t)
    (hz3 : ∀ t, 1 ≤ t → z t % 3 = 2)
    (t u : Nat) (ht : 1 ≤ t)
    (hbad : GSTSeededBadTraceS 1 (GSTHardPrefixOneTailS Q z t (3*u+2))) :
    GSTSeededBadTraceS 1
      ((z t + GSTCanonicalBlockS t * Q (t+1) 1 +
        GSTCanonicalBlockS t * GSTCanonicalBlockS (t+1)) / 3 +
       GSTCanonicalBlockS t * GSTCanonicalBlockS (t+1) *
        GSTHardPrefixOneTailS Q z (t+1) u) := by
  have hsuffix := gst_seeded_bad_trace_regenerates_tailS
    1 (GSTHardPrefixOneTailS Q z t (3*u+2)) hbad
  have hd1 := gst_hard_tail_origin_two_mod3S Q hQ z hunit hz3 t u ht
  have hseed :
      gstAffineMulCarryS 4 1 (GSTHardPrefixOneTailS Q z t (3*u+2)) 1 = 1 := by
    rw [gst_parent_seed_after_regenerationS, hd1]
    decide
  rw [hseed, gst_hard_tail_origin_two_div3S Q hQ z hunit t u ht] at hsuffix
  exact hsuffix

/-- Generic modular fixed-point adapter: if M divides 1+3H, then the seeded
map H -> 1+4H fixes H modulo M. -/
theorem gst_seed_one_fixed_of_parent_divisorS
    (M H : Nat) (hdiv : M ∣ 1 + 3*H) :
    (1 + 4*H) % M = H % M := by
  have hshape : 1 + 4*H = H + (1 + 3*H) := by ring
  rw [hshape, Nat.add_mod, Nat.mod_eq_zero_of_dvd hdiv,
    Nat.add_zero, Nat.mod_mod]

/-- Odd child origin => the parent origin 1+3n is even.  Therefore the full
level-t binary quotient Q_t(2) divides the parent Navigation constant and the
hard seed-one tail is a fixed point modulo Q_t(2). -/
theorem gst_hard_tail_odd_origin_binary_fixedS
    (Q : Nat → Nat → Nat)
    (hQ : GSTCanonicalOriginEnergyS Q)
    (z : Nat → Nat)
    (hunit : ∀ t, 1 ≤ t → Q t 1 = 1 + 3*z t)
    (t n : Nat) (ht : 1 ≤ t)
    (hnodd : n % 2 = 1) :
    (1 + 4*GSTHardPrefixOneTailS Q z t n) % Q t 2 =
      GSTHardPrefixOneTailS Q z t n % Q t 2 := by
  have hbEven : (1 + 3*n) % 2 = 0 := by omega
  have hmod := gst_canonical_origin_modulusS Q hQ t (1+3*n) 2 ht
  rw [hbEven, gst_canonical_origin_zeroS Q hQ t ht,
    Nat.zero_mod] at hmod
  have hparent := gst_hard_tail_parent_navigationS Q hQ z hunit t n ht
  have hdiv : Q t 2 ∣ 1 + 3*GSTHardPrefixOneTailS Q z t n := by
    rw [← hparent]
    exact Nat.dvd_of_mod_eq_zero hmod
  exact gst_seed_one_fixed_of_parent_divisorS _ _ hdiv
