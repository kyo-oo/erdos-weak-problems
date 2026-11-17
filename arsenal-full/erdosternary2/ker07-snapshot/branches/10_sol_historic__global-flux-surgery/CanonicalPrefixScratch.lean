/- ======================================================================
/- CHRONOLOGICAL LABEL -- #0402 / 1132
/-    Path         : branches/sol_global-flux-surgery/CanonicalPrefixScratch.lean
/-    Ref          : origin/sol/global-flux-surgery
/-    First-commit : 2026-08-15 20:17:00 +0530  (482edc5)
/-    Last-commit  : 2026-08-15 21:37:25 +0530  (4d7b1f6)
/-    Total commits: 6
/- ======================================================================
/- GIT HISTORY (chronological, oldest first)
/- ======================================================================
/- [01/6] 2026-08-15 20:17:00 +0530  482edc5  (ker07-dev)
/-        Formalize canonical finite-prefix origin recurrence
/- [02/6] 2026-08-15 20:26:44 +0530  ac48ef6  (ker07-dev)
/-        Add exact canonical origin-to-Navigation residue causality
/- [03/6] 2026-08-15 20:40:36 +0530  5e1eaed  (ker07-dev)
/-        Fix canonical prefix recurrence orientation
/- [04/6] 2026-08-15 21:27:41 +0530  96d984e  (ker07-dev)
/-        Fix canonical prefix recurrence proof shape
/- [05/6] 2026-08-15 21:35:33 +0530  9973597  (ker07-dev)
/-        Finish canonical prefix Lean elaboration repair
/- [06/6] 2026-08-15 21:37:25 +0530  4d7b1f6  (ker07-dev)
/-        Restore canonical prefix causality API
/- ====================================================================== -/

import PurePowerCarrierScratch

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

/-- Arbitrary finite ternary-origin prefix recurrence for a canonical
    Navigation map.  This is the exact many-trit version of
    `origin_digit_recurrenceS`. -/
theorem gst_canonical_prefix_recurrenceS
    (Q : Nat → Nat → Nat)
    (hQ : GSTCanonicalOriginEnergyS Q)
    (t a q m : Nat) (ht : 1 ≤ t) :
    Q t (a + 3^q*m) =
      Q t a + 3^q * 4^(3^t*a) * Q (t+q) m := by
  have hbase := hQ t a ht
  have hdeep := hQ (t+q) m (by omega)
  have hwhole := hQ t (a + 3^q*m) ht
  have hexp :
      3^t * (a + 3^q*m) = 3^t*a + 3^(t+q)*m := by
    rw [Nat.mul_add, Nat.pow_add]
    ring
  have hpow :
      4^(3^t * (a + 3^q*m)) =
        4^(3^t*a) * 4^(3^(t+q)*m) := by
    rw [hexp, Nat.pow_add]
  have hden : 3^(t+q+1) = 3^(t+1) * 3^q := by
    rw [show t+q+1 = (t+1)+q by omega, Nat.pow_add]
  have hcur :
      1 + 3^(t+1) * Q t (a + 3^q*m) =
        4^(3^t*a) *
          (1 + 3^(t+1) * 3^q * Q (t+q) m) := by
    calc
      1 + 3^(t+1) * Q t (a + 3^q*m) =
          4^(3^t * (a + 3^q*m)) := hwhole.symm
      _ = 4^(3^t*a) * 4^(3^(t+q)*m) := hpow
      _ = 4^(3^t*a) * (1 + 3^(t+q+1) * Q (t+q) m) := by rw [hdeep]
      _ = 4^(3^t*a) *
          (1 + 3^(t+1) * 3^q * Q (t+q) m) := by rw [hden]
  exact origin_navigation_algebraS
    (3^(t+1)) (4^(3^t*a)) (Q t a)
    (Q t (a + 3^q*m)) (Q (t+q) m) (3^q)
    (Nat.pow_pos (by decide)) hbase hcur

/-- Prefix/tail specialization at the actual finite prefix of a natural origin. -/
theorem gst_canonical_prefix_mod_divS
    (Q : Nat → Nat → Nat)
    (hQ : GSTCanonicalOriginEnergyS Q)
    (t n q : Nat) (ht : 1 ≤ t) :
    Q t n = Q t (n % 3^q) +
      3^q * 4^(3^t * (n % 3^q)) * Q (t+q) (n / 3^q) := by
  have hn : n = n % 3^q + 3^q * (n / 3^q) := by
    have h := Nat.mod_add_div n (3^q)
    omega
  calc
    Q t n = Q t (n % 3^q + 3^q * (n / 3^q)) :=
      congrArg (fun x : Nat => Q t x) hn
    _ = Q t (n % 3^q) +
        3^q * 4^(3^t * (n % 3^q)) * Q (t+q) (n / 3^q) :=
      gst_canonical_prefix_recurrenceS Q hQ t (n % 3^q) q (n / 3^q) ht

/-- Exact origin causality: the first q ternary digits of the canonical
    Navigation value depend only on the first q ternary trits of the origin. -/
theorem gst_canonical_prefix_residueS
    (Q : Nat → Nat → Nat)
    (hQ : GSTCanonicalOriginEnergyS Q)
    (t n q : Nat) (ht : 1 ≤ t) :
    Q t n % 3^q = Q t (n % 3^q) % 3^q := by
  rw [gst_canonical_prefix_mod_divS Q hQ t n q ht]
  simp [Nat.add_mod, Nat.mul_mod]
