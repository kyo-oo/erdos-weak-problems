/- ======================================================================
/- CHRONOLOGICAL LABEL -- #0914 / 1132
/-    Path         : branches/sol_physical-phase-crossing-surgery-plan/CanonicalOriginModulusScratch.lean
/-    Ref          : origin/sol/physical-phase-crossing-surgery-plan
/-    First-commit : 2026-08-17 08:18:04 +0530  (eed2dc4)
/-    Last-commit  : 2026-08-17 08:18:04 +0530  (eed2dc4)
/-    Total commits: 1
/- ======================================================================
/- GIT HISTORY (chronological, oldest first)
/- ======================================================================
/- [01/1] 2026-08-17 08:18:04 +0530  eed2dc4  (ker07-dev)
/-        Formalize universal canonical origin modulus embedding
/- ====================================================================== -/

import CanonicalPrefixScratch

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

/-!
# Universal finite-origin quotient of a canonical Navigation map

For every positive canonical level, addition in origin space becomes an affine
addition law in physical Q-space.  Consequently every finite origin modulus
`m` is represented exactly by the physical modulus `Q t m`.
-/

/-- The zero origin has zero Navigation value. -/
theorem gst_canonical_origin_zeroS
    (Q : Nat → Nat → Nat)
    (hQ : GSTCanonicalOriginEnergyS Q)
    (t : Nat) (ht : 1 ≤ t) :
    Q t 0 = 0 := by
  have h := hQ t 0 ht
  norm_num at h
  have hp : 0 < 3^(t+1) := Nat.pow_pos (by decide)
  omega

/-- Exact additive origin law. -/
theorem gst_canonical_origin_addS
    (Q : Nat → Nat → Nat)
    (hQ : GSTCanonicalOriginEnergyS Q)
    (t a b : Nat) (ht : 1 ≤ t) :
    Q t (a+b) = Q t a + 4^(3^t*a) * Q t b := by
  let D := 3^(t+1)
  let A := 4^(3^t*a)
  have hA0 := hQ t a ht
  have hb := hQ t b ht
  have hab := hQ t (a+b) ht
  have hexp : 3^t*(a+b) = 3^t*a + 3^t*b := by ring
  have hpow : 4^(3^t*(a+b)) = A * 4^(3^t*b) := by
    dsimp [A]
    rw [hexp, Nat.pow_add]
  have hA : A = 1 + D * Q t a := by
    simpa [A, D] using hA0
  have hcur :
      1 + D * Q t (a+b) =
        A * (1 + D * 1 * Q t b) := by
    calc
      1 + D * Q t (a+b) = 4^(3^t*(a+b)) := by
        simpa [D] using hab.symm
      _ = A * 4^(3^t*b) := hpow
      _ = A * (1 + D * Q t b) := by rw [hb]
      _ = A * (1 + D * 1 * Q t b) := by ring
  exact origin_navigation_algebraS
    D A (Q t a) (Q t (a+b)) (Q t b) 1
    (Nat.pow_pos (by decide)) hA hcur

/-- Every integral multiple of an origin modulus maps to a physical value
that is divisible by `Q t m`. -/
theorem gst_canonical_origin_multiple_dvdS
    (Q : Nat → Nat → Nat)
    (hQ : GSTCanonicalOriginEnergyS Q)
    (t m q : Nat) (ht : 1 ≤ t) :
    Q t m ∣ Q t (q*m) := by
  induction q with
  | zero =>
      have h0 := gst_canonical_origin_zeroS Q hQ t ht
      simp [h0]
  | succ q ih =>
      have hadd := gst_canonical_origin_addS Q hQ t (q*m) m ht
      have hshape : (q+1)*m = q*m + m := by ring
      rw [hshape, hadd]
      exact dvd_add ih (dvd_mul_of_dvd_right (dvd_refl (Q t m)) _)

/-- Universal origin-modulus embedding.

`Q t b` reduced modulo the physical modulus `Q t m` is exactly the canonical
image of the finite origin residue `b mod m` reduced by the same modulus.
-/
theorem gst_canonical_origin_modulusS
    (Q : Nat → Nat → Nat)
    (hQ : GSTCanonicalOriginEnergyS Q)
    (t b m : Nat) (ht : 1 ≤ t) :
    Q t b % Q t m = Q t (b % m) % Q t m := by
  let r := b % m
  let q := b / m
  have hb : b = r + q*m := by
    dsimp [r, q]
    have h := Nat.mod_add_div b m
    omega
  have hadd := gst_canonical_origin_addS Q hQ t r (q*m) ht
  have hdvdQ : Q t m ∣ Q t (q*m) :=
    gst_canonical_origin_multiple_dvdS Q hQ t m q ht
  have hdvdTerm : Q t m ∣ 4^(3^t*r) * Q t (q*m) :=
    dvd_mul_of_dvd_right hdvdQ _
  rw [hb, hadd, Nat.add_mod, Nat.mod_eq_zero_of_dvd hdvdTerm,
    Nat.add_zero, Nat.mod_mod]

/-- The first binary origin modulus is exactly 455. -/
theorem gst_canonical_Q_one_two_eq_455S
    (Q : Nat → Nat → Nat)
    (hQ : GSTCanonicalOriginEnergyS Q) :
    Q 1 2 = 455 := by
  have h := hQ 1 2 (by decide)
  norm_num at h
  omega

/-- Origin parity is therefore represented exactly in Q-space modulo 455 at
level one. -/
theorem gst_canonical_origin_parity_mod455S
    (Q : Nat → Nat → Nat)
    (hQ : GSTCanonicalOriginEnergyS Q)
    (b : Nat) :
    Q 1 b % 455 = Q 1 (b % 2) % 455 := by
  have hmod := gst_canonical_origin_modulusS Q hQ 1 b 2 (by decide)
  rw [gst_canonical_Q_one_two_eq_455S Q hQ] at hmod
  exact hmod
