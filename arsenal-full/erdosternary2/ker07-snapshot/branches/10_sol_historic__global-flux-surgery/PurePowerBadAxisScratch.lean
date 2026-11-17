/- ======================================================================
/- CHRONOLOGICAL LABEL -- #0372 / 1132
/-    Path         : branches/sol_global-flux-surgery/PurePowerBadAxisScratch.lean
/-    Ref          : origin/sol/global-flux-surgery
/-    First-commit : 2026-08-15 18:29:37 +0530  (d2c4655)
/-    Last-commit  : 2026-08-15 22:18:19 +0530  (a69a796)
/-    Total commits: 9
/- ======================================================================
/- GIT HISTORY (chronological, oldest first)
/- ======================================================================
/- [01/9] 2026-08-15 18:29:37 +0530  d2c4655  (ker07-dev)
/-        Add pure-power axis certificate scratch
/- [02/9] 2026-08-15 18:55:02 +0530  7e2945b  (ker07-dev)
/-        Fix pure-power binary axis rewrite
/- [03/9] 2026-08-15 19:55:54 +0530  647b2b0  (ker07-dev)
/-        Fix pure-power binary axis rewrite seam
/- [04/9] 2026-08-15 20:27:51 +0530  a69e081  (ker07-dev)
/-        Kernel-check canonical GST causality blade
/- [05/9] 2026-08-15 21:39:58 +0530  d0a6214  (ker07-dev)
/-        Add exact canonical prefix-one energy certificates
/- [06/9] 2026-08-15 21:54:17 +0530  2cfce39  (ker07-dev)
/-        Use canonical prefix API directly in pure-power axis
/- [07/9] 2026-08-15 21:56:05 +0530  9d9e6c4  (ker07-dev)
/-        Kernelize forced-prefix seed zero/one bridge
/- [08/9] 2026-08-15 22:07:02 +0530  baa8c2e  (ker07-dev)
/-        Repair forced-prefix quotient elaboration
/- [09/9] 2026-08-15 22:18:19 +0530  a69a796  (ker07-dev)
/-        Identify forced parent prefix with seed-one GST tail
/- ====================================================================== -/

import InformationDescentScratch
import CanonicalPrefixScratch

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

/-!
Exact orthogonal certificate for the prefix-one information-descent surgery.
This file proves only algebraic consequences of the canonical perfect-power
origin.  It makes no universal Erdős claim and introduces no axiom.
-/

/-- Let `A = 1 + D*c`, `c = 1 + 3*z`, and let the child perfect-power
    energy be `E = 1 + 3*D*T`.  For the prefix-one affine tail `X = z + A*T`,
    the parent linear form collapses exactly to `A*E`:

      3*D*X + (1+D) = A*E.

    This is the exact 2-adic/pure-power axis missing from arbitrary affine
    counterexamples. -/
theorem gst_prefix_one_pure_power_axisS
    (A D c z T E : Nat)
    (hA : A = 1 + D*c)
    (hc : c = 1 + 3*z)
    (hE : E = 1 + 3*D*T) :
    3*D*(z + A*T) + (1+D) = A*E := by
  rw [hA, hc, hE]
  ring

/-- If both canonical energy factors are powers of four, the parent linear
    form is itself one exact power of four. -/
theorem gst_prefix_one_pure_power_axis_powS
    (A D c z T E N K : Nat)
    (hA : A = 1 + D*c)
    (hc : c = 1 + 3*z)
    (hE : E = 1 + 3*D*T)
    (hApow : A = 4^N)
    (hEpow : E = 4^K) :
    3*D*(z + A*T) + (1+D) = 4^(N+K) := by
  rw [gst_prefix_one_pure_power_axisS A D c z T E hA hc hE,
      hApow, hEpow]
  exact (Nat.pow_add 4 N K).symm

/-- The same certificate exposes exact binary purity: after rewriting the two
    canonical factors as powers of two, no odd cofactor remains. -/
theorem gst_prefix_one_pure_two_axisS
    (A D c z T E N K : Nat)
    (hA : A = 1 + D*c)
    (hc : c = 1 + 3*z)
    (hE : E = 1 + 3*D*T)
    (hApow : A = 2^(2*N))
    (hEpow : E = 2^(2*K)) :
    3*D*(z + A*T) + (1+D) = 2^(2*(N+K)) := by
  have haxis := gst_prefix_one_pure_power_axisS A D c z T E hA hc hE
  rw [hApow, hEpow] at haxis
  rw [hApow]
  calc
    3*D*(z + 2^(2*N)*T) + (1+D) = 2^(2*N) * 2^(2*K) := haxis
    _ = 2^(2*N + 2*K) := (Nat.pow_add 2 (2*N) (2*K)).symm
    _ = 2^(2*(N+K)) := by congr 1 <;> omega

/-- Exact canonical prefix-one recurrence, expressed only through the
    perfect-power Navigation map.  This is the origin-specific replacement for
    an unrestricted affine lift. -/
theorem gst_canonical_prefix_one_recurrenceS
    (Q : Nat → Nat → Nat)
    (hQ : GSTCanonicalOriginEnergyS Q)
    (t n : Nat) (ht : 1 ≤ t) :
    Q t (1 + 3*n) =
      Q t 1 + 3 * 4^(3^t) * Q (t+1) n := by
  have h := gst_canonical_prefix_recurrenceS Q hQ t 1 1 n ht
  simpa [Nat.pow_one, Nat.mul_one, Nat.add_assoc, Nat.mul_assoc] using h

/-- The parent and child canonical energies form one exact commuting
    pure-power square.  This is the certificate absent from arbitrary affine
    counterexamples. -/
theorem gst_canonical_prefix_one_energy_squareS
    (Q : Nat → Nat → Nat)
    (hQ : GSTCanonicalOriginEnergyS Q)
    (t n : Nat) (ht : 1 ≤ t) :
    1 + 3^(t+1) * Q t (1 + 3*n) =
      4^(3^t) * (1 + 3^(t+2) * Q (t+1) n) := by
  have hparent := hQ t (1 + 3*n) ht
  have hchild := hQ (t+1) n (by omega)
  have hexp :
      3^t * (1 + 3*n) = 3^t + 3^(t+1) * n := by
    rw [Nat.pow_succ]
    ring
  calc
    1 + 3^(t+1) * Q t (1 + 3*n) =
        4^(3^t * (1 + 3*n)) := hparent.symm
    _ = 4^(3^t) * 4^(3^(t+1) * n) := by
      rw [hexp, Nat.pow_add]
    _ = 4^(3^t) * (1 + 3^(t+2) * Q (t+1) n) := by
      rw [hchild]

/-- Stripping an actual ternary prefix does not change the digits of the tail. -/
theorem gst_prefixed_tail_digitS
    (L X r q : Nat) (hL : L < 3^r) :
    gstDigitS (L + 3^r * X) (r+q) = gstDigitS X q := by
  rw [gst_seeded_affine_digit_shiftS (L + 3^r * X) r q]
  have htail : (L + 3^r * X) / 3^r = X := by
    rw [Nat.add_mul_div_left L X (Nat.pow_pos (by decide))]
    rw [Nat.div_eq_of_lt hL]
    simp
  rw [htail]

/-- Stripping a ternary prefix retains its multiplication-by-four effect as an
    explicit incoming carry seed.  This is the generic arithmetic source of
    the child seed `0` versus parent seed `1` distinction. -/
theorem gst_prefixed_tail_carryS
    (L X r q : Nat) (hL : L < 3^r) :
    gstCarryS (L + 3^r * X) (r+q) =
      gstAffineMulCarryS 4 ((4*L) / 3^r) X q := by
  have hre := gst_child_carry_reindex_seededS (L + 3^r * X) r q
  have htail : (L + 3^r * X) / 3^r = X := by
    rw [Nat.add_mul_div_left L X (Nat.pow_pos (by decide))]
    rw [Nat.div_eq_of_lt hL]
    simp
  have hmod : (L + 3^r * X) % 3^r = L := by
    rw [Nat.add_mod, Nat.mul_mod]
    simp [Nat.mod_eq_of_lt hL]
  have hseed : gstCarryS (L + 3^r * X) r = (4*L) / 3^r := by
    unfold gstCarryS
    rw [hmod]
  rw [hre, htail, hseed]

/-- The child perfect-power energy has exactly the ordinary seed-zero child
    state after its forced `s+2` ternary prefix is stripped. -/
theorem gst_child_energy_stateS
    (s T q : Nat) (hs : 1 ≤ s) :
    let E := 1 + 3^(s+2) * T
    gstDigitS E (s+2+q) = gstDigitS T q ∧
      gstCarryS E (s+2+q) = gstCarryS T q := by
  dsimp only
  have hpow : 4 < 3^(s+2) := by
    have h27 : 27 ≤ 3^(s+2) := by
      rw [show (27:Nat) = 3^3 by decide]
      exact Nat.pow_le_pow_of_le (by decide : 1 < 3) (by omega)
    omega
  have hL : 1 < 3^(s+2) := by omega
  constructor
  · exact gst_prefixed_tail_digitS 1 T (s+2) q hL
  · have h := gst_prefixed_tail_carryS 1 T (s+2) q hL
    have hseed : (4*1) / 3^(s+2) = 0 := Nat.div_eq_of_lt (by simpa using hpow)
    rw [hseed] at h
    simpa [gstCarryS, gstAffineMulCarryS] using h

/-- The forced parent prefix `1 + 3^(s+1)` contributes exactly incoming seed
    one when stripped at depth `s+2`. -/
theorem gst_parent_forced_prefix_seedS
    (s : Nat) (hs : 1 ≤ s) :
    (4 * (1 + 3^(s+1))) / 3^(s+2) = 1 := by
  let D := 3^(s+1)
  have hD : 3 ≤ D := by
    dsimp [D]
    have h9 : 9 ≤ 3^(s+1) := by
      rw [show (9:Nat) = 3^2 by decide]
      exact Nat.pow_le_pow_of_le (by decide : 1 < 3) (by omega)
    omega
  have hB : 3^(s+2) = 3*D := by
    dsimp [D]
    rw [show s+2 = (s+1)+1 by omega, Nat.pow_succ]
    ac_rfl
  have hrem : D + 4 < 3*D := by omega
  rw [hB]
  have hshape : 4 * (1 + D) = (D+4) + (3*D)*1 := by ring
  rw [show 3^(s+1) = D by rfl, hshape]
  rw [Nat.add_mul_div_left (D+4) 1 (by positivity : 0 < 3*D)]
  rw [Nat.div_eq_of_lt hrem]

/-- The parent pure-power prefix is exactly the seed-one affine GST state of
    its high ternary tail.  This is the parent analogue of
    `gst_child_energy_stateS`. -/
theorem gst_parent_energy_stateS
    (s X q : Nat) (hs : 1 ≤ s) :
    let P := (1 + 3^(s+1)) + 3^(s+2) * X
    gstDigitS P (s+2+q) = gstDigitS X q ∧
      gstCarryS P (s+2+q) = gstAffineMulCarryS 4 1 X q := by
  dsimp only
  have hL : 1 + 3^(s+1) < 3^(s+2) := by
    rw [show s+2 = (s+1)+1 by omega, Nat.pow_succ]
    have hpos : 0 < 3^(s+1) := Nat.pow_pos (by decide)
    omega
  constructor
  · exact gst_prefixed_tail_digitS (1 + 3^(s+1)) X (s+2) q hL
  · have h := gst_prefixed_tail_carryS
      (1 + 3^(s+1)) X (s+2) q hL
    have hseed := gst_parent_forced_prefix_seedS s hs
    rw [hseed] at h
    exact h