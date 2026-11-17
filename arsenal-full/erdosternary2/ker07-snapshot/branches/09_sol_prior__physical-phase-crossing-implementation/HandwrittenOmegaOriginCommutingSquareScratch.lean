/- ======================================================================
/- CHRONOLOGICAL LABEL -- #0931 / 1132
/-    Path         : branches/sol_physical-phase-crossing-implementation/HandwrittenOmegaOriginCommutingSquareScratch.lean
/-    Ref          : origin/sol/physical-phase-crossing-implementation
/-    First-commit : 2026-08-17 08:29:16 +0530  (4055486)
/-    Last-commit  : 2026-08-17 08:29:16 +0530  (4055486)
/-    Total commits: 1
/- ======================================================================
/- GIT HISTORY (chronological, oldest first)
/- ======================================================================
/- [01/1] 2026-08-17 08:29:16 +0530  4055486  (ker07-dev)
/-        Add exact Omega-origin commuting square and residue fingerprint
/- ====================================================================== -/

import HandwrittenOmegaOperatorScratch
import InformationRegenerationScratch
import CanonicalPrefixScratch

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

/-!
# Exact Ω-information / natural-origin commuting square

Boss's handwritten operator has two natural axes:

* origin time `t` (the Pi constructor), and
* information position `i` (the BIG-N Sigma constructor).

For a canonical Navigation map the two axes meet on the same finite residue:
the Ω Past after K information steps is exactly the ternary residue fingerprint
created by the first K natural-origin trits.
-/

/-- Exact one-trit recurrence in the canonical Navigation map. -/
theorem gst_canonical_natural_origin_recurrenceS
    (Q : Nat → Nat → Nat)
    (hQ : GSTCanonicalOriginEnergyS Q)
    (t n : Nat) (ht : 1 ≤ t) :
    Q t n =
      Q t (n % 3) +
        3 * (4^(3^t))^(n % 3) * Q (t+1) (n/3) := by
  have hrec := gst_canonical_prefix_recurrenceS
    Q hQ t (n%3) 1 (n/3) ht
  norm_num at hrec
  have hn : n = n%3 + 3*(n/3) := by
    have h := Nat.mod_add_div n 3
    omega
  rw [← hn] at hrec
  have hpow : 4^(3^t * (n%3)) = (4^(3^t))^(n%3) := by
    rw [Nat.pow_mul]
  simpa [hpow, Nat.mul_assoc] using hrec

/-- The Omega Past at information depth K is exactly the canonical Q-image of
the first K origin trits, reduced to the same information depth. -/
theorem gst_omega_past_is_origin_prefixS
    (Q : Nat → Nat → Nat)
    (hQ : GSTCanonicalOriginEnergyS Q)
    (t n K : Nat) (ht : 1 ≤ t) :
    gstOmegaNaturalPastS t (Q t n) K =
      3^(t+1) * (Q t (n % 3^K) % 3^K) := by
  unfold gstOmegaNaturalPastS
  rw [gst_canonical_prefix_residueS Q hQ t n K ht]

/-- The same Past coordinate is literally the perfect-power residue created by
that finite origin prefix. -/
theorem gst_omega_past_origin_power_fingerprintS
    (Q : Nat → Nat → Nat)
    (hQ : GSTCanonicalOriginEnergyS Q)
    (t n K : Nat) (ht : 1 ≤ t) :
    4^(3^t * (n % 3^K)) % 3^(t+1+K) =
      1 + gstOmegaNaturalPastS t (Q t n) K := by
  let a := n % 3^K
  have hE := hQ t a ht
  have hp : 0 < 3^K := Nat.pow_pos (by decide)
  have hq : Q t a % 3^K < 3^K := Nat.mod_lt _ hp
  have hM : 3^(t+1+K) = 3^(t+1) * 3^K := by
    rw [Nat.pow_add]
  have hsmall :
      1 + 3^(t+1) * (Q t a % 3^K) < 3^(t+1+K) := by
    rw [hM]
    have hbase : 1 < 3^(t+1) := by
      have ht1 : 1 ≤ t+1 := by omega
      exact Nat.one_lt_pow (by decide) (by omega)
    have hle : Q t a % 3^K + 1 ≤ 3^K := Nat.succ_le_of_lt hq
    have hmul :
        3^(t+1) * (Q t a % 3^K + 1) ≤
          3^(t+1) * 3^K := Nat.mul_le_mul_left _ hle
    rw [Nat.mul_add, Nat.mul_one] at hmul
    omega
  have hres :
      (1 + 3^(t+1) * Q t a) % 3^(t+1+K) =
        1 + 3^(t+1) * (Q t a % 3^K) := by
    rw [hM]
    have hdecomp :
        Q t a = 3^K * (Q t a / 3^K) + Q t a % 3^K :=
      (Nat.div_add_mod (Q t a) (3^K)).symm
    conv_lhs => rw [hdecomp]
    have hshape :
        1 + 3^(t+1) *
          (3^K * (Q t a / 3^K) + Q t a % 3^K) =
        (3^(t+1)*3^K) * (Q t a / 3^K) +
          (1 + 3^(t+1) * (Q t a % 3^K)) := by
      ring
    rw [hshape, Nat.add_mod]
    have hzero :
        ((3^(t+1)*3^K) * (Q t a / 3^K)) %
          (3^(t+1)*3^K) = 0 :=
      Nat.mod_eq_zero_of_dvd (Nat.dvd_mul_right _ _)
    rw [hzero, Nat.zero_add, Nat.mod_eq_of_lt]
    exact hsmall
  rw [hE]
  change (1 + 3^(t+1) * Q t a) % 3^(t+1+K) = _
  rw [hres, gst_omega_past_is_origin_prefixS Q hQ t n K ht]
  rfl

/-- One origin trit may be consumed at the same time that the canonical affine
information state regenerates.  The affine multiplier absorbs exactly the
perfect-power phase removed from the remaining U energy. -/
theorem gst_canonical_information_U_commuting_stepS
    (Q : Nat → Nat → Nat)
    (hQ : GSTCanonicalOriginEnergyS Q)
    (t n childOffset childMul A Z : Nat) (ht : 1 ≤ t) :
    let originA := 4^(3^t)
    let E := childOffset + childMul * Q t (n%3)
    let r := E % 3
    let childOffset' := E / 3
    let childMul' := childMul * originA^(n%3)
    let Y' := childOffset' + childMul' * Q (t+1) (n/3)
    let e := (Z + A*r) % 3
    let Z' := (Z + A*r) / 3
    childOffset + childMul * Q t n = r + 3*Y' ∧
      Z + A*(childOffset + childMul * Q t n) =
        e + 3*(Z' + A*Y') ∧
      childMul * gstOriginRemainingUS t n =
        childMul' * gstOriginRemainingUS (t+1) (n/3) := by
  dsimp only
  have hrec := gst_canonical_natural_origin_recurrenceS Q hQ t n ht
  have hinfo := gst_canonical_information_regeneratesS
    Q t n childOffset childMul (4^(3^t)) A Z hrec
  dsimp only at hinfo
  refine ⟨hinfo.1, hinfo.2, ?_⟩
  have hU := gst_origin_simultaneous_mul_divS childMul t n
  simpa [gstOriginMultiplierStepS, gstOriginConsumedPhaseS] using hU

/-- Therefore the two handwritten directions reconstruct the same canonical
energy at their finite natural ceilings: origin-phase Pi on the exponent side,
and Omega Sigma on the Navigation-information side. -/
theorem gst_handwritten_two_axis_same_energyS
    (Q : Nat → Nat → Nat)
    (hQ : GSTCanonicalOriginEnergyS Q)
    (t n : Nat) (ht : 1 ≤ t) :
    4^(∑ r in Finset.range (n+1),
      3^(t+r) * gstOriginNaturalTritS n r) =
    1 + (∑ i in Finset.range (Q t n + 1),
      gstOmegaNaturalTransferS t (Q t n) i) := by
  rw [gst_origin_phase_reconstructs_energyS,
    gst_handwritten_navigation_omega_budgetS Q hQ t n ht]
