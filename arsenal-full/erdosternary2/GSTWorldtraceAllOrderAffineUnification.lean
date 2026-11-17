import GSTWorldtraceBlockLift
import GSTFourPowerAffineOrbit
import GSTFourPowerDirectExistence

set_option maxRecDepth 1000000
set_option maxHeartbeats 30000000

/-!
# GST all-order exact cumulative ledger and original affine-orbit identity

Rather than truncating at a fixed trit band, integrate the source-specific
GST quotient increment over every exponent block. This gives an exact
untruncated integer identity for 4^(M+u*3^L) at EVERY ternary row.

At physical scale L=0 the new ledger is proved to equal exactly the
older 4-power affine orbit A_K=(4^K-1)/3; thus the GST Worldtrace and
earlier affine BAD-controller paths are the SAME arithmetic object,
not two substitute notions. This is a precise cross-route dictionary.

The separate mathematical obligation to prove a shared digit two for
all K>=5, K !=7 remains and is not silently postulated.
-/

namespace GSTWorldtraceAllOrderAffineUnification

open GSTWorldtraceBlockLift
open GSTFourPowerDirectResidue
open GSTFourPowerDirectExistence
open GSTFourPowerAffineOrbit

/-- Exact GST cumulative information ledger: each physical exponent
increment contributes its full untruncated source multiplier. -/
def cumulativeWorldtrace (T c : Nat) : Nat → Nat
  | 0 => 0
  | u+1 => cumulativeWorldtrace T c u + (1+T*c)^u

@[simp] theorem cumulative_zero (T c : Nat) :
    cumulativeWorldtrace T c 0 = 0 := rfl

@[simp] theorem cumulative_succ (T c u : Nat) :
    cumulativeWorldtrace T c (u+1) =
      cumulativeWorldtrace T c u + (1+T*c)^u := rfl

/-- ALL-ORDER, UNTRUNCATED GST quotient law: every physical carry is
included, for arbitrary scale and multiplier. No modulus or bound. -/
theorem quotient_exact_all_orders
    (A c u T : Nat) (hT : 0 < T) :
    (A*(1+T*c)^u)/T =
      A/T + c*A*cumulativeWorldtrace T c u := by
  induction u with
  | zero =>
      simp [cumulativeWorldtrace]
  | succ u ih =>
      have hpow :
          A*(1+T*c)^(u+1) =
            (A*(1+T*c)^u)*(1+T*c) := by
        rw [pow_succ]
        ring
      calc
        (A*(1+T*c)^(u+1))/T =
          ((A*(1+T*c)^u)*(1+T*c))/T := by rw [hpow]
        _ = (A*(1+T*c)^u)/T + c*(A*(1+T*c)^u) :=
            quotient_multiply_step _ _ _ hT
        _ = A/T+c*A*cumulativeWorldtrace T c u +
            c*A*(1+T*c)^u := by
              rw [ih]
              ring
        _ = A/T + c*A*cumulativeWorldtrace T c (u+1) := by
              rw [cumulative_succ]
              ring

/-- Original physical perfect-power exact GST quotient at EVERY
digit depth, with source 4^M and neighboring source 4^(M+1)
retained. This subsumes all fixed-degree block-window identities as
untruncated equalities. -/
theorem pow4_exact_all_order_quotient (M u L : Nat) :
    4^(M+u*3^L)/3^(L+1) =
      4^M/3^(L+1) +
        GSTCanonicalTailLTE.lteCoeff L*4^M*
          cumulativeWorldtrace (3^(L+1)) (GSTCanonicalTailLTE.lteCoeff L) u := by
  have hp :
      4^(M+u*3^L) =
        4^M*(1+3^(L+1)*GSTCanonicalTailLTE.lteCoeff L)^u := by
    rw [show M+u*3^L=M+3^L*u by ac_rfl, pow_add,
      pow_mul, GSTCanonicalTailLTE.pow4_three_power_lte_exact L]
  rw [hp]
  exact quotient_exact_all_orders _ _ _ _ (by positivity)

/-- Generalized full-depth word: no finite postcut width is imposed. -/
def allOrderFingerprint (M u L : Nat) : Nat :=
  4^M/3^(L+1) +
    GSTCanonicalTailLTE.lteCoeff L*4^M*
      cumulativeWorldtrace (3^(L+1)) (GSTCanonicalTailLTE.lteCoeff L) u

/-- Exact physical digit read at ANY postcut row, including arbitrarily
far beyond the earlier cubic window. -/
theorem all_order_physical_digit_exact
    (M u L k : Nat) :
    digit3 (4^(M+u*3^L)) (L+1+k) =
      digit3 (allOrderFingerprint M u L) k := by
  have hq := pow4_exact_all_order_quotient M u L
  calc
    digit3 (4^(M+u*3^L)) (L+1+k) =
      digit3 (4^(M+u*3^L)/3^(L+1)) k := by
        unfold digit3
        have hp : 3^(L+1+k)=3^(L+1)*3^k := by rw [pow_add]
        rw [hp, ← Nat.div_div_eq_div_mul]
    _ = digit3 (allOrderFingerprint M u L) k := by
        rw [hq]
        rfl

/-- At L=0 and c_0=1 the full Worldtrace ledger is the historical
4-power affine orbit, EXACTLY, for EVERY natural exponent K. -/
theorem worldtrace_zero_scale_eq_affineOrbit
    (K : Nat) :
    cumulativeWorldtrace 3 1 K = affineOrbit K := by
  induction K with
  | zero => rfl
  | succ K ih =>
      rw [cumulative_succ, ih]
      have hpow := four_pow_eq_one_plus_three_affineOrbit K
      simpa only [show (1+3*1:Nat)=4 by decide] using
        (show affineOrbit K + 4^K = affineOrbit (K+1) by
          rw [hpow, affineOrbit_succ]
          ring)

/-- The actual source and neighbor affine-orbit words recover the
complete untruncated GST fingerprints at zero scale. -/
theorem zero_scale_original_source_fingerprint (K : Nat) :
    allOrderFingerprint 0 K 0 = affineOrbit K := by
  simp [allOrderFingerprint, GSTCanonicalTailLTE.lteCoeff,
    worldtrace_zero_scale_eq_affineOrbit]

theorem zero_scale_original_neighbor_fingerprint (K : Nat) :
    allOrderFingerprint 1 K 0 = affineOrbit (K+1) := by
  simp only [allOrderFingerprint, GSTCanonicalTailLTE.lteCoeff,
    show (3:Nat)^(0+1)=3 by decide,
    show (4:Nat)^1=4 by decide]
  rw [worldtrace_zero_scale_eq_affineOrbit]
  simp only [Nat.zero_add, show (4:Nat)/3=1 by decide,
    Nat.one_mul, Nat.mul_one]
  rw [affineOrbit_succ]
  ring

/-- The former BAD-channel obstruction can now be stated in this
independent, exact ALL-ORDER GST physical ledger vocabulary. -/
theorem original_CommonTwo_iff_worldtrace_affine_pair
    (K : Nat) :
    CommonTwo K ↔
      ∃ k : Nat,
        digit3 (allOrderFingerprint 0 K 0) k = 2 ∧
        digit3 (allOrderFingerprint 1 K 0) k = 2 := by
  rw [zero_scale_original_source_fingerprint,
      zero_scale_original_neighbor_fingerprint]
  exact (power_common_two_iff_affine K).trans Iff.rfl

#print axioms quotient_exact_all_orders
#print axioms pow4_exact_all_order_quotient
#print axioms all_order_physical_digit_exact
#print axioms worldtrace_zero_scale_eq_affineOrbit
#print axioms zero_scale_original_source_fingerprint
#print axioms zero_scale_original_neighbor_fingerprint
#print axioms original_CommonTwo_iff_worldtrace_affine_pair

end GSTWorldtraceAllOrderAffineUnification
