import GSTWorldtraceCubicBlockLift
import GSTFourPowerDirectExistence

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
# All-exponent cubic GST coupled Worldtrace fingerprint

For EVERY original exponent K, two correlated cubic perfect-power fingerprints
recover the actual digits of 4^K and 4^(K+1) through three full scale bands.
This contains neither any renamed hGate assumption nor a finite-sweep
hypothesis. The exact global exit question is intentionally kept separate.
-/

namespace GSTWorldtraceCubicGlobalFingerprint

open GSTWorldtraceCubicBlockLift
open GSTWorldtraceQuadraticBlockLift
open GSTFourPowerDirectResidue
open GSTFourPowerDirectExistence

/-- The complete three-band exact GST fingerprint, with the genuine
source offset 4^M retained. -/
def cubicFingerprint (M u L : Nat) : Nat :=
  4^M/3^(L+1) +
  u*GSTCanonicalTailLTE.lteCoeff L*4^M +
  triangle u*3^(L+1)*(GSTCanonicalTailLTE.lteCoeff L)^2*4^M +
  tetra u*(3^(L+1))^2*(GSTCanonicalTailLTE.lteCoeff L)^3*4^M

/-- Digit reconstruction for the full physical perfect power.
No symbolic replacement or forced Happy event. -/
theorem cubic_fingerprint_digit_exact
    (M u L w k : Nat)
    (hw : 1 ≤ w) (hband : w ≤ 3*(L+1)) (hk : k < w) :
    digit3 (4^(M+u*3^L)) (L+1+k) =
      digit3 (cubicFingerprint M u L) k := by
  have hmodw :
      (4^(M+u*3^L)/3^(L+1))%3^w =
        (cubicFingerprint M u L)%3^w :=
      pow4_cubic_window_lift M u L w hw hband
  have hdiv : 3^(k+1) ∣ 3^w := Nat.pow_dvd_pow 3 (by omega)
  have hmod :
      (4^(M+u*3^L)/3^(L+1))%3^(k+1) =
        (cubicFingerprint M u L)%3^(k+1) := by
    calc
      (4^(M+u*3^L)/3^(L+1))%3^(k+1) =
          ((4^(M+u*3^L)/3^(L+1))%3^w)%3^(k+1) :=
            (Nat.mod_mod_of_dvd _ hdiv).symm
      _ = ((cubicFingerprint M u L)%3^w)%3^(k+1) := by rw [hmodw]
      _ = (cubicFingerprint M u L)%3^(k+1) :=
            Nat.mod_mod_of_dvd _ hdiv
  have hread :
      digit3 (4^(M+u*3^L)/3^(L+1)) k =
        digit3 (cubicFingerprint M u L) k :=
      digit3_eq_of_mod_next _ _ k hmod
  calc
    digit3 (4^(M+u*3^L)) (L+1+k) =
      digit3 (4^(M+u*3^L)/3^(L+1)) k := by
        unfold digit3
        have hp : 3^(L+1+k)=3^(L+1)*3^k := by rw [pow_add]
        rw [hp, ← Nat.div_div_eq_div_mul]
    _ = digit3 (cubicFingerprint M u L) k := hread

/-- The SAME two physical powers, reconstructed from any exponent
split K = (K mod 3^L) + floor(K/3^L)*3^L. -/
theorem cubic_fingerprint_both_physical_digits
    (K L w k : Nat)
    (hw : 1 ≤ w) (hband : w ≤ 3*(L+1)) (hk : k < w) :
    digit3 (4^K) (L+1+k) =
      digit3 (cubicFingerprint (K%3^L) (K/3^L) L) k ∧
    digit3 (4^(K+1)) (L+1+k) =
      digit3 (cubicFingerprint (K%3^L+1) (K/3^L) L) k := by
  have hsplit : K=K%3^L+(K/3^L)*3^L := by
    simpa only [Nat.mul_comm] using
      (Nat.mod_add_div K (3^L)).symm
  constructor
  · calc
      digit3 (4^K) (L+1+k) =
        digit3 (4^(K%3^L+(K/3^L)*3^L)) (L+1+k) := by
          exact congrArg (fun n : Nat => digit3 (4^n) (L+1+k)) hsplit
      _ = digit3 (cubicFingerprint (K%3^L) (K/3^L) L) k :=
          cubic_fingerprint_digit_exact
            (K%3^L) (K/3^L) L w k hw hband hk
  · have hsplit1 : K+1=(K%3^L+1)+(K/3^L)*3^L := by omega
    calc
      digit3 (4^(K+1)) (L+1+k) =
        digit3 (4^((K%3^L+1)+(K/3^L)*3^L)) (L+1+k) := by
          exact congrArg (fun n : Nat => digit3 (4^n) (L+1+k)) hsplit1
      _ = digit3 (cubicFingerprint (K%3^L+1) (K/3^L) L) k :=
          cubic_fingerprint_digit_exact
            (K%3^L+1) (K/3^L) L w k hw hband hk

/-- Noncircular exact common-two constructor for arbitrary exponents
whenever a real three-band collision certificate is furnished. -/
theorem cubic_certificate_to_original_CommonTwo
    (K L w k : Nat)
    (hw : 1 ≤ w) (hband : w ≤ 3*(L+1)) (hk : k < w)
    (hs : digit3 (cubicFingerprint (K%3^L) (K/3^L) L) k=2)
    (hn : digit3 (cubicFingerprint (K%3^L+1) (K/3^L) L) k=2) :
    CommonTwo K := by
  obtain ⟨h4,h5⟩ :=
    cubic_fingerprint_both_physical_digits K L w k hw hband hk
  exact ⟨L+1+k, by omega, h4.trans hs, h5.trans hn⟩

/-- Any hypothetical original bad exponent avoids every correlated
third-order GST collision window. This is the exact missing-exit
condition, without pretending that it is already contradictory. -/
theorem noCommonTwo_excludes_all_cubic_windows
    (K L w k : Nat)
    (hNo : ¬ CommonTwo K)
    (hw : 1 ≤ w) (hband : w ≤ 3*(L+1)) (hk : k < w) :
    ¬ (digit3 (cubicFingerprint (K%3^L) (K/3^L) L) k=2 ∧
       digit3 (cubicFingerprint (K%3^L+1) (K/3^L) L) k=2) := by
  rintro ⟨hs,hn⟩
  exact hNo (cubic_certificate_to_original_CommonTwo K L w k hw hband hk hs hn)

#print axioms cubic_fingerprint_digit_exact
#print axioms cubic_fingerprint_both_physical_digits
#print axioms cubic_certificate_to_original_CommonTwo
#print axioms noCommonTwo_excludes_all_cubic_windows

end GSTWorldtraceCubicGlobalFingerprint
