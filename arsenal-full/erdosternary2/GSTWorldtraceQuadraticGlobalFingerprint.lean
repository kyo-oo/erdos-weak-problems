import GSTWorldtraceQuadraticBlockLift
import GSTFourPowerDirectExistence

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
# Global all-exponent exact quadratic GST two-wave fingerprint

No exponent is excluded from this construction. Any natural K has the
literal Euclidean decomposition
  K = M + u*3^L,
  M=K%3^L, u=K/3^L.

The second-order Worldtrace block theorem derives the EXACT physical
source and neighboring target trit at ANY k<w<=2*(L+1), without
assuming their value is two and without inventing a BAD controller.
When both explicit quadratic fingerprints have digit two, this gives
the original source-neighbor CommonTwo K for arbitrary K.

Conversely every real counterexample must avoid simultaneous twos
in these correlated quadratic fingerprints AT EVERY scale and width.
The latter is a new necessary constraint on a hypothetical
exceptional path, NOT a theorem asserting no such path exists.
-/

namespace GSTWorldtraceQuadraticGlobalFingerprint

open GSTFourPowerDirectResidue
open GSTFourPowerDirectExistence
open GSTWorldtraceQuadraticBlockLift

/-- The exact physical first-two-scale-band arithmetic fingerprint
of the source 4^(M+u*3^L), including its initial quotient and all
quadratic carry effects that survive modulo 3^(2L+2). -/
def quadraticFingerprint (M u L : Nat) : Nat :=
  4^M/3^(L+1) +
    u*GSTCanonicalTailLTE.lteCoeff L*4^M +
    triangle u*3^(L+1)*(GSTCanonicalTailLTE.lteCoeff L)^2*4^M

/-- Exact digit read-back for arbitrary source offset M, scale L and
multiplier u, up to twice the previous GST scale band. -/
theorem quadratic_fingerprint_digit_exact
    (M u L w k : Nat)
    (hw : 1 ≤ w) (hband : w ≤ 2*(L+1)) (hk : k < w) :
    digit3 (4^(M+u*3^L)) (L+1+k) =
      digit3 (quadraticFingerprint M u L) k := by
  have hmodw :
      (4^(M+u*3^L)/3^(L+1))%3^w =
        (quadraticFingerprint M u L)%3^w := by
    exact pow4_quadratic_window_lift M u L w hw hband
  have hdiv : 3^(k+1) ∣ 3^w := Nat.pow_dvd_pow 3 (by omega)
  have hmod :
      (4^(M+u*3^L)/3^(L+1))%3^(k+1) =
        (quadraticFingerprint M u L)%3^(k+1) := by
    calc
      (4^(M+u*3^L)/3^(L+1))%3^(k+1) =
        ((4^(M+u*3^L)/3^(L+1))%3^w)%3^(k+1) :=
          (Nat.mod_mod_of_dvd _ hdiv).symm
      _ = ((quadraticFingerprint M u L)%3^w)%3^(k+1) := by
          rw [hmodw]
      _ = (quadraticFingerprint M u L)%3^(k+1) :=
          Nat.mod_mod_of_dvd _ hdiv
  have hd := digit3_eq_of_mod_next
    (4^(M+u*3^L)/3^(L+1)) (quadraticFingerprint M u L) k hmod
  calc
    digit3 (4^(M+u*3^L)) (L+1+k) =
      digit3 (4^(M+u*3^L)/3^(L+1)) k := by
        unfold digit3
        have hpow : 3^(L+1+k)=3^(L+1)*3^k := by rw [pow_add]
        rw [hpow, ← Nat.div_div_eq_div_mul]
    _ = digit3 (quadraticFingerprint M u L) k := hd

/-- The exact physical GST two-wave source and neighbor are
simultaneously reconstructed from the Euclidean exponent split,
for EVERY natural exponent K and chosen scale L. -/
theorem quadratic_fingerprint_both_physical_digits
    (K L w k : Nat)
    (hw : 1 ≤ w) (hband : w ≤ 2*(L+1)) (hk : k < w) :
    digit3 (4^K) (L+1+k) =
      digit3 (quadraticFingerprint (K%3^L) (K/3^L) L) k ∧
    digit3 (4^(K+1)) (L+1+k) =
      digit3 (quadraticFingerprint (K%3^L+1) (K/3^L) L) k := by
  have hsplit : K=K%3^L+(K/3^L)*3^L := by
    simpa only [Nat.mul_comm] using
      (Nat.mod_add_div K (3^L)).symm
  constructor
  · calc
      digit3 (4^K) (L+1+k) =
        digit3 (4^(K%3^L+(K/3^L)*3^L)) (L+1+k) := by
          exact congrArg (fun n : Nat => digit3 (4^n) (L+1+k)) hsplit
      _ = digit3 (quadraticFingerprint (K%3^L) (K/3^L) L) k :=
          quadratic_fingerprint_digit_exact
            (K%3^L) (K/3^L) L w k hw hband hk
  · have hsplit1 :
        K+1=(K%3^L+1)+(K/3^L)*3^L := by omega
    calc
      digit3 (4^(K+1)) (L+1+k) =
        digit3 (4^((K%3^L+1)+(K/3^L)*3^L)) (L+1+k) := by
          exact congrArg (fun n : Nat => digit3 (4^n) (L+1+k)) hsplit1
      _ = digit3 (quadraticFingerprint (K%3^L+1) (K/3^L) L) k :=
          quadratic_fingerprint_digit_exact
            (K%3^L+1) (K/3^L) L w k hw hband hk

/-- An all-exponent axiom-free GST certificate constructor.
No special residual class, no circular existence hypothesis,
and no restriction to exponents K == 4 (mod 3^L). -/
theorem quadratic_all_exponents_certificate
    (K L w k : Nat)
    (hw : 1 ≤ w) (hband : w ≤ 2*(L+1)) (hk : k < w)
    (hsource :
      digit3 (quadraticFingerprint (K%3^L) (K/3^L) L) k=2)
    (hneighbor :
      digit3 (quadraticFingerprint (K%3^L+1) (K/3^L) L) k=2) :
    CommonTwo K := by
  obtain ⟨hs, hn⟩ :=
    quadratic_fingerprint_both_physical_digits K L w k hw hband hk
  refine ⟨L+1+k, by omega, ?_, ?_⟩
  · rw [hs]
    exact hsource
  · rw [hn]
    exact hneighbor

/-- Every hypothetical CommonTwo counterexample must avoid ALL finite
two-scale-band quadratic GST fingerprints, at every scale L, window
and row. The unresolved universal problem is now visibly localized
to a perfect-power-path exclusion in this explicit arithmetic family. -/
theorem noCommonTwo_forbids_all_quadratic_fingerprint_pairs
    (K L w k : Nat)
    (hNo : ¬ CommonTwo K)
    (hw : 1 ≤ w) (hband : w ≤ 2*(L+1)) (hk : k < w) :
    ¬ (digit3 (quadraticFingerprint (K%3^L) (K/3^L) L) k=2 ∧
       digit3 (quadraticFingerprint (K%3^L+1) (K/3^L) L) k=2) := by
  rintro ⟨hs, hn⟩
  exact hNo (quadratic_all_exponents_certificate
    K L w k hw hband hk hs hn)

#print axioms quadratic_fingerprint_digit_exact
#print axioms quadratic_fingerprint_both_physical_digits
#print axioms quadratic_all_exponents_certificate
#print axioms noCommonTwo_forbids_all_quadratic_fingerprint_pairs

end GSTWorldtraceQuadraticGlobalFingerprint
