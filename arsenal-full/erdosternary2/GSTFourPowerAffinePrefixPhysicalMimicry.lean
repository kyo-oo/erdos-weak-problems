import GSTFourPowerAffineOntologicalCompleteness
import GSTFourPowerAffineOrbit

set_option maxRecDepth 1000000
set_option maxHeartbeats 25000000

/-!
# GST exact physical mimicry of every finite affine source-neighbor prefix

Prefix-surjectivity of the original 4-power affine orbit lets any finite
arbitrary BAD-controller coordinate X be represented, at the same finite
digit depth, by an actual original integer perfect-power exponent K.
Both source 4^K and neighbor 4^(K+1) are matched simultaneously.

This is NOT a counterexample to Erdős 406: finite matching does not
yield an all-depth physical BAD trace. It proves that a finite residue
filter alone cannot exclude generic bad-coordinate patterns as
nonphysical. The universal proof needs a cross-depth or terminal
invariant that distinguishes a single fixed natural exponent.
-/

namespace GSTFourPowerAffinePrefixPhysicalMimicry

open GSTFourPowerDirectResidue
open GSTFourPowerAffineOrbit
open GSTFourPowerAffineOntologicalCompleteness

private theorem digit_eq_from_equal_finite_prefix
    (p R S j : Nat) (hj : j < p)
    (hmod : R%3^p=S%3^p) :
    digit3 R j=digit3 S j := by
  have hdiv : 3^(j+1) ∣ 3^p :=
    Nat.pow_dvd_pow 3 (by omega)
  apply digit3_eq_of_mod_next
  calc
    R%3^(j+1) = (R%3^p)%3^(j+1) :=
      (Nat.mod_mod_of_dvd _ hdiv).symm
    _ = (S%3^p)%3^(j+1) := by rw [hmod]
    _ = S%3^(j+1) := Nat.mod_mod_of_dvd _ hdiv

/-- Every prescribed finite pair word (X, 4X+1) is the simultaneous
first-p-trit physical image of some actual consecutive powers
(4^K,4^(K+1)), shifted by the compulsory low 4-power trit. -/
theorem every_finite_affine_pair_prefix_is_physically_realized
    (p X : Nat) :
    ∃ K : Nat, K<3^p ∧
      ∀ j : Nat, j<p →
        digit3 (4^K) (j+1)=digit3 X j ∧
        digit3 (4^(K+1)) (j+1)=digit3 (4*X+1) j := by
  obtain ⟨K,hK,hmod⟩ :=
    every_arbitrary_coordinate_has_physical_prefix p X
  have hstep :
      (4*affineOrbit K+1)%3^p=(4*X+1)%3^p := by
    have hsource : affineOrbit K ≡ X [MOD 3^p] := hmod
    have h := (hsource.mul_left 4).add_left 1
    change (1+4*affineOrbit K)%3^p = (1+4*X)%3^p at h
    simpa only [Nat.add_comm] using h
  refine ⟨K,hK,?_⟩
  intro j hj
  constructor
  · calc
      digit3 (4^K) (j+1) = digit3 (affineOrbit K) j :=
        four_pow_digit_affine_shift K j
      _ = digit3 X j :=
        digit_eq_from_equal_finite_prefix p (affineOrbit K) X j hj hmod
  · calc
      digit3 (4^(K+1)) (j+1) =
          digit3 (affineOrbit (K+1)) j :=
        four_pow_digit_affine_shift (K+1) j
      _ = digit3 (4*affineOrbit K+1) j := by rw [affineOrbit_succ]
      _ = digit3 (4*X+1) j :=
        digit_eq_from_equal_finite_prefix p
          (4*affineOrbit K+1) (4*X+1) j hj hstep

/-- A generic finite bad source-neighbor controller prefix always
has an actual perfect-power physical mimic to that same finite depth.
It is therefore unsound to infer a universal contradiction solely
from the absence of a bounded-prefix pattern in an arbitrary source. -/
theorem any_finite_bad_pair_prefix_has_physical_mimic
    (p X : Nat)
    (hbad : ∀ j : Nat, j<p →
      ¬ (digit3 X j=2 ∧ digit3 (4*X+1) j=2)) :
    ∃ K : Nat, K<3^p ∧
      ∀ j : Nat, j<p →
        ¬ (digit3 (4^K) (j+1)=2 ∧
           digit3 (4^(K+1)) (j+1)=2) := by
  obtain ⟨K,hK,hpair⟩ :=
    every_finite_affine_pair_prefix_is_physically_realized p X
  refine ⟨K,hK,?_⟩
  intro j hj hp
  obtain ⟨hs,hn⟩ := hpair j hj
  exact hbad j hj ⟨hs.symm.trans hp.1, hn.symm.trans hp.2⟩

#print axioms digit_eq_from_equal_finite_prefix
#print axioms every_finite_affine_pair_prefix_is_physically_realized
#print axioms any_finite_bad_pair_prefix_has_physical_mimic

end GSTFourPowerAffinePrefixPhysicalMimicry
