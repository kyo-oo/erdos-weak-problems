import GSTCMNumberManipulationTrace

/-!
# GST CM Number Manipulation: dual rational conjugate detection

Unlike a SINGLE field trace, which annihilates purely imaginary
nonzero CM periods, the PAIR of rational CM channels detects
every nonzero Gaussian-rational CM value.

At any corrected zeta index m, if x^(m+1) ≠ y^(m+2)
in Q(i), then its inverse is a nonzero Gaussian-rational value
and at least ONE of two canonical Q-valued number-theoretic
readouts is nonzero:
   Tr_Re(u⁻¹) = 2*Re(u⁻¹),
   Tr_Im(u⁻¹) = 2*Im(u⁻¹).
The fixed factor ζ(0)=-1/2 preserves this nonvanishing
disjunction. Neither an arbitrary coefficient nor an assumed
nonzero trace is inserted.

This is a concrete dual-NM arithmetic *detector*, not yet a
canonical abelian-variety period map. To force actual Hodge
cycle directions, a cup/Gysin correspondence must be proved
to realize these scalar readouts on actual algebraic cycles.
-/

set_option maxHeartbeats 20000000
noncomputable section
namespace GSTCMNumberManipulationTrace

def cmImagTrace (z : CMQ) : ℚ := 2*z.2

/-- Any nonzero Gaussian-rational scalar is detected by at least
one of its two Q-rational CM channels. -/
theorem cm_dual_channels_nonzero
    (z : CMQ) (hz : z ≠ 0) :
    cmTrace z ≠ 0 ∨ cmImagTrace z ≠ 0 := by
  by_contra h
  push_neg at h
  apply hz
  apply Prod.ext
  · have hfst : (2:ℚ) * z.1 = 0 := by simpa [cmTrace] using h.1
    exact (mul_eq_zero.mp hfst).resolve_left (by norm_num)
  · have hsnd : (2:ℚ) * z.2 = 0 := by simpa [cmImagTrace] using h.2
    exact (mul_eq_zero.mp hsnd).resolve_left (by norm_num)

/-- The actual Gaussian inverse is nonzero at every nonzero
CM denominator. This is proved by its verified multiplicative
inverse identity, not by totalized-field heuristics. -/
theorem cmInv_nonzero (z : CMQ) (hz : z ≠ 0) :
    cmInv z ≠ 0 := by
  intro hinv
  have hmul := cmMul_inv z hz
  rw [hinv] at hmul
  simp [cmMul] at hmul

/-- The corrected CM-indexed NM denominator has two independently
computed rational channels. Their joint detector NEVER erases a
nonzero complex reciprocal, unlike the trace alone. -/
theorem cmIndexedNM_dual_detector
    (x y : CMQ) (m : ℕ)
    (hlegal : cmIndexedDenominator x y m ≠ 0) :
    cmIndexedNMTrace x y m ≠ 0 ∨
      cmImagTrace (cmInv (cmIndexedDenominator x y m)) ≠ 0 := by
  exact cm_dual_channels_nonzero _
    (cmInv_nonzero _ hlegal)

/-- Fixed ζ(0)=-1/2 scaling is not chosen to match a target
geometry and preserves the exact dual-channel nonvanishing. -/
theorem cmIndexedNM_fixed_zeta_dual_detector
    (x y : CMQ) (m : ℕ)
    (hlegal : cmIndexedDenominator x y m ≠ 0) :
    (-1/2:ℚ)*cmIndexedNMTrace x y m ≠ 0 ∨
      (-1/2:ℚ)*cmImagTrace
        (cmInv (cmIndexedDenominator x y m)) ≠ 0 := by
  rcases cmIndexedNM_dual_detector x y m hlegal with hreal | himag
  · exact Or.inl (mul_ne_zero (by norm_num) hreal)
  · exact Or.inr (mul_ne_zero (by norm_num) himag)

#check cm_dual_channels_nonzero
#check cmInv_nonzero
#check cmIndexedNM_dual_detector
#check cmIndexedNM_fixed_zeta_dual_detector

#print axioms cm_dual_channels_nonzero
#print axioms cmIndexedNM_dual_detector
#print axioms cmIndexedNM_fixed_zeta_dual_detector

end GSTCMNumberManipulationTrace
