import Mathlib

/-!
# Exact rational-lattice quantization of approximate GST native Betti sources

Geometry (independently proved in the companion derivation):
research/derivations/GST_20261112_approximate_native_Hodge_source_quantized_lattice_return.tex

For any original X, rational prescribed alpha with d*alpha integral,
and a ACTUAL algebraic cycle beta with m*beta integral, m<=C,
a canonical Betti class within the STRICT rational-integral lattice
threshold 1/(d*C) of alpha MUST BE EXACTLY alpha.
This reduces the geometric GST input from exact target matching
to bounded-degree ACTUAL Chow cycles with approximate Betti targets.
It does not construct those cycles or their degree bound by fiat.

This file formalizes the ARITHMETIC CORE over Q, usable
coordinatewise on the free integral cohomology lattice of X.
-/

set_option maxHeartbeats 2500000
noncomputable section

namespace GSTNativeQuantizedApproximateSource

/-- Any nonzero integer has rational absolute value at least one,
so no scaled nonzero integral cohomology coordinate can lie strictly
inside the GST native unit threshold. -/
theorem integer_gap_for_scaled_native_error
    (x : ℚ) (k : ℤ) (D M C : ℕ)
    (hD : 0 < D) (hM : 0 < M) (hMC : M ≤ C)
    (hScaled : (D : ℚ) * (M : ℚ) * x = (k : ℚ))
    (hBound : (D : ℚ) * (C : ℚ) * |x| < 1) :
    x = 0 := by
  have hd : (0 : ℚ) < D := by exact_mod_cast hD
  have hm : (0 : ℚ) < M := by exact_mod_cast hM
  have hmc : (M : ℚ) ≤ C := by exact_mod_cast hMC
  have hLE :
      (D : ℚ) * (M : ℚ) * |x| ≤
        (D : ℚ) * (C : ℚ) * |x| := by
    gcongr
  have hkLt : |(k : ℚ)| < 1 := by
    rw [← hScaled]
    have h := lt_of_le_of_lt hLE hBound
    simpa only [abs_mul, abs_of_pos hd, abs_of_pos hm] using h
  have hkInt : |k| < 1 := by exact_mod_cast hkLt
  have hkPos : k < 1 := lt_of_le_of_lt (le_abs_self k) hkInt
  have hkNeg : -k < 1 := lt_of_le_of_lt (neg_le_abs k) hkInt
  have hkZero : k = 0 := by omega
  have hProd : (D : ℚ) * (M : ℚ) * x = 0 := by
    simpa [hkZero] using hScaled
  exact (mul_eq_zero.mp hProd).resolve_left
    (mul_ne_zero (ne_of_gt hd) (ne_of_gt hm))

/-- Main EXACT numeric conversion: bounded-denominator APPROXIMATE
native rational Hodge source equals the original PRESCRIBED target.
No abstract Hodge-to-Chow selector and no source-existence axiom. -/
theorem approximate_native_rational_target_is_exact
    (alpha beta : ℚ) (a b : ℤ) (D M C : ℕ)
    (hD : 0 < D) (hM : 0 < M) (hMC : M ≤ C)
    (hAlphaIntegral : (D : ℚ) * alpha = (a : ℚ))
    (hBetaIntegral : (M : ℚ) * beta = (b : ℚ))
    (hClose : (D : ℚ) * (C : ℚ) * |beta-alpha| < 1) :
    beta = alpha := by
  have hScaled :
      (D : ℚ) * (M : ℚ) * (beta-alpha) =
        ((b * (D : ℤ) - a * (M : ℤ)) : ℚ) := by
    calc
      (D : ℚ) * (M : ℚ) * (beta-alpha) =
          (D : ℚ) * ((M : ℚ) * beta) -
            (M : ℚ) * ((D : ℚ) * alpha) := by ring
      _ = (D : ℚ) * (b : ℚ) - (M : ℚ) * (a : ℚ) := by
        rw [hBetaIntegral, hAlphaIntegral]
      _ = ((b * (D : ℤ) - a * (M : ℤ)) : ℚ) := by
        push_cast
        ring
  have hZero := integer_gap_for_scaled_native_error
    (beta-alpha) (b * (D : ℤ) - a * (M : ℤ)) D M C
    hD hM hMC (by
      push_cast
      exact hScaled) hClose
  exact sub_eq_zero.mp hZero

/-- The exact 1/(d*C) boundary is strictly necessary:
the rational target 2/5 differs from the actual rational input 3/7
by exactly 1/35. -/
theorem native_quantized_threshold_sharp :
    |(3/7 : ℚ) - (2/5 : ℚ)| = 1/35 := by
  norm_num

#check integer_gap_for_scaled_native_error
#check approximate_native_rational_target_is_exact
#check native_quantized_threshold_sharp
#print axioms approximate_native_rational_target_is_exact
#print axioms native_quantized_threshold_sharp

end GSTNativeQuantizedApproximateSource
