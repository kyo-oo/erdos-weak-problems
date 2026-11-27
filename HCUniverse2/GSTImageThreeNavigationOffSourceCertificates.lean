import Mathlib

/-!
# GST Image 3 — PHYSICAL NAVIGATION OFF / ZERO CURVATURE F19 certificate

The author's ORIGINAL 12-state fold F_(a,0) = U + J + a M
has exact native 12-fold Krylov determinant

 -4 a² (1+a) Q8(a) Q9(a),

where the integer-coefficient factors Q8, Q9 are defined below.
Independent symbolic construction of the original U,J,M and the exact
2+10 resultant decomposition is recorded in the research computation.

This Lean file kernel-checks the COMPLETE finite residue obstruction:
Q8 and Q9 do not vanish anywhere in F19 and their leading coefficients
are units. The rational-root reduction and source determinant identity
are separately documented; they are NOT silently postulated as Lean
theorems in this file.

Consequently the mathematical rational-source criterion is:
F_(a,0) is cyclic iff a ≠ 0 and a ≠ -1.
No canonical original-X Chow/Hodge realization follows from this fact.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 6000000

namespace GSTImageThreeNavigationOffSourceCertificates

/-- Original ten-cell Q8 factor evaluated on ALL nineteen possible
mod-19 direct SURVIVE strengths. -/
def navigationOffQ8Mod19 (a : ZMod 19) : ZMod 19 :=
  411701 + 899200*a - 342272*a^2 - 123812*a^3 -
  14492*a^4 - 25296*a^5 + 4672*a^6 - 832*a^7 + 256*a^8

/-- Original inter-block spectral Q9 factor at navigation off. -/
def navigationOffQ9Mod19 (a : ZMod 19) : ZMod 19 :=
  12176 + 45312*a + 72685*a^2 + 59539*a^3 +
  15088*a^4 - 15320*a^5 - 13120*a^6 -
  1376*a^7 + 1984*a^8 + 640*a^9

/-- Exhaustive finite-field exclusion for every element of ZMod19. -/
theorem navigationOffQ8Mod19_no_roots :
    ∀ a : ZMod 19, navigationOffQ8Mod19 a ≠ 0 := by
  decide

/-- Exhaustive finite-field exclusion for original cross-spectrum Q9. -/
theorem navigationOffQ9Mod19_no_roots :
    ∀ a : ZMod 19, navigationOffQ9Mod19 a ≠ 0 := by
  decide

/-- The product never vanishes at any mod-19 direct SURVIVE source. -/
theorem navigationOffProductMod19_nonzero (a : ZMod 19) :
    navigationOffQ8Mod19 a * navigationOffQ9Mod19 a ≠ 0 := by
  letI : Fact (Nat.Prime 19) := ⟨by decide⟩
  exact mul_ne_zero (navigationOffQ8Mod19_no_roots a)
    (navigationOffQ9Mod19_no_roots a)

/-- Rational-root reduction is legitimate because mod-19 denominators
cannot divide the highest coefficients 256 and 640. -/
theorem navigationOffLeadingCoefficientsMod19_units :
    (256 : ZMod 19) ≠ 0 ∧ (640 : ZMod 19) ≠ 0 := by
  decide

#check navigationOffQ8Mod19_no_roots
#check navigationOffQ9Mod19_no_roots
#check navigationOffProductMod19_nonzero
#check navigationOffLeadingCoefficientsMod19_units

#print axioms navigationOffQ8Mod19_no_roots
#print axioms navigationOffQ9Mod19_no_roots
#print axioms navigationOffProductMod19_nonzero

end GSTImageThreeNavigationOffSourceCertificates
