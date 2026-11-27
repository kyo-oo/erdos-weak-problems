import Mathlib

/-!
# GST K3 diagonal transcendental primitive — a non-divisor geometric source

For a smooth projective complex K3 surface S and ample divisor h with
degree d = ∫_S h² > 0, let Y=S×S. The genuine codimension-two cycles

  Δ : diagonal(S), U : {pt}×S, V : S×{pt}, B : h×h

supply a NEW rational primitive algebraic cycle

  P = Δ - U - V - (1/d) B.

In rational H^4(Y), the Lefschetz operator for polarization
H = pr₁*h+pr₂*h satisfies (write A=pr₁*[pt]·pr₂*h,
T=pr₁*h·pr₂*[pt]):

  H · cl(Δ) = 2(A+T)
  H · cl(U) = A
  H · cl(V) = T
  H · cl(B) = d(A+T).

Consequently H·cl(P)=0. These identities follow geometrically from
the diagonal projection formula and the Künneth ring of K3 surfaces.
They are NOT statements about a generic abstract GST orbit.

If u,v are transcendental rational degree-two classes orthogonal to h
with ∫_S u∧v = q≠0, the genuine intersection readout against
pr₁*u · pr₂*v evaluates to q on Δ and zero on U,V,B.
It follows that P is NONZERO and cannot be a rational divisor-word
combination when Pic(S)=Q h. More generally it lies outside the
full divisor-word subspace whenever u and v are orthogonal to NS(S).

The Lean kernel below verifies the exact rational cycle constructor,
its Lefschetz-kernel cancellation, and the independent transcendental
detector obstruction. The actual K3 scheme construction, Betti/Künneth
comparison, diagonal Gysin identities and Néron-Severi nondegeneracy
remain separately stated geometric obligations. Nothing assumes a
representative of a missing Hodge class or universal cycle-class
surjectivity.
-/

set_option maxHeartbeats 3000000
noncomputable section

namespace GSTK3DiagonalPrimitive

variable {C H4 H6 : Type*}
  [AddCommGroup C] [Module ℚ C]
  [AddCommGroup H4] [Module ℚ H4]
  [AddCommGroup H6] [Module ℚ H6]

/-- A genuine NEW native cycle built from the diagonal and three already
algebraic product cycles. It is not a selected Hodge-class preimage. -/
def diagonalPrimitiveCycle
    (diagonal pointLeft pointRight hCrossH : C)
    (degree : ℚ) : C :=
  diagonal - pointLeft - pointRight - degree⁻¹ • hCrossH

/-- Algebraic-cycle naturality determines the class of the explicit
diagonal primitive candidate by Q-linearity. -/
theorem diagonalPrimitiveCycle_class
    (cl : C →ₗ[ℚ] H4)
    (diagonal pointLeft pointRight hCrossH : C)
    (degree : ℚ) :
    cl (diagonalPrimitiveCycle diagonal pointLeft pointRight hCrossH degree) =
      cl diagonal - cl pointLeft - cl pointRight -
        degree⁻¹ • cl hCrossH := by
  simp [diagonalPrimitiveCycle, map_sub, map_smul]

/-- The exact K3×K3 primitive identity, with no previously
assumed primitive Hodge vector. The only geometric inputs are the
FOUR independently calculable diagonal/product Lefschetz identities. -/
theorem diagonalPrimitiveCycle_is_primitive
    (cl : C →ₗ[ℚ] H4)
    (L : H4 →ₗ[ℚ] H6)
    (diagonal pointLeft pointRight hCrossH : C)
    (degree : ℚ) (hdegree : degree ≠ 0)
    (a t : H6)
    (hdiag : L (cl diagonal) = (2 : ℚ) • (a + t))
    (hleft : L (cl pointLeft) = a)
    (hright : L (cl pointRight) = t)
    (hcross : L (cl hCrossH) = degree • (a + t)) :
    L (cl (diagonalPrimitiveCycle diagonal pointLeft pointRight hCrossH degree)) =
      0 := by
  rw [diagonalPrimitiveCycle_class]
  simp only [map_sub, map_smul, hdiag, hleft, hright, hcross,
    smul_smul]
  rw [inv_mul_cancel₀ hdegree, one_smul]
  rw [show (2 : ℚ) • (a + t) = (a + t) + (a + t) by
    simp only [two_smul] <;> abel]
  abel

/-- Intersection readout of the primitive diagonal against an
independent transcendental pair u⊗v. Algebraic divisor words
are invisible to this functional, but the genuine diagonal is not. -/
theorem diagonalPrimitiveCycle_transcendental_readout
    (cl : C →ₗ[ℚ] H4)
    (ell : H4 →ₗ[ℚ] ℚ)
    (diagonal pointLeft pointRight hCrossH : C)
    (degree q : ℚ)
    (hdiag : ell (cl diagonal) = q)
    (hleft : ell (cl pointLeft) = 0)
    (hright : ell (cl pointRight) = 0)
    (hcross : ell (cl hCrossH) = 0) :
    ell (cl (diagonalPrimitiveCycle diagonal pointLeft pointRight hCrossH degree)) =
      q := by
  simp [diagonalPrimitiveCycle, map_sub, map_smul,
    hdiag, hleft, hright, hcross]

/-- NONZERO source beyond the hyperplane/divisor algebra.
The sole nonvanishing is an independent transcendental intersection
pairing of the true K3 surface. -/
theorem diagonalPrimitiveCycle_nonzero
    (cl : C →ₗ[ℚ] H4)
    (ell : H4 →ₗ[ℚ] ℚ)
    (diagonal pointLeft pointRight hCrossH : C)
    (degree q : ℚ)
    (hdiag : ell (cl diagonal) = q)
    (hleft : ell (cl pointLeft) = 0)
    (hright : ell (cl pointRight) = 0)
    (hcross : ell (cl hCrossH) = 0)
    (hq : q ≠ 0) :
    cl (diagonalPrimitiveCycle diagonal pointLeft pointRight hCrossH degree)
      ≠ 0 := by
  intro hzero
  have hread :=
    diagonalPrimitiveCycle_transcendental_readout
      cl ell diagonal pointLeft pointRight hCrossH degree q
      hdiag hleft hright hcross
  rw [hzero, map_zero] at hread
  exact hq hread.symm

/-- A transversal diagonal primitive is NOT in a submodule killed
by all transcendental readouts. On a K3 product, this submodule
can be instantiated by the algebra of divisor-word Hodge classes.
This is a true rank advance beyond divisor/hyperplane words, not a
change of notation for an existing word. -/
theorem diagonalPrimitiveCycle_outside_divisor_words
    (cl : C →ₗ[ℚ] H4)
    (ell : H4 →ₗ[ℚ] ℚ)
    (D : Submodule ℚ H4)
    (diagonal pointLeft pointRight hCrossH : C)
    (degree q : ℚ)
    (hdiag : ell (cl diagonal) = q)
    (hleft : ell (cl pointLeft) = 0)
    (hright : ell (cl pointRight) = 0)
    (hcross : ell (cl hCrossH) = 0)
    (hdivisor : D ≤ LinearMap.ker ell)
    (hq : q ≠ 0) :
    cl (diagonalPrimitiveCycle diagonal pointLeft pointRight hCrossH degree)
      ∉ D := by
  intro hmem
  have hz : ell
      (cl (diagonalPrimitiveCycle diagonal pointLeft pointRight hCrossH degree))
        = 0 := hdivisor hmem
  have hnonzero : ell
      (cl (diagonalPrimitiveCycle diagonal pointLeft pointRight hCrossH degree))
        = q :=
    diagonalPrimitiveCycle_transcendental_readout
      cl ell diagonal pointLeft pointRight hCrossH degree q
      hdiag hleft hright hcross
  exact hq (hnonzero.symm.trans hz)

#check diagonalPrimitiveCycle
#check diagonalPrimitiveCycle_is_primitive
#check diagonalPrimitiveCycle_nonzero
#check diagonalPrimitiveCycle_outside_divisor_words
#print axioms diagonalPrimitiveCycle_is_primitive
#print axioms diagonalPrimitiveCycle_outside_divisor_words

end GSTK3DiagonalPrimitive
