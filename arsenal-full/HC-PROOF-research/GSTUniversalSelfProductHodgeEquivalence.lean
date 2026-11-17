import GSTUniversalChowRetractToTarget

/-!
# GST exact self-product-to-X Hodge representability equivalence

For every smooth projective complex X and every rational (p,p)
Hodge alpha, the standard product Y=X×X with d=dim X and ample
h provides the canonical cohomological Hodge lift

   sigma(alpha) = pr1^*(alpha) cup pr2^*(h^d) / degree(h^d)

of bidegree (p+d,p+d). Projection pr1_* is a left inverse:
pr1_* sigma(alpha)=alpha.

The native correspondence in the opposite direction is external
product with h^d / degree(h^d). This means:

  alpha is a rational algebraic class on X
     IFF
  sigma(alpha) is a rational algebraic class on X×X.

This file proves the *logical equivalence* for ACTUAL Stage-2G
codimension-cycle modules and rational Betti cycle-class maps,
from the independently established genuine product/pushforward
naturality identities.

This is a STRICTLY MORE PRECISE research target than requiring
all Hodge classes of X×X to be algebraic: only the special
sigma(image of Hodge(X)) classes need representatives.

It is NOT a proof of algebraicity of sigma(alpha) for arbitrary
alpha, nor does the alternating self-product hyperplane primitive
supply that. The target is not replaced by an assumed surjectivity
axiom; this states exact forward/backward geometry to test.
-/

set_option maxHeartbeats 6000000
noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTUniversalChowRetractToTarget

namespace GSTUniversalSelfProductHodgeEquivalence

variable {Y X : SmoothProjectiveComplexScheme}
variable {D : HodgeBigradedBettiData Y}
variable {H : HodgeBigradedBettiData X}
variable {q p : Nat}

/-- Native external-product-with-ample-top-power section, with
the class-level Kunneth/projection-formula naturality identity.
No arbitrary Hodge-class native witness is a premise. -/
structure NativeProductSection
    (R : NativeHodgeRetract Y X D H q p) where
  nativeSection :
    codimensionCycles X.X p →ₗ[ℚ] codimensionCycles Y.X q
  cycleClass_section_natural :
    ∀ Z : codimensionCycles X.X p,
      D.cycleClass q (nativeSection Z) =
        R.hodgeSection (H.cycleClass p Z)

/-- Exact equivalence for EACH target Hodge class: a real algebraic
cycle on X exists IFF the geometrically marked PRODUCT-SECTION
cohomology class is algebraic on Y. The cycle constructor is
explicit in both directions, via native external product and
native proper Gysin pushforward. -/
theorem representable_on_X_iff_marked_product_section_representable
    (R : NativeHodgeRetract Y X D H q p)
    (S : NativeProductSection R)
    (alpha : RationalSingularCohomology H.analytification (2 * p)) :
    (∃ Z : codimensionCycles X.X p, H.cycleClass p Z = alpha) ↔
    (∃ W : codimensionCycles Y.X q,
      D.cycleClass q W = R.hodgeSection alpha) := by
  constructor
  · rintro ⟨Z, hZ⟩
    refine ⟨S.nativeSection Z, ?_⟩
    rw [S.cycleClass_section_natural, hZ]
  · intro hSource
    exact construct_target_cycle_from_source_hodge_lift R alpha hSource

/-- The full quantified target Hodge conjecture at weight p is
equivalent to the algebraicity of ONLY its geometrically marked
Kunneth-section subspace in Y, not the full Hodge theory of Y.

This is a non-circular exact product reduction, but not a proof
that the marked section is algebraic. -/
theorem every_Hodge_on_X_iff_every_marked_product_section_algebraic
    (R : NativeHodgeRetract Y X D H q p)
    (S : NativeProductSection R) :
    (∀ alpha : RationalSingularCohomology H.analytification (2 * p),
      alpha ∈ rationalHodgeSubspace (H.hodgeBigrading p) →
        ∃ Z : codimensionCycles X.X p,
          H.cycleClass p Z = alpha) ↔
    (∀ alpha : RationalSingularCohomology H.analytification (2 * p),
      alpha ∈ rationalHodgeSubspace (H.hodgeBigrading p) →
        ∃ W : codimensionCycles Y.X q,
          D.cycleClass q W = R.hodgeSection alpha) := by
  constructor
  · intro hx alpha hAlpha
    exact (representable_on_X_iff_marked_product_section_representable
      R S alpha).mp (hx alpha hAlpha)
  · intro hy alpha hAlpha
    exact (representable_on_X_iff_marked_product_section_representable
      R S alpha).mpr (hy alpha hAlpha)

#check representable_on_X_iff_marked_product_section_representable
#check every_Hodge_on_X_iff_every_marked_product_section_algebraic
#print axioms representable_on_X_iff_marked_product_section_representable
#print axioms every_Hodge_on_X_iff_every_marked_product_section_algebraic

end GSTUniversalSelfProductHodgeEquivalence
