import GSTClassicalHodgeAmbientBettiSelfProduct

/-!
# GST CLASSICAL HODGE — BETTI CUP/GYSIN PRIMITIVES

This module is deliberately below every Hodge-conjecture and correspondence
statement.  It isolates the ordinary rational Betti operations which are not
currently supplied by the pinned Mathlib singular-cohomology API:

* graded cup product on H*(X_an x X_an,Q);
* integration/Gysin along the two projections X_an x X_an -> X_an;
* functoriality of those operations under factor swap.

No algebraic cycle, no Hodge class, no correspondence kernel, and no
surjectivity statement occurs here.  These are standard algebraic-topology
primitives only.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

namespace GSTClassicalHodgeBettiCupGysinPrimitives

open GSTProjectiveOverC
open GSTGeometricRealizationStage2F
open GSTClassicalHodgeAmbientBettiSelfProduct

variable {V : SmoothProjectiveComplexScheme}
variable (A : AnalytificationData V)

abbrev XCoh (n : Nat) := RationalSingularCohomology A n
abbrev X2Coh (n : Nat) := ProductCohomology A n

/-- Graded rational cup product on the actual singular cohomology of the
analytic self-product.  The only law stored here is the ordinary naturality
of cup product under the genuine factor-swap map. -/
structure RationalProductCupTheory where
  cup : ∀ a b : Nat,
    X2Coh A a →ₗ[ℚ] (X2Coh A b →ₗ[ℚ] X2Coh A (a + b))

  swap_natural :
    ∀ a b (u : X2Coh A a) (v : X2Coh A b),
      swapCohomologyPullback A (a + b) (cup a b u v) =
        cup a b
          (swapCohomologyPullback A a u)
          (swapCohomologyPullback A b v)

namespace RationalProductCupTheory

/-- Cup on the left by a fixed cohomology class. -/
noncomputable def cupLeft
    (C : RationalProductCupTheory A)
    {a b : Nat}
    (u : X2Coh A a) :
    X2Coh A b →ₗ[ℚ] X2Coh A (a + b) :=
  C.cup a b u

/-- Factor swap commutes with the left-cup operation. -/
theorem swap_cupLeft
    (C : RationalProductCupTheory A)
    {a b : Nat}
    (u : X2Coh A a)
    (v : X2Coh A b) :
    swapCohomologyPullback A (a + b) (cupLeft A C u v) =
      cupLeft A C (swapCohomologyPullback A a u)
        (swapCohomologyPullback A b v) :=
  C.swap_natural a b u v

end RationalProductCupTheory

/-- Poincare/Gysin integration along the two projections of the analytic
self-product of a complex d-fold.

The shift by `2*d` is the real fiber dimension.  The two swap laws express
that factor exchange conjugates p2_! to p1_! and vice versa. -/
structure RationalProjectionGysinTheory (d : Nat) where
  sndGysin : ∀ n : Nat,
    X2Coh A (2 * d + n) →ₗ[ℚ] XCoh A n

  fstGysin : ∀ n : Nat,
    X2Coh A (2 * d + n) →ₗ[ℚ] XCoh A n

  snd_swap :
    ∀ n (z : X2Coh A (2 * d + n)),
      sndGysin n (swapCohomologyPullback A (2 * d + n) z) =
        fstGysin n z

  fst_swap :
    ∀ n (z : X2Coh A (2 * d + n)),
      fstGysin n (swapCohomologyPullback A (2 * d + n) z) =
        sndGysin n z

/-- Exact low-level input needed by ambient algebraic correspondences: ordinary
cup product plus ordinary projection Gysin theory. -/
structure RationalBettiIntersectionPrimitives (d : Nat) where
  cupTheory : RationalProductCupTheory A
  gysinTheory : RationalProjectionGysinTheory A d

namespace RationalBettiIntersectionPrimitives

abbrev cup
    {d : Nat}
    (P : RationalBettiIntersectionPrimitives A d) :=
  P.cupTheory.cup

abbrev sndGysin
    {d : Nat}
    (P : RationalBettiIntersectionPrimitives A d) :=
  P.gysinTheory.sndGysin

abbrev fstGysin
    {d : Nat}
    (P : RationalBettiIntersectionPrimitives A d) :=
  P.gysinTheory.fstGysin

/-- The swap identities are consequences of the two independent low-level
standard theories, not correspondence axioms. -/
theorem swap_cup
    {d : Nat}
    (P : RationalBettiIntersectionPrimitives A d)
    (a b : Nat) (u : X2Coh A a) (v : X2Coh A b) :
    swapCohomologyPullback A (a + b) (cup A P a b u v) =
      cup A P a b
        (swapCohomologyPullback A a u)
        (swapCohomologyPullback A b v) :=
  P.cupTheory.swap_natural a b u v

/-- Swap converts second projection integration to first projection
integration. -/
theorem sndGysin_swap
    {d : Nat}
    (P : RationalBettiIntersectionPrimitives A d)
    (n : Nat) (z : X2Coh A (2 * d + n)) :
    sndGysin A P n (swapCohomologyPullback A (2 * d + n) z) =
      fstGysin A P n z :=
  P.gysinTheory.snd_swap n z

/-- Symmetric projection-swap law. -/
theorem fstGysin_swap
    {d : Nat}
    (P : RationalBettiIntersectionPrimitives A d)
    (n : Nat) (z : X2Coh A (2 * d + n)) :
    fstGysin A P n (swapCohomologyPullback A (2 * d + n) z) =
      sndGysin A P n z :=
  P.gysinTheory.fst_swap n z

end RationalBettiIntersectionPrimitives

#check RationalProductCupTheory
#check RationalProjectionGysinTheory
#check RationalBettiIntersectionPrimitives
#check RationalBettiIntersectionPrimitives.swap_cup
#check RationalBettiIntersectionPrimitives.sndGysin_swap

#print axioms RationalBettiIntersectionPrimitives.swap_cup
#print axioms RationalBettiIntersectionPrimitives.sndGysin_swap

end GSTClassicalHodgeBettiCupGysinPrimitives
