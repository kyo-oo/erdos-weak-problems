import GSTGeometricRealizationStage2G

/-!
# GST original-X primitive middle classes and hyperplane-relative geometry

This file attacks the exact geometric mechanism of Gate 3:
  how does an arbitrary rational primitive middle-Hodge class on X
  behave under a genuine smooth hyperplane section i:Y -> X?

For every smooth projective X of even complex dimension 2p and
every smooth ample hyperplane section Y, the ordinary geometric maps
in rational singular Betti cohomology satisfy

  i_* i^* = L      (self-intersection formula),
  i_* injective    (Gysin form of weak Lefschetz),
  im(H^(2p)(X,Y) -> H^(2p)(X)) = ker(i^*).

It follows, for EVERY primitive middle class alpha, that:
  i^* alpha = 0,
  alpha has a relative Betti lift in H^(2p)(X,Y).

Hence an arbitrary nonzero primitive class CANNOT be recovered
from its restriction to one hyperplane: the restriction is zero.
The relative source is a genuine universal cohomological carrier,
but a relative Betti lift is NOT an algebraic codimension-p cycle.
The remaining mathematical task is to produce such an algebraic
cycle without assuming that primitive algebraicity in its input.

The structure below tracks standard topological hyperplane/relative
comparison theorems as independent geometry inputs. It supplies
no target-surjectivity field and chooses no Chow cycle for alpha.
-/

set_option maxHeartbeats 12000000

noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G

namespace GSTUniversalPrimitiveHyperplaneRelative

variable {X Y : SmoothProjectiveComplexScheme}
variable {HX : HodgeBigradedBettiData X}
variable {HY : HodgeBigradedBettiData Y}
variable {W : Type*} [AddCommGroup W] [Module ℚ W]

/-- Rational singular-Betti data for a *genuine smooth hyperplane*
Y⊂X with dim_C X=2p. The relative space W is intended to be
H^(2p)(X_an,Y_an;Q), or H_c^(2p)(X_an\Y_an;Q).

All fields are standard topological identities about an actual
hyperplane, not the Hodge conjecture or its desired cycle witness. -/
structure SmoothMiddleHyperplaneBetti
    (p : ℕ)
    (X Y : SmoothProjectiveComplexScheme)
    (HX : HodgeBigradedBettiData X)
    (HY : HodgeBigradedBettiData Y)
    (W : Type*) [AddCommGroup W] [Module ℚ W] where
  middleRestriction :
    RationalSingularCohomology HX.analytification (2*p) →ₗ[ℚ]
      RationalSingularCohomology HY.analytification (2*p)
  middleGysin :
    RationalSingularCohomology HY.analytification (2*p) →ₗ[ℚ]
      RationalSingularCohomology HX.analytification (2*p+2)
  ampleCup :
    RationalSingularCohomology HX.analytification (2*p) →ₗ[ℚ]
      RationalSingularCohomology HX.analytification (2*p+2)
  gysin_injective : Function.Injective middleGysin
  self_intersection :
    ∀ a : RationalSingularCohomology HX.analytification (2*p),
      middleGysin (middleRestriction a) = ampleCup a
  relativeToX :
    W →ₗ[ℚ]
      RationalSingularCohomology HX.analytification (2*p)
  relative_exact :
    ∀ a : RationalSingularCohomology HX.analytification (2*p),
      middleRestriction a = 0 ↔ a ∈ LinearMap.range relativeToX

/-- For every even-dimensional original X, the geometric middle
primitive condition is EXACTLY vanishing on a smooth hyperplane. -/
theorem SmoothMiddleHyperplaneBetti.primitive_iff_restriction_zero
    {p : ℕ}
    (G : SmoothMiddleHyperplaneBetti p X Y HX HY W)
    (alpha : RationalSingularCohomology HX.analytification (2*p)) :
    G.ampleCup alpha = 0 ↔ G.middleRestriction alpha = 0 := by
  constructor
  · intro hPrimitive
    apply G.gysin_injective
    calc
      G.middleGysin (G.middleRestriction alpha) =
        G.ampleCup alpha := G.self_intersection alpha
      _ = 0 := hPrimitive
      _ = G.middleGysin 0 := (map_zero G.middleGysin).symm
  · intro hRestricted
    calc
      G.ampleCup alpha =
        G.middleGysin (G.middleRestriction alpha) :=
        (G.self_intersection alpha).symm
      _ = G.middleGysin 0 := by rw [hRestricted]
      _ = 0 := map_zero G.middleGysin

/-- Every rational primitive middle class on every original even
dimensional X is the image of an actual relative BETTI class for
the pair (X,Y). No algebraic source has been selected here. -/
theorem SmoothMiddleHyperplaneBetti.primitive_has_relative_betti_lift
    {p : ℕ}
    (G : SmoothMiddleHyperplaneBetti p X Y HX HY W)
    (alpha : RationalSingularCohomology HX.analytification (2*p))
    (hPrimitive : G.ampleCup alpha = 0) :
    ∃ w : W, G.relativeToX w = alpha := by
  have hr : G.middleRestriction alpha = 0 :=
    (G.primitive_iff_restriction_zero alpha).mp hPrimitive
  exact (G.relative_exact alpha).mp hr

/-- The Hodge-rational subspace is preserved as a PROPERTY of alpha.
The relative lift is topological and its Hodge/algebraic realization
is precisely the next genuinely geometric part of Gate 3. -/
theorem SmoothMiddleHyperplaneBetti.primitive_hodge_relative_lift
    {p : ℕ}
    (G : SmoothMiddleHyperplaneBetti p X Y HX HY W)
    (alpha : RationalSingularCohomology HX.analytification (2*p))
    (hHodge : alpha ∈ rationalHodgeSubspace (HX.hodgeBigrading p))
    (hPrimitive : G.ampleCup alpha = 0) :
    (∃ w : W, G.relativeToX w = alpha) ∧
      alpha ∈ rationalHodgeSubspace (HX.hodgeBigrading p) := by
  exact ⟨G.primitive_has_relative_betti_lift alpha hPrimitive, hHodge⟩

/-- CRITICAL source-filtering theorem: restriction to a single
smooth hyperplane loses EVERY middle-primitive direction.
Any linear procedure using only that restricted class returns
zero, so it cannot reconstruct a nonzero primitive Hodge class. -/
theorem SmoothMiddleHyperplaneBetti.no_recovery_from_restriction
    {p : ℕ}
    (G : SmoothMiddleHyperplaneBetti p X Y HX HY W)
    (alpha : RationalSingularCohomology HX.analytification (2*p))
    (hPrimitive : G.ampleCup alpha = 0)
    (hNonzero : alpha ≠ 0)
    (recover :
      RationalSingularCohomology HY.analytification (2*p) →ₗ[ℚ]
        RationalSingularCohomology HX.analytification (2*p)) :
    recover (G.middleRestriction alpha) ≠ alpha := by
  have hr : G.middleRestriction alpha = 0 :=
    (G.primitive_iff_restriction_zero alpha).mp hPrimitive
  intro hReconstruct
  have hz : (0 :
      RationalSingularCohomology HX.analytification (2*p)) = alpha := by
    calc
      0 = recover 0 := (map_zero recover).symm
      _ = recover (G.middleRestriction alpha) := by rw [hr]
      _ = alpha := hReconstruct
  exact hNonzero hz.symm

/-! ## The first native *algebraic* source mechanism: matched boundary cycles

The preceding theorems located primitive middle cohomology in
relative Betti classes. Here we produce actual native rational
codimension-p algebraic cycles on the ORIGINAL X, not merely
relative cohomology classes.

Choose two independently constructed algebraic codimension-p cycles
Z0,Z1 whose canonical Betti restrictions to Y agree. Their signed
difference Z0-Z1 is automatically primitive. It is nonzero whenever
their original canonical Betti classes differ.

This gives a mathematically exact and computable construction
criterion based on genuine subvarieties with matching boundary.
The remaining original Hodge objective is to derive enough such
pairs on arbitrary X to represent every rational primitive Hodge
target, without assuming their existence or full rank as an input.
-/

/-- True native rational codimension-p algebraic source on original X. -/
def signedNativeBoundaryDifference
    (p : ℕ)
    (Z0 Z1 : codimensionCycles X.X p) :
    codimensionCycles X.X p := Z0 - Z1

/-- Two genuine codimension-p algebraic cycles with identical
hyperplane Betti boundary measurements yield an ACTUAL primitive
native rational cycle on the original X in all even dimensions. -/
theorem SmoothMiddleHyperplaneBetti.signed_boundary_difference_primitive
    {p : ℕ}
    (G : SmoothMiddleHyperplaneBetti p X Y HX HY W)
    (Z0 Z1 : codimensionCycles X.X p)
    (hEqualBoundary :
      G.middleRestriction (HX.cycleClass p Z0) =
        G.middleRestriction (HX.cycleClass p Z1)) :
    G.ampleCup
      (HX.cycleClass p (signedNativeBoundaryDifference p Z0 Z1)) = 0 := by
  apply (G.primitive_iff_restriction_zero _).mpr
  change G.middleRestriction (HX.cycleClass p (Z0 - Z1)) = 0
  rw [map_sub, map_sub]
  exact sub_eq_zero.mpr hEqualBoundary

/-- If the original cycle classes are distinct, the signed
boundary-matched construction generates a NONZERO primitive
algebraic middle class on the ORIGINAL X. -/
theorem SmoothMiddleHyperplaneBetti.signed_boundary_difference_nonzero
    {p : ℕ}
    (G : SmoothMiddleHyperplaneBetti p X Y HX HY W)
    (Z0 Z1 : codimensionCycles X.X p)
    (hEqualBoundary :
      G.middleRestriction (HX.cycleClass p Z0) =
        G.middleRestriction (HX.cycleClass p Z1))
    (hDistinct :
      HX.cycleClass p Z0 ≠ HX.cycleClass p Z1) :
    G.ampleCup
      (HX.cycleClass p (signedNativeBoundaryDifference p Z0 Z1)) = 0 ∧
    HX.cycleClass p (signedNativeBoundaryDifference p Z0 Z1) ≠ 0 := by
  constructor
  · exact G.signed_boundary_difference_primitive Z0 Z1 hEqualBoundary
  · intro hZero
    apply hDistinct
    apply sub_eq_zero.mp
    have hDifference :
      HX.cycleClass p (Z0 - Z1) = 0 := hZero
    simpa only [map_sub] using hDifference

#check signedNativeBoundaryDifference
#check SmoothMiddleHyperplaneBetti.signed_boundary_difference_primitive
#check SmoothMiddleHyperplaneBetti.signed_boundary_difference_nonzero

/-! ## Bring the relative-middle mechanism back to EVERY ambient dimension

Let dim_C(X)=n and 2p<=n, and choose r=n-2p general
hyperplane sections. Their smooth complete intersection
j:Y^(2p) -> X^n has the weak-Lefschetz-injective rational
restriction j*:H^(2p)(X,Q)->H^(2p)(Y,Q).

The repeated Gysin identity j_*j*=h^r and projection formula
j_* (h_Y cup j*alpha)=h_X^(r+1) cup alpha
prove that every primitive alpha on original X restricts to
a primitive MIDDLE class on Y. Injectivity of the higher Gysin
is the dual weak Lefschetz theorem in the upper degree.

This applies to every ambient dimension n and every
codimension p with 2p<=n, NOT only fourfolds. It brings
the arbitrary-X primitive target into the relative Betti
setting; producing a cycle on original X from the relative
source is a distinct algebraic transfer obligation.
-/

/-- Genuine complete-intersection restriction and Gysin
geometry for an arbitrary original n-fold X, codimension p,
with r=n-2p successive hyperplane sections. -/
structure SmoothCompleteIntersectionMiddleBridge
    (p r : ℕ)
    (X Y : SmoothProjectiveComplexScheme)
    (HX : HodgeBigradedBettiData X)
    (HY : HodgeBigradedBettiData Y) where
  restriction :
    RationalSingularCohomology HX.analytification (2*p) →ₗ[ℚ]
      RationalSingularCohomology HY.analytification (2*p)
  restriction_injective : Function.Injective restriction
  middlePush :
    RationalSingularCohomology HY.analytification (2*p) →ₗ[ℚ]
      RationalSingularCohomology HX.analytification (2*p+2*r)
  higherPush :
    RationalSingularCohomology HY.analytification (2*p+2) →ₗ[ℚ]
      RationalSingularCohomology HX.analytification (2*p+2*r+2)
  higherPush_injective : Function.Injective higherPush
  middleLefschetzCup :
    RationalSingularCohomology HY.analytification (2*p) →ₗ[ℚ]
      RationalSingularCohomology HY.analytification (2*p+2)
  originalLefschetzPower :
    RationalSingularCohomology HX.analytification (2*p) →ₗ[ℚ]
      RationalSingularCohomology HX.analytification (2*p+2*r)
  originalNextCup :
    RationalSingularCohomology HX.analytification (2*p+2*r) →ₗ[ℚ]
      RationalSingularCohomology HX.analytification (2*p+2*r+2)
  originalPrimitiveTest :
    RationalSingularCohomology HX.analytification (2*p) →ₗ[ℚ]
      RationalSingularCohomology HX.analytification (2*p+2*r+2)
  complete_intersection_self_intersection :
    ∀ alpha : RationalSingularCohomology HX.analytification (2*p),
      middlePush (restriction alpha) = originalLefschetzPower alpha
  cup_power_compatibility :
    ∀ alpha : RationalSingularCohomology HX.analytification (2*p),
      originalNextCup (originalLefschetzPower alpha) =
        originalPrimitiveTest alpha
  gysin_projection :
    ∀ alpha : RationalSingularCohomology HX.analytification (2*p),
      higherPush (middleLefschetzCup (restriction alpha)) =
        originalNextCup (middlePush (restriction alpha))

/-- ALL original smooth projective n-folds: any primitive
degree-2p rational Betti class restricts to a primitive MIDDLE
class on the chosen smooth 2p-dimensional hyperplane cut. -/
theorem SmoothCompleteIntersectionMiddleBridge.restrict_primitive_to_middle
    {p r : ℕ}
    (B : SmoothCompleteIntersectionMiddleBridge p r X Y HX HY)
    (alpha : RationalSingularCohomology HX.analytification (2*p))
    (hPrimitive : B.originalPrimitiveTest alpha = 0) :
    B.middleLefschetzCup (B.restriction alpha) = 0 := by
  apply B.higherPush_injective
  calc
    B.higherPush (B.middleLefschetzCup (B.restriction alpha)) =
      B.originalNextCup (B.middlePush (B.restriction alpha)) :=
        B.gysin_projection alpha
    _ = B.originalNextCup (B.originalLefschetzPower alpha) := by
          rw [B.complete_intersection_self_intersection alpha]
    _ = B.originalPrimitiveTest alpha := B.cup_power_compatibility alpha
    _ = 0 := hPrimitive
    _ = B.higherPush 0 := (map_zero B.higherPush).symm

/-- A nonzero primitive rational Betti class on an arbitrary
original n-fold remains NONZERO after cutting to middle degree:
the relative target is faithfully preserved by weak Lefschetz. -/
theorem SmoothCompleteIntersectionMiddleBridge.restrict_nonzero
    {p r : ℕ}
    (B : SmoothCompleteIntersectionMiddleBridge p r X Y HX HY)
    (alpha : RationalSingularCohomology HX.analytification (2*p))
    (hNonzero : alpha ≠ 0) :
    B.restriction alpha ≠ 0 := by
  intro hzero
  apply hNonzero
  apply B.restriction_injective
  simpa only [map_zero] using hzero

/-- Every primitive rational Hodge class on arbitrary X
therefore has a genuine RELATIVE rational Betti lift after
smoothly cutting to the even-dimensional middle. The relative
source is not silently assumed to be an algebraic cycle. -/
theorem SmoothCompleteIntersectionMiddleBridge.primitive_has_middle_relative_lift
    {p r : ℕ} {Z : SmoothProjectiveComplexScheme}
    {HZ : HodgeBigradedBettiData Z}
    (B : SmoothCompleteIntersectionMiddleBridge p r X Y HX HY)
    (R : SmoothMiddleHyperplaneBetti p Y Z HY HZ W)
    (hSameCup : ∀ beta :
      RationalSingularCohomology HY.analytification (2*p),
      R.ampleCup beta = B.middleLefschetzCup beta)
    (alpha : RationalSingularCohomology HX.analytification (2*p))
    (hPrimitive : B.originalPrimitiveTest alpha = 0) :
    ∃ w : W, R.relativeToX w = B.restriction alpha := by
  have hMiddle : B.middleLefschetzCup (B.restriction alpha) = 0 :=
    B.restrict_primitive_to_middle alpha hPrimitive
  have hRelativePrimitive : R.ampleCup (B.restriction alpha) = 0 := by
    rw [hSameCup]
    exact hMiddle
  exact R.primitive_has_relative_betti_lift
    (B.restriction alpha) hRelativePrimitive

#check SmoothCompleteIntersectionMiddleBridge.restrict_primitive_to_middle
#check SmoothCompleteIntersectionMiddleBridge.restrict_nonzero
#check SmoothCompleteIntersectionMiddleBridge.primitive_has_middle_relative_lift

#check SmoothMiddleHyperplaneBetti.primitive_iff_restriction_zero
#check SmoothMiddleHyperplaneBetti.primitive_has_relative_betti_lift
#check SmoothMiddleHyperplaneBetti.primitive_hodge_relative_lift
#check SmoothMiddleHyperplaneBetti.no_recovery_from_restriction
#print axioms SmoothMiddleHyperplaneBetti.no_recovery_from_restriction

end GSTUniversalPrimitiveHyperplaneRelative
