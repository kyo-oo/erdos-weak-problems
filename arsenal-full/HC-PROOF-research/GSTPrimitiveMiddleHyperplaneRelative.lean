import Mathlib

/-!
# Mathbox: primitive middle Hodge classes hide from hyperplane sections

Original all-X goal: for every primitive rational Hodge (p,p) class,
construct a CLOSED INTEGRAL CURRENT in one fixed ample-shifted homology
class with zero Kähler calibration defect.

A direct strategy would restrict a primitive class on a smooth 2p-fold
X to a smooth hyperplane Y of dimension 2p-1, realize its restriction
using known lower-dimensional algebraic geometry, and push the cycle
back. THIS STRATEGY IS IMPOSSIBLE AS STATED: the primitive middle class
restricts to zero. The phenomenon is proved below from only:
  * weak Lefschetz, i* : H^{2p-2}(X) -> H^{2p-2}(Y) surjective;
  * Poincaré duality on Y;
  * the push-pull intersection identity;
  * primitivity h cup alpha = 0.

The same derivation shows every such primitive alpha is represented
by a RELATIVE cohomology class in H^{2p}(X,Y), through exactness
of the pair's long exact sequence.

The relative lift is not an integral calibrated cycle. No
Hodge-surjectivity, ghost-killing axiom, or analytic-current
existence result is inserted into the hypotheses.
-/

set_option maxHeartbeats 10000000

noncomputable section

namespace GSTPrimitiveMiddleHyperplaneRelative

variable {XM XL XH YM YL Relative : Type*}
variable [AddCommGroup XM] [Module ℚ XM]
variable [AddCommGroup XL] [Module ℚ XL]
variable [AddCommGroup XH] [Module ℚ XH]
variable [AddCommGroup YM] [Module ℚ YM]
variable [AddCommGroup YL] [Module ℚ YL]
variable [AddCommGroup Relative] [Module ℚ Relative]

/-- Cohomological hyperplane data for a 2p-dimensional smooth projective X,
a smooth hyperplane Y and middle degree 2p. Every axiom in this structure
is a standard geometric identity, not Hodge algebraicity. -/
structure HyperplanePoincareData
    (XM XL XH YM YL : Type*)
    [AddCommGroup XM] [Module ℚ XM]
    [AddCommGroup XL] [Module ℚ XL]
    [AddCommGroup XH] [Module ℚ XH]
    [AddCommGroup YM] [Module ℚ YM]
    [AddCommGroup YL] [Module ℚ YL] where
  pullMid : XM →ₗ[ℚ] YM
  pullLow : XL →ₗ[ℚ] YL
  lefschetzLow : XL →ₗ[ℚ] XM
  lefschetzMid : XM →ₗ[ℚ] XH
  pairX : XM →ₗ[ℚ] XM →ₗ[ℚ] ℚ
  pairHigher : XH →ₗ[ℚ] XL →ₗ[ℚ] ℚ
  pairY : YM →ₗ[ℚ] YL →ₗ[ℚ] ℚ
  weakLefschetzLow : Function.Surjective pullLow
  poincareY : ∀ y : YM, (∀ v : YL, pairY y v = 0) → y = 0
  projection : ∀ (a : XM) (u : XL),
    pairY (pullMid a) (pullLow u) = pairX a (lefschetzLow u)
  cupAdjoint : ∀ (a : XM) (u : XL),
    pairX a (lefschetzLow u) = pairHigher (lefschetzMid a) u

variable (G : HyperplanePoincareData XM XL XH YM YL)

/-- The key geometric calculation, for all primitive middle classes.
The class alpha can be nonzero on X, but restricts to zero on Y. -/
theorem primitive_middle_restriction_vanishes
    (alpha : XM) (hprimitive : G.lefschetzMid alpha = 0) :
    G.pullMid alpha = 0 := by
  apply G.poincareY
  intro v
  obtain ⟨u, rfl⟩ := G.weakLefschetzLow v
  rw [G.projection, G.cupAdjoint, hprimitive]
  simp

/-- Exactness in relative cohomology moves the primitive class into
H^(2p)(X,Y), where a relative geometric carrier must be studied.
This does NOT assert that the carrier is holomorphic/algebraic. -/
theorem primitive_middle_has_relative_cohomology_lift
    (toAbsolute : Relative →ₗ[ℚ] XM)
    (hexact : LinearMap.range toAbsolute = LinearMap.ker G.pullMid)
    (alpha : XM) (hprimitive : G.lefschetzMid alpha = 0) :
    ∃ gamma : Relative, toAbsolute gamma = alpha := by
  have hker : alpha ∈ LinearMap.ker G.pullMid := by
    change G.pullMid alpha = 0
    exact primitive_middle_restriction_vanishes G alpha hprimitive
  rw [← hexact] at hker
  exact hker

/-- A relative representative of a primitive middle class cannot be
detected from its restriction to smooth hyperplane sections. -/
theorem primitive_middle_hyperplane_detection_zero
    (alpha : XM) (hprimitive : G.lefschetzMid alpha = 0)
    (read : YM →ₗ[ℚ] ℚ) :
    read (G.pullMid alpha) = 0 := by
  rw [primitive_middle_restriction_vanishes G alpha hprimitive]
  simp

#check primitive_middle_restriction_vanishes
#check primitive_middle_has_relative_cohomology_lift
#check primitive_middle_hyperplane_detection_zero
#print axioms primitive_middle_restriction_vanishes
#print axioms primitive_middle_has_relative_cohomology_lift


/-! ## Exact primitive-kernel = hyperplane-invisible-kernel upgrade

The original theorem established primitive ⇒ invisible to Y. The
geometric Gysin identity i_* i^* alpha = h cup alpha makes the converse
equally exact. This strengthens the relative-cohomology formulation
to a *full equality of rational subspaces*, not a mere existence
claim. The Gysin relation is a standard projection-formula input;
its proof is NOT obtained by assuming any Hodge class algebraic.
-/

/-- Primitive middle classes are EXACTLY those whose restriction
to the smooth hyperplane is zero. -/
theorem primitive_iff_hyperplane_invisible
    (gysin : YM →ₗ[ℚ] XH)
    (hGysin : ∀ a : XM,
      gysin (G.pullMid a) = G.lefschetzMid a)
    (alpha : XM) :
    G.lefschetzMid alpha = 0 ↔ G.pullMid alpha = 0 := by
  constructor
  · exact primitive_middle_restriction_vanishes G alpha
  · intro hz
    rw [← hGysin alpha, hz]
    exact gysin.map_zero

/-- Under the exact sequence of the pair (X,Y), the ENTIRE image of
relative middle cohomology equals the middle primitive Lefschetz
kernel. This is stronger than selecting a relative carrier one by one. -/
theorem relative_middle_image_eq_primitive_kernel
    (gysin : YM →ₗ[ℚ] XH)
    (hGysin : ∀ a : XM,
      gysin (G.pullMid a) = G.lefschetzMid a)
    (toAbsolute : Relative →ₗ[ℚ] XM)
    (hexact : LinearMap.range toAbsolute = LinearMap.ker G.pullMid) :
    LinearMap.range toAbsolute = LinearMap.ker G.lefschetzMid := by
  rw [hexact]
  ext a
  change G.pullMid a = 0 ↔ G.lefschetzMid a = 0
  exact (primitive_iff_hyperplane_invisible G gysin hGysin a).symm

#check primitive_iff_hyperplane_invisible
#check relative_middle_image_eq_primitive_kernel
#print axioms relative_middle_image_eq_primitive_kernel


/-! ## Elementwise exact relative/primitive classification

The subspace equality gives an explicit and fully reversible
classification of primitive middle classes by relative lifts.
This upgrades a one-directional lifting result to an iff; the
relative cohomology witness is NOT automatically an algebraic cycle. -/

/-- A rational middle class is primitive exactly when it lifts
from the cohomology of the pair (X,Y), under the standard Gysin and
long-exact-sequence conditions. -/
theorem primitive_iff_has_relative_middle_lift
    (gysin : YM →ₗ[ℚ] XH)
    (hGysin : ∀ a : XM,
      gysin (G.pullMid a) = G.lefschetzMid a)
    (toAbsolute : Relative →ₗ[ℚ] XM)
    (hexact : LinearMap.range toAbsolute = LinearMap.ker G.pullMid)
    (alpha : XM) :
    G.lefschetzMid alpha = 0 ↔
      ∃ gamma : Relative, toAbsolute gamma = alpha := by
  have himage :=
    relative_middle_image_eq_primitive_kernel G gysin hGysin
      toAbsolute hexact
  constructor
  · intro hprimitive
    have hmem : alpha ∈ LinearMap.ker G.lefschetzMid := by
      change G.lefschetzMid alpha = 0
      exact hprimitive
    rw [← himage] at hmem
    exact hmem
  · rintro ⟨gamma, hgamma⟩
    have hmem : alpha ∈ LinearMap.range toAbsolute := ⟨gamma, hgamma⟩
    rw [himage] at hmem
    change G.lefschetzMid alpha = 0 at hmem
    exact hmem

#check primitive_iff_has_relative_middle_lift
#print axioms primitive_iff_has_relative_middle_lift


/-! ## No linear resurrection from a vanishing primitive restriction

The geometry has an exact primitive=relative-kernel identification.
A proposed linear reconstruction from a hyperplane's own middle
cohomology must FAIL on each nonzero primitive middle class: that
class restricts to zero, and any linear recovery maps zero to zero.
This proves an obstruction to a specific universal construction,
without ruling out independent relative algebraic geometry.
-/

/-- No rational-linear read/recover operation on hyperplane middle
cohomology can reproduce a nonzero primitive class on X. -/
theorem no_linear_hyperplane_recovery_of_nonzero_primitive
    (alpha : XM)
    (hprimitive : G.lefschetzMid alpha = 0)
    (hnonzero : alpha ≠ 0)
    (recover : YM →ₗ[ℚ] XM) :
    recover (G.pullMid alpha) ≠ alpha := by
  rw [primitive_middle_restriction_vanishes G alpha hprimitive,
      map_zero]
  exact Ne.symm hnonzero

#check no_linear_hyperplane_recovery_of_nonzero_primitive
#print axioms no_linear_hyperplane_recovery_of_nonzero_primitive

end GSTPrimitiveMiddleHyperplaneRelative
