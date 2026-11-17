import GSTClassicalHodgePointNormalForm
import GSTClassicalHodgePrincipalCutSuccessorOperator
import GSTClassicalHodgeLimitlessCosmicMatrixUnits
import GSTClassicalHodgeLimitlessProjectiveLefschetzTower
import GSTClassicalHodgeTransferSeedUniverse
import GSTClassicalHodgePointKernelOperatorLift

/-!
# GST CLASSICAL HODGE — NATIVE CYCLE / LIMITLESS COSMIC SHADOW

Actual projective algebraic cycles and the limitless GST Hodge universe should
not remain disjoint languages.  Every native codimension-p cycle on a smooth
projective carrier has a finite point presentation.  Summing its rational
point coefficients gives a canonical mass, and that mass can be placed at the
unbounded cosmic Hodge weight `p`.

This produces an unconditional rational-linear shadow map

  codimension-p native cycles -> Nat ->₀ Q

which sends every unit point cycle to the canonical limitless basis seed at
weight `p`.  No Betti cycle-class map and no Hodge-surjectivity statement is
used.  The construction therefore gives a direct artery from genuine
projective cycles into the limitless GST address universe.
-/

set_option maxHeartbeats 50000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry
open scoped BigOperators

namespace GSTClassicalHodgeNativeCycleCosmicShadow

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTNativeCodimensionCyclePresentation
open GSTCompactNativeCyclePresentation
open GSTClassicalHodgePointNormalForm
open GSTClassicalHodgePrincipalCutSuccessorOperator
open GSTClassicalHodgeLimitlessCosmicMatrixUnits
open GSTClassicalHodgeLimitlessProjectiveLefschetzTower
open GSTClassicalHodgePointKernelOperatorLift
open GSTClassicalHodgeCrossWeightNativePropagation

/-- Rational augmentation of one finite point presentation. -/
noncomputable def presentationMass
    {X : Scheme} {p : Nat} :
    FiniteCodimensionPresentation X p →ₗ[ℚ] ℚ where
  toFun φ := φ.sum fun _ q => q
  map_add' := by
    intro φ ψ
    classical
    simp [Finsupp.sum_add_index']
  map_smul' := by
    intro q φ
    classical
    rw [Finsupp.sum_smul_index' (fun _ => rfl), smul_eq_mul,
      Finsupp.sum, Finsupp.sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by simp

@[simp]
theorem presentationMass_single
    {X : Scheme} {p : Nat}
    (x : CodimensionPoint X p) (q : ℚ) :
    presentationMass (Finsupp.single x q) = q := by
  classical
  simp [presentationMass]

/-- Total rational mass of an actual native cycle, computed through its exact
finite projective point normal form. -/
noncomputable def nativeCycleMass
    (V : SmoothProjectiveComplexScheme)
    (p : Nat) : codimensionCycles V.X p →ₗ[ℚ] ℚ := by
  letI : CompactSpace V.X := smoothProjectiveCompactSpace V
  exact presentationMass.comp (presentationOfNativeCycleLinear V.X p)

/-- The mass of a unit point cycle is one. -/
@[simp]
theorem nativeCycleMass_point
    (V : SmoothProjectiveComplexScheme)
    (p : Nat) (x : CodimensionPoint V.X p) :
    nativeCycleMass V p (codimensionPointCycle V.X p x) = 1 := by
  letI : CompactSpace V.X := smoothProjectiveCompactSpace V
  simp [nativeCycleMass, presentationMass, presentationOfNativeCycle_point]

/-- Canonical limitless rational cosmic shadow of a native codimension-p
cycle. -/
noncomputable def nativeCycleCosmicShadow
    (V : SmoothProjectiveComplexScheme)
    (p : Nat) :
    codimensionCycles V.X p →ₗ[ℚ] RationalPureCosmos where
  toFun Z := Finsupp.single p (nativeCycleMass V p Z)
  map_add' := by intro Z W; ext q; simp
  map_smul' := by intro a Z; ext q; simp

/-- Every unit codimension-p point cycle maps to the exact limitless basis
seed at weight p. -/
@[simp]
theorem nativeCycleCosmicShadow_point
    (V : SmoothProjectiveComplexScheme)
    (p : Nat) (x : CodimensionPoint V.X p) :
    nativeCycleCosmicShadow V p (codimensionPointCycle V.X p x) =
      rationalCosmicBasis p := by
  ext q
  simp [nativeCycleCosmicShadow, rationalCosmicBasis]

/-- Any finite native cycle is therefore a scalar multiple of the canonical
weight-p transfer direction after forgetting its internal projective support. -/
theorem nativeCycleCosmicShadow_eq_mass_smul
    (V : SmoothProjectiveComplexScheme)
    (p : Nat) (Z : codimensionCycles V.X p) :
    nativeCycleCosmicShadow V p Z =
      nativeCycleMass V p Z • rationalCosmicBasis p := by
  ext q
  simp [nativeCycleCosmicShadow, rationalCosmicBasis]

/-- Matrix-unit read/write on a native cycle shadow moves the entire native
mass from weight p to any target weight q. -/
theorem cosmicMatrixUnit_nativeCycleShadow
    (V : SmoothProjectiveComplexScheme)
    (p q : Nat) (Z : codimensionCycles V.X p) :
    rationalCosmicMatrixUnit p q (nativeCycleCosmicShadow V p Z) =
      nativeCycleMass V p Z • rationalCosmicBasis q := by
  rw [nativeCycleCosmicShadow_eq_mass_smul]
  ext n
  simp [rationalCosmicMatrixUnit, rationalCosmicBasis]

/-- Mass of one exact-stratum successor presentation. -/
noncomputable def successorMass
    (V : SmoothProjectiveComplexScheme)
    (p : Nat) (x : CodimensionPoint V.X p) : ℚ :=
  presentationMass (successorPresentation V p x)

/-- The native mass of one geometry-built successor point cycle is exactly the
finite mass of its successor presentation. -/
theorem nativeCycleMass_successor_point
    (V : SmoothProjectiveComplexScheme)
    (p : Nat) (x : CodimensionPoint V.X p) :
    nativeCycleMass V (p + 1)
      (successorNativeOperator V p (codimensionPointCycle V.X p x)) =
      successorMass V p x := by
  rw [successorNativeOperator_point]
  letI : CompactSpace V.X := smoothProjectiveCompactSpace V
  simp [nativeCycleMass, successorMass, presentationMass,
    presentation_realizeFiniteCodimensionPresentation]

/-- The cosmic shadow of one geometry-built successor cycle is exactly its
finite successor mass on the next limitless weight. -/
theorem successorNativeOperator_cosmicShadow_point
    (V : SmoothProjectiveComplexScheme)
    (p : Nat) (x : CodimensionPoint V.X p) :
    nativeCycleCosmicShadow V (p+1)
      (successorNativeOperator V p (codimensionPointCycle V.X p x)) =
      successorMass V p x • rationalCosmicBasis (p+1) := by
  rw [successorNativeOperator_point]
  rw [nativeCycleCosmicShadow_eq_mass_smul]
  congr 1
  letI : CompactSpace V.X := smoothProjectiveCompactSpace V
  simp [nativeCycleMass, successorMass, presentationMass,
    presentation_realizeFiniteCodimensionPresentation]

/-- **POINT-TO-GLOBAL MASS PROPAGATION.**
If every genuine codimension-p point acquires the same limitless successor
mass, then the entire native principal-cut operator multiplies canonical mass
by that scalar.  The proof uses the exact compact point normal form, so no
arbitrary-cycle hypothesis is required. -/
theorem nativeCycleMass_successor_of_pointMass
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (hpoint : ∀ x : CodimensionPoint V.X p,
      successorMass V p x = limitlessLefschetzScalar p (p + 1))
    (Z : codimensionCycles V.X p) :
    nativeCycleMass V (p + 1) (successorNativeOperator V p Z) =
      limitlessLefschetzScalar p (p + 1) * nativeCycleMass V p Z := by
  have hzero :
      (nativeCycleMass V (p + 1)).comp (successorNativeOperator V p) -
          (limitlessLefschetzScalar p (p + 1)) • nativeCycleMass V p = 0 := by
    apply nativeLinearMap_eq_zero_of_points V p
    intro x
    simp [nativeCycleMass_successor_point, hpoint x, smul_eq_mul]
  have heq :
      (nativeCycleMass V (p + 1)).comp (successorNativeOperator V p) =
          (limitlessLefschetzScalar p (p + 1)) • nativeCycleMass V p :=
    sub_eq_zero.mp hzero
  have hZ := LinearMap.congr_fun heq Z
  simpa [smul_eq_mul] using hZ

/-- Linear form of the principal-cut shadow law. -/
theorem successorNativeOperator_cosmicShadow
    (V : SmoothProjectiveComplexScheme)
    (p : Nat) (Z : codimensionCycles V.X p) :
    nativeCycleCosmicShadow V (p+1) (successorNativeOperator V p Z) =
      nativeCycleMass V (p+1) (successorNativeOperator V p Z) •
        rationalCosmicBasis (p+1) :=
  nativeCycleCosmicShadow_eq_mass_smul V (p+1)
    (successorNativeOperator V p Z)

/-- The projective cut tower therefore has a canonical state at every weight
of the unrestricted rational cosmic Hodge universe. -/
noncomputable def projectiveTowerCosmicShadow
    (V : SmoothProjectiveComplexScheme)
    (p : Nat) : RationalPureCosmos :=
  nativeCycleCosmicShadow V p (projectiveCutTower V p)

/-- Exact support law: the projective tower shadow is concentrated at its true
codimension weight and nowhere else. -/
theorem projectiveTowerCosmicShadow_support
    (V : SmoothProjectiveComplexScheme)
    (p q : Nat) (hpq : q ≠ p) :
    projectiveTowerCosmicShadow V p q = 0 := by
  simp [projectiveTowerCosmicShadow, nativeCycleCosmicShadow, hpq]

/-- Exact coefficient on the tower's own limitless weight. -/
theorem projectiveTowerCosmicShadow_self
    (V : SmoothProjectiveComplexScheme)
    (p : Nat) :
    projectiveTowerCosmicShadow V p p =
      nativeCycleMass V p (projectiveCutTower V p) := by
  simp [projectiveTowerCosmicShadow, nativeCycleCosmicShadow]

/-- The native projective tower and the internal limitless transfer universe
share the same canonical weight basis; only the geometric mass coefficient
remains. -/
theorem projectiveTowerShadow_transfer_direction
    (V : SmoothProjectiveComplexScheme)
    (p : Nat) :
    projectiveTowerCosmicShadow V p =
      nativeCycleMass V p (projectiveCutTower V p) •
        rationalCosmicBasis p := by
  exact nativeCycleCosmicShadow_eq_mass_smul V p (projectiveCutTower V p)

/-- Crown: every genuine native point atom and every recursively constructed
projective tower level lives on the same unbounded Hodge address basis as the
limitless GST transfer universe. -/
theorem native_cycle_limitless_shadow_crown
    (V : SmoothProjectiveComplexScheme) :
    (∀ p (x : CodimensionPoint V.X p),
      nativeCycleCosmicShadow V p (codimensionPointCycle V.X p x) =
        rationalCosmicBasis p)
    ∧ (∀ p,
      projectiveTowerCosmicShadow V p =
        nativeCycleMass V p (projectiveCutTower V p) •
          rationalCosmicBasis p) := by
  exact ⟨nativeCycleCosmicShadow_point V,
    projectiveTowerShadow_transfer_direction V⟩

#check presentationMass
#check nativeCycleMass
#check nativeCycleCosmicShadow
#check nativeCycleCosmicShadow_point
#check cosmicMatrixUnit_nativeCycleShadow
#check nativeCycleMass_successor_point
#check nativeCycleMass_successor_of_pointMass
#check successorNativeOperator_cosmicShadow_point
#check projectiveTowerCosmicShadow
#check native_cycle_limitless_shadow_crown

#print axioms nativeCycleMass_point
#print axioms nativeCycleCosmicShadow_point
#print axioms cosmicMatrixUnit_nativeCycleShadow
#print axioms nativeCycleMass_successor_point
#print axioms nativeCycleMass_successor_of_pointMass
#print axioms successorNativeOperator_cosmicShadow_point
#print axioms projectiveTowerShadow_transfer_direction
#print axioms native_cycle_limitless_shadow_crown

end GSTClassicalHodgeNativeCycleCosmicShadow