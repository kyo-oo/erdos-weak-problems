import GSTClassicalHodgePointNormalForm
import GSTClassicalHodgeFiberedCycleClassDefect
import GSTClassicalHodgeThreeUniverseSeedIdentification
import GSTClassicalHodgeSynchronizedDefectOrbit

/-!
# GST CLASSICAL HODGE — SYNCHRONIZED SEED FIBERED LANDING

This module identifies the exact lower obstruction to placing one already
synchronized native Hodge seed inside the common fibered native/Hodge universe.

A `NativeHodgeOrbitSeed` already gives the genuine equality

  cycleClass(S.cycle) = S.hodge.

Its two finite marginals are also canonical:

* the Hodge marginal is the coordinate vector of `S.hodge` in the genuine
  classical Hodge basis;
* the native marginal is the compact point presentation of `S.cycle`.

The fibered pullback theorem says that two finite marginals glue iff their
augmentations agree.  Therefore a synchronized seed admits one exact joint
fibered representative iff

  classicalHodgeMass(S.hodge) = nativeCycleMass(S.cycle).

When that scalar balance holds, the resulting joint state has zero classical
cycle-class defect automatically, by the seed's existing synchronization law.
No target Hodge sheet, ghost, basis-cycle supply, Hodge surjectivity, branch
packet, projective spoke, or bare-L2 closure is assumed.

This moves the active construction problem one layer lower: before asking
geometry to transport a seed between multiplicity sheets, first synchronize
the finite native and Hodge marginals by one scalar conservation law.
-/

set_option maxHeartbeats 90000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeSynchronizedSeedFiberedLanding

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeFiberedNativePullback
open GSTClassicalHodgeFiberedCycleClassDefect
open GSTClassicalHodgeThreeUniverseSeedIdentification
open GSTClassicalHodgeSynchronizedDefectOrbit
open GSTClassicalHodgeNativeCycleCosmicShadow
open GSTCompactNativeCyclePresentation
open GSTClassicalHodgePointNormalForm
open GSTNativeCodimensionCyclePresentation

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- Exact classical multiplicity marginal of a synchronized Hodge seed. -/
noncomputable def seedHodgeMarginal
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p)) :
    ClassicalHodgeBasisIndex V H p →₀ ℚ :=
  (classicalHodgeBasis V H p).repr S.hodge

/-- Exact finite native point marginal of the seed's actual algebraic cycle. -/
noncomputable def seedNativeMarginal
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p)) :
    FiniteCodimensionPresentation V.X p := by
  letI : CompactSpace V.X := smoothProjectiveCompactSpace V
  exact presentationOfNativeCycle V.X p S.cycle

/-- The single scalar compatibility required for the two canonical seed
marginals to inhabit one finite fibered-native state. -/
def SeedFiberedMassBalance
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p)) : Prop :=
  classicalHodgeMass V H p S.hodge = nativeCycleMass V p S.cycle

/-- The augmentation of the Hodge marginal is the classical Hodge mass. -/
theorem multiplicityMass_seedHodgeMarginal
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p)) :
    multiplicityMass V H p (seedHodgeMarginal S) =
      classicalHodgeMass V H p S.hodge := by
  rfl

/-- The augmentation of the canonical native marginal is the native cycle
mass. -/
theorem presentationMass_seedNativeMarginal
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p)) :
    presentationMass (seedNativeMarginal S) =
      nativeCycleMass V p S.cycle := by
  letI : CompactSpace V.X := smoothProjectiveCompactSpace V
  rfl

/-- **EXACT GLUING CRITERION FOR ONE SYNCHRONIZED SEED.**

Given any anchor point at the same codimension, the seed's exact Hodge and
native marginals admit a common fibered representative iff their scalar masses
agree. -/
theorem exists_seedJointState_iff_massBalance
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p))
    (x₀ : CodimensionPoint V.X p) :
    (∃ Φ : FiberedNativeAddress V H p,
      forgetPoint V H p Φ = seedHodgeMarginal S ∧
      forgetMultiplicity V H p Φ = seedNativeMarginal S) ↔
      SeedFiberedMassBalance S := by
  rw [exists_joint_marginals_iff
    (V := V) (H := H) (p := p) S.sourceIndex x₀
    (seedHodgeMarginal S) (seedNativeMarginal S)]
  rw [multiplicityMass_seedHodgeMarginal,
    presentationMass_seedNativeMarginal]
  rfl

/-- A joint state with the exact seed marginals reconstructs the seed's actual
native cycle. -/
theorem seedJointState_nativeFace
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p))
    (Φ : FiberedNativeAddress V H p)
    (hNative : forgetMultiplicity V H p Φ = seedNativeMarginal S) :
    toNativeCycle V H p Φ = S.cycle := by
  letI : CompactSpace V.X := smoothProjectiveCompactSpace V
  change realizeFiniteCodimensionPresentation V.X p
    (forgetMultiplicity V H p Φ) = S.cycle
  rw [hNative]
  exact realize_presentationOfNativeCycle V.X p S.cycle

/-- A joint state with the exact Hodge marginal reconstructs the seed's genuine
Hodge vector. -/
theorem seedJointState_hodgeFace
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p))
    (Φ : FiberedNativeAddress V H p)
    (hHodge : forgetPoint V H p Φ = seedHodgeMarginal S) :
    fiberedHodgeClass (V := V) (H := H) (p := p) Φ = S.hodge := by
  simp only [fiberedHodgeClass, LinearMap.comp_apply]
  rw [hHodge]
  simp [seedHodgeMarginal]

/-- **SYNCHRONIZATION DESCENDS TO ZERO FIBERED DEFECT.**

Once the two exact marginals coexist, no new Hodge assertion is required:
the seed's stored cycle-class equality kills the fibered defect. -/
theorem seedJointState_defect_zero
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p))
    (Φ : FiberedNativeAddress V H p)
    (hHodge : forgetPoint V H p Φ = seedHodgeMarginal S)
    (hNative : forgetMultiplicity V H p Φ = seedNativeMarginal S) :
    fiberedCycleClassDefect (V := V) (H := H) (p := p) Φ = 0 := by
  rw [defect_eq_zero_iff_faces_agree]
  rw [seedJointState_nativeFace S Φ hNative,
    seedJointState_hodgeFace S Φ hHodge]
  exact S.class_eq

/-- **MASS BALANCE IS EXACTLY THE EXISTENCE OF A DEFECT-ZERO JOINT SEED.**

The defect-zero clause adds no hidden algebraicity: it follows automatically
from the synchronized seed equality.  Thus the full common-refinement landing
for one known algebraic seed is equivalent to one scalar conservation law. -/
theorem exists_defectZero_seedJointState_iff_massBalance
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p))
    (x₀ : CodimensionPoint V.X p) :
    (∃ Φ : FiberedNativeAddress V H p,
      forgetPoint V H p Φ = seedHodgeMarginal S ∧
      forgetMultiplicity V H p Φ = seedNativeMarginal S ∧
      fiberedCycleClassDefect (V := V) (H := H) (p := p) Φ = 0) ↔
      SeedFiberedMassBalance S := by
  constructor
  · rintro ⟨Φ, hHodge, hNative, _hdef⟩
    exact (exists_seedJointState_iff_massBalance S x₀).1
      ⟨Φ, hHodge, hNative⟩
  · intro hmass
    obtain ⟨Φ, hHodge, hNative⟩ :=
      (exists_seedJointState_iff_massBalance S x₀).2 hmass
    exact ⟨Φ, hHodge, hNative,
      seedJointState_defect_zero S Φ hHodge hNative⟩

#check seedHodgeMarginal
#check seedNativeMarginal
#check SeedFiberedMassBalance
#check multiplicityMass_seedHodgeMarginal
#check presentationMass_seedNativeMarginal
#check exists_seedJointState_iff_massBalance
#check seedJointState_nativeFace
#check seedJointState_hodgeFace
#check seedJointState_defect_zero
#check exists_defectZero_seedJointState_iff_massBalance

#print axioms exists_seedJointState_iff_massBalance
#print axioms seedJointState_defect_zero
#print axioms exists_defectZero_seedJointState_iff_massBalance

end GSTClassicalHodgeSynchronizedSeedFiberedLanding
