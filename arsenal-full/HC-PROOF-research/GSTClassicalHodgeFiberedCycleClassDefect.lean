import GSTClassicalHodgeNormalizedFiberedSpectralAtom
import GSTClassicalHodgeAtomicDefectDuality
import GSTWorldRecoordinationGroupoid
import GSTClassicalHodgeFiberedTransferCompletion

/-!
# GST CLASSICAL HODGE — FIBERED CYCLE-CLASS DEFECT

The common-refinement universe remembers both pieces of data that must agree
in the classical landing:

* the classical Hodge multiplicity coordinate;
* the genuine native codimension-p algebraic cycle.

The limitless GST base address of those faces already agrees identically.  The
remaining classical question is therefore the vertical defect between the
actual cohomology class of the native face and the actual Hodge vector encoded
by the multiplicity face.

This file packages that difference as one linear map.  It is the precise
quantity on which the limitless projector, Poincare, recoordination and native
correspondence arsenal must act.  No cycle-class surjectivity statement is
assumed.
-/

set_option maxHeartbeats 60000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeFiberedCycleClassDefect

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTWorldRecoordinationGroupoid
open GSTClassicalHodgeFiberedNativeRecoordination
open GSTClassicalHodgeFiberedTransferCompletion
open GSTClassicalHodgeFiniteSupportArsenalConjugation
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeFiberedNativePullback
open GSTClassicalHodgeNormalizedFiberedSpectralAtom

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- Reconstruct the genuine Hodge vector encoded by the multiplicity face of a
fibered native state. -/
noncomputable def fiberedHodgeClass :
    FiberedNativeAddress V H p →ₗ[ℚ] ClassicalHodgeFiber V H p :=
  (classicalHodgeBasis V H p).repr.symm.toLinearMap.comp
    (forgetPoint V H p)

/-- Ambient rational cohomology class carried by the Hodge face. -/
noncomputable def fiberedHodgeAmbient :
    FiberedNativeAddress V H p →ₗ[ℚ]
      RationalSingularCohomology H.analytification (2 * p) :=
  (rationalHodgeSubspace (H.hodgeBigrading p)).subtype.comp
    (fiberedHodgeClass (V := V) (H := H) (p := p))

/-- Actual cohomology class carried by the genuine native cycle face. -/
noncomputable def fiberedNativeCycleClass :
    FiberedNativeAddress V H p →ₗ[ℚ]
      RationalSingularCohomology H.analytification (2 * p) :=
  (H.cycleClass p).comp (toNativeCycle V H p)

/-- **THE FIBERED CLASSICAL DEFECT.**
Native cycle class minus the genuine Hodge class encoded by the multiplicity
face. -/
noncomputable def fiberedCycleClassDefect :
    FiberedNativeAddress V H p →ₗ[ℚ]
      RationalSingularCohomology H.analytification (2 * p) :=
  fiberedNativeCycleClass (V := V) (H := H) (p := p) -
    fiberedHodgeAmbient (V := V) (H := H) (p := p)

@[simp]
theorem fiberedHodgeClass_atom
    (i : ClassicalHodgeBasisIndex V H p)
    (x : GSTNativeCodimensionCyclePresentation.CodimensionPoint V.X p) :
    fiberedHodgeClass (V := V) (H := H) (p := p)
      (atom V H p i x) = classicalHodgeBasis V H p i := by
  simp [fiberedHodgeClass]

@[simp]
theorem fiberedHodgeAmbient_atom
    (i : ClassicalHodgeBasisIndex V H p)
    (x : GSTNativeCodimensionCyclePresentation.CodimensionPoint V.X p) :
    fiberedHodgeAmbient (V := V) (H := H) (p := p)
      (atom V H p i x) = (classicalHodgeBasis V H p i).1 := by
  simp [fiberedHodgeAmbient]

@[simp]
theorem fiberedNativeCycleClass_atom
    (i : ClassicalHodgeBasisIndex V H p)
    (x : GSTNativeCodimensionCyclePresentation.CodimensionPoint V.X p) :
    fiberedNativeCycleClass (V := V) (H := H) (p := p)
      (atom V H p i x) =
      H.cycleClass p
        (GSTNativeCodimensionCyclePresentation.codimensionPointCycle V.X p x) := by
  simp [fiberedNativeCycleClass]

/-- On one common atom the defect is exactly the difference between the genuine
point-cycle class and the selected genuine Hodge basis vector. -/
@[simp]
theorem fiberedCycleClassDefect_atom
    (i : ClassicalHodgeBasisIndex V H p)
    (x : GSTNativeCodimensionCyclePresentation.CodimensionPoint V.X p) :
    fiberedCycleClassDefect (V := V) (H := H) (p := p)
      (atom V H p i x) =
      H.cycleClass p
          (GSTNativeCodimensionCyclePresentation.codimensionPointCycle V.X p x) -
        (classicalHodgeBasis V H p i).1 := by
  simp [fiberedCycleClassDefect]

/-- Defect zero on one atom is exactly the desired genuine classical equality
for that point cycle and Hodge basis direction. -/
theorem fiberedCycleClassDefect_atom_eq_zero_iff
    (i : ClassicalHodgeBasisIndex V H p)
    (x : GSTNativeCodimensionCyclePresentation.CodimensionPoint V.X p) :
    fiberedCycleClassDefect (V := V) (H := H) (p := p)
        (atom V H p i x) = 0 ↔
      H.cycleClass p
          (GSTNativeCodimensionCyclePresentation.codimensionPointCycle V.X p x) =
        (classicalHodgeBasis V H p i).1 := by
  rw [fiberedCycleClassDefect_atom]
  exact sub_eq_zero

/-- The normalized GST spectral atom has the same Hodge face as the selected
live basis sheet and the same native face as the chosen genuine point.  Its
classical defect is therefore the same atomic difference. -/
theorem normalizedSpectralAtom_defect
    (alpha : ClassicalHodgeFiber V H p)
    (S : GSTWorldShape (liveRank alpha))
    (y : ShapeState S)
    (x : GSTNativeCodimensionCyclePresentation.CodimensionPoint V.X p) :
    fiberedCycleClassDefect (V := V) (H := H) (p := p)
        (normalizedSpectralAtom alpha S y x) =
      H.cycleClass p
          (GSTNativeCodimensionCyclePresentation.codimensionPointCycle V.X p x) -
        (classicalHodgeBasis V H p
          (shapedLiveBasisIndex alpha S y)).1 := by
  unfold fiberedCycleClassDefect fiberedNativeCycleClass fiberedHodgeAmbient
  rw [LinearMap.sub_apply]
  rw [LinearMap.comp_apply, LinearMap.comp_apply]
  rw [normalized_nativeFace_exact alpha S y x]
  have hhodge :
      fiberedHodgeClass (V := V) (H := H) (p := p)
        (normalizedSpectralAtom alpha S y x) =
        classicalHodgeBasis V H p (shapedLiveBasisIndex alpha S y) := by
    apply (classicalHodgeBasis V H p).repr.injective
    apply Finsupp.embDomain_injective (weightFiberEmbedding V H p)
    simpa [fiberedHodgeClass, toGlobalHodgeAddress,
      weightFiberEmbedding, fiberedSheetGenerator] using
      normalized_hodgeFace_exact alpha S y x
  rw [hhodge]
  rfl

/-- A fibered state is a genuine classical landing state precisely when its
native cycle class equals its reconstructed Hodge face. -/
theorem defect_eq_zero_iff_faces_agree
    (Φ : FiberedNativeAddress V H p) :
    fiberedCycleClassDefect (V := V) (H := H) (p := p) Φ = 0 ↔
      H.cycleClass p (toNativeCycle V H p Φ) =
        (fiberedHodgeClass (V := V) (H := H) (p := p) Φ).1 := by
  change
    fiberedNativeCycleClass (V := V) (H := H) (p := p) Φ -
        fiberedHodgeAmbient (V := V) (H := H) (p := p) Φ = 0 ↔ _
  simp [fiberedNativeCycleClass, fiberedHodgeAmbient, sub_eq_zero]

/-- If one defect-zero fibered state realizes every Hodge basis sheet, then the
exact Stage-2G statement follows by unrestricted finite-support reconstruction.
This is a linear-algebra landing theorem; the states themselves are to be
manufactured by the limitless/native operator arsenal. -/
theorem bigradedBettiHodge_of_defectZero_basisStates
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (state : ∀ p : Nat, ClassicalHodgeBasisIndex V H p →
      FiberedNativeAddress V H p)
    (hhodge : ∀ p i,
      fiberedHodgeClass (V := V) (H := H) (p := p) (state p i) =
        classicalHodgeBasis V H p i)
    (hdefect : ∀ p i,
      fiberedCycleClassDefect (V := V) (H := H) (p := p) (state p i) = 0) :
    BigradedBettiHodgeStatement V H := by
  intro p alpha halpha
  let R : ClassicalHodgeBasisIndex V H p →
      codimensionCycles V.X p := fun i => toNativeCycle V H p (state p i)
  have hR : ∀ i,
      H.cycleClass p (R i) = (classicalHodgeBasis V H p i).1 := by
    intro i
    have hz := (defect_eq_zero_iff_faces_agree
      (V := V) (H := H) (p := p) (state p i)).mp (hdefect p i)
    simpa [R, hhodge p i] using hz
  let lift : ClassicalHodgeFiber V H p →ₗ[ℚ] codimensionCycles V.X p :=
    (classicalHodgeBasis V H p).constr ℚ R
  let alphaH : ClassicalHodgeFiber V H p := ⟨alpha, halpha⟩
  refine ⟨lift alphaH, ?_⟩
  have hmaps : (H.cycleClass p).comp lift =
      (rationalHodgeSubspace (H.hodgeBigrading p)).subtype := by
    apply (classicalHodgeBasis V H p).ext
    intro i
    simp [lift, hR]
  change ((H.cycleClass p).comp lift) alphaH = alpha
  rw [hmaps]
  rfl

#check fiberedHodgeClass
#check fiberedNativeCycleClass
#check fiberedCycleClassDefect
#check fiberedCycleClassDefect_atom
#check normalizedSpectralAtom_defect
#check defect_eq_zero_iff_faces_agree
#check bigradedBettiHodge_of_defectZero_basisStates

#print axioms fiberedCycleClassDefect_atom
#print axioms normalizedSpectralAtom_defect
#print axioms defect_eq_zero_iff_faces_agree
#print axioms bigradedBettiHodge_of_defectZero_basisStates

/-! ## Defect descends through the exact two-marginal normal form -/

@[simp] theorem fiberedHodgeClass_anchoredNormalization
    (i₀ : ClassicalHodgeBasisIndex V H p)
    (x₀ : GSTNativeCodimensionCyclePresentation.CodimensionPoint V.X p)
    (Φ : FiberedNativeAddress V H p) :
    fiberedHodgeClass (V := V) (H := H) (p := p)
        (anchoredNormalization V H p i₀ x₀ Φ) =
      fiberedHodgeClass (V := V) (H := H) (p := p) Φ := by
  simp [fiberedHodgeClass]

@[simp] theorem fiberedHodgeAmbient_anchoredNormalization
    (i₀ : ClassicalHodgeBasisIndex V H p)
    (x₀ : GSTNativeCodimensionCyclePresentation.CodimensionPoint V.X p)
    (Φ : FiberedNativeAddress V H p) :
    fiberedHodgeAmbient (V := V) (H := H) (p := p)
        (anchoredNormalization V H p i₀ x₀ Φ) =
      fiberedHodgeAmbient (V := V) (H := H) (p := p) Φ := by
  simp [fiberedHodgeAmbient]

@[simp] theorem fiberedNativeCycleClass_anchoredNormalization
    (i₀ : ClassicalHodgeBasisIndex V H p)
    (x₀ : GSTNativeCodimensionCyclePresentation.CodimensionPoint V.X p)
    (Φ : FiberedNativeAddress V H p) :
    fiberedNativeCycleClass (V := V) (H := H) (p := p)
        (anchoredNormalization V H p i₀ x₀ Φ) =
      fiberedNativeCycleClass (V := V) (H := H) (p := p) Φ := by
  simp [fiberedNativeCycleClass]

/-- Normalizing the joint presentation changes none of the actual defect. -/
@[simp] theorem fiberedCycleClassDefect_anchoredNormalization
    (i₀ : ClassicalHodgeBasisIndex V H p)
    (x₀ : GSTNativeCodimensionCyclePresentation.CodimensionPoint V.X p)
    (Φ : FiberedNativeAddress V H p) :
    fiberedCycleClassDefect (V := V) (H := H) (p := p)
        (anchoredNormalization V H p i₀ x₀ Φ) =
      fiberedCycleClassDefect (V := V) (H := H) (p := p) Φ := by
  simp [fiberedCycleClassDefect]

theorem circulation_nativeFace_zero
    (Φ : FiberedNativeAddress V H p)
    (hΦ : Φ ∈ circulationSector V H p) :
    toNativeCycle V H p Φ = 0 := by
  obtain ⟨_, hn⟩ := (mem_circulationSector_iff V H p Φ).1 hΦ
  simp [toNativeCycle, hn]

theorem circulation_hodgeFace_zero
    (Φ : FiberedNativeAddress V H p)
    (hΦ : Φ ∈ circulationSector V H p) :
    fiberedHodgeClass (V := V) (H := H) (p := p) Φ = 0 := by
  obtain ⟨hh, _⟩ := (mem_circulationSector_iff V H p Φ).1 hΦ
  simp [fiberedHodgeClass, hh]

theorem circulation_defect_zero
    (Φ : FiberedNativeAddress V H p)
    (hΦ : Φ ∈ circulationSector V H p) :
    fiberedCycleClassDefect (V := V) (H := H) (p := p) Φ = 0 := by
  rw [defect_eq_zero_iff_faces_agree,
    circulation_nativeFace_zero Φ hΦ, circulation_hodgeFace_zero Φ hΦ]
  simp

/-- Finite native/Hodge circulation corrections cannot change a genuine
landing discrepancy. This rules out cancellation by invisible rectangles. -/
theorem defect_add_circulation
    (Φ Ψ : FiberedNativeAddress V H p)
    (hΨ : Ψ ∈ circulationSector V H p) :
    fiberedCycleClassDefect (V := V) (H := H) (p := p) (Φ + Ψ) =
      fiberedCycleClassDefect (V := V) (H := H) (p := p) Φ := by
  rw [map_add, circulation_defect_zero Ψ hΨ, add_zero]

theorem defect_eq_of_same_marginals
    (Φ Ψ : FiberedNativeAddress V H p)
    (hh : forgetPoint V H p Φ = forgetPoint V H p Ψ)
    (hn : forgetMultiplicity V H p Φ = forgetMultiplicity V H p Ψ) :
    fiberedCycleClassDefect (V := V) (H := H) (p := p) Φ =
      fiberedCycleClassDefect (V := V) (H := H) (p := p) Ψ := by
  have hc : Φ - Ψ ∈ circulationSector V H p := by
    rw [mem_circulationSector_iff]
    simp [hh, hn]
  have hz := circulation_defect_zero (Φ - Ψ) hc
  rw [map_sub] at hz
  exact sub_eq_zero.mp hz

#print axioms circulation_defect_zero
#print axioms defect_add_circulation
#print axioms defect_eq_of_same_marginals


/-! ## GST NATIVE MASS-CALIBRATED FULL FIBER SOURCE BIRTH
A nonzero-mass nullhomologous native cycle calibrates the two common-refinement
marginals without changing the actual original-X Betti cycle class.
The independent hyperplane-source construction is derived in
research/derivations/GST_fibered_native_mass_calibrated_cycle_birthday_2026-10-22.tex.
-/

/-- A signed rational correction by a genuine nullhomologous native source. -/
noncomputable def massBalancedPresentation
    (a : ClassicalHodgeBasisIndex V H p →₀ ℚ)
    (b ν : GSTNativeCodimensionCyclePresentation.FiniteCodimensionPresentation V.X p) :
    GSTNativeCodimensionCyclePresentation.FiniteCodimensionPresentation V.X p :=
  b + (GSTClassicalHodgeFiberedNativePullback.multiplicityMass V H p a -
       GSTClassicalHodgeNativeCycleCosmicShadow.presentationMass b) • ν

/-- Actual finite presentation augmentation is precisely target Hodge mass. -/
theorem massBalancedPresentation_mass
    (a : ClassicalHodgeBasisIndex V H p →₀ ℚ)
    (b ν : GSTNativeCodimensionCyclePresentation.FiniteCodimensionPresentation V.X p)
    (hνmass : GSTClassicalHodgeNativeCycleCosmicShadow.presentationMass ν = 1) :
    GSTClassicalHodgeNativeCycleCosmicShadow.presentationMass
      (massBalancedPresentation (V := V) (H := H) (p := p) a b ν) =
        GSTClassicalHodgeFiberedNativePullback.multiplicityMass V H p a := by
  simp only [massBalancedPresentation, map_add, map_smul, hνmass,
    smul_eq_mul, mul_one]
  ring

/-- Calibration leaves canonical Betti realization of the genuine source intact. -/
theorem massBalancedPresentation_cycleClass
    (a : ClassicalHodgeBasisIndex V H p →₀ ℚ)
    (b ν : GSTNativeCodimensionCyclePresentation.FiniteCodimensionPresentation V.X p)
    (hνclass :
      H.cycleClass p
        (GSTNativeCodimensionCyclePresentation.realizeFiniteCodimensionPresentation
          V.X p ν) = 0) :
    H.cycleClass p
      (GSTNativeCodimensionCyclePresentation.realizeFiniteCodimensionPresentation
        V.X p (massBalancedPresentation (V := V) (H := H) (p := p) a b ν)) =
      H.cycleClass p
        (GSTNativeCodimensionCyclePresentation.realizeFiniteCodimensionPresentation
          V.X p b) := by
  simp only [massBalancedPresentation,
    GSTNativeCodimensionCyclePresentation.realizeFiniteCodimensionPresentation_add,
    GSTNativeCodimensionCyclePresentation.realizeFiniteCodimensionPresentation_smul,
    map_add, map_smul, hνclass, smul_zero, add_zero]

/-- An ACTUAL independent native candidate lands on the full Hodge multiplicity
face, without an extra mass restriction, exactly when its true Betti class
agrees. The proof uses the EXISTING geometric marginal gluing operation. -/
theorem gluedMassBalancedState_defect_zero_iff
    (i₀ : ClassicalHodgeBasisIndex V H p)
    (x₀ : GSTNativeCodimensionCyclePresentation.CodimensionPoint V.X p)
    (a : ClassicalHodgeBasisIndex V H p →₀ ℚ)
    (b ν : GSTNativeCodimensionCyclePresentation.FiniteCodimensionPresentation V.X p)
    (hνmass : GSTClassicalHodgeNativeCycleCosmicShadow.presentationMass ν = 1)
    (hνclass :
      H.cycleClass p
        (GSTNativeCodimensionCyclePresentation.realizeFiniteCodimensionPresentation
          V.X p ν) = 0) :
    fiberedCycleClassDefect (V := V) (H := H) (p := p)
      (GSTClassicalHodgeFiberedNativePullback.glueMarginals V H p i₀ x₀ a
        (massBalancedPresentation (V := V) (H := H) (p := p) a b ν)) = 0 ↔
      H.cycleClass p
        (GSTNativeCodimensionCyclePresentation.realizeFiniteCodimensionPresentation
          V.X p b) =
      ((classicalHodgeBasis V H p).repr.symm a).1 := by
  let bc := massBalancedPresentation (V := V) (H := H) (p := p) a b ν
  let Φ := GSTClassicalHodgeFiberedNativePullback.glueMarginals V H p i₀ x₀ a bc
  have hmass : GSTClassicalHodgeNativeCycleCosmicShadow.presentationMass bc =
      GSTClassicalHodgeFiberedNativePullback.multiplicityMass V H p a :=
    massBalancedPresentation_mass (V := V) (H := H) (p := p)
      a b ν hνmass
  have hNative :
      GSTClassicalHodgeFiberedNativePullback.toNativeCycle V H p Φ =
        GSTNativeCodimensionCyclePresentation.realizeFiniteCodimensionPresentation
          V.X p bc := by
    change GSTNativeCodimensionCyclePresentation.realizeFiniteCodimensionPresentation
        V.X p (GSTClassicalHodgeFiberedNativePullback.forgetMultiplicity V H p Φ) = _
    rw [GSTClassicalHodgeFiberedNativePullback.glueMarginals_forgetMultiplicity]
  have hHodge :
      fiberedHodgeClass (V := V) (H := H) (p := p) Φ =
        (classicalHodgeBasis V H p).repr.symm a := by
    change (classicalHodgeBasis V H p).repr.symm
      (GSTClassicalHodgeFiberedNativePullback.forgetPoint V H p Φ) =
        (classicalHodgeBasis V H p).repr.symm a
    rw [GSTClassicalHodgeFiberedNativePullback.glueMarginals_forgetPoint
      V H p i₀ x₀ a bc hmass.symm]
  change fiberedCycleClassDefect (V := V) (H := H) (p := p) Φ = 0 ↔ _
  rw [defect_eq_zero_iff_faces_agree, hNative, hHodge,
    massBalancedPresentation_cycleClass (V := V) (H := H) (p := p)
      a b ν hνclass]

#check massBalancedPresentation_mass
#check massBalancedPresentation_cycleClass
#check gluedMassBalancedState_defect_zero_iff
#print axioms massBalancedPresentation_mass
#print axioms massBalancedPresentation_cycleClass
#print axioms gluedMassBalancedState_defect_zero_iff

end GSTClassicalHodgeFiberedCycleClassDefect
