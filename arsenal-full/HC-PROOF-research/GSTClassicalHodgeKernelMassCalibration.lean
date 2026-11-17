import GSTClassicalHodgeSynchronizedSeedFiberedLanding

/-!
# GST CLASSICAL HODGE — KERNEL MASS CALIBRATION

This file removes the scalar fibered-joint-state obstruction whenever native
mass has a nontrivial direction invisible to the actual cycle-class map.

For a synchronized algebraic Hodge seed S and a null-class cycle K with
nonzero canonical native mass, set

  calibratedCycle(S,K)
    = S.cycle
      + ((classicalHodgeMass(S.hodge) - nativeCycleMass(S.cycle))
           * nativeCycleMass(K)^(-1)) • K.

The calibrated cycle has *exactly the same genuine cohomology class* as S.
Its native mass is exactly the mass of S's genuine Hodge coordinate vector.
The two finite marginals therefore glue into an explicit fibered-native state
with zero actual cycle-class defect.

The final dichotomy is unconditional and contains no Hodge conclusion:

* either native mass annihilates the cycle-class kernel at weight p; or
* every ALREADY algebraic synchronized seed at that weight admits a finite
  defect-zero joint representation.

This is a mass-calibration and internal lifting theorem, not a construction
of previously nonalgebraic target Hodge basis cycles. No Hodge-surjectivity,
ghost-targeted closure, D/branch packet, projective spoke, or two-successor
cardinality law appears as a premise.
-/

set_option maxHeartbeats 90000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeKernelMassCalibration

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeSynchronizedDefectOrbit
open GSTClassicalHodgeSynchronizedSeedFiberedLanding
open GSTClassicalHodgeFiberedNativePullback
open GSTClassicalHodgeFiberedCycleClassDefect
open GSTClassicalHodgeNativeCycleCosmicShadow
open GSTNativeCodimensionCyclePresentation
open GSTCompactNativeCyclePresentation
open GSTClassicalHodgePointNormalForm
open GSTClassicalHodgePointKernelOperatorLift
open GSTClassicalHodgeCycleOperatorNaturality
open GSTClassicalHodgeThreeUniverseSeedIdentification

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- Native mass vanishes on every cohomologically null native cycle at this
fixed weight. The negation is precisely the calibration witness below. -/
def NativeMassKernelLawAtWeight : Prop :=
  ∀ K : codimensionCycles V.X p,
    H.cycleClass p K = 0 → nativeCycleMass V p K = 0

/-- An explicit affine correction of a genuine synchronized seed along one
native cycle. Its coefficient is chosen to match the Hodge coordinate mass. -/
noncomputable def massCalibratedCycle
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p))
    (K : codimensionCycles V.X p) : codimensionCycles V.X p :=
  S.cycle +
    ((classicalHodgeMass V H p S.hodge - nativeCycleMass V p S.cycle) *
      (nativeCycleMass V p K)⁻¹) • K

/-- Calibration along a genuinely null-class cycle preserves the entire real
cycle-class image of the original seed, not merely its cosmic shadow. -/
theorem massCalibratedCycle_class
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p))
    (K : codimensionCycles V.X p)
    (hK : H.cycleClass p K = 0) :
    H.cycleClass p (massCalibratedCycle S K) = S.hodge.1 := by
  simp [massCalibratedCycle, hK, S.class_eq]

/-- If the null-class calibration direction has nonzero native mass, the new
genuine cycle has exactly the prescribed classical Hodge coordinate mass. -/
theorem massCalibratedCycle_mass
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p))
    (K : codimensionCycles V.X p)
    (hK : nativeCycleMass V p K ≠ 0) :
    nativeCycleMass V p (massCalibratedCycle S K) =
      classicalHodgeMass V H p S.hodge := by
  simp only [massCalibratedCycle, map_add, map_smul, smul_eq_mul]
  rw [mul_assoc, inv_mul_cancel₀ hK, mul_one]
  abel

/-- The corrected native cycle is again a genuine nonzero synchronized
algebraic Hodge seed, with the same Hodge vector as the input seed. -/
noncomputable def massCalibratedSeed
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p))
    (K : codimensionCycles V.X p)
    (hK : H.cycleClass p K = 0) :
    NativeHodgeOrbitSeed (V := V) (H := H) (p := p) where
  cycle := massCalibratedCycle S K
  hodge := S.hodge
  hodge_ne_zero := S.hodge_ne_zero
  class_eq := massCalibratedCycle_class S K hK

/-- The corrected seed has the exact scalar balance required by the existing
explicit common-refinement gluing theorem. -/
theorem massCalibratedSeed_balanced
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p))
    (K : codimensionCycles V.X p)
    (hKclass : H.cycleClass p K = 0)
    (hKmass : nativeCycleMass V p K ≠ 0) :
    SeedFiberedMassBalance (massCalibratedSeed S K hKclass) := by
  change classicalHodgeMass V H p S.hodge =
    nativeCycleMass V p (massCalibratedCycle S K)
  exact (massCalibratedCycle_mass S K hKmass).symm

/-- **CONSTRUCTIVE ZERO-DEFECT SEED LIFT.**

At any actual native codimension-p point anchor, a null-class/nonzero-mass
direction constructs a finite fibered state representing exactly the original
Hodge seed while preserving its original cycle class. -/
theorem exists_massCalibrated_defectZero_jointSeed
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p))
    (K : codimensionCycles V.X p)
    (hKclass : H.cycleClass p K = 0)
    (hKmass : nativeCycleMass V p K ≠ 0)
    (x₀ : CodimensionPoint V.X p) :
    ∃ Φ : FiberedNativeAddress V H p,
      fiberedHodgeClass (V := V) (H := H) (p := p) Φ = S.hodge
      ∧ toNativeCycle V H p Φ = massCalibratedCycle S K
      ∧ fiberedCycleClassDefect (V := V) (H := H) (p := p) Φ = 0 := by
  let T := massCalibratedSeed S K hKclass
  have hb : SeedFiberedMassBalance T :=
    massCalibratedSeed_balanced S K hKclass hKmass
  obtain ⟨Φ, hh, hn, hd⟩ :=
    (exists_defectZero_seedJointState_iff_massBalance T x₀).2 hb
  refine ⟨Φ, ?_, ?_, hd⟩
  · simpa [T, massCalibratedSeed] using
      seedJointState_hodgeFace T Φ hh
  · simpa [T, massCalibratedSeed] using
      seedJointState_nativeFace T Φ hn

/-- **UNCONDITIONAL NATIVE-MASS CALIBRATION DICHOTOMY.**

At a fixed weight with at least one native point, either mass is already
well-defined on actual cohomological cycle classes, OR every existing
synchronized algebraic seed admits an exact finite zero-defect representation.

The conclusion does not generate nonalgebraic Hodge target sheets. It resolves
the scalar gluing barrier independently of the stronger projective two-step
Lefschetz target-realization problem. -/
theorem kernelLaw_or_allSynchronizedSeeds_have_defectZero_jointState
    (x₀ : CodimensionPoint V.X p) :
    NativeMassKernelLawAtWeight (V := V) (H := H) (p := p)
      ∨ ∀ S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p),
        ∃ Φ : FiberedNativeAddress V H p,
          fiberedHodgeClass (V := V) (H := H) (p := p) Φ = S.hodge
          ∧ fiberedCycleClassDefect (V := V) (H := H) (p := p) Φ = 0 := by
  classical
  by_cases hker : NativeMassKernelLawAtWeight (V := V) (H := H) (p := p)
  · exact Or.inl hker
  · right
    have hK : ∃ K : codimensionCycles V.X p,
        H.cycleClass p K = 0 ∧ nativeCycleMass V p K ≠ 0 := by
      by_contra hn
      apply hker
      intro K hz
      by_contra hm
      exact hn ⟨K, hz, hm⟩
    obtain ⟨K, hz, hm⟩ := hK
    intro S
    obtain ⟨Φ, hface, _, hdef⟩ :=
      exists_massCalibrated_defectZero_jointSeed S K hz hm x₀
    exact ⟨Φ, hface, hdef⟩

#check NativeMassKernelLawAtWeight
#check massCalibratedCycle
#check massCalibratedCycle_class
#check massCalibratedCycle_mass
#check massCalibratedSeed
#check massCalibratedSeed_balanced
#check exists_massCalibrated_defectZero_jointSeed
#check kernelLaw_or_allSynchronizedSeeds_have_defectZero_jointState

#print axioms massCalibratedCycle_class
#print axioms massCalibratedCycle_mass
#print axioms exists_massCalibrated_defectZero_jointSeed
#print axioms kernelLaw_or_allSynchronizedSeeds_have_defectZero_jointState

/-! ## Arbitrary-cycle calibration and explicit simultaneous landing

The construction now acts on every actual cycle and every prescribed Hodge
face, including zero.  Its class is preserved and its scalar mass is repaired.
The final defect formula retains the entire original class mismatch, so the
construction cannot manufacture algebraicity by changing a label.
-/

/-- Calibration at a prescribed Hodge face, without a nonzero-seed wrapper. -/
noncomputable def calibratedRepresentative
    (K : codimensionCycles V.X p)
    (alpha : ClassicalHodgeFiber V H p)
    (Z : codimensionCycles V.X p) : codimensionCycles V.X p :=
  Z + ((classicalHodgeMass V H p alpha - nativeCycleMass V p Z) *
    (nativeCycleMass V p K)⁻¹) • K

theorem calibratedRepresentative_class
    (K : codimensionCycles V.X p)
    (hK : H.cycleClass p K = 0)
    (alpha : ClassicalHodgeFiber V H p)
    (Z : codimensionCycles V.X p) :
    H.cycleClass p (calibratedRepresentative K alpha Z) =
      H.cycleClass p Z := by
  simp [calibratedRepresentative, hK]

theorem calibratedRepresentative_mass
    (K : codimensionCycles V.X p)
    (hK : nativeCycleMass V p K ≠ 0)
    (alpha : ClassicalHodgeFiber V H p)
    (Z : codimensionCycles V.X p) :
    nativeCycleMass V p (calibratedRepresentative K alpha Z) =
      classicalHodgeMass V H p alpha := by
  simp only [calibratedRepresentative, map_add, map_smul, smul_eq_mul]
  rw [mul_assoc, inv_mul_cancel₀ hK, mul_one]
  abel

theorem calibratedRepresentative_eq_self_iff
    (K : codimensionCycles V.X p)
    (hK : nativeCycleMass V p K ≠ 0)
    (alpha : ClassicalHodgeFiber V H p)
    (Z : codimensionCycles V.X p) :
    calibratedRepresentative K alpha Z = Z ↔
      classicalHodgeMass V H p alpha = nativeCycleMass V p Z := by
  constructor
  · intro h
    rw [← calibratedRepresentative_mass K hK alpha Z, h]
  · intro h
    simp [calibratedRepresentative, h]

theorem calibratedRepresentative_idempotent
    (K : codimensionCycles V.X p)
    (hK : nativeCycleMass V p K ≠ 0)
    (alpha : ClassicalHodgeFiber V H p)
    (Z : codimensionCycles V.X p) :
    calibratedRepresentative K alpha (calibratedRepresentative K alpha Z) =
      calibratedRepresentative K alpha Z := by
  exact (calibratedRepresentative_eq_self_iff K hK alpha _).2
    (calibratedRepresentative_mass K hK alpha Z).symm

/-- Recalibration to a second target mass forgets the first target mass. -/
theorem calibratedRepresentative_retarget
    (K : codimensionCycles V.X p)
    (hK : nativeCycleMass V p K ≠ 0)
    (alpha beta : ClassicalHodgeFiber V H p)
    (Z : codimensionCycles V.X p) :
    calibratedRepresentative K beta (calibratedRepresentative K alpha Z) =
      calibratedRepresentative K beta Z := by
  change calibratedRepresentative K alpha Z +
      ((classicalHodgeMass V H p beta -
        nativeCycleMass V p (calibratedRepresentative K alpha Z)) *
        (nativeCycleMass V p K)⁻¹) • K = _
  rw [calibratedRepresentative_mass K hK alpha Z]
  unfold calibratedRepresentative
  rw [add_assoc, ← add_smul]
  congr 1
  congr 1
  ring

/-- The correction is linear in the pair consisting of the target Hodge face
and its actual native representative. -/
theorem calibratedRepresentative_add
    (K : codimensionCycles V.X p)
    (alpha beta : ClassicalHodgeFiber V H p)
    (Z W : codimensionCycles V.X p) :
    calibratedRepresentative K (alpha + beta) (Z + W) =
      calibratedRepresentative K alpha Z + calibratedRepresentative K beta W := by
  simp only [calibratedRepresentative, map_add]
  have hc :
      ((classicalHodgeMass V H p alpha + classicalHodgeMass V H p beta -
          (nativeCycleMass V p Z + nativeCycleMass V p W)) *
          (nativeCycleMass V p K)⁻¹) =
        (classicalHodgeMass V H p alpha - nativeCycleMass V p Z) *
            (nativeCycleMass V p K)⁻¹ +
          (classicalHodgeMass V H p beta - nativeCycleMass V p W) *
            (nativeCycleMass V p K)⁻¹ := by ring
  rw [hc, add_smul]
  abel

theorem calibratedRepresentative_smul
    (K : codimensionCycles V.X p) (q : ℚ)
    (alpha : ClassicalHodgeFiber V H p)
    (Z : codimensionCycles V.X p) :
    calibratedRepresentative K (q • alpha) (q • Z) =
      q • calibratedRepresentative K alpha Z := by
  simp only [calibratedRepresentative, map_smul, smul_eq_mul,
    smul_add, smul_smul]
  congr 1
  congr 1
  ring

/-- Explicit finite joint state for a prescribed native cycle and Hodge face.
The native face is always exact; the Hodge face is exact when masses agree. -/
noncomputable def jointRepresentative
    (i₀ : ClassicalHodgeBasisIndex V H p)
    (x₀ : CodimensionPoint V.X p)
    (alpha : ClassicalHodgeFiber V H p)
    (Z : codimensionCycles V.X p) : FiberedNativeAddress V H p := by
  letI : CompactSpace V.X := smoothProjectiveCompactSpace V
  exact glueMarginals V H p i₀ x₀
    ((classicalHodgeBasis V H p).repr alpha)
    (presentationOfNativeCycleLinear V.X p Z)

theorem jointRepresentative_nativeFace
    (i₀ : ClassicalHodgeBasisIndex V H p)
    (x₀ : CodimensionPoint V.X p)
    (alpha : ClassicalHodgeFiber V H p)
    (Z : codimensionCycles V.X p) :
    toNativeCycle V H p (jointRepresentative i₀ x₀ alpha Z) = Z := by
  letI : CompactSpace V.X := smoothProjectiveCompactSpace V
  change realizeFiniteCodimensionPresentation V.X p
      (forgetMultiplicity V H p
        (glueMarginals V H p i₀ x₀
          ((classicalHodgeBasis V H p).repr alpha)
          (presentationOfNativeCycle V.X p Z))) = Z
  rw [glueMarginals_forgetMultiplicity, realize_presentationOfNativeCycle]

theorem jointRepresentative_hodgeMarginal
    (i₀ : ClassicalHodgeBasisIndex V H p)
    (x₀ : CodimensionPoint V.X p)
    (alpha : ClassicalHodgeFiber V H p)
    (Z : codimensionCycles V.X p)
    (hbalance : classicalHodgeMass V H p alpha = nativeCycleMass V p Z) :
    forgetPoint V H p (jointRepresentative i₀ x₀ alpha Z) =
      (classicalHodgeBasis V H p).repr alpha := by
  letI : CompactSpace V.X := smoothProjectiveCompactSpace V
  apply glueMarginals_forgetPoint
  change classicalHodgeMass V H p alpha = nativeCycleMass V p Z
  exact hbalance

theorem jointRepresentative_hodgeFace
    (i₀ : ClassicalHodgeBasisIndex V H p)
    (x₀ : CodimensionPoint V.X p)
    (alpha : ClassicalHodgeFiber V H p)
    (Z : codimensionCycles V.X p)
    (hbalance : classicalHodgeMass V H p alpha = nativeCycleMass V p Z) :
    fiberedHodgeClass (V := V) (H := H) (p := p)
        (jointRepresentative i₀ x₀ alpha Z) = alpha := by
  apply (classicalHodgeBasis V H p).repr.injective
  simpa [fiberedHodgeClass] using
    jointRepresentative_hodgeMarginal i₀ x₀ alpha Z hbalance

theorem jointRepresentative_defect
    (i₀ : ClassicalHodgeBasisIndex V H p)
    (x₀ : CodimensionPoint V.X p)
    (alpha : ClassicalHodgeFiber V H p)
    (Z : codimensionCycles V.X p)
    (hbalance : classicalHodgeMass V H p alpha = nativeCycleMass V p Z) :
    fiberedCycleClassDefect (V := V) (H := H) (p := p)
        (jointRepresentative i₀ x₀ alpha Z) = H.cycleClass p Z - alpha.1 := by
  change H.cycleClass p (toNativeCycle V H p
      (jointRepresentative i₀ x₀ alpha Z)) -
    (fiberedHodgeClass (V := V) (H := H) (p := p)
      (jointRepresentative i₀ x₀ alpha Z)).1 = _
  rw [jointRepresentative_nativeFace, jointRepresentative_hodgeFace _ _ _ _ hbalance]

/-- Calibration followed by actual finite common-refinement gluing. -/
noncomputable def calibratedJointRepresentative
    (i₀ : ClassicalHodgeBasisIndex V H p)
    (x₀ : CodimensionPoint V.X p)
    (K : codimensionCycles V.X p)
    (alpha : ClassicalHodgeFiber V H p)
    (Z : codimensionCycles V.X p) : FiberedNativeAddress V H p :=
  jointRepresentative i₀ x₀ alpha (calibratedRepresentative K alpha Z)

theorem calibratedJointRepresentative_nativeFace
    (i₀ : ClassicalHodgeBasisIndex V H p)
    (x₀ : CodimensionPoint V.X p)
    (K : codimensionCycles V.X p)
    (alpha : ClassicalHodgeFiber V H p)
    (Z : codimensionCycles V.X p) :
    toNativeCycle V H p (calibratedJointRepresentative i₀ x₀ K alpha Z) =
      calibratedRepresentative K alpha Z :=
  jointRepresentative_nativeFace i₀ x₀ alpha _

theorem calibratedJointRepresentative_hodgeFace
    (i₀ : ClassicalHodgeBasisIndex V H p)
    (x₀ : CodimensionPoint V.X p)
    (K : codimensionCycles V.X p)
    (hKmass : nativeCycleMass V p K ≠ 0)
    (alpha : ClassicalHodgeFiber V H p)
    (Z : codimensionCycles V.X p) :
    fiberedHodgeClass (V := V) (H := H) (p := p)
        (calibratedJointRepresentative i₀ x₀ K alpha Z) = alpha :=
  jointRepresentative_hodgeFace i₀ x₀ alpha _
    (calibratedRepresentative_mass K hKmass alpha Z).symm

/-- **EXACT RESIDUAL DEFECT LAW.** Repairing the scalar gluing obstruction
leaves precisely the original genuine cycle-class discrepancy. -/
theorem calibratedJointRepresentative_defect
    (i₀ : ClassicalHodgeBasisIndex V H p)
    (x₀ : CodimensionPoint V.X p)
    (K : codimensionCycles V.X p)
    (hKclass : H.cycleClass p K = 0)
    (hKmass : nativeCycleMass V p K ≠ 0)
    (alpha : ClassicalHodgeFiber V H p)
    (Z : codimensionCycles V.X p) :
    fiberedCycleClassDefect (V := V) (H := H) (p := p)
        (calibratedJointRepresentative i₀ x₀ K alpha Z) =
      H.cycleClass p Z - alpha.1 := by
  rw [calibratedJointRepresentative,
    jointRepresentative_defect _ _ _ _
      (calibratedRepresentative_mass K hKmass alpha Z).symm,
    calibratedRepresentative_class K hKclass alpha Z]

theorem calibratedJointRepresentative_defect_zero_iff
    (i₀ : ClassicalHodgeBasisIndex V H p)
    (x₀ : CodimensionPoint V.X p)
    (K : codimensionCycles V.X p)
    (hKclass : H.cycleClass p K = 0)
    (hKmass : nativeCycleMass V p K ≠ 0)
    (alpha : ClassicalHodgeFiber V H p)
    (Z : codimensionCycles V.X p) :
    fiberedCycleClassDefect (V := V) (H := H) (p := p)
        (calibratedJointRepresentative i₀ x₀ K alpha Z) = 0 ↔
      H.cycleClass p Z = alpha.1 := by
  rw [calibratedJointRepresentative_defect i₀ x₀ K hKclass hKmass alpha Z]
  exact sub_eq_zero

/-- The two faces of every finite state necessarily have equal mass. -/
theorem fiberedFaces_mass_balance
    (Φ : FiberedNativeAddress V H p) :
    classicalHodgeMass V H p
        (fiberedHodgeClass (V := V) (H := H) (p := p) Φ) =
      nativeCycleMass V p (toNativeCycle V H p Φ) := by
  have hm := marginal_mass_balance V H p Φ
  change multiplicityMass V H p
      ((classicalHodgeBasis V H p).repr
        (fiberedHodgeClass (V := V) (H := H) (p := p) Φ)) = _
  have hh : (classicalHodgeBasis V H p).repr
      (fiberedHodgeClass (V := V) (H := H) (p := p) Φ) =
      forgetPoint V H p Φ := by simp [fiberedHodgeClass]
  rw [hh]
  change multiplicityMass V H p (forgetPoint V H p Φ) =
      nativeCycleMass V p (realizeFiniteCodimensionPresentation V.X p
        (forgetMultiplicity V H p Φ))
  rw [nativeCycleMass_realize]
  exact hm

/-- **COMPLETE TWO-FACE LANDING CRITERION.** A prescribed Hodge state lands
iff it has an actual native representative with the required scalar balance. -/
theorem exists_defectZero_face_iff_balanced_cycle
    (i₀ : ClassicalHodgeBasisIndex V H p)
    (x₀ : CodimensionPoint V.X p)
    (alpha : ClassicalHodgeFiber V H p) :
    (∃ Φ : FiberedNativeAddress V H p,
      fiberedHodgeClass (V := V) (H := H) (p := p) Φ = alpha ∧
      fiberedCycleClassDefect (V := V) (H := H) (p := p) Φ = 0) ↔
    (∃ Z : codimensionCycles V.X p,
      H.cycleClass p Z = alpha.1 ∧
      nativeCycleMass V p Z = classicalHodgeMass V H p alpha) := by
  constructor
  · rintro ⟨Φ, hh, hd⟩
    refine ⟨toNativeCycle V H p Φ, ?_, ?_⟩
    · simpa [hh] using (defect_eq_zero_iff_faces_agree Φ).1 hd
    · simpa [hh] using (fiberedFaces_mass_balance Φ).symm
  · rintro ⟨Z, hclass, hmass⟩
    refine ⟨jointRepresentative i₀ x₀ alpha Z,
      jointRepresentative_hodgeFace i₀ x₀ alpha Z hmass.symm, ?_⟩
    rw [jointRepresentative_defect i₀ x₀ alpha Z hmass.symm, hclass, sub_self]

theorem exists_defectZero_face_iff_class_representative
    (i₀ : ClassicalHodgeBasisIndex V H p)
    (x₀ : CodimensionPoint V.X p)
    (K : codimensionCycles V.X p)
    (hKclass : H.cycleClass p K = 0)
    (hKmass : nativeCycleMass V p K ≠ 0)
    (alpha : ClassicalHodgeFiber V H p) :
    (∃ Φ : FiberedNativeAddress V H p,
      fiberedHodgeClass (V := V) (H := H) (p := p) Φ = alpha ∧
      fiberedCycleClassDefect (V := V) (H := H) (p := p) Φ = 0) ↔
      alpha.1 ∈ LinearMap.range (H.cycleClass p) := by
  constructor
  · intro h
    obtain ⟨Z, hZ, _⟩ := (exists_defectZero_face_iff_balanced_cycle i₀ x₀ alpha).1 h
    exact ⟨Z, hZ⟩
  · rintro ⟨Z, hZ⟩
    refine ⟨calibratedJointRepresentative i₀ x₀ K alpha Z,
      calibratedJointRepresentative_hodgeFace i₀ x₀ K hKmass alpha Z, ?_⟩
    exact (calibratedJointRepresentative_defect_zero_iff
      i₀ x₀ K hKclass hKmass alpha Z).2 hZ

/-! ## The other branch: exact native mass descent to actual cycle classes -/

theorem nativeMass_eq_of_class_eq
    (hker : NativeMassKernelLawAtWeight (V := V) (H := H) (p := p))
    (Z W : codimensionCycles V.X p)
    (hclass : H.cycleClass p Z = H.cycleClass p W) :
    nativeCycleMass V p Z = nativeCycleMass V p W := by
  have hz : H.cycleClass p (Z - W) = 0 := by simp [hclass]
  have hm := hker (Z - W) hz
  rw [map_sub] at hm
  exact sub_eq_zero.mp hm

/-- Choose a representative only for a class already in the native range. -/
noncomputable def rangeCycleRepresentative
    (a : LinearMap.range (H.cycleClass p)) : codimensionCycles V.X p :=
  Classical.choose a.property

theorem rangeCycleRepresentative_spec
    (a : LinearMap.range (H.cycleClass p)) :
    H.cycleClass p (rangeCycleRepresentative a) = a.1 :=
  Classical.choose_spec a.property

/-- If native mass kills the class kernel, it canonically descends to the
actual native cycle-class range. Independence of representatives proves the
linearity fields; no Hodge-surjectivity hypothesis is involved. -/
noncomputable def descendedNativeMass
    (hker : NativeMassKernelLawAtWeight (V := V) (H := H) (p := p)) :
    LinearMap.range (H.cycleClass p) →ₗ[ℚ] ℚ where
  toFun a := nativeCycleMass V p (rangeCycleRepresentative a)
  map_add' := by
    intro a b
    have hc : H.cycleClass p (rangeCycleRepresentative (a + b)) =
        H.cycleClass p (rangeCycleRepresentative a + rangeCycleRepresentative b) := by
      simp [rangeCycleRepresentative_spec]
    rw [nativeMass_eq_of_class_eq hker _ _ hc, map_add]
  map_smul' := by
    intro q a
    have hc : H.cycleClass p (rangeCycleRepresentative (q • a)) =
        H.cycleClass p (q • rangeCycleRepresentative a) := by
      simp [rangeCycleRepresentative_spec]
    rw [nativeMass_eq_of_class_eq hker _ _ hc, map_smul, RingHom.id_apply]

theorem descendedNativeMass_class
    (hker : NativeMassKernelLawAtWeight (V := V) (H := H) (p := p))
    (Z : codimensionCycles V.X p) :
    descendedNativeMass hker ⟨H.cycleClass p Z, ⟨Z, rfl⟩⟩ =
      nativeCycleMass V p Z := by
  apply nativeMass_eq_of_class_eq hker
  exact rangeCycleRepresentative_spec _

theorem descendedNativeMass_unique
    (hker : NativeMassKernelLawAtWeight (V := V) (H := H) (p := p))
    (m : LinearMap.range (H.cycleClass p) →ₗ[ℚ] ℚ)
    (hm : ∀ Z : codimensionCycles V.X p,
      m ⟨H.cycleClass p Z, ⟨Z, rfl⟩⟩ = nativeCycleMass V p Z) :
    m = descendedNativeMass hker := by
  apply LinearMap.ext
  intro a
  let Z := rangeCycleRepresentative a
  have ha : (⟨H.cycleClass p Z, ⟨Z, rfl⟩⟩ :
      LinearMap.range (H.cycleClass p)) = a := by
    apply Subtype.ext
    exact rangeCycleRepresentative_spec a
  rw [← ha, hm Z, descendedNativeMass_class hker Z]

/-- This is a characterization of the kernel law, not an assumed mass bridge. -/
theorem nativeMassKernelLaw_iff_range_factorization :
    NativeMassKernelLawAtWeight (V := V) (H := H) (p := p) ↔
    ∃ m : LinearMap.range (H.cycleClass p) →ₗ[ℚ] ℚ,
      ∀ Z : codimensionCycles V.X p,
        m ⟨H.cycleClass p Z, ⟨Z, rfl⟩⟩ = nativeCycleMass V p Z := by
  constructor
  · intro hker
    exact ⟨descendedNativeMass hker, descendedNativeMass_class hker⟩
  · rintro ⟨m, hm⟩ K hK
    have hz : (⟨H.cycleClass p K, ⟨K, rfl⟩⟩ :
        LinearMap.range (H.cycleClass p)) = 0 := by
      apply Subtype.ext
      exact hK
    rw [← hm K, hz, map_zero]

/-- In the kernel-law branch, landing is controlled by the descended scalar
on the actual class; no representative change can repair a mismatch. -/
theorem exists_defectZero_face_iff_descended_mass
    (i₀ : ClassicalHodgeBasisIndex V H p)
    (x₀ : CodimensionPoint V.X p)
    (hker : NativeMassKernelLawAtWeight (V := V) (H := H) (p := p))
    (alpha : ClassicalHodgeFiber V H p)
    (halg : alpha.1 ∈ LinearMap.range (H.cycleClass p)) :
    (∃ Φ : FiberedNativeAddress V H p,
      fiberedHodgeClass (V := V) (H := H) (p := p) Φ = alpha ∧
      fiberedCycleClassDefect (V := V) (H := H) (p := p) Φ = 0) ↔
    descendedNativeMass hker ⟨alpha.1, halg⟩ =
      classicalHodgeMass V H p alpha := by
  rw [exists_defectZero_face_iff_balanced_cycle i₀ x₀ alpha]
  constructor
  · rintro ⟨Z, hZ, hm⟩
    have ha : (⟨H.cycleClass p Z, ⟨Z, rfl⟩⟩ :
        LinearMap.range (H.cycleClass p)) = ⟨alpha.1, halg⟩ := by
      apply Subtype.ext
      exact hZ
    rw [← ha, descendedNativeMass_class hker Z, hm]
  · intro hm
    exact ⟨rangeCycleRepresentative ⟨alpha.1, halg⟩,
      rangeCycleRepresentative_spec _, hm⟩

/-- **EXACT UNCONDITIONAL LANDING CLASSIFICATION.** For any prescribed Hodge
face, zero-defect landing requires its actual algebraicity. The scalar
condition is either freely repairable along the class kernel, or is the same
for every representative of that class. Both directions are derived here. -/
theorem exists_defectZero_face_iff_kernel_alternatives
    (i₀ : ClassicalHodgeBasisIndex V H p)
    (x₀ : CodimensionPoint V.X p)
    (alpha : ClassicalHodgeFiber V H p) :
    (∃ Φ : FiberedNativeAddress V H p,
      fiberedHodgeClass (V := V) (H := H) (p := p) Φ = alpha ∧
      fiberedCycleClassDefect (V := V) (H := H) (p := p) Φ = 0) ↔
    (alpha.1 ∈ LinearMap.range (H.cycleClass p) ∧
      (¬ NativeMassKernelLawAtWeight (V := V) (H := H) (p := p) ∨
        ∀ Z : codimensionCycles V.X p,
          H.cycleClass p Z = alpha.1 →
          nativeCycleMass V p Z = classicalHodgeMass V H p alpha)) := by
  classical
  constructor
  · intro hland
    obtain ⟨Z, hZ, hm⟩ :=
      (exists_defectZero_face_iff_balanced_cycle i₀ x₀ alpha).1 hland
    refine ⟨⟨Z, hZ⟩, ?_⟩
    by_cases hker : NativeMassKernelLawAtWeight (V := V) (H := H) (p := p)
    · right
      intro W hW
      rw [nativeMass_eq_of_class_eq hker W Z (hW.trans hZ.symm), hm]
    · exact Or.inl hker
  · rintro ⟨halg, hcase⟩
    rcases hcase with hnonker | hall
    · have hK : ∃ K : codimensionCycles V.X p,
          H.cycleClass p K = 0 ∧ nativeCycleMass V p K ≠ 0 := by
        by_contra hn
        apply hnonker
        intro K hz
        by_contra hm
        exact hn ⟨K, hz, hm⟩
      obtain ⟨K, hz, hm⟩ := hK
      exact (exists_defectZero_face_iff_class_representative
        i₀ x₀ K hz hm alpha).2 halg
    · obtain ⟨Z, hZ⟩ := halg
      exact (exists_defectZero_face_iff_balanced_cycle i₀ x₀ alpha).2
        ⟨Z, hZ, hall Z hZ⟩

#print axioms calibratedRepresentative_retarget
#print axioms calibratedJointRepresentative_defect
#print axioms nativeMassKernelLaw_iff_range_factorization
#print axioms exists_defectZero_face_iff_kernel_alternatives

/-! ## Linear repaired transport on the full joint universe

An actual cycle-natural operator already determines which native classes it
can transport.  Rebuilding the joint state from that transported native cycle
and its transported Hodge face removes the presentation-level mismatch.
The resulting defect is exactly the ambient image of the old defect.
Nothing here constructs a missing geometric operator or a new target sheet.
-/

theorem jointRepresentative_add
    (i₀ : ClassicalHodgeBasisIndex V H p)
    (x₀ : CodimensionPoint V.X p)
    (alpha beta : ClassicalHodgeFiber V H p)
    (Z W : codimensionCycles V.X p) :
    jointRepresentative i₀ x₀ (alpha + beta) (Z + W) =
      jointRepresentative i₀ x₀ alpha Z + jointRepresentative i₀ x₀ beta W := by
  letI : CompactSpace V.X := smoothProjectiveCompactSpace V
  simp only [jointRepresentative, glueMarginals, map_add, add_smul]
  abel

theorem jointRepresentative_smul
    (i₀ : ClassicalHodgeBasisIndex V H p)
    (x₀ : CodimensionPoint V.X p) (q : ℚ)
    (alpha : ClassicalHodgeFiber V H p)
    (Z : codimensionCycles V.X p) :
    jointRepresentative i₀ x₀ (q • alpha) (q • Z) =
      q • jointRepresentative i₀ x₀ alpha Z := by
  letI : CompactSpace V.X := smoothProjectiveCompactSpace V
  simp [jointRepresentative, glueMarginals, smul_add, smul_sub, smul_smul]

theorem calibratedJointRepresentative_add
    (i₀ : ClassicalHodgeBasisIndex V H p)
    (x₀ : CodimensionPoint V.X p)
    (K : codimensionCycles V.X p)
    (alpha beta : ClassicalHodgeFiber V H p)
    (Z W : codimensionCycles V.X p) :
    calibratedJointRepresentative i₀ x₀ K (alpha + beta) (Z + W) =
      calibratedJointRepresentative i₀ x₀ K alpha Z +
        calibratedJointRepresentative i₀ x₀ K beta W := by
  rw [calibratedJointRepresentative, calibratedRepresentative_add,
    jointRepresentative_add]
  rfl

theorem calibratedJointRepresentative_smul
    (i₀ : ClassicalHodgeBasisIndex V H p)
    (x₀ : CodimensionPoint V.X p)
    (K : codimensionCycles V.X p) (q : ℚ)
    (alpha : ClassicalHodgeFiber V H p)
    (Z : codimensionCycles V.X p) :
    calibratedJointRepresentative i₀ x₀ K (q • alpha) (q • Z) =
      q • calibratedJointRepresentative i₀ x₀ K alpha Z := by
  rw [calibratedJointRepresentative, calibratedRepresentative_smul,
    jointRepresentative_smul]
  rfl

/-- Explicit linear transport with synchronized Hodge/native faces.
The two operator arguments are genuine actions; their compatibility is used
in the theorem below, rather than baked into a conclusion-shaped axiom. -/
noncomputable def repairedNativeTransport
    (i₀ : ClassicalHodgeBasisIndex V H p)
    (x₀ : CodimensionPoint V.X p)
    (K : codimensionCycles V.X p)
    (A : Module.End ℚ (codimensionCycles V.X p))
    (B : Module.End ℚ (ClassicalHodgeFiber V H p)) :
    Module.End ℚ (FiberedNativeAddress V H p) where
  toFun Φ := calibratedJointRepresentative i₀ x₀ K
    (B (fiberedHodgeClass (V := V) (H := H) (p := p) Φ))
    (A (toNativeCycle V H p Φ))
  map_add' := by
    intro Φ Ψ
    simp only [map_add]
    exact calibratedJointRepresentative_add i₀ x₀ K _ _ _ _
  map_smul' := by
    intro q Φ
    simp only [map_smul]
    exact calibratedJointRepresentative_smul i₀ x₀ K q _ _

theorem repairedNativeTransport_nativeFace
    (i₀ : ClassicalHodgeBasisIndex V H p)
    (x₀ : CodimensionPoint V.X p)
    (K : codimensionCycles V.X p)
    (A : Module.End ℚ (codimensionCycles V.X p))
    (B : Module.End ℚ (ClassicalHodgeFiber V H p))
    (Φ : FiberedNativeAddress V H p) :
    toNativeCycle V H p (repairedNativeTransport i₀ x₀ K A B Φ) =
      calibratedRepresentative K
        (B (fiberedHodgeClass (V := V) (H := H) (p := p) Φ))
        (A (toNativeCycle V H p Φ)) :=
  calibratedJointRepresentative_nativeFace i₀ x₀ K _ _

theorem repairedNativeTransport_hodgeFace
    (i₀ : ClassicalHodgeBasisIndex V H p)
    (x₀ : CodimensionPoint V.X p)
    (K : codimensionCycles V.X p)
    (hKmass : nativeCycleMass V p K ≠ 0)
    (A : Module.End ℚ (codimensionCycles V.X p))
    (B : Module.End ℚ (ClassicalHodgeFiber V H p))
    (Φ : FiberedNativeAddress V H p) :
    fiberedHodgeClass (V := V) (H := H) (p := p)
        (repairedNativeTransport i₀ x₀ K A B Φ) =
      B (fiberedHodgeClass (V := V) (H := H) (p := p) Φ) :=
  calibratedJointRepresentative_hodgeFace i₀ x₀ K hKmass _ _

theorem repairedNativeTransport_nativeClass
    (i₀ : ClassicalHodgeBasisIndex V H p)
    (x₀ : CodimensionPoint V.X p)
    (K : codimensionCycles V.X p)
    (hKclass : H.cycleClass p K = 0)
    (A : Module.End ℚ (codimensionCycles V.X p))
    (B : Module.End ℚ (ClassicalHodgeFiber V H p))
    (Φ : FiberedNativeAddress V H p) :
    H.cycleClass p (toNativeCycle V H p
        (repairedNativeTransport i₀ x₀ K A B Φ)) =
      H.cycleClass p (A (toNativeCycle V H p Φ)) := by
  rw [repairedNativeTransport_nativeFace, calibratedRepresentative_class K hKclass]

/-- **REPAIRED FULL-STATE DEFECT EQUIVARIANCE.** Every genuine cycle-natural
operator preserving the Hodge fiber has an explicit mass-calibrated lift.
No point-transition scalar or sheetwise tensor intertwiner is required. -/
theorem repairedNativeTransport_defect
    (i₀ : ClassicalHodgeBasisIndex V H p)
    (x₀ : CodimensionPoint V.X p)
    (K : codimensionCycles V.X p)
    (hKclass : H.cycleClass p K = 0)
    (hKmass : nativeCycleMass V p K ≠ 0)
    (T : CycleClassOperatorPair V H p)
    (B : Module.End ℚ (ClassicalHodgeFiber V H p))
    (hB : ∀ alpha : ClassicalHodgeFiber V H p,
      T.cohomologyOperator alpha.1 = (B alpha).1)
    (Φ : FiberedNativeAddress V H p) :
    fiberedCycleClassDefect (V := V) (H := H) (p := p)
        (repairedNativeTransport i₀ x₀ K T.cycleOperator B Φ) =
      T.cohomologyOperator
        (fiberedCycleClassDefect (V := V) (H := H) (p := p) Φ) := by
  change fiberedCycleClassDefect (V := V) (H := H) (p := p)
      (calibratedJointRepresentative i₀ x₀ K
        (B (fiberedHodgeClass (V := V) (H := H) (p := p) Φ))
        (T.cycleOperator (toNativeCycle V H p Φ))) = _
  rw [calibratedJointRepresentative_defect i₀ x₀ K hKclass hKmass,
    T.cycleClass_cycleOperator, ← hB]
  change T.cohomologyOperator (H.cycleClass p (toNativeCycle V H p Φ)) -
      T.cohomologyOperator
        (fiberedHodgeClass (V := V) (H := H) (p := p) Φ).1 =
    T.cohomologyOperator
      (H.cycleClass p (toNativeCycle V H p Φ) -
        (fiberedHodgeClass (V := V) (H := H) (p := p) Φ).1)
  exact (T.cohomologyOperator.map_sub _ _).symm

theorem repairedNativeTransport_preserves_zeroDefect
    (i₀ : ClassicalHodgeBasisIndex V H p)
    (x₀ : CodimensionPoint V.X p)
    (K : codimensionCycles V.X p)
    (hKclass : H.cycleClass p K = 0)
    (hKmass : nativeCycleMass V p K ≠ 0)
    (T : CycleClassOperatorPair V H p)
    (B : Module.End ℚ (ClassicalHodgeFiber V H p))
    (hB : ∀ alpha : ClassicalHodgeFiber V H p,
      T.cohomologyOperator alpha.1 = (B alpha).1)
    (Φ : FiberedNativeAddress V H p)
    (hΦ : fiberedCycleClassDefect (V := V) (H := H) (p := p) Φ = 0) :
    fiberedCycleClassDefect (V := V) (H := H) (p := p)
        (repairedNativeTransport i₀ x₀ K T.cycleOperator B Φ) = 0 := by
  rw [repairedNativeTransport_defect i₀ x₀ K hKclass hKmass T B hB Φ,
    hΦ, map_zero]

/-- The identity repair is exactly the anchored two-marginal normalization.
Mass balance of every existing joint state makes its calibration coefficient
zero; this proves an operator identity, not a new compatibility assumption. -/
theorem repairedNativeTransport_id
    (i₀ : ClassicalHodgeBasisIndex V H p)
    (x₀ : CodimensionPoint V.X p)
    (K : codimensionCycles V.X p)
    (hKmass : nativeCycleMass V p K ≠ 0) :
    repairedNativeTransport i₀ x₀ K LinearMap.id LinearMap.id =
      anchoredNormalization V H p i₀ x₀ := by
  apply LinearMap.ext
  intro Φ
  change jointRepresentative i₀ x₀
      (fiberedHodgeClass (V := V) (H := H) (p := p) Φ)
      (calibratedRepresentative K
        (fiberedHodgeClass (V := V) (H := H) (p := p) Φ)
        (toNativeCycle V H p Φ)) = _
  rw [(calibratedRepresentative_eq_self_iff K hKmass _ _).2
    (fiberedFaces_mass_balance Φ)]
  letI : CompactSpace V.X := smoothProjectiveCompactSpace V
  have hh : (classicalHodgeBasis V H p).repr
      (fiberedHodgeClass (V := V) (H := H) (p := p) Φ) =
      forgetPoint V H p Φ := by simp [fiberedHodgeClass]
  change glueMarginals V H p i₀ x₀
      ((classicalHodgeBasis V H p).repr
        (fiberedHodgeClass (V := V) (H := H) (p := p) Φ))
      (presentationOfNativeCycle V.X p
        (realizeFiniteCodimensionPresentation V.X p (forgetMultiplicity V H p Φ))) = _
  rw [hh, presentationOfNativeCycle_realize]
  rfl

/-- Every identity-repaired state is fixed by a second repair. -/
theorem repairedNativeTransport_id_idempotent
    (i₀ : ClassicalHodgeBasisIndex V H p)
    (x₀ : CodimensionPoint V.X p)
    (K : codimensionCycles V.X p)
    (hKmass : nativeCycleMass V p K ≠ 0)
    (Φ : FiberedNativeAddress V H p) :
    repairedNativeTransport i₀ x₀ K LinearMap.id LinearMap.id
        (repairedNativeTransport i₀ x₀ K LinearMap.id LinearMap.id Φ) =
      repairedNativeTransport i₀ x₀ K LinearMap.id LinearMap.id Φ := by
  simp only [repairedNativeTransport_id i₀ x₀ K hKmass]
  exact anchoredNormalization_idempotent V H p i₀ x₀ Φ

#print axioms repairedNativeTransport_defect
#print axioms repairedNativeTransport_preserves_zeroDefect
#print axioms repairedNativeTransport_id

end GSTClassicalHodgeKernelMassCalibration
