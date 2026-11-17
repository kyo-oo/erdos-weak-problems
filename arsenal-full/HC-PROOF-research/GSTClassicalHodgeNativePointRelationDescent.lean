import GSTClassicalHodgePointKernelOperatorLift
import Mathlib.Algebra.Module.Projective

/-!
# GST native-first finite-relation descent

Upgrade of `PointClassTransitionKernel.nativeCycleOperator_natural`:
the old theorem starts with an ambient operator T and a kernel whose point
action already matches T. Here a RAW native point-transition kernel comes
first. Preservation of finite point-class relations constructs the ambient
operator and then constructs the old transition-kernel package.

The criterion quantifies over actual finite native relations. It assumes no
target representative and no all-target algebraicity. Ambient extension is
unique on the actual cycle-class range, with no uniqueness claim outside it.
-/

noncomputable section

open AlgebraicGeometry
open GSTGeometricRealizationStage2D
open GSTNativeCodimensionCyclePresentation
open GSTCompactNativeCyclePresentation
open GSTClassicalHodgePointNormalForm
open GSTClassicalHodgePointKernelOperatorLift
open GSTClassicalHodgeGeneratorwiseAtomicStability
open GSTClassicalHodgeAtomicSpan

namespace GSTClassicalHodgeNativePointRelationDescent

universe u v
variable {X : Scheme.{u}}
variable {Coh : Type v} [AddCommGroup Coh] [Module ℚ Coh]
variable {p : Nat}

/-- Explicitly retain the class map in the kernel condition. -/
def NativeClassKernelStable
    (cl : codimensionCycles X p →ₗ[ℚ] Coh)
    (A : Module.End ℚ (codimensionCycles X p)) : Prop :=
  ∀ Z, cl Z = 0 → cl (A Z) = 0

theorem transformedClass_congr
    (cl : codimensionCycles X p →ₗ[ℚ] Coh)
    (A : Module.End ℚ (codimensionCycles X p))
    (hk : NativeClassKernelStable cl A)
    {Z W : codimensionCycles X p} (hZW : cl Z = cl W) :
    cl (A Z) = cl (A W) := by
  have hz : cl (Z - W) = 0 := by rw [map_sub, hZW, sub_self]
  have h := hk (Z - W) hz
  simp only [map_sub] at h
  exact sub_eq_zero.mp h

def classRangeRepresentative
    (cl : codimensionCycles X p →ₗ[ℚ] Coh)
    (y : LinearMap.range cl) : codimensionCycles X p := Classical.choose y.2

@[simp] theorem classRangeRepresentative_spec
    (cl : codimensionCycles X p →ₗ[ℚ] Coh) (y : LinearMap.range cl) :
    cl (classRangeRepresentative cl y) = y.1 := Classical.choose_spec y.2

/-- The action is well-defined on the actual native class range because of
kernel preservation, independently of which native preimage is chosen. -/
def nativeClassRangeAction
    (cl : codimensionCycles X p →ₗ[ℚ] Coh)
    (A : Module.End ℚ (codimensionCycles X p))
    (hk : NativeClassKernelStable cl A) : LinearMap.range cl →ₗ[ℚ] Coh where
  toFun y := cl (A (classRangeRepresentative cl y))
  map_add' := by
    intro x y
    have heq : cl (classRangeRepresentative cl (x + y)) =
        cl (classRangeRepresentative cl x + classRangeRepresentative cl y) := by simp
    calc
      cl (A (classRangeRepresentative cl (x + y))) =
          cl (A (classRangeRepresentative cl x + classRangeRepresentative cl y)) :=
        transformedClass_congr cl A hk heq
      _ = _ := by simp
  map_smul' := by
    intro q x
    have heq : cl (classRangeRepresentative cl (q • x)) =
        cl (q • classRangeRepresentative cl x) := by simp
    calc
      cl (A (classRangeRepresentative cl (q • x))) =
          cl (A (q • classRangeRepresentative cl x)) :=
        transformedClass_congr cl A hk heq
      _ = _ := by simp

/-- **CANONICAL GEOMETRIC IMAGE DYNAMICS.** A finite-relation-preserving
native operator acts on the *actual geometric cycle-class image* itself,
without choosing any ambient action on possibly nonalgebraic cohomology.
The image constraint is constructed from an actual native cycle. -/
def nativeClassRangeEnd
    (cl : codimensionCycles X p →ₗ[ℚ] Coh)
    (A : Module.End ℚ (codimensionCycles X p))
    (hk : NativeClassKernelStable cl A) : Module.End ℚ (LinearMap.range cl) where
  toFun y := ⟨nativeClassRangeAction cl A hk y,
    ⟨A (classRangeRepresentative cl y), rfl⟩⟩
  map_add' := by
    intro y z
    apply Subtype.ext
    exact (nativeClassRangeAction cl A hk).map_add y z
  map_smul' := by
    intro q y
    apply Subtype.ext
    exact (nativeClassRangeAction cl A hk).map_smul q y

/-- Naturality is forced on the full geometric image, with no selected
cohomology operator or target-cycle witness as an input. -/
theorem nativeClassRangeEnd_natural
    (cl : codimensionCycles X p →ₗ[ℚ] Coh)
    (A : Module.End ℚ (codimensionCycles X p))
    (hk : NativeClassKernelStable cl A)
    (Z : codimensionCycles X p) :
    nativeClassRangeEnd cl A hk (cl.rangeRestrict Z) =
      cl.rangeRestrict (A Z) := by
  apply Subtype.ext
  exact transformedClass_congr cl A hk
    (classRangeRepresentative_spec cl (cl.rangeRestrict Z))

/-- Relations are stable under sequential native dynamics. -/
theorem nativeClassKernelStable_comp
    (cl : codimensionCycles X p →ₗ[ℚ] Coh)
    (A B : Module.End ℚ (codimensionCycles X p))
    (hA : NativeClassKernelStable cl A)
    (hB : NativeClassKernelStable cl B) :
    NativeClassKernelStable cl (A.comp B) := by
  intro Z hZ
  exact hA (B Z) (hB Z hZ)

/-- **GEOMETRIC IMAGE REPRESENTATION LAW.** Descending a composite native
operation is the composite of its canonical actions on actual cycle classes.
This has no ambient extension or cyclic-generation assumption. -/
theorem nativeClassRangeEnd_comp
    (cl : codimensionCycles X p →ₗ[ℚ] Coh)
    (A B : Module.End ℚ (codimensionCycles X p))
    (hA : NativeClassKernelStable cl A)
    (hB : NativeClassKernelStable cl B) :
    nativeClassRangeEnd cl (A.comp B)
      (nativeClassKernelStable_comp cl A B hA hB) =
      (nativeClassRangeEnd cl A hA).comp
        (nativeClassRangeEnd cl B hB) := by
  ext y
  let Z : codimensionCycles X p := classRangeRepresentative cl y
  have hrepr : cl.rangeRestrict Z = y := by
    apply Subtype.ext
    exact classRangeRepresentative_spec cl y
  rw [← hrepr]
  simp only [LinearMap.comp_apply, nativeClassRangeEnd_natural]

/-- **EXACT KERNEL OF THE GEOMETRIC IMAGE REPRESENTATION.**
An operator becomes zero on the actual algebraic class image precisely when
ALL of its native outputs are homologically invisible.  This is a sharp
obstruction, not an extra Hodge assumption: it identifies exactly which
native operations the geometric class observation cannot distinguish. -/
theorem nativeClassRangeEnd_eq_zero_iff
    (cl : codimensionCycles X p →ₗ[ℚ] Coh)
    (A : Module.End ℚ (codimensionCycles X p))
    (hk : NativeClassKernelStable cl A) :
    nativeClassRangeEnd cl A hk = 0 ↔
      ∀ Z : codimensionCycles X p, cl (A Z) = 0 := by
  constructor
  · intro h Z
    have heval : cl.rangeRestrict (A Z) = 0 := by
      have hfun := LinearMap.congr_fun h (cl.rangeRestrict Z)
      simpa only [nativeClassRangeEnd_natural, LinearMap.zero_apply] using hfun
    have hcoe := congrArg Subtype.val heval
    change cl (A Z) = 0 at hcoe
    exact hcoe
  · intro h
    apply LinearMap.ext
    intro y
    let Z : codimensionCycles X p := classRangeRepresentative cl y
    have hrepr : cl.rangeRestrict Z = y := by
      apply Subtype.ext
      exact classRangeRepresentative_spec cl y
    rw [← hrepr]
    apply Subtype.ext
    simpa [nativeClassRangeEnd_natural, LinearMap.zero_apply,
      show (cl.rangeRestrict (A Z)).val = cl (A Z) from rfl] using h Z

/-- **ONE UNIVERSAL CLASS-IMAGE RETRACTION.** Choose a rational-linear
projection onto the actual algebraic class image ONCE, independently of the
native operator.  This fixes the ambient complement action coherently. -/
noncomputable def nativeClassRangeRetraction
    (cl : codimensionCycles X p →ₗ[ℚ] Coh) :
    Coh →ₗ[ℚ] LinearMap.range cl :=
  Classical.choose (LinearMap.exists_extend
    (LinearMap.id : Module.End ℚ (LinearMap.range cl)))

theorem nativeClassRangeRetraction_spec
    (cl : codimensionCycles X p →ₗ[ℚ] Coh) :
    (nativeClassRangeRetraction cl).comp (LinearMap.range cl).subtype =
      LinearMap.id :=
  Classical.choose_spec (LinearMap.exists_extend
    (LinearMap.id : Module.End ℚ (LinearMap.range cl)))

@[simp] theorem nativeClassRangeRetraction_range
    (cl : codimensionCycles X p →ₗ[ℚ] Coh)
    (y : LinearMap.range cl) :
    nativeClassRangeRetraction cl y.1 = y :=
  LinearMap.congr_fun (nativeClassRangeRetraction_spec cl) y

/-- **COHERENT AMBIENT DESCENT, NOT INDEPENDENT OUTPUT CHOICES.**
Every native operator uses the SAME projection onto the geometric image,
followed by its canonically descended geometric operator.  In particular,
the complementary sector is annihilated and the full ambient composition law
holds. This strengthens the original independently chosen extension. -/
def nativeAmbientAction
    (cl : codimensionCycles X p →ₗ[ℚ] Coh)
    (A : Module.End ℚ (codimensionCycles X p))
    (hk : NativeClassKernelStable cl A) : Module.End ℚ Coh :=
  ((LinearMap.range cl).subtype.comp
    (nativeClassRangeEnd cl A hk)).comp
      (nativeClassRangeRetraction cl)

/-- Canonical ambient descent agrees with actual native operations on
all genuine cycle classes, without manufacturing any new Hodge seed. -/
theorem nativeAmbientAction_natural
    (cl : codimensionCycles X p →ₗ[ℚ] Coh)
    (A : Module.End ℚ (codimensionCycles X p))
    (hk : NativeClassKernelStable cl A) (Z : codimensionCycles X p) :
    nativeAmbientAction cl A hk (cl Z) = cl (A Z) := by
  have hr : nativeClassRangeRetraction cl (cl Z) = cl.rangeRestrict Z :=
    nativeClassRangeRetraction_range cl (cl.rangeRestrict Z)
  change ((nativeClassRangeEnd cl A hk)
    (nativeClassRangeRetraction cl (cl Z))).1 = cl (A Z)
  rw [hr, nativeClassRangeEnd_natural]
  rfl

/-- **UNCONDITIONAL COMPOSITION OF ALL COHERENT AMBIENT ACTIONS.**
Kernel-preserving native operators have a full ambient composition law;
the law uses only the one fixed retraction, without assuming the Hodge
conjecture or any cyclicity/generation of nonalgebraic classes. -/
theorem nativeAmbientAction_comp
    (cl : codimensionCycles X p →ₗ[ℚ] Coh)
    (A B : Module.End ℚ (codimensionCycles X p))
    (hA : NativeClassKernelStable cl A)
    (hB : NativeClassKernelStable cl B) :
    nativeAmbientAction cl (A.comp B)
      (nativeClassKernelStable_comp cl A B hA hB) =
      (nativeAmbientAction cl A hA).comp (nativeAmbientAction cl B hB) := by
  apply LinearMap.ext
  intro z
  change
    ((nativeClassRangeEnd cl (A.comp B)
      (nativeClassKernelStable_comp cl A B hA hB))
        (nativeClassRangeRetraction cl z)).1 =
    ((nativeClassRangeEnd cl A hA)
      (nativeClassRangeRetraction cl
        (((nativeClassRangeEnd cl B hB)
          (nativeClassRangeRetraction cl z)).1))).1
  rw [nativeClassRangeRetraction_range]
  exact congrArg Subtype.val
    (LinearMap.congr_fun (nativeClassRangeEnd_comp cl A B hA hB)
      (nativeClassRangeRetraction cl z))

/-- **NO-ESCAPE INVARIANT FOR EVERY COHERENT NATIVE OPERATOR.**
Every constructed ambient action has its ENTIRE image in the genuine
cycle-class image.  Thus no amount of native composition, even at the
unrestricted ambient cohomology level, can produce a class beyond the
algebraic image without a separately constructed geometric source. -/
theorem nativeAmbientAction_range_le_classRange
    (cl : codimensionCycles X p →ₗ[ℚ] Coh)
    (A : Module.End ℚ (codimensionCycles X p))
    (hk : NativeClassKernelStable cl A) :
    LinearMap.range (nativeAmbientAction cl A hk) ≤ LinearMap.range cl := by
  rintro y ⟨x, rfl⟩
  change ((nativeClassRangeEnd cl A hk)
    (nativeClassRangeRetraction cl x)).1 ∈ LinearMap.range cl
  exact ((nativeClassRangeEnd cl A hk)
    (nativeClassRangeRetraction cl x)).2

/-- The complementary sector is invisible to the coherent extension. This
precisely localizes what the native operator algebra cannot observe. -/
theorem nativeAmbientAction_zero_of_retraction_zero
    (cl : codimensionCycles X p →ₗ[ℚ] Coh)
    (A : Module.End ℚ (codimensionCycles X p))
    (hk : NativeClassKernelStable cl A)
    (x : Coh)
    (hx : nativeClassRangeRetraction cl x = 0) :
    nativeAmbientAction cl A hk x = 0 := by
  change ((nativeClassRangeEnd cl A hk)
    (nativeClassRangeRetraction cl x)).1 = 0
  rw [hx, map_zero]
  rfl

/-- Native kernel preservation is also necessary. -/
theorem exists_nativeAmbientAction_iff
    (cl : codimensionCycles X p →ₗ[ℚ] Coh)
    (A : Module.End ℚ (codimensionCycles X p)) :
    (∃ T : Module.End ℚ Coh, cl.comp A = T.comp cl) ↔ NativeClassKernelStable cl A := by
  constructor
  · rintro ⟨T, hT⟩ Z hZ
    have h := LinearMap.congr_fun hT Z
    simpa [hZ] using h
  · intro hk
    refine ⟨nativeAmbientAction cl A hk, ?_⟩
    ext Z
    exact (nativeAmbientAction_natural cl A hk Z).symm

/-- Raw point transition: finite native output at each genuine point. -/
def rawPresentationOperator
    (κ : CodimensionPoint X p → FiniteCodimensionPresentation X p) :
    Module.End ℚ (FiniteCodimensionPresentation X p) := Finsupp.linearCombination ℚ κ

@[simp] theorem rawPresentationOperator_single
    (κ : CodimensionPoint X p → FiniteCodimensionPresentation X p)
    (x : CodimensionPoint X p) :
    rawPresentationOperator κ (Finsupp.single x 1) = κ x := by
  simp [rawPresentationOperator]

def rawNativeOperator [CompactSpace X]
    (κ : CodimensionPoint X p → FiniteCodimensionPresentation X p) :
    Module.End ℚ (codimensionCycles X p) :=
  (compactCyclePresentationLinearEquiv X p).toLinearMap.comp
    ((rawPresentationOperator κ).comp
      (compactCyclePresentationLinearEquiv X p).symm.toLinearMap)

@[simp] theorem rawNativeOperator_realize [CompactSpace X]
    (κ : CodimensionPoint X p → FiniteCodimensionPresentation X p)
    (φ : FiniteCodimensionPresentation X p) :
    rawNativeOperator κ (realizeFiniteCodimensionPresentation X p φ) =
      realizeFiniteCodimensionPresentation X p (rawPresentationOperator κ φ) := by
  simp [rawNativeOperator, presentation_realizeFiniteCodimensionPresentation]

@[simp] theorem rawNativeOperator_point [CompactSpace X]
    (κ : CodimensionPoint X p → FiniteCodimensionPresentation X p)
    (x : CodimensionPoint X p) :
    rawNativeOperator κ (codimensionPointCycle X p x) =
      realizeFiniteCodimensionPresentation X p (κ x) := by
  simp [rawNativeOperator, presentationOfNativeCycle_point]

/-- Finite class relations are preserved by the raw transition. -/
def PreservesFiniteClassRelations
    (cl : codimensionCycles X p →ₗ[ℚ] Coh)
    (κ : CodimensionPoint X p → FiniteCodimensionPresentation X p) : Prop :=
  ∀ φ : FiniteCodimensionPresentation X p,
    cl (realizeFiniteCodimensionPresentation X p φ) = 0 →
      cl (realizeFiniteCodimensionPresentation X p (rawPresentationOperator κ φ)) = 0

/-- Point relations detect exactly the genuine native kernel condition. -/
theorem finiteRelations_iff_nativeKernelStable [CompactSpace X]
    (cl : codimensionCycles X p →ₗ[ℚ] Coh)
    (κ : CodimensionPoint X p → FiniteCodimensionPresentation X p) :
    PreservesFiniteClassRelations cl κ ↔ NativeClassKernelStable cl (rawNativeOperator κ) := by
  constructor
  · intro h Z hZ
    let φ := presentationOfNativeCycle X p Z
    have hφ : realizeFiniteCodimensionPresentation X p φ = Z :=
      GSTClassicalHodgePointNormalForm.realize_presentationOfNativeCycle X p Z
    have hz := h φ (by simpa [hφ] using hZ)
    rw [← rawNativeOperator_realize, hφ] at hz
    exact hz
  · intro h φ hφ
    simpa using h (realizeFiniteCodimensionPresentation X p φ) hφ

/-- **NATIVE-FIRST ACTION SYNTHESIS.** The cohomological action is an OUTPUT
of a raw finite native transition precisely when its finite class relations
are respected. No action equation or target cycle is included as input. -/
theorem rawTransition_has_ambientAction_iff [CompactSpace X]
    (cl : codimensionCycles X p →ₗ[ℚ] Coh)
    (κ : CodimensionPoint X p → FiniteCodimensionPresentation X p) :
    (∃ T : Module.End ℚ Coh, cl.comp (rawNativeOperator κ) = T.comp cl) ↔
      PreservesFiniteClassRelations cl κ := by
  rw [exists_nativeAmbientAction_iff, finiteRelations_iff_nativeKernelStable]

/-- Upgrade the already-compiled point-kernel interface: both the ambient
action and the point action equation are now derived from raw native data. -/
def derivedPointClassTransitionKernel [CompactSpace X]
    (cl : codimensionCycles X p →ₗ[ℚ] Coh)
    (κ : CodimensionPoint X p → FiniteCodimensionPresentation X p)
    (hκ : PreservesFiniteClassRelations cl κ) :
    PointClassTransitionKernel (p := p) (cl := cl)
      (nativeAmbientAction cl (rawNativeOperator κ)
        ((finiteRelations_iff_nativeKernelStable cl κ).mp hκ)) where
  transition := κ
  transition_spec := by
    intro x
    have h := nativeAmbientAction_natural cl (rawNativeOperator κ)
      ((finiteRelations_iff_nativeKernelStable cl κ).mp hκ)
      (codimensionPointCycle X p x)
    simpa [rawNativeOperator_point, finitePointCycleClassMap_eq_cycleClass_realize]
      using h.symm

#print axioms nativeClassRangeEnd_comp
#print axioms nativeClassRangeEnd_eq_zero_iff
#print axioms nativeAmbientAction_natural
#print axioms nativeAmbientAction_comp
#print axioms nativeAmbientAction_range_le_classRange
#print axioms exists_nativeAmbientAction_iff
#print axioms finiteRelations_iff_nativeKernelStable
#print axioms rawTransition_has_ambientAction_iff
#print axioms derivedPointClassTransitionKernel

end GSTClassicalHodgeNativePointRelationDescent
