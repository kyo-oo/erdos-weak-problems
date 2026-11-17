import GSTClassicalHodgePointKernelOperatorLift
import Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic
import GSTCompactNativeCyclePresentation
import GSTClassicalHodgeGeneratorwiseAtomicStability
import GSTClassicalHodgeNativePointRelationDescent

/-!
# GST CLASSICAL HODGE — PROJECTIVE POINT TRANSPORT

This module is the first external geometric transport layer of the classical
landing.  It works with actual Mathlib schemes, actual scheme morphisms, and
actual native algebraic cycles.

Mathlib's pushforward of algebraic cycles attaches the residue-degree weight
to the image of a generic point and may be filtered by a weight function.  For
the codimension-p layer we use coheight itself as that weight.  On generators
this says exactly:

* a genuine codimension-p generic point `x` is transported to `f x` when the
  target point still has coheight p;
* its coefficient is multiplied by the residue degree of `f` at `x`;
* if the image leaves codimension p, the codimension-p component is zero.

The free finite-presentation module lets us extend this point transport
linearly, and the compact/projective normal form then extends it to every
native codimension-p cycle on a smooth projective scheme.

No cohomological surjectivity or Hodge conclusion appears here.  This is a
pure native-cycle transport construction.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000000

noncomputable section

open CategoryTheory
open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTClassicalHodgePointKernelOperatorLift
open GSTClassicalHodgeAtomicSpan
open GSTNativeCodimensionCyclePresentation
open GSTCompactNativeCyclePresentation
open GSTClassicalHodgeGeneratorwiseAtomicStability

namespace GSTClassicalHodgeProjectivePointTransport

universe u v

variable {X : Scheme.{u}} {Y : Scheme.{u}}

/-- Residue-degree coefficient carried by one point under a scheme morphism. -/
noncomputable def pointResidueWeight
    (f : X ⟶ Y) (x : X) : ℚ :=
  (Scheme.Hom.residueDegree f x : ℚ)

/-- Codimension-p component of the geometric pushforward of one genuine point
cycle. -/
noncomputable def pointPushforwardPresentation
    (f : X ⟶ Y) (p : Nat)
    (x : CodimensionPoint X p) :
    FiniteCodimensionPresentation Y p := by
  classical
  by_cases hcod : Order.coheight (f x.1) = p
  · exact Finsupp.single ⟨f x.1, hcod⟩ (pointResidueWeight f x.1)
  · exact 0

/-- The point pushforward presentation is supported on exactly the geometric
image point whenever codimension is preserved. -/
theorem pointPushforwardPresentation_eq_single
    (f : X ⟶ Y) (p : Nat)
    (x : CodimensionPoint X p)
    (hcod : Order.coheight (f x.1) = p) :
    pointPushforwardPresentation f p x =
      Finsupp.single ⟨f x.1, hcod⟩ (pointResidueWeight f x.1) := by
  classical
  simp [pointPushforwardPresentation, hcod]

/-- If the geometric image leaves codimension p, the p-component vanishes. -/
theorem pointPushforwardPresentation_eq_zero
    (f : X ⟶ Y) (p : Nat)
    (x : CodimensionPoint X p)
    (hcod : Order.coheight (f x.1) ≠ p) :
    pointPushforwardPresentation f p x = 0 := by
  classical
  simp [pointPushforwardPresentation, hcod]

/-- Linear extension of the geometric point transport to arbitrary finite
codimension-p presentations. -/
noncomputable def pushforwardPresentation
    (f : X ⟶ Y) (p : Nat) :
    FiniteCodimensionPresentation X p →ₗ[ℚ]
      FiniteCodimensionPresentation Y p where
  toFun φ := φ.sum fun x q => q • pointPushforwardPresentation f p x
  map_add' := by
    intro φ ψ
    classical
    rw [Finsupp.sum_add_index']
    · intro i; simp
    · intro i b₁ b₂; simp [add_smul]
  map_smul' := by
    intro q φ
    classical
    rw [RingHom.id_apply]
    first
    | rw [Finsupp.sum_smul_index]
      intro i
      simp
    | by_cases hq : q = 0
      · subst q
        simp
      · have hsup : (q • φ).support = φ.support := by
          ext a
          simp [Finsupp.mem_support_iff, mul_ne_zero_iff, hq]
        simp only [Finsupp.sum, Finsupp.smul_apply, smul_eq_mul,
          Finset.smul_sum, smul_smul]
        rw [hsup]
    | simp [Finsupp.sum, Finset.smul_sum, smul_eq_mul, smul_smul,
      RingHom.id_apply, mul_comm, mul_assoc, mul_left_comm, mul_ne_zero]

@[simp]
theorem pushforwardPresentation_single
    (f : X ⟶ Y) (p : Nat)
    (x : CodimensionPoint X p) (q : ℚ) :
    pushforwardPresentation f p (Finsupp.single x q) =
      q • pointPushforwardPresentation f p x := by
  classical
  simp [pushforwardPresentation]

/-- Realize the transported point presentation as an actual native target
codimension-p algebraic cycle. -/
noncomputable def nativePointPushforward
    (f : X ⟶ Y) (p : Nat)
    (x : CodimensionPoint X p) : codimensionCycles Y p :=
  realizeFiniteCodimensionPresentation Y p
    (pointPushforwardPresentation f p x)

/-- Native point transport has the expected single-point formula whenever
codimension is preserved. -/
theorem nativePointPushforward_eq
    (f : X ⟶ Y) (p : Nat)
    (x : CodimensionPoint X p)
    (hcod : Order.coheight (f x.1) = p) :
    nativePointPushforward f p x =
      pointResidueWeight f x.1 •
        codimensionPointCycle Y p ⟨f x.1, hcod⟩ := by
  rw [nativePointPushforward,
    pointPushforwardPresentation_eq_single f p x hcod]
  exact realizeFiniteCodimensionPresentation_single
    Y p ⟨f x.1, hcod⟩ (pointResidueWeight f x.1)

/-- Realize finite geometric transport as a native codimension-p cycle. -/
noncomputable def realizePushforwardPresentation
    (f : X ⟶ Y) (p : Nat) :
    FiniteCodimensionPresentation X p →ₗ[ℚ] codimensionCycles Y p where
  toFun φ :=
    realizeFiniteCodimensionPresentation Y p
      (pushforwardPresentation f p φ)
  map_add' := by
    intro φ ψ
    classical
    have hop : pushforwardPresentation f p (φ + ψ) =
        pushforwardPresentation f p φ +
          pushforwardPresentation f p ψ :=
      (pushforwardPresentation f p).map_add φ ψ
    rw [hop, realizeFiniteCodimensionPresentation_add]
  map_smul' := by
    intro q φ
    classical
    rw [RingHom.id_apply]
    have hop : pushforwardPresentation f p (q • φ) =
        q • pushforwardPresentation f p φ :=
      (pushforwardPresentation f p).map_smul q φ
    rw [hop, realizeFiniteCodimensionPresentation_smul]

@[simp]
theorem realizePushforwardPresentation_single
    (f : X ⟶ Y) (p : Nat)
    (x : CodimensionPoint X p) :
    realizePushforwardPresentation f p (Finsupp.single x 1) =
      nativePointPushforward f p x := by
  simp [realizePushforwardPresentation, nativePointPushforward]

/-- On a smooth projective source, every native codimension-p cycle admits a
finite point normal form, so point transport extends canonically to all native
cycles. -/
noncomputable def smoothProjectiveNativePushforward
    (V : SmoothProjectiveComplexScheme)
    (f : V.X ⟶ V.X) (p : Nat) :
    codimensionCycles V.X p →ₗ[ℚ] codimensionCycles V.X p := by
  letI : CompactSpace V.X := smoothProjectiveCompactSpace V
  exact (realizePushforwardPresentation f p).comp
    (presentationOfNativeCycleLinear V.X p)

/-- **EXACT GEOMETRIC PRESENTATION NATURALITY.**
On every finite rational codimension-p point presentation, the actual native
projective transport agrees with the explicitly computed residue-weighted
point pushforward before realization. This is a commuting square of two
constructive geometric operations, with no Hodge-generation premise. -/
noncomputable instance smoothProjectiveCompactSpace_inst
    (V : SmoothProjectiveComplexScheme) :
    CompactSpace V.X := smoothProjectiveCompactSpace V

theorem smoothProjectiveNativePushforward_realize
    (V : SmoothProjectiveComplexScheme)
    (f : V.X ⟶ V.X) (p : Nat)
    (φ : FiniteCodimensionPresentation V.X p) :
    smoothProjectiveNativePushforward V f p
      (realizeFiniteCodimensionPresentation V.X p φ) =
    realizeFiniteCodimensionPresentation V.X p
      (pushforwardPresentation f p φ) := by
  letI : CompactSpace V.X := smoothProjectiveCompactSpace V
  simp only [smoothProjectiveNativePushforward, LinearMap.comp_apply,
    presentationOfNativeCycleLinear_apply]
  rw [presentation_realizeFiniteCodimensionPresentation]
  rfl

/-- The smooth-projective native transport is determined by its action on
point-cycle generators. -/
theorem smoothProjectiveNativePushforward_point
    (V : SmoothProjectiveComplexScheme)
    (f : V.X ⟶ V.X) (p : Nat)
    (x : CodimensionPoint V.X p) :
    smoothProjectiveNativePushforward V f p
        (codimensionPointCycle V.X p x) =
      nativePointPushforward f p x := by
  letI : CompactSpace V.X := smoothProjectiveCompactSpace V
  simp only [smoothProjectiveNativePushforward, LinearMap.comp_apply,
    presentationOfNativeCycleLinear_apply, presentationOfNativeCycle_point]
  exact realizePushforwardPresentation_single f p x

/-- **PROJECTIVE TRANSPORT IS EXACTLY A RAW GEOMETRIC POINT KERNEL.**
The genuine scheme self-map produces its native operator from the actual
residue-degree action on finite codimension-point presentations.  There is
no independent cohomology action, algebraic-basis input, or Hodge premise. -/
theorem smoothProjectiveNativePushforward_eq_rawPointKernel
    (V : SmoothProjectiveComplexScheme)
    (f : V.X ⟶ V.X) (p : Nat) :
    smoothProjectiveNativePushforward V f p =
      GSTClassicalHodgeNativePointRelationDescent.rawNativeOperator
        (fun x => pointPushforwardPresentation f p x) := by
  letI : CompactSpace V.X := smoothProjectiveCompactSpace V
  have hzero :
      smoothProjectiveNativePushforward V f p -
        GSTClassicalHodgeNativePointRelationDescent.rawNativeOperator
          (fun x => pointPushforwardPresentation f p x) = 0 := by
    apply GSTClassicalHodgePointNormalForm.nativeLinearMap_eq_zero_of_points V p
    intro x
    simp only [LinearMap.sub_apply, sub_eq_zero]
    rw [smoothProjectiveNativePushforward_point,
      GSTClassicalHodgeNativePointRelationDescent.rawNativeOperator_point]
    rfl
  exact sub_eq_zero.mp hzero

/-- **EXACT EXTERNALIZATION CRITERION FOR ACTUAL PROJECTIVE MAPS.**
A genuine native projective transport admits an ambient rational-linear
cohomological action if and only if it preserves the finite relations among
actual point cycle classes.  The relation test is intrinsic and constructive;
it does NOT require prior realization of arbitrary Hodge targets. -/
theorem geometricPushforward_has_ambientAction_iff
    (V : SmoothProjectiveComplexScheme)
    (f : V.X ⟶ V.X) (p : Nat)
    {Coh : Type*} [AddCommGroup Coh] [Module ℚ Coh]
    (cl : codimensionCycles V.X p →ₗ[ℚ] Coh) :
    (∃ T : Module.End ℚ Coh,
      cl.comp (smoothProjectiveNativePushforward V f p) = T.comp cl) ↔
      GSTClassicalHodgeNativePointRelationDescent.PreservesFiniteClassRelations
        cl (fun x => pointPushforwardPresentation f p x) := by
  letI : CompactSpace V.X := smoothProjectiveCompactSpace V
  rw [smoothProjectiveNativePushforward_eq_rawPointKernel]
  exact GSTClassicalHodgeNativePointRelationDescent.rawTransition_has_ambientAction_iff
    cl (fun x => pointPushforwardPresentation f p x)

/-- The native construction, when it respects all actual point-class
relations, induces its uniquely determined action on the *geometric image*
itself. No arbitrary extension to a nonalgebraic complement is involved. -/
noncomputable def geometricPushforwardOnClassImage
    (V : SmoothProjectiveComplexScheme)
    (f : V.X ⟶ V.X) (p : Nat)
    {Coh : Type*} [AddCommGroup Coh] [Module ℚ Coh]
    (cl : codimensionCycles V.X p →ₗ[ℚ] Coh)
    (hrel : GSTClassicalHodgeNativePointRelationDescent.PreservesFiniteClassRelations
      cl (fun x => pointPushforwardPresentation f p x)) :
    Module.End ℚ (LinearMap.range cl) := by
  letI : CompactSpace V.X := smoothProjectiveCompactSpace V
  have hk : GSTClassicalHodgeNativePointRelationDescent.NativeClassKernelStable
      cl (smoothProjectiveNativePushforward V f p) := by
    rw [smoothProjectiveNativePushforward_eq_rawPointKernel]
    exact (GSTClassicalHodgeNativePointRelationDescent.finiteRelations_iff_nativeKernelStable
      cl (fun x => pointPushforwardPresentation f p x)).mp hrel
  exact GSTClassicalHodgeNativePointRelationDescent.nativeClassRangeEnd
    cl (smoothProjectiveNativePushforward V f p) hk

/-- Every genuine geometric class is transported by the canonical image
operator according to its actual finite native pushforward. -/
theorem geometricPushforwardOnClassImage_natural
    (V : SmoothProjectiveComplexScheme)
    (f : V.X ⟶ V.X) (p : Nat)
    {Coh : Type*} [AddCommGroup Coh] [Module ℚ Coh]
    (cl : codimensionCycles V.X p →ₗ[ℚ] Coh)
    (hrel : GSTClassicalHodgeNativePointRelationDescent.PreservesFiniteClassRelations
      cl (fun x => pointPushforwardPresentation f p x))
    (Z : codimensionCycles V.X p) :
    geometricPushforwardOnClassImage V f p cl hrel (cl.rangeRestrict Z) =
      cl.rangeRestrict (smoothProjectiveNativePushforward V f p Z) := by
  unfold geometricPushforwardOnClassImage
  exact GSTClassicalHodgeNativePointRelationDescent.nativeClassRangeEnd_natural
    cl (smoothProjectiveNativePushforward V f p) _ Z

/-- The native transport construction itself supplies a point-lift family for
its own point-generator action. -/
theorem nativePointPushforward_exists
    (V : SmoothProjectiveComplexScheme)
    (f : V.X ⟶ V.X) (p : Nat)
    (x : CodimensionPoint V.X p) :
    ∃ Z : codimensionCycles V.X p,
      Z = smoothProjectiveNativePushforward V f p
        (codimensionPointCycle V.X p x) := by
  exact ⟨nativePointPushforward f p x,
    (smoothProjectiveNativePushforward_point V f p x).symm⟩

#check pointResidueWeight
#check pointPushforwardPresentation
#check pushforwardPresentation
#check nativePointPushforward
#check realizePushforwardPresentation
#check smoothProjectiveNativePushforward
#check smoothProjectiveNativePushforward_point

#print axioms pointPushforwardPresentation_eq_single
#print axioms nativePointPushforward_eq
#print axioms smoothProjectiveNativePushforward_point
#print axioms smoothProjectiveNativePushforward_eq_rawPointKernel
#print axioms geometricPushforward_has_ambientAction_iff
#print axioms geometricPushforwardOnClassImage_natural

end GSTClassicalHodgeProjectivePointTransport
