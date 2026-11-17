import GSTClassicalHodgeFiberedNativeProjectiveTransport
import GSTClassicalHodgeProjectiveCorrespondenceAlgebra
import GSTClassicalHodgeFiberedNativePullback

/-!
# GST CLASSICAL HODGE — FIBERED NATIVE OPERATOR LIFT

The projective-correspondence algebra acts on genuine native codimension-p
cycles.  The multiplicity-preserving pullback carries an additional classical
Hodge sheet label.  This file lifts every native operator to the pullback by
acting on the genuine point coordinate and leaving the multiplicity label
untouched.

The point normal form makes this canonical: apply the native operator to a
point cycle, take its exact finite point presentation, and relabel every target
point with the same classical sheet.

The resulting lift satisfies a strict commuting square

  toNativeCycle ∘ lift(A) = A ∘ toNativeCycle.

Thus every genuine projective correspondence operator has an exact action on
the same fibered/limitless universe used by the GST multiplicity calculus.
-/

set_option maxHeartbeats 60000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry
open scoped BigOperators

namespace GSTClassicalHodgeFiberedNativeOperatorLift

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTNativeCodimensionCyclePresentation
open GSTCompactNativeCyclePresentation
open GSTClassicalHodgePointNormalForm
open GSTClassicalHodgePointKernelOperatorLift
open GSTClassicalHodgeFiberedNativePullback
open GSTClassicalHodgeNativeCycleCosmicShadow
open GSTClassicalHodgeNativeTransferAddressIdentification
open GSTClassicalHodgeProjectiveCorrespondenceAlgebra

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- Attach one fixed classical multiplicity label to every point of a finite
native point presentation. -/
noncomputable def labelPresentation
    (i : ClassicalHodgeBasisIndex V H p) :
    FiniteCodimensionPresentation V.X p →ₗ[ℚ]
      FiberedNativeAddress V H p :=
  Finsupp.linearCombination ℚ (fun x => atom V H p i x)

@[simp]
theorem labelPresentation_single
    (i : ClassicalHodgeBasisIndex V H p)
    (x : CodimensionPoint V.X p) (q : ℚ) :
    labelPresentation i (Finsupp.single x q) =
      q • atom V H p i x := by
  classical
  simp [labelPresentation]

/-- Forgetting the label after labelling a finite presentation realizes exactly
the original native cycle. -/
theorem toNativeCycle_labelPresentation
    (i : ClassicalHodgeBasisIndex V H p)
    (φ : FiniteCodimensionPresentation V.X p) :
    toNativeCycle V H p (labelPresentation i φ) =
      realizeFiniteCodimensionPresentation V.X p φ := by
  classical
  induction φ using Finsupp.induction_linear with
  | zero => simp [labelPresentation, toNativeCycle]
  | add f g hf hg =>
      simp [hf, hg, realizeFiniteCodimensionPresentation_add]
  | single x q =>
      simp [labelPresentation_single, toNativeCycle_atom,
        realizeFiniteCodimensionPresentation_single]

/-- Canonical fibrewise lift of an arbitrary native codimension-p cycle
operator. -/
noncomputable def liftNativeOperator
    (A : Module.End ℚ (codimensionCycles V.X p)) :
    Module.End ℚ (FiberedNativeAddress V H p) :=
  Finsupp.linearCombination ℚ (fun ix =>
    labelPresentation ix.1
      (GSTClassicalHodgeProjectiveCorrespondenceAlgebra.operatorPointPresentation
        V p A ix.2))

/-- Exact action of the lifted operator on a common-refinement atom. -/
@[simp]
theorem liftNativeOperator_atom
    (A : Module.End ℚ (codimensionCycles V.X p))
    (i : ClassicalHodgeBasisIndex V H p)
    (x : CodimensionPoint V.X p) :
    liftNativeOperator A (atom V H p i x) =
      labelPresentation i
        (GSTClassicalHodgeProjectiveCorrespondenceAlgebra.operatorPointPresentation
          V p A x) := by
  classical
  simp [liftNativeOperator, atom]

/-- **STRICT NATIVE COMMUTING SQUARE.**
For every native operator, forgetting multiplicity after the fibrewise lift is
exactly the original native operator after forgetting multiplicity. -/
theorem toNativeCycle_liftNativeOperator
    (A : Module.End ℚ (codimensionCycles V.X p))
    (Φ : FiberedNativeAddress V H p) :
    toNativeCycle V H p (liftNativeOperator A Φ) =
      A (toNativeCycle V H p Φ) := by
  classical
  induction Φ using Finsupp.induction_linear with
  | zero => simp [liftNativeOperator]
  | add f g hf hg => simp [hf, hg]
  | single ix q =>
      rw [show Finsupp.single ix q = q • atom V H p ix.1 ix.2 by
        simp [atom]]
      rw [map_smul, map_smul]
      rw [liftNativeOperator_atom]
      rw [map_smul]
      rw [toNativeCycle_labelPresentation]
      rw [GSTClassicalHodgeProjectiveCorrespondenceAlgebra.operatorPointPresentation_realize]
      rw [toNativeCycle_atom]
      simp only [map_smul]

/-- Operator equality form of the strict commuting square. -/
theorem toNativeCycle_comp_liftNativeOperator
    (A : Module.End ℚ (codimensionCycles V.X p)) :
    (toNativeCycle V H p).comp (liftNativeOperator A) =
      A.comp (toNativeCycle V H p) := by
  apply LinearMap.ext
  intro Φ
  exact toNativeCycle_liftNativeOperator A Φ

/-- The identity native operator lifts to an operator whose native face is
identity. -/
theorem liftNativeOperator_id_nativeFace
    (Φ : FiberedNativeAddress V H p) :
    toNativeCycle V H p
        (liftNativeOperator
          (LinearMap.id : Module.End ℚ (codimensionCycles V.X p)) Φ) =
      toNativeCycle V H p Φ := by
  simpa using toNativeCycle_liftNativeOperator
    (V:=V) (H:=H) (p:=p)
    (LinearMap.id : Module.End ℚ (codimensionCycles V.X p)) Φ

/-- Composition of native operators is represented correctly after forgetting
the multiplicity fiber. -/
theorem liftNativeOperator_comp_nativeFace
    (A B : Module.End ℚ (codimensionCycles V.X p))
    (Φ : FiberedNativeAddress V H p) :
    toNativeCycle V H p
        (liftNativeOperator A (liftNativeOperator B Φ)) =
      (A.comp B) (toNativeCycle V H p Φ) := by
  rw [toNativeCycle_liftNativeOperator]
  rw [toNativeCycle_liftNativeOperator]
  rfl

/-- Rational linear combinations are represented correctly on the native face. -/
theorem liftNativeOperator_add_nativeFace
    (A B : Module.End ℚ (codimensionCycles V.X p))
    (Φ : FiberedNativeAddress V H p) :
    toNativeCycle V H p (liftNativeOperator (A+B) Φ) =
      A (toNativeCycle V H p Φ) + B (toNativeCycle V H p Φ) := by
  rw [toNativeCycle_liftNativeOperator]
  rfl

/-- Every projective-correspondence kernel therefore acts canonically on the
fibered pullback. -/
noncomputable def liftProjectiveKernel
    (K : ProjectiveNativeKernel V p) :
    Module.End ℚ (FiberedNativeAddress V H p) :=
  liftNativeOperator K.1

/-- Native face of one lifted projective-correspondence kernel. -/
theorem toNativeCycle_liftProjectiveKernel
    (K : ProjectiveNativeKernel V p)
    (Φ : FiberedNativeAddress V H p) :
    toNativeCycle V H p (liftProjectiveKernel K Φ) =
      K.1 (toNativeCycle V H p Φ) :=
  toNativeCycle_liftNativeOperator K.1 Φ

/-- The limitless base face of a lifted native operator is exactly the cosmic
shadow of the genuine native operator output. -/
theorem limitlessFace_liftNativeOperator
    (A : Module.End ℚ (codimensionCycles V.X p))
    (Φ : FiberedNativeAddress V H p) :
    pureWeightToUniversalAddress
      (nativeCycleCosmicShadow V p
        (toNativeCycle V H p (liftNativeOperator A Φ))) =
      pureWeightToUniversalAddress
        (nativeCycleCosmicShadow V p
          (A (toNativeCycle V H p Φ))) := by
  rw [toNativeCycle_liftNativeOperator]

/-- Crown: the entire native projective operator algebra acts on the common
fibered/limitless universe with an exact native commuting square. -/
theorem fibered_native_operator_lift_crown :
    ∀ A : Module.End ℚ (codimensionCycles V.X p),
      (toNativeCycle V H p).comp (liftNativeOperator A) =
        A.comp (toNativeCycle V H p) := by
  intro A
  exact toNativeCycle_comp_liftNativeOperator A

#check labelPresentation
#check liftNativeOperator
#check liftNativeOperator_atom
#check toNativeCycle_liftNativeOperator
#check toNativeCycle_comp_liftNativeOperator
#check liftProjectiveKernel
#check limitlessFace_liftNativeOperator
#check fibered_native_operator_lift_crown

#print axioms toNativeCycle_labelPresentation
#print axioms toNativeCycle_liftNativeOperator
#print axioms toNativeCycle_comp_liftNativeOperator
#print axioms liftNativeOperator_comp_nativeFace
#print axioms toNativeCycle_liftProjectiveKernel
#print axioms fibered_native_operator_lift_crown

/-! ## The lift is a faithful representation on the full finite state

The earlier commuting square determines only the native face.  Exact point
normal form proves the stronger identity and composition laws before either
face is forgotten.
-/

/-- Canonical labelling of an arbitrary actual cycle. -/
noncomputable def nativeCycleLabel
    (i : ClassicalHodgeBasisIndex V H p) :
    codimensionCycles V.X p →ₗ[ℚ] FiberedNativeAddress V H p := by
  letI : CompactSpace V.X := smoothProjectiveCompactSpace V
  exact (labelPresentation i).comp (presentationOfNativeCycleLinear V.X p)

@[simp] theorem nativeCycleLabel_point
    (i : ClassicalHodgeBasisIndex V H p)
    (x : CodimensionPoint V.X p) :
    nativeCycleLabel i (codimensionPointCycle V.X p x) =
      atom V H p i x := by
  letI : CompactSpace V.X := smoothProjectiveCompactSpace V
  simp [nativeCycleLabel, presentationOfNativeCycleLinear_apply,
    presentationOfNativeCycle_point]

@[simp] theorem toNativeCycle_nativeCycleLabel
    (i : ClassicalHodgeBasisIndex V H p)
    (Z : codimensionCycles V.X p) :
    toNativeCycle V H p (nativeCycleLabel i Z) = Z := by
  letI : CompactSpace V.X := smoothProjectiveCompactSpace V
  change toNativeCycle V H p
      (labelPresentation i (presentationOfNativeCycle V.X p Z)) = Z
  rw [toNativeCycle_labelPresentation, realize_presentationOfNativeCycle]

@[simp] theorem nativeCycleLabel_realize
    (i : ClassicalHodgeBasisIndex V H p)
    (φ : FiniteCodimensionPresentation V.X p) :
    nativeCycleLabel i (realizeFiniteCodimensionPresentation V.X p φ) =
      labelPresentation i φ := by
  letI : CompactSpace V.X := smoothProjectiveCompactSpace V
  change labelPresentation i
      (presentationOfNativeCycle V.X p
        (realizeFiniteCodimensionPresentation V.X p φ)) = _
  rw [presentationOfNativeCycle_realize]

theorem nativeCycleLabel_injective
    (i : ClassicalHodgeBasisIndex V H p) :
    Function.Injective (nativeCycleLabel (V := V) (H := H) (p := p) i) := by
  intro Z W h
  simpa using congrArg (toNativeCycle V H p) h

theorem liftNativeOperator_atom_as_nativeCycleLabel
    (A : Module.End ℚ (codimensionCycles V.X p))
    (i : ClassicalHodgeBasisIndex V H p)
    (x : CodimensionPoint V.X p) :
    liftNativeOperator A (atom V H p i x) =
      nativeCycleLabel i (A (codimensionPointCycle V.X p x)) := by
  letI : CompactSpace V.X := smoothProjectiveCompactSpace V
  rw [liftNativeOperator_atom]
  rfl

/-- **EXACT SINGLE-SHEET INTERTWINING.** The whole labelled state is
transported, including every coefficient of its native point presentation. -/
theorem liftNativeOperator_nativeCycleLabel
    (A : Module.End ℚ (codimensionCycles V.X p))
    (i : ClassicalHodgeBasisIndex V H p)
    (Z : codimensionCycles V.X p) :
    liftNativeOperator A (nativeCycleLabel i Z) = nativeCycleLabel i (A Z) := by
  have hmap :
      (liftNativeOperator A).comp (nativeCycleLabel i) -
        (nativeCycleLabel i).comp A = 0 := by
    apply nativeLinearMap_eq_zero_of_points V p
    intro x
    simp only [LinearMap.sub_apply, LinearMap.comp_apply,
      nativeCycleLabel_point, liftNativeOperator_atom_as_nativeCycleLabel,
      sub_self]
  have hZ := LinearMap.congr_fun hmap Z
  change liftNativeOperator A (nativeCycleLabel i Z) -
      nativeCycleLabel i (A Z) = 0 at hZ
  exact sub_eq_zero.mp hZ

theorem liftNativeOperator_labelPresentation
    (A : Module.End ℚ (codimensionCycles V.X p))
    (i : ClassicalHodgeBasisIndex V H p)
    (φ : FiniteCodimensionPresentation V.X p) :
    liftNativeOperator A (labelPresentation i φ) =
      nativeCycleLabel i (A (realizeFiniteCodimensionPresentation V.X p φ)) := by
  rw [← nativeCycleLabel_realize, liftNativeOperator_nativeCycleLabel]

/-- Identity holds on the full pullback, not only after native projection. -/
theorem liftNativeOperator_id :
    liftNativeOperator (V := V) (H := H) (p := p)
        (LinearMap.id : Module.End ℚ (codimensionCycles V.X p)) =
      LinearMap.id := by
  apply LinearMap.ext
  intro Φ
  classical
  induction Φ using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp [ha, hb]
  | single ix q =>
    rw [show Finsupp.single ix q = q • atom V H p ix.1 ix.2 by simp [atom]]
    simp only [map_smul, LinearMap.id_apply,
      liftNativeOperator_atom_as_nativeCycleLabel, nativeCycleLabel_point]

/-- **FULL COMPOSITION LAW.** Native word evaluation and lifting commute
exactly before passing to cohomology or the limitless scalar shadow. -/
theorem liftNativeOperator_comp
    (A B : Module.End ℚ (codimensionCycles V.X p)) :
    liftNativeOperator (V := V) (H := H) (p := p) (A.comp B) =
      (liftNativeOperator A).comp (liftNativeOperator B) := by
  apply LinearMap.ext
  intro Φ
  classical
  induction Φ using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp [ha, hb]
  | single ix q =>
    rw [show Finsupp.single ix q = q • atom V H p ix.1 ix.2 by simp [atom]]
    simp only [LinearMap.comp_apply, map_smul,
      liftNativeOperator_atom_as_nativeCycleLabel,
      liftNativeOperator_nativeCycleLabel]

theorem liftNativeOperator_zero :
    liftNativeOperator (V := V) (H := H) (p := p)
        (0 : Module.End ℚ (codimensionCycles V.X p)) = 0 := by
  apply LinearMap.ext
  intro Φ
  classical
  induction Φ using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp [ha, hb]
  | single ix q =>
    rw [show Finsupp.single ix q = q • atom V H p ix.1 ix.2 by simp [atom]]
    simp only [map_smul, LinearMap.zero_apply,
      liftNativeOperator_atom_as_nativeCycleLabel, map_zero, smul_zero]

theorem liftNativeOperator_add
    (A B : Module.End ℚ (codimensionCycles V.X p)) :
    liftNativeOperator (V := V) (H := H) (p := p) (A + B) =
      liftNativeOperator A + liftNativeOperator B := by
  apply LinearMap.ext
  intro Φ
  classical
  induction Φ using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb =>
    simp [ha, hb] <;> abel
  | single ix q =>
    rw [show Finsupp.single ix q = q • atom V H p ix.1 ix.2 by simp [atom]]
    simp only [map_smul, LinearMap.add_apply,
      liftNativeOperator_atom_as_nativeCycleLabel, map_add, smul_add]

theorem liftNativeOperator_smul
    (q : ℚ) (A : Module.End ℚ (codimensionCycles V.X p)) :
    liftNativeOperator (V := V) (H := H) (p := p) (q • A) =
      q • liftNativeOperator A := by
  apply LinearMap.ext
  intro Φ
  classical
  induction Φ using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp [ha, hb, smul_add]
  | single ix r =>
    rw [show Finsupp.single ix r = r • atom V H p ix.1 ix.2 by simp [atom]]
    simp only [map_smul, LinearMap.smul_apply,
      liftNativeOperator_atom_as_nativeCycleLabel, RingHom.id_apply]

/-- A populated multiplicity fiber makes the native representation faithful. -/
theorem liftNativeOperator_injective
    (i : ClassicalHodgeBasisIndex V H p) :
    Function.Injective
      (liftNativeOperator (V := V) (H := H) (p := p)) := by
  intro A B h
  apply LinearMap.ext
  intro Z
  have hZ := LinearMap.congr_fun h (nativeCycleLabel i Z)
  have hn := congrArg (toNativeCycle V H p) hZ
  simpa only [toNativeCycle_liftNativeOperator,
    toNativeCycle_nativeCycleLabel] using hn

#print axioms liftNativeOperator_comp
#print axioms liftNativeOperator_injective

end GSTClassicalHodgeFiberedNativeOperatorLift
