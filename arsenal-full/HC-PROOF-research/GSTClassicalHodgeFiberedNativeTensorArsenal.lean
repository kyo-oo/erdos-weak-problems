import GSTClassicalHodgeFiberedNativeOperatorLift
import GSTClassicalHodgeLimitlessCosmicMatrixUnits
import GSTClassicalHodgeRankFreeArsenalIrreducibility
import GSTClassicalHodgeFiberedTransferCompletion

/-!
# GST CLASSICAL HODGE — FIBERED NATIVE TENSOR ARSENAL

The common-refinement universe has two genuinely independent coordinates:

* a classical Hodge multiplicity label `i`;
* a genuine codimension-p projective point `x`.

The full operator algebra therefore has two commuting factors.

1. **Multiplicity matrix units** read one Hodge-fiber label and rewrite it as
   another label while leaving the native point untouched.
2. **Native correspondence operators** act on the projective point/cycle
   coordinate through exact finite point normal form while leaving the Hodge
   label untouched.

These factors commute on every atom and hence on every finite state.  The
result is the natural tensor-product architecture demanded by arbitrary Hodge
multiplicity: limitless GST sheet algebra on one axis, genuine projective
correspondence algebra on the other.
-/

set_option maxHeartbeats 60000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry
open scoped BigOperators

namespace GSTClassicalHodgeFiberedNativeTensorArsenal

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeFiberedNativePullback
open GSTClassicalHodgeFiberedNativeOperatorLift
open GSTClassicalHodgeNativeCycleCosmicShadow
open GSTClassicalHodgeNativeTransferAddressIdentification
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTNativeCodimensionCyclePresentation
open GSTClassicalHodgeFiberedTransferCompletion
open scoped Classical

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- Matrix unit on the fixed-weight multiplicity coordinate of the pullback.
It leaves every genuine native point untouched.  Built by the same
`Finsupp.linearCombination` carrier as the green `labelPresentation` lift,
so linearity is structural and only the labelled atom behaviour is proved. -/
noncomputable def multiplicityMatrixUnit
    (i j : ClassicalHodgeBasisIndex V H p) :
    Module.End ℚ (FiberedNativeAddress V H p) :=
  Finsupp.linearCombination ℚ
    (fun kx : FiberedNativeAtom V H p => if kx.1 = i then atom V H p j kx.2 else 0)

@[simp]
theorem multiplicityMatrixUnit_atom_source
    (i j : ClassicalHodgeBasisIndex V H p)
    (x : CodimensionPoint V.X p) :
    multiplicityMatrixUnit i j (atom V H p i x) =
      atom V H p j x := by
  classical
  simp [multiplicityMatrixUnit, atom]

@[simp]
theorem multiplicityMatrixUnit_atom_other
    (i j k : ClassicalHodgeBasisIndex V H p)
    (hki : k ≠ i)
    (x : CodimensionPoint V.X p) :
    multiplicityMatrixUnit i j (atom V H p k x) = 0 := by
  classical
  simp [multiplicityMatrixUnit, atom, hki]

/-- Fixed-weight coordinate matrix unit on the pure classical multiplicity
address `i ->₀ Q`. -/
noncomputable def multiplicityAddressMatrixUnit
    (i j : ClassicalHodgeBasisIndex V H p) :
    Module.End ℚ (ClassicalHodgeBasisIndex V H p →₀ ℚ) where
  toFun a := Finsupp.single j (a i)
  map_add' := by intro a b; ext k; simp
  map_smul' := by intro q a; ext k; simp

/-- Forgetting the native point intertwines the pullback matrix unit with the
ordinary matrix unit on Hodge multiplicity coordinates. -/
theorem forgetPoint_multiplicityMatrixUnit
    (i j : ClassicalHodgeBasisIndex V H p)
    (Φ : FiberedNativeAddress V H p) :
    forgetPoint V H p (multiplicityMatrixUnit i j Φ) =
      multiplicityAddressMatrixUnit i j (forgetPoint V H p Φ) := by
  classical
  induction Φ using Finsupp.induction_linear with
  | zero => simp [multiplicityMatrixUnit, multiplicityAddressMatrixUnit]
  | add f g hf hg => simp only [map_add, hf, hg]
  | single kx q =>
      rw [show Finsupp.single kx q = q • atom V H p kx.1 kx.2 by simp [atom]]
      simp only [map_smul]
      by_cases hki : kx.1 = i
      · rw [hki, multiplicityMatrixUnit_atom_source]
        simp [forgetPoint_atom, multiplicityAddressMatrixUnit, smul_smul]
      · rw [multiplicityMatrixUnit_atom_other i j kx.1 hki]
        simp [multiplicityAddressMatrixUnit, Finsupp.single_apply,
          if_neg hki, map_zero]

/-- Pullback multiplicity matrix units satisfy the exact matrix-unit
composition law. -/
theorem multiplicityMatrixUnit_comp
    (i j k : ClassicalHodgeBasisIndex V H p) :
    (multiplicityMatrixUnit j k).comp (multiplicityMatrixUnit i j) =
      multiplicityMatrixUnit i k := by
  apply LinearMap.ext
  intro Φ
  classical
  induction Φ using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | single lx q =>
      rw [show Finsupp.single lx q = q • atom V H p lx.1 lx.2 by simp [atom]]
      simp only [map_smul]
      by_cases hli : lx.1 = i
      · rw [hli]
        simp only [LinearMap.comp_apply, multiplicityMatrixUnit_atom_source]
      · simp only [LinearMap.comp_apply, multiplicityMatrixUnit_atom_other i j lx.1 hli,
          multiplicityMatrixUnit_atom_other i k lx.1 hli, map_zero, smul_zero]

/-- Mismatched intermediate labels annihilate exactly. -/
theorem multiplicityMatrixUnit_comp_zero
    (i j k l : ClassicalHodgeBasisIndex V H p)
    (hjk : j ≠ k) :
    (multiplicityMatrixUnit k l).comp (multiplicityMatrixUnit i j) = 0 := by
  apply LinearMap.ext
  intro Φ
  classical
  induction Φ using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | single mx q =>
      rw [show Finsupp.single mx q = q • atom V H p mx.1 mx.2 by simp [atom]]
      simp only [map_smul]
      by_cases hmi : mx.1 = i
      · rw [hmi]
        simp only [LinearMap.comp_apply, multiplicityMatrixUnit_atom_source,
          multiplicityMatrixUnit_atom_other k l j hjk,
          LinearMap.zero_apply, smul_zero]
      · simp only [LinearMap.comp_apply, multiplicityMatrixUnit_atom_other i j mx.1 hmi,
          map_zero, LinearMap.zero_apply, smul_zero]

/-- The diagonal matrix unit is the exact multiplicity projector. -/
def multiplicityProjector
    (i : ClassicalHodgeBasisIndex V H p) :
    Module.End ℚ (FiberedNativeAddress V H p) :=
  multiplicityMatrixUnit i i

@[simp]
theorem multiplicityProjector_atom_self
    (i : ClassicalHodgeBasisIndex V H p)
    (x : CodimensionPoint V.X p) :
    multiplicityProjector i (atom V H p i x) = atom V H p i x := by
  simp [multiplicityProjector]

@[simp]
theorem multiplicityProjector_atom_other
    (i k : ClassicalHodgeBasisIndex V H p)
    (hki : k ≠ i)
    (x : CodimensionPoint V.X p) :
    multiplicityProjector i (atom V H p k x) = 0 := by
  simp [multiplicityProjector, multiplicityMatrixUnit_atom_other, hki]

/-- The matrix unit relabels an entire labelled presentation.  This is the
naturality bridge used by the tensor-commutation law. -/
theorem multiplicityMatrixUnit_labelPresentation
    (i j : ClassicalHodgeBasisIndex V H p)
    (φ : FiniteCodimensionPresentation V.X p) :
    multiplicityMatrixUnit i j (labelPresentation i φ) =
      labelPresentation j φ := by
  classical
  induction φ using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | single x q =>
      simp only [labelPresentation_single, map_smul,
        multiplicityMatrixUnit_atom_source]

/-- A mismatched labelled presentation is annihilated. -/
theorem multiplicityMatrixUnit_labelPresentation_other
    (i j k : ClassicalHodgeBasisIndex V H p) (hki : k ≠ i)
    (φ : FiniteCodimensionPresentation V.X p) :
    multiplicityMatrixUnit i j (labelPresentation k φ) = 0 := by
  classical
  induction φ using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg, map_zero, add_zero, zero_add]
  | single x q =>
      simp only [labelPresentation_single, map_smul,
        multiplicityMatrixUnit_atom_other i j k hki, smul_zero, map_zero]

/-- **TENSOR COMMUTATION LAW.**
Multiplicity matrix units and arbitrary lifted native cycle operators commute
exactly because they act on independent coordinates of the common pullback. -/
theorem multiplicityMatrixUnit_commutes_liftNativeOperator
    (i j : ClassicalHodgeBasisIndex V H p)
    (A : Module.End ℚ (codimensionCycles V.X p)) :
    (multiplicityMatrixUnit i j).comp (liftNativeOperator A) =
      (liftNativeOperator A).comp (multiplicityMatrixUnit i j) := by
  apply LinearMap.ext
  intro Φ
  classical
  induction Φ using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | single kx q =>
      rw [show Finsupp.single kx q = q • atom V H p kx.1 kx.2 by simp [atom]]
      simp only [map_smul, LinearMap.comp_apply]
      rw [liftNativeOperator_atom]
      by_cases hki : kx.1 = i
      · rw [hki, multiplicityMatrixUnit_labelPresentation,
          multiplicityMatrixUnit_atom_source, liftNativeOperator_atom]
      · rw [multiplicityMatrixUnit_labelPresentation_other i j kx.1 hki,
          multiplicityMatrixUnit_atom_other i j kx.1 hki, map_zero, smul_zero]

/-- Consequently every multiplicity matrix unit commutes with every actual
projective-correspondence kernel lifted to the pullback. -/
theorem multiplicityMatrixUnit_commutes_projectiveKernel
    (i j : ClassicalHodgeBasisIndex V H p)
    (K : GSTClassicalHodgeProjectiveCorrespondenceAlgebra.ProjectiveNativeKernel V p) :
    (multiplicityMatrixUnit i j).comp (liftProjectiveKernel K) =
      (liftProjectiveKernel K).comp (multiplicityMatrixUnit i j) :=
  multiplicityMatrixUnit_commutes_liftNativeOperator i j K.operator

/-- Tensor word: first apply one genuine native operator, then one unrestricted
Hodge multiplicity matrix unit.  By commutation the order is irrelevant. -/
noncomputable def tensorWord
    (i j : ClassicalHodgeBasisIndex V H p)
    (A : Module.End ℚ (codimensionCycles V.X p)) :
    Module.End ℚ (FiberedNativeAddress V H p) :=
  (multiplicityMatrixUnit i j).comp (liftNativeOperator A)

/-- Exact tensor-word action on an atom in the source multiplicity sheet. -/
theorem tensorWord_atom_source
    (i j : ClassicalHodgeBasisIndex V H p)
    (A : Module.End ℚ (codimensionCycles V.X p))
    (x : CodimensionPoint V.X p) :
    tensorWord i j A (atom V H p i x) =
      labelPresentation j
        (GSTClassicalHodgeProjectiveCorrespondenceAlgebra.operatorPointPresentation
          V p A x) := by
  rw [tensorWord]
  simp only [LinearMap.comp_apply, liftNativeOperator_atom]
  exact multiplicityMatrixUnit_labelPresentation i j _

/-- Native face of a tensor word is the native operator applied to the selected
source multiplicity slice. -/
theorem tensorWord_nativeFace_atom_source
    (i j : ClassicalHodgeBasisIndex V H p)
    (A : Module.End ℚ (codimensionCycles V.X p))
    (x : CodimensionPoint V.X p) :
    toNativeCycle V H p (tensorWord i j A (atom V H p i x)) =
      A (codimensionPointCycle V.X p x) := by
  rw [tensorWord_atom_source]
  rw [toNativeCycle_labelPresentation]
  exact GSTClassicalHodgeProjectiveCorrespondenceAlgebra.operatorPointPresentation_realize
    V p A x

/-- A finite native presentation placed on one multiplicity sheet becomes its
total coefficient mass times the corresponding global sheet generator. -/
theorem toGlobalHodgeAddress_labelPresentation
    (j : ClassicalHodgeBasisIndex V H p)
    (φ : FiniteCodimensionPresentation V.X p) :
    toGlobalHodgeAddress V H p (labelPresentation j φ) =
      GSTClassicalHodgeNativeCycleCosmicShadow.presentationMass φ •
        fiberedSheetGenerator V H ⟨p, j⟩ := by
  classical
  induction φ using Finsupp.induction_linear with
  | zero => simp [labelPresentation]
  | add f g hf hg => simp [hf, hg, add_smul]
  | single x q =>
      simp [labelPresentation_single,
        GSTClassicalHodgeNativeCycleCosmicShadow.presentationMass_single]

/-- Multiplicity face of the same tensor word lands entirely in the target
classical sheet j. -/
theorem tensorWord_hodgeFace_supported_at_target
    (i j : ClassicalHodgeBasisIndex V H p)
    (A : Module.End ℚ (codimensionCycles V.X p))
    (x : CodimensionPoint V.X p) :
    ∃ q : ℚ,
      toGlobalHodgeAddress V H p (tensorWord i j A (atom V H p i x)) =
        q • fiberedSheetGenerator V H ⟨p,j⟩ := by
  refine ⟨GSTClassicalHodgeNativeCycleCosmicShadow.presentationMass
      (GSTClassicalHodgeProjectiveCorrespondenceAlgebra.operatorPointPresentation
        V p A x), ?_⟩
  rw [tensorWord_atom_source]
  exact toGlobalHodgeAddress_labelPresentation j _

/-- **FIBERED NATIVE TENSOR-ARSENAL CROWN.**
The unrestricted classical multiplicity matrix-unit algebra and the genuine
native projective operator algebra act as two commuting factors on one common
limitless pullback universe. -/
theorem fibered_native_tensor_arsenal_crown :
    (∀ i j k : ClassicalHodgeBasisIndex V H p,
      (multiplicityMatrixUnit j k).comp (multiplicityMatrixUnit i j) =
        multiplicityMatrixUnit i k)
    ∧ (∀ (i j : ClassicalHodgeBasisIndex V H p)
        (A : Module.End ℚ (codimensionCycles V.X p)),
      (multiplicityMatrixUnit i j).comp (liftNativeOperator A) =
        (liftNativeOperator A).comp (multiplicityMatrixUnit i j)) := by
  exact ⟨multiplicityMatrixUnit_comp,
    multiplicityMatrixUnit_commutes_liftNativeOperator⟩

#check multiplicityMatrixUnit
#check multiplicityAddressMatrixUnit
#check forgetPoint_multiplicityMatrixUnit
#check multiplicityMatrixUnit_comp
#check multiplicityMatrixUnit_commutes_liftNativeOperator
#check tensorWord
#check tensorWord_atom_source
#check tensorWord_nativeFace_atom_source
#check fibered_native_tensor_arsenal_crown

#print axioms forgetPoint_multiplicityMatrixUnit
#print axioms multiplicityMatrixUnit_comp
#print axioms multiplicityMatrixUnit_commutes_liftNativeOperator
#print axioms tensorWord_atom_source
#print axioms tensorWord_nativeFace_atom_source
#print axioms fibered_native_tensor_arsenal_crown

/-! ## Exact descent through the native face

Commutation on the labelled universe does not by itself produce a native
operator after labels are forgotten. The following calculation determines
that descent question exactly for the tensor words constructed above.
-/

/-- Two distinct labels on the same native point differ by a native-kernel
vector. Its multiplicity information remains nonzero. -/
def sheetDifference
    (i k : ClassicalHodgeBasisIndex V H p) (x : CodimensionPoint V.X p) :
    FiberedNativeAddress V H p := atom V H p i x - atom V H p k x

@[simp] theorem sheetDifference_nativeFace
    (i k : ClassicalHodgeBasisIndex V H p) (x : CodimensionPoint V.X p) :
    toNativeCycle V H p (sheetDifference i k x) = 0 := by
  simp [sheetDifference]

theorem sheetDifference_multiplicityFace_ne_zero
    (i k : ClassicalHodgeBasisIndex V H p) (hik : i ≠ k)
    (x : CodimensionPoint V.X p) :
    forgetPoint V H p (sheetDifference i k x) ≠ 0 := by
  intro hz
  have hi := congrArg (fun a : ClassicalHodgeBasisIndex V H p →₀ ℚ => a i) hz
  simpa [sheetDifference, hik, Ne.symm hik] using hi

/-- Exact native face of an arbitrary tensor word. The selected multiplicity
slice, rather than the sum of all slices, is what feeds the native operator. -/
theorem tensorWord_nativeFace
    (i j : ClassicalHodgeBasisIndex V H p)
    (A : Module.End ℚ (codimensionCycles V.X p))
    (Φ : FiberedNativeAddress V H p) :
    toNativeCycle V H p (tensorWord i j A Φ) =
      A (toNativeCycle V H p (multiplicityMatrixUnit i j Φ)) := by
  calc
    toNativeCycle V H p (tensorWord i j A Φ) =
        toNativeCycle V H p (liftNativeOperator A (multiplicityMatrixUnit i j Φ)) :=
      congrArg (toNativeCycle V H p)
        (LinearMap.congr_fun (multiplicityMatrixUnit_commutes_liftNativeOperator i j A) Φ)
    _ = _ := toNativeCycle_liftNativeOperator A _

/-- A tensor word sends a native-kernel difference to the actual native
image of its point atom. This is the precise obstruction to descent. -/
theorem tensorWord_sheetDifference_nativeFace
    (i j k : ClassicalHodgeBasisIndex V H p) (hki : k ≠ i)
    (A : Module.End ℚ (codimensionCycles V.X p))
    (x : CodimensionPoint V.X p) :
    toNativeCycle V H p (tensorWord i j A (sheetDifference i k x)) =
      A (codimensionPointCycle V.X p x) := by
  rw [tensorWord_nativeFace]
  simp [sheetDifference, multiplicityMatrixUnit_atom_other i j k hki]

/-- With two source labels available, a tensor word factors through the
native-cycle projection exactly when its native operator is zero. Thus
arbitrary multiplicity matrix units cannot be externalized merely by their
commutation with lifted projective operators. -/
theorem tensorWord_descends_native_iff_zero
    (i j k : ClassicalHodgeBasisIndex V H p) (hki : k ≠ i)
    (A : Module.End ℚ (codimensionCycles V.X p)) :
    (∃ B : Module.End ℚ (codimensionCycles V.X p),
      (toNativeCycle V H p).comp (tensorWord i j A) =
        B.comp (toNativeCycle V H p)) ↔ A = 0 := by
  constructor
  · rintro ⟨B, hB⟩
    apply GSTClassicalHodgePointNormalForm.nativeOperator_eq_zero_of_points V p A
    intro x
    have hx := LinearMap.congr_fun hB (sheetDifference i k x)
    change toNativeCycle V H p (tensorWord i j A (sheetDifference i k x)) =
      B (toNativeCycle V H p (sheetDifference i k x)) at hx
    rw [tensorWord_sheetDifference_nativeFace i j k hki,
      sheetDifference_nativeFace, map_zero] at hx
    exact hx
  · rintro rfl
    refine ⟨0, ?_⟩
    apply LinearMap.ext
    intro Φ
    change toNativeCycle V H p (tensorWord i j 0 Φ) = 0
    rw [tensorWord_nativeFace]
    rfl

/-- The original multiplicity matrix unit itself fails to descend whenever
there are two labels and one genuine native point. -/
theorem multiplicityMatrixUnit_not_descend_native
    (i j k : ClassicalHodgeBasisIndex V H p) (hki : k ≠ i)
    (x : CodimensionPoint V.X p) :
    ¬ ∃ B : Module.End ℚ (codimensionCycles V.X p),
      (toNativeCycle V H p).comp (multiplicityMatrixUnit i j) =
        B.comp (toNativeCycle V H p) := by
  rintro ⟨B, hB⟩
  have hx := LinearMap.congr_fun hB (sheetDifference i k x)
  change toNativeCycle V H p (multiplicityMatrixUnit i j (sheetDifference i k x)) =
    B (toNativeCycle V H p (sheetDifference i k x)) at hx
  have hz : codimensionPointCycle V.X p x = 0 := by
    simpa [sheetDifference, multiplicityMatrixUnit_atom_other i j k hki] using hx
  have hm := GSTClassicalHodgeNativeCycleCosmicShadow.nativeCycleMass_point V p x
  rw [hz, map_zero] at hm
  norm_num at hm

#print axioms sheetDifference_multiplicityFace_ne_zero
#print axioms tensorWord_descends_native_iff_zero
#print axioms multiplicityMatrixUnit_not_descend_native

/-- Even descent through actual cycle class, which is weaker than native
cycle descent, forces the entire native image to be homologically zero.
This rules out obtaining a nonzero Hodge matrix-unit action merely by tensoring
an independent multiplicity rewrite with a native operator. -/
theorem tensorWord_descends_cycleClass_iff_zero
    (i j k : ClassicalHodgeBasisIndex V H p) (hki : k ≠ i)
    (A : Module.End ℚ (codimensionCycles V.X p)) :
    (∃ T : Module.End ℚ
        (GSTGeometricRealizationStage2F.RationalSingularCohomology
          H.analytification (2*p)),
      ((H.cycleClass p).comp (toNativeCycle V H p)).comp (tensorWord i j A) =
        T.comp ((H.cycleClass p).comp (toNativeCycle V H p))) ↔
      (H.cycleClass p).comp A = 0 := by
  constructor
  · rintro ⟨T, hT⟩
    apply GSTClassicalHodgePointNormalForm.nativeLinearMap_eq_zero_of_points
      V p ((H.cycleClass p).comp A)
    intro x
    have hx := LinearMap.congr_fun hT (sheetDifference i k x)
    change H.cycleClass p
        (toNativeCycle V H p (tensorWord i j A (sheetDifference i k x))) =
      T (H.cycleClass p (toNativeCycle V H p (sheetDifference i k x))) at hx
    rw [tensorWord_sheetDifference_nativeFace i j k hki,
      sheetDifference_nativeFace, map_zero, map_zero] at hx
    exact hx
  · intro hA
    refine ⟨0, ?_⟩
    apply LinearMap.ext
    intro Φ
    change H.cycleClass p (toNativeCycle V H p (tensorWord i j A Φ)) = 0
    rw [tensorWord_nativeFace]
    exact LinearMap.congr_fun hA (toNativeCycle V H p (multiplicityMatrixUnit i j Φ))

#print axioms tensorWord_descends_cycleClass_iff_zero

end GSTClassicalHodgeFiberedNativeTensorArsenal
