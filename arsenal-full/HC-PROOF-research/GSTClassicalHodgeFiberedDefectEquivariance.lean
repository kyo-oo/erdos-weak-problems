import GSTClassicalHodgeFiberedCycleClassDefect
import GSTClassicalHodgeFiberedNativeTensorArsenal
import GSTClassicalHodgeCycleOperatorNaturality

/-!
# GST CLASSICAL HODGE — FIBERED DEFECT EQUIVARIANCE

The fibered defect is the difference between the actual cycle class of the
native face and the actual classical Hodge vector carried by the multiplicity
face.  This file proves the exact transport law for the commuting tensor
arsenal.

A genuine native cycle operator `A` comes with a cohomological realization `T`
through a cycle-class naturality square.  On one source point atom, the lifted
native operator produces a finite point presentation whose total rational mass
is an explicit scalar `m`.  The GST multiplicity matrix unit rewrites the
source Hodge label `i` to the target label `j`, carrying exactly that same
scalar `m`.

Therefore, whenever the cohomological operator sends the source Hodge basis
vector to `m` times the target basis vector, the fibered defect after the full
tensor word is exactly `T` applied to the original defect.  In particular,
defect zero propagates through every such genuine geometric/GST transport.
-/

set_option maxHeartbeats 60000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry
open scoped BigOperators

namespace GSTClassicalHodgeFiberedDefectEquivariance

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2G
open GSTNativeCodimensionCyclePresentation
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeFiberedNativePullback
open GSTClassicalHodgeFiberedNativeOperatorLift
open GSTClassicalHodgeFiberedNativeTensorArsenal
open GSTClassicalHodgeFiberedCycleClassDefect
open GSTClassicalHodgeCycleOperatorNaturality
open GSTClassicalHodgeNativeCycleCosmicShadow
open GSTClassicalHodgeProjectiveCorrespondenceAlgebra

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- Total coefficient carried by the exact finite point normal form of one
native operator applied to one genuine point atom. -/
noncomputable def pointTransitionMass
    (A : Module.End ℚ (codimensionCycles V.X p))
    (x : CodimensionPoint V.X p) : ℚ :=
  presentationMass (operatorPointPresentation V p A x)

/-- Labelling a finite point presentation by one Hodge sheet forgets back to
its total mass times that single Hodge coordinate. -/
theorem forgetPoint_labelPresentation
    (j : ClassicalHodgeBasisIndex V H p)
    (φ : FiniteCodimensionPresentation V.X p) :
    forgetPoint V H p (labelPresentation j φ) =
      presentationMass φ • Finsupp.single j 1 := by
  classical
  induction φ using Finsupp.induction_linear with
  | zero => simp [labelPresentation, presentationMass]
  | add f g hf hg => simp [hf, hg, add_smul]
  | single x q =>
      simp [labelPresentation_single, presentationMass,
        forgetPoint_atom, smul_smul]

/-- The Hodge vector encoded by a labelled native presentation is exactly its
total mass times the chosen genuine Hodge basis vector. -/
theorem fiberedHodgeClass_labelPresentation
    (j : ClassicalHodgeBasisIndex V H p)
    (φ : FiniteCodimensionPresentation V.X p) :
    fiberedHodgeClass (V := V) (H := H) (p := p)
        (labelPresentation j φ) =
      presentationMass φ • classicalHodgeBasis V H p j := by
  apply (classicalHodgeBasis V H p).repr.injective
  simp [fiberedHodgeClass, forgetPoint_labelPresentation]

/-- Exact Hodge-side action of one tensor word on a source point atom. -/
theorem fiberedHodgeClass_tensorWord_atom_source
    (i j : ClassicalHodgeBasisIndex V H p)
    (A : Module.End ℚ (codimensionCycles V.X p))
    (x : CodimensionPoint V.X p) :
    fiberedHodgeClass (V := V) (H := H) (p := p)
        (tensorWord i j A (atom V H p i x)) =
      pointTransitionMass A x • classicalHodgeBasis V H p j := by
  rw [tensorWord_atom_source]
  exact fiberedHodgeClass_labelPresentation j
    (operatorPointPresentation V p A x)

/-- A native/cohomological operator pair is a GST tensor transport from basis
sheet `i` to basis sheet `j` at a point `x` when its cohomological action on
that source sheet has exactly the scalar read from the native point
presentation. -/
def TensorIntertwinesAt
    (T : CycleClassOperatorPair V H p)
    (i j : ClassicalHodgeBasisIndex V H p)
    (x : CodimensionPoint V.X p) : Prop :=
  T.cohomologyOperator (classicalHodgeBasis V H p i).1 =
    pointTransitionMass T.cycleOperator x •
      (classicalHodgeBasis V H p j).1

/-- **FIBERED DEFECT EQUIVARIANCE ON A GENERATOR.**
For a genuine cycle-natural tensor transport, the new defect is precisely the
cohomological image of the old defect. -/
theorem defect_tensorWord_atom_eq_map
    (T : CycleClassOperatorPair V H p)
    (i j : ClassicalHodgeBasisIndex V H p)
    (x : CodimensionPoint V.X p)
    (hT : TensorIntertwinesAt T i j x) :
    fiberedCycleClassDefect (V := V) (H := H) (p := p)
        (tensorWord i j T.cycleOperator (atom V H p i x)) =
      T.cohomologyOperator
        (fiberedCycleClassDefect (V := V) (H := H) (p := p)
          (atom V H p i x)) := by
  rw [fiberedCycleClassDefect_atom]
  unfold fiberedCycleClassDefect fiberedNativeCycleClass fiberedHodgeAmbient
  rw [LinearMap.sub_apply]
  rw [LinearMap.comp_apply, LinearMap.comp_apply]
  rw [tensorWord_nativeFace_atom_source]
  rw [fiberedHodgeClass_tensorWord_atom_source]
  rw [T.cycleClass_cycleOperator]
  rw [map_sub, hT]
  rfl

/-- Defect-zero propagates through one genuine tensor transport. -/
theorem defectZero_tensorWord_atom
    (T : CycleClassOperatorPair V H p)
    (i j : ClassicalHodgeBasisIndex V H p)
    (x : CodimensionPoint V.X p)
    (hT : TensorIntertwinesAt T i j x)
    (hzero :
      fiberedCycleClassDefect (V := V) (H := H) (p := p)
        (atom V H p i x) = 0) :
    fiberedCycleClassDefect (V := V) (H := H) (p := p)
        (tensorWord i j T.cycleOperator (atom V H p i x)) = 0 := by
  rw [defect_tensorWord_atom_eq_map T i j x hT, hzero]
  exact T.cohomologyOperator.map_zero

/-- Operator-pair form of the same statement with the source defect exposed as
a genuine cycle-class equality. -/
theorem tensorWord_lands_classically_of_source_class
    (T : CycleClassOperatorPair V H p)
    (i j : ClassicalHodgeBasisIndex V H p)
    (x : CodimensionPoint V.X p)
    (hT : TensorIntertwinesAt T i j x)
    (hx :
      H.cycleClass p (codimensionPointCycle V.X p x) =
        (classicalHodgeBasis V H p i).1) :
    H.cycleClass p
        (toNativeCycle V H p
          (tensorWord i j T.cycleOperator (atom V H p i x))) =
      (fiberedHodgeClass (V := V) (H := H) (p := p)
        (tensorWord i j T.cycleOperator (atom V H p i x))).1 := by
  apply (defect_eq_zero_iff_faces_agree
    (V := V) (H := H) (p := p)
    (tensorWord i j T.cycleOperator (atom V H p i x))).mp
  apply defectZero_tensorWord_atom T i j x hT
  exact (fiberedCycleClassDefect_atom_eq_zero_iff
    (V := V) (H := H) (p := p) i x).2 hx

/-- Uniform version: one cycle-natural operator whose point-transition scalar
is constant and whose Hodge action sends `i` to that scalar times `j` carries
every defect-zero source atom in sheet `i` to a defect-zero target state. -/
def UniformTensorIntertwiner
    (T : CycleClassOperatorPair V H p)
    (i j : ClassicalHodgeBasisIndex V H p) : Prop :=
  ∃ lam : ℚ,
    (∀ x : CodimensionPoint V.X p,
      pointTransitionMass T.cycleOperator x = lam) ∧
    T.cohomologyOperator (classicalHodgeBasis V H p i).1 =
      lam • (classicalHodgeBasis V H p j).1

/-- A uniform intertwiner supplies the pointwise intertwining law at every
native point atom automatically. -/
theorem UniformTensorIntertwiner.at
    {T : CycleClassOperatorPair V H p}
    {i j : ClassicalHodgeBasisIndex V H p}
    (h : UniformTensorIntertwiner T i j)
    (x : CodimensionPoint V.X p) :
    TensorIntertwinesAt T i j x := by
  rcases h with ⟨lam, hmass, hbasis⟩
  unfold TensorIntertwinesAt
  rw [hmass x]
  exact hbasis

/-- **ZERO-DEFECT ORBIT STEP.**
A uniform genuine projective/GST tensor generator propagates every zero-defect
point atom from its source Hodge sheet into a zero-defect target fibered state. -/
theorem uniformTensorIntertwiner_propagates_zeroDefect
    (T : CycleClassOperatorPair V H p)
    (i j : ClassicalHodgeBasisIndex V H p)
    (hT : UniformTensorIntertwiner T i j)
    (x : CodimensionPoint V.X p)
    (hx :
      H.cycleClass p (codimensionPointCycle V.X p x) =
        (classicalHodgeBasis V H p i).1) :
    fiberedCycleClassDefect (V := V) (H := H) (p := p)
        (tensorWord i j T.cycleOperator (atom V H p i x)) = 0 := by
  apply defectZero_tensorWord_atom T i j x (hT.at x)
  exact (fiberedCycleClassDefect_atom_eq_zero_iff
    (V := V) (H := H) (p := p) i x).2 hx

#check pointTransitionMass
#check TensorIntertwinesAt
#check defect_tensorWord_atom_eq_map
#check defectZero_tensorWord_atom
#check UniformTensorIntertwiner
#check uniformTensorIntertwiner_propagates_zeroDefect

#print axioms defect_tensorWord_atom_eq_map
#print axioms defectZero_tensorWord_atom
#print axioms tensorWord_lands_classically_of_source_class
#print axioms uniformTensorIntertwiner_propagates_zeroDefect

end GSTClassicalHodgeFiberedDefectEquivariance
