import GSTClassicalHodgeCrossCarrierExplicitPointKernel
import GSTClassicalHodgeCMNativeRationalDescent
import GSTClassicalHodgeGradedCorrespondenceProgramOrbit
import GSTClassicalHodgeNativeExecutablePlane

/-!
# CM / Kuga-Satake / Gale -> existing GST programs -> native Hodge basis

This file plugs algebraic source constructions INTO the original HC-PROOF
native-cycle proof, rather than founding an independent Hodge surrogate.

A packet supplies a genuinely finite cross-variety point incidence kernel,
one ACTUAL GST graded full-correspondence/cut program, independent auxiliary
source cycles and a finite algebraic-coefficient expansion of the TARGET
basis tensor. Its rational output cycle is calculated by finite sums.

There is no input field of type 'native target cycle with desired class'.
Naturality is derived from point incidence and the old GST program calculus.
Algebraic-number coefficients are descended to rational native cycles.

The existence of suitable CM surface/Clifford/Gale packets for arbitrary
target basis sheets is a mathematical construction task, not a postulate
added in this module.

NEEDS CI RUN LATER.
-/

set_option maxHeartbeats 50000000
set_option maxRecDepth 900000

noncomputable section

open scoped BigOperators
open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeCrossCarrierExplicitPointKernel
open GSTClassicalHodgeCMNativeRationalDescent
open GSTClassicalHodgeGradedCorrespondenceProgramOrbit
open GSTClassicalHodgeGradedCorrespondenceProgramOrbit.GradedCorrespondenceProgram
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeNativeExecutablePlane

namespace GSTClassicalHodgeCMGSTNativeBasisCompiler

variable {K : Type*} [Field K] [Algebra ℚ K]
variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- One explicit geometric source -> GST-program -> basis-sheet packet.
The full-correspondence program is the EXISTING program syntax in HC-PROOF.
The scalar coefficients may lie in any field extension K of Q. -/
structure CMGSTNativeSheetProgram
    (G : GeometricCycleClassSpine V H)
    (q : Nat) (j : ClassicalHodgeBasisIndex V H q) where
  source : SmoothProjectiveComplexScheme
  sourceData : HodgeBigradedBettiData source
  sourceCodim : Nat
  entryCodim : Nat
  pointKernel :
    FiniteCrossCarrierPointKernel source V sourceCodim entryCodim
  betti :
    RationalSingularCohomology sourceData.analytification (2 * sourceCodim) →ₗ[ℚ]
      RationalSingularCohomology H.analytification (2 * entryCodim)
  geometricPointLaw :
    RealizesFinitePointKernelOnBetti (H := sourceData) (J := H)
      pointKernel betti
  gstProgram :
    GradedCorrespondenceProgram V H entryCodim q
  active : Finset Nat
  sourceCycle : Nat → codimensionCycles source.X sourceCodim
  coefficient : Nat → K
  basisPeriodExpansion :
    let b := Module.Free.chooseBasis ℚ
      (RationalSingularCohomology H.analytification (2 * q))
    ∀ i : Module.Free.ChooseBasisIndex ℚ
      (RationalSingularCohomology H.analytification (2 * q)),
      algebraMap ℚ K ((b.repr (classicalHodgeBasis V H q j).1) i) =
        ∑ a ∈ active, coefficient a * algebraMap ℚ K
          ((b.repr
            (gstProgram.cohomologyEval G
              (betti (sourceData.cycleClass sourceCodim (sourceCycle a))))) i)

namespace CMGSTNativeSheetProgram

variable {G : GeometricCycleClassSpine V H}
variable {q : Nat} {j : ClassicalHodgeBasisIndex V H q}

/-- Source geometry is evaluated as an actual native cycle, then passed
through the ORIGINAL GST correspondence/cut program. -/
noncomputable def nativeTerm
    (C : CMGSTNativeSheetProgram (K := K) G q j) (a : Nat) :
    codimensionCycles V.X q :=
  C.gstProgram.cycleEval G
    (nativeOfFinitePointKernel C.pointKernel (C.sourceCycle a))

/-- Entirely explicit output: a finite rational combination of actual
native GST program outputs, with Q coefficients descended from K. -/
noncomputable def nativeBasisCycle
    (C : CMGSTNativeSheetProgram (K := K) G q j) :
    codimensionCycles V.X q :=
  rationalCycleFromExtensionCoefficients
    (K := K) C.active C.nativeTerm C.coefficient

/-- Each geometric source term obeys the Betti computation required by
the CM period expansion. The two naturality statements are BOTH derived
in the existing Lean development, not injected into the finale. -/
theorem nativeTerm_cycleClass
    (C : CMGSTNativeSheetProgram (K := K) G q j) (a : Nat) :
    H.cycleClass q (C.nativeTerm a) =
      C.gstProgram.cohomologyEval G
        (C.betti (C.sourceData.cycleClass C.sourceCodim (C.sourceCycle a))) := by
  unfold nativeTerm
  rw [C.gstProgram.cycleClass_cycleEval G]
  rw [finitePointKernel_naturality
    C.pointKernel C.betti C.geometricPointLaw]

/-- The constructed rational native cycle has EXACTLY the prescribed
classical Hodge basis class; no Hodge preimage supplied or selected. -/
theorem nativeBasisCycle_spec
    (C : CMGSTNativeSheetProgram (K := K) G q j) :
    H.cycleClass q C.nativeBasisCycle =
      (classicalHodgeBasis V H q j).1 := by
  apply rationalCycleFromExtensionCoefficients_spec
    C.active C.nativeTerm C.coefficient
    (classicalHodgeBasis V H q j).1
  intro b i
  simpa only [C.nativeTerm_cycleClass] using C.basisPeriodExpansion i

/-- A concrete GST surface packet independently establishes algebraicity of
this ONE basis direction, without requiring a universal plane assumption. -/
theorem one_basis_sheet_is_algebraic
    (C : CMGSTNativeSheetProgram (K := K) G q j) :
    (classicalHodgeBasis V H q j).1 ∈
      LinearMap.range (H.cycleClass q) :=
  ⟨C.nativeBasisCycle, C.nativeBasisCycle_spec⟩

end CMGSTNativeSheetProgram

/-! ## Finite-support, class-local constructive GST surface geometry

The full Hodge conjecture quantifies over every rational Hodge state.
For ONE fixed target state, its Hodge basis presentation has finite
support. We need corresponding geometric source packets ONLY at those
finitely many active basis slots, not on unrelated directions.
This is the intended live-packet optimization in the original Pi
and GST source-specific research lineage. -/

/-- Construct ONE algebraic cycle for a Hodge class from explicit
CM/Gale/Kuga-Satake source packets on precisely its finite live
basis support, using the original GST full-correspondence programs.
No global basis-packet or global Hodge-surjectivity premise is used. -/
theorem native_cycle_of_finite_CM_GST_packet_support
    (G : GeometricCycleClassSpine V H)
    (q : Nat)
    (alpha : ClassicalHodgeFiber V H q)
    (hActive :
      ∀ j : ClassicalHodgeBasisIndex V H q,
        j ∈ ((classicalHodgeBasis V H q).repr alpha).support →
        Nonempty (CMGSTNativeSheetProgram (K := K) G q j)) :
    ∃ Z : codimensionCycles V.X q,
      H.cycleClass q Z = alpha.1 := by
  classical
  let coeff := (classicalHodgeBasis V H q).repr alpha
  let cycleFor (j : ClassicalHodgeBasisIndex V H q) :
      codimensionCycles V.X q :=
    if hj : j ∈ coeff.support then
      (Classical.choice (hActive j hj)).nativeBasisCycle
    else 0
  have cycleFor_spec (j : ClassicalHodgeBasisIndex V H q)
      (hj : j ∈ coeff.support) :
      H.cycleClass q (cycleFor j) =
        (classicalHodgeBasis V H q j).1 := by
    simp only [cycleFor, dif_pos hj]
    exact (Classical.choice (hActive j hj)).nativeBasisCycle_spec
  let Z : codimensionCycles V.X q :=
    ∑ j ∈ coeff.support, coeff j • cycleFor j
  refine ⟨Z, ?_⟩
  have hexp :
      (alpha : RationalSingularCohomology H.analytification (2 * q)) =
        ∑ j ∈ coeff.support,
          coeff j • ((classicalHodgeBasis V H q j).1 :
            RationalSingularCohomology H.analytification (2 * q)) := by
    have h := ((classicalHodgeBasis V H q).linearCombination_repr alpha).symm
    rw [Finsupp.linearCombination_apply] at h
    conv_lhs => rw [h]
    simp [coeff, Finsupp.sum, Submodule.coe_sum, Submodule.coe_smul_of_tower]
  calc
    H.cycleClass q Z =
        ∑ j ∈ coeff.support, coeff j • H.cycleClass q (cycleFor j) := by
          simp [Z, map_sum, map_smul]
    _ = ∑ j ∈ coeff.support,
          coeff j • ((classicalHodgeBasis V H q j).1 :
            RationalSingularCohomology H.analytification (2 * q)) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [cycleFor_spec j hj]
    _ = alpha.1 := hexp.symm

/-- Geometry packet supply is a statement about ACTUAL finite source
incidence plus ACTUAL existing GST programs, not arbitrary Betti lifts. -/
def CMGSTNativeBasisProgramSupply
    (G : GeometricCycleClassSpine V H) : Prop :=
  ∀ q : Nat, ∀ j : ClassicalHodgeBasisIndex V H q,
    Nonempty (CMGSTNativeSheetProgram (K := K) G q j)

/-- The new source/compiler packets feed the EXISTING basis-cycle supply,
rather than defining a competing Hodge proposition. -/
theorem basisCycleSupply_of_CM_GST_programs
    (G : GeometricCycleClassSpine V H)
    (h : CMGSTNativeBasisProgramSupply (K := K) G) :
    HodgeBasisCycleSupply (V := V) (H := H) := by
  intro q j
  obtain ⟨C⟩ := h q j
  exact ⟨C.nativeBasisCycle, C.nativeBasisCycle_spec⟩

/-- Integration into the previously proved Stage-2G Hodge landing.
The mathematical burden is exactly the supply of the explicit geometric
packets, which can be developed using CM surfaces, KS, and Gale cycles. -/
theorem bigradedBettiHodge_of_CM_GST_programs
    (G : GeometricCycleClassSpine V H)
    (h : CMGSTNativeBasisProgramSupply (K := K) G) :
    BigradedBettiHodgeStatement V H :=
  hodge_of_basisCycleSupply
    (basisCycleSupply_of_CM_GST_programs G h)

#check CMGSTNativeSheetProgram.nativeBasisCycle
#check CMGSTNativeSheetProgram.nativeTerm_cycleClass
#check CMGSTNativeSheetProgram.nativeBasisCycle_spec
#check basisCycleSupply_of_CM_GST_programs
#check bigradedBettiHodge_of_CM_GST_programs
#print axioms bigradedBettiHodge_of_CM_GST_programs

end GSTClassicalHodgeCMGSTNativeBasisCompiler
