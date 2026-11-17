import GSTClassicalHodgeCMGSTNativeBasisCompiler
import GSTClassicalHodgeCrossCarrierCupGysinConstruction

/-!
# Geometric cup/Gysin source -> original GST -> native Hodge basis

This strengthens the CM/GST integration by REPLACING its freely supplied
Betti correspondence map with the actual degree-checked geometric kernel
formula determined by:
   * pullback from source to source x target;
   * cup product with the chosen correspondence kernel class;
   * projection Gysin integration to the target.

The other correspondence input is an explicit finite rational point-incidence
kernel. Their ONE-point geometric compatibility derives global naturality.

The result is fed directly into the SAME CMGSTNativeSheetProgram previously
connected to HodgeConjecture.lean. There is no new target proposition.

The topology data of product cup/Gysin are still supplied because the pinned
Mathlib singular-cohomology stack does not implement the full arbitrary
source x target intersection-calculus construction. The surface kernel class
must still be geometrically realized; this file does NOT assume that all
Hodge tensors admit such a realization.

NEEDS CI RUN LATER.
-/

set_option maxHeartbeats 40000000
set_option maxRecDepth 900000

noncomputable section

open scoped BigOperators
open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeGradedCorrespondenceProgramOrbit
open GSTClassicalHodgeGradedCorrespondenceProgramOrbit.GradedCorrespondenceProgram
open GSTClassicalHodgeCrossCarrierExplicitPointKernel
open GSTClassicalHodgeCrossCarrierCupGysinConstruction
open GSTClassicalHodgeCMGSTNativeBasisCompiler

namespace GSTClassicalHodgeCMSurfaceCupGysinGSTCompiler

variable {K : Type*} [Field K] [Algebra ℚ K]
variable {PCoh : Nat → Type*}
variable [∀ n, AddCommGroup (PCoh n)] [∀ n, Module ℚ (PCoh n)]
variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- A concrete source-to-destination geometric cup/Gysin packet followed
by a genuine ORIGINAL GST graded full-correspondence/cut program.
There is NO freely supplied Betti operator: the action is DEFINED
from cup, pullback, Gysin and the actual kernel class. -/
structure CupGysinGSTSheetProgram
    (G : GeometricCycleClassSpine V H)
    (q : Nat) (j : ClassicalHodgeBasisIndex V H q) where
  source : SmoothProjectiveComplexScheme
  sourceData : HodgeBigradedBettiData source
  sourceCodim : Nat
  entryCodim : Nat
  sourceDimension : Nat
  kernelCodim : Nat
  geometry :
    CrossProductCupGysin source V sourceData H PCoh
      sourceDimension sourceCodim entryCodim kernelCodim
  finiteIncidence :
    FiniteCrossCarrierPointKernel source V sourceCodim entryCodim
  geometricPointLaw :
    CupGysinPointIncidence geometry finiteIncidence
  gstProgram : GradedCorrespondenceProgram V H entryCodim q
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
              (geometry.action
                (sourceData.cycleClass sourceCodim (sourceCycle a))))) i)

namespace CupGysinGSTSheetProgram

variable {G : GeometricCycleClassSpine V H}
variable {q : Nat} {j : ClassicalHodgeBasisIndex V H q}

/-- Specialize genuinely geometric cup/Gysin incidence into the common
GST-native source packet, retaining the SAME original graded program. -/
noncomputable def toNativeGSTSheetProgram
    (C : CupGysinGSTSheetProgram (K := K) (PCoh := PCoh) G q j) :
    CMGSTNativeSheetProgram (K := K) G q j where
  source := C.source
  sourceData := C.sourceData
  sourceCodim := C.sourceCodim
  entryCodim := C.entryCodim
  pointKernel := C.finiteIncidence
  betti := C.geometry.action
  geometricPointLaw := by
    intro x
    simpa only [CrossProductCupGysin.action_apply] using C.geometricPointLaw x
  gstProgram := C.gstProgram
  active := C.active
  sourceCycle := C.sourceCycle
  coefficient := C.coefficient
  basisPeriodExpansion := C.basisPeriodExpansion

/-- Surface kernel/Gysin geometry plus original GST programs and algebraic
period coefficients build an actual RATIONAL native algebraic cycle. -/
noncomputable def nativeBasisCycle
    (C : CupGysinGSTSheetProgram (K := K) (PCoh := PCoh) G q j) :
    codimensionCycles V.X q :=
  C.toNativeGSTSheetProgram.nativeBasisCycle

/-- Every geometric sheet packet realizes its Hodge basis class by a
genuine codimension-q native algebraic cycle on the original variety. -/
theorem nativeBasisCycle_spec
    (C : CupGysinGSTSheetProgram (K := K) (PCoh := PCoh) G q j) :
    H.cycleClass q C.nativeBasisCycle =
      (classicalHodgeBasis V H q j).1 :=
  C.toNativeGSTSheetProgram.nativeBasisCycle_spec

end CupGysinGSTSheetProgram

/-- Class-local geometric completion from only the FINITELY MANY live
basis directions. Each sheet is powered by true product cup/Gysin data,
finite native incidence and original GST correspondences/cuts. -/
theorem finite_target_from_cupGysin_GST_sheet_packets
    (G : GeometricCycleClassSpine V H)
    (q : Nat)
    (alpha : ClassicalHodgeFiber V H q)
    (hActive :
      ∀ j : ClassicalHodgeBasisIndex V H q,
        j ∈ ((classicalHodgeBasis V H q).repr alpha).support →
        Nonempty (CupGysinGSTSheetProgram (K := K) (PCoh := PCoh) G q j)) :
    ∃ Z : codimensionCycles V.X q,
      H.cycleClass q Z = alpha.1 := by
  apply native_cycle_of_finite_CM_GST_packet_support (K := K) G q alpha
  intro j hj
  obtain ⟨C⟩ := hActive j hj
  exact ⟨C.toNativeGSTSheetProgram⟩

/-- The universal version runs through the original Stage-2G public target
once geometrically realized cup/Gysin packets have been CONSTRUCTED in every
basis direction. No Hodge-surjectivity field is included in a packet. -/
theorem exact_stage2G_of_cupGysin_GST_sheet_packets
    (G : GeometricCycleClassSpine V H)
    (h :
      ∀ q : Nat, ∀ j : ClassicalHodgeBasisIndex V H q,
        Nonempty (CupGysinGSTSheetProgram (K := K) (PCoh := PCoh) G q j)) :
    BigradedBettiHodgeStatement V H := by
  apply bigradedBettiHodge_of_CM_GST_programs (K := K) G
  intro q j
  obtain ⟨C⟩ := h q j
  exact ⟨C.toNativeGSTSheetProgram⟩

#check CupGysinGSTSheetProgram.toNativeGSTSheetProgram
#check finite_target_from_cupGysin_GST_sheet_packets
#check exact_stage2G_of_cupGysin_GST_sheet_packets
#print axioms exact_stage2G_of_cupGysin_GST_sheet_packets

end GSTClassicalHodgeCMSurfaceCupGysinGSTCompiler
