import GSTClassicalHodgeProjectiveDegreeTrace
import GSTClassicalHodgeGlobalSheetCosmos
import GSTClassicalHodgeGSTSourceProgramCompiler
import GSTClassicalHodgeGSTDefectExtinction

/-!
# GST CLASSICAL HODGE — PROJECTIVE-DEGREE CERTIFIED GST SOURCE

The limitless GST native mass is an exact combinatorial shadow, but raw
component-count mass is not the correct general cohomological degree invariant
for projective cycles.  Genuine nonvanishing must be certified by projective
intersection degree.

`ProjectiveDegreeTraceSemantics` already supplies that geometry: a Betti trace
coming from complementary hyperplane intersection, positive degree on every
irreducible projective cycle, and exact compatibility with the genuine cycle
class.  One exact principal-cut successor therefore has nonzero Betti class.

This file feeds that degree-certified algebraic Hodge seed directly into the
global GST sheet cosmos and the source-specific geometry compiler.  No
`NativeMassCycleClassBridge` is used.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeGSTDegreeCertifiedSource

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeGlobalSheetCosmos
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeSynchronizedDefectOrbit
open GSTClassicalHodgeProjectiveDegreeTrace
open GSTClassicalHodgePointClosureRelativeCut
open GSTClassicalHodgeSingleExactSuccessorSurvival
open GSTClassicalHodgeGSTSourceProgramCompiler
open GSTClassicalHodgeGlobalSheetSaturation
open GSTClassicalHodgeGSTDefectExtinction
open GSTClassicalHodgeSingleSheetCrown

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-! ## ALL-X DEGREE-CERTIFIED ORIGINAL-CHOW GST BRIDGE

The full original-X native Chow address-span saturation no longer asks
for an independently supplied NativeMass bridge OR an arbitrary nonzero
Hodge seed. Any actual codimension-p irreducible projective cycle has
nonzero cycle class because its true projective degree is positive.

This constructs the only starting Chow source required by the
GST matrix-unit saturation argument, directly from existing geometry.
The remaining original Hodge obligation is the ACTUAL native-operator
realization/stability of every required GST source-to-target move;
that property is NOT inferred from a formal Hodge basis matrix unit.
-/

/-- Positive projective degree provides an independently geometric
nonzero native source at every real codimension-p point. Using
the freshly proved M-free original-X GST bridge, no NativeMass
or Hodge-target preimage is an additional hypothesis.

The precise remaining unproved universal condition is hstable:
that the unrestricted abstract GST sheet units preserve the
genuine original-X algebraic Chow address span. -/
theorem degreeCertifiedOriginalXChowSheet_saturation
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (hstable :
      SameWeightGSTStable (V := V) (H := H) p
        (nativeAlgebraicWeightAddressSpan G p)) :
    FixedWeightSheetSubspace (V := V) (H := H) p ≤
      nativeAlgebraicWeightAddressSpan G p := by
  apply nativeAlgebraicWeightAddress_saturates_of_GST_stability_and_source
    G p (codimensionPointCycle V.X p x) ?_ hstable
  intro hz
  have htrace := D.trace_point_cycleClass p x
  rw [hz, LinearMap.map_zero] at htrace
  have hpos := D.pointDegree_pos p x
  rw [← htrace] at hpos
  exact lt_irrefl 0 hpos

#check degreeCertifiedOriginalXChowSheet_saturation
#print axioms degreeCertifiedOriginalXChowSheet_saturation

/-- The actual nonzero algebraic Hodge seed in weight `p+1` obtained from one
exact projective principal-cut successor and certified by positive projective
degree. -/
noncomputable def degreeCertifiedSuccessorSeed
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (hlive : ProjectivelyLiveSource V.projective.n
      (V.projective.immersion x.1))
    (hExact :
      Order.coheight
        (ambientSuccessorPoint V x.1
          (relativeHeightOneSeparatorSuccessor V x.1 hlive)) = p + 1) :
    NativeHodgeOrbitSeed (V := V) (H := H) (p := p + 1) :=
  D.separator_successor_nativeHodgeSeed G p x hlive hExact

/-- Total GST sheet address of the degree-certified algebraic seed. -/
noncomputable def degreeCertifiedAddress
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (hlive : ProjectivelyLiveSource V.projective.n
      (V.projective.immersion x.1))
    (hExact :
      Order.coheight
        (ambientSuccessorPoint V x.1
          (relativeHeightOneSeparatorSuccessor V x.1 hlive)) = p + 1) :
    GSTClassicalHodgeFiberedTransferCompletion.FiberedHodgeAddress V H :=
  GSTClassicalHodgeFiberedCosmology.fiberedWeightCoordinates V H (p + 1)
    (degreeCertifiedSuccessorSeed G D p x hlive hExact).hodge

/-- Selected nonzero GST source sheet of the degree-certified seed. -/
noncomputable def degreeCertifiedSourceSheet
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (hlive : ProjectivelyLiveSource V.projective.n
      (V.projective.immersion x.1))
    (hExact :
      Order.coheight
        (ambientSuccessorPoint V x.1
          (relativeHeightOneSeparatorSuccessor V x.1 hlive)) = p + 1) :
    GSTClassicalHodgeFiberedTransferCompletion.FiberedHodgeIndex V H :=
  ⟨p + 1, (degreeCertifiedSuccessorSeed G D p x hlive hExact).sourceIndex⟩

/-- Projective-degree nonvanishing becomes a nonzero global GST Poincare-style
sheet probe. -/
theorem degreeCertifiedSourceProbe_ne_zero
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (hlive : ProjectivelyLiveSource V.projective.n
      (V.projective.immersion x.1))
    (hExact :
      Order.coheight
        (ambientSuccessorPoint V x.1
          (relativeHeightOneSeparatorSuccessor V x.1 hlive)) = p + 1) :
    sheetProbe (degreeCertifiedSourceSheet G D p x hlive hExact)
      (degreeCertifiedAddress G D p x hlive hExact) ≠ 0 := by
  simpa [degreeCertifiedSourceSheet, degreeCertifiedAddress,
    sheetProbe_fiberedWeightCoordinates, hodgeCoordinate] using
    (degreeCertifiedSuccessorSeed G D p x hlive hExact).sourceCoefficient_ne_zero

/-- Source-specific genuine geometry program from the degree-certified source
to one target Hodge sheet. -/
abbrev DegreeCertifiedGSTProgram
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (hlive : ProjectivelyLiveSource V.projective.n
      (V.projective.immersion x.1))
    (hExact :
      Order.coheight
        (ambientSuccessorPoint V x.1
          (relativeHeightOneSeparatorSuccessor V x.1 hlive)) = p + 1)
    (j : ClassicalHodgeBasisIndex V H (p + 1)) :=
  GSTSourceTargetProgram G
    (degreeCertifiedSuccessorSeed G D p x hlive hExact) j

/-- A synchronized geometric execution from the degree-certified GST source
constructs the exact target algebraic cycle. -/
theorem degreeCertifiedProgram_targetCycle
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (hlive : ProjectivelyLiveSource V.projective.n
      (V.projective.immersion x.1))
    (hExact :
      Order.coheight
        (ambientSuccessorPoint V x.1
          (relativeHeightOneSeparatorSuccessor V x.1 hlive)) = p + 1)
    (j : ClassicalHodgeBasisIndex V H (p + 1))
    (R : DegreeCertifiedGSTProgram G D p x hlive hExact j) :
    ∃ Z : codimensionCycles V.X (p + 1),
      H.cycleClass (p + 1) Z =
        (classicalHodgeBasis V H (p + 1) j).1 := by
  exact ⟨R.targetCycle, R.targetCycle_spec⟩

/-- The same synchronized execution extinguishes the target fibered defect and
single-sheet separator. -/
theorem degreeCertifiedProgram_no_separator
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (hlive : ProjectivelyLiveSource V.projective.n
      (V.projective.immersion x.1))
    (hExact :
      Order.coheight
        (ambientSuccessorPoint V x.1
          (relativeHeightOneSeparatorSuccessor V x.1 hlive)) = p + 1)
    (j : ClassicalHodgeBasisIndex V H (p + 1))
    (R : DegreeCertifiedGSTProgram G D p x hlive hExact j) :
    IsEmpty (GSTClassicalHodgeSingleSheetCrown.BasisAtomicSeparator
      V H (p + 1) j) := by
  exact GSTClassicalHodgeGSTDefectExtinction.isEmpty_basisSeparator_of_sourceProgram
    G (degreeCertifiedSuccessorSeed G D p x hlive hExact) j R

/-- If the degree-certified source has a synchronized GST/geometric program to
every target sheet, the exact Hodge statement follows in that weight. -/
theorem hodge_weight_of_degreeCertifiedPrograms
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (hlive : ProjectivelyLiveSource V.projective.n
      (V.projective.immersion x.1))
    (hExact :
      Order.coheight
        (ambientSuccessorPoint V x.1
          (relativeHeightOneSeparatorSuccessor V x.1 hlive)) = p + 1)
    (R : ∀ j : ClassicalHodgeBasisIndex V H (p + 1),
      DegreeCertifiedGSTProgram G D p x hlive hExact j) :
    rationalHodgeSubspace (H.hodgeBigrading (p + 1)) ≤
      LinearMap.range (H.cycleClass (p + 1)) := by
  intro alpha halpha
  let alphaH : ClassicalHodgeFiber V H (p + 1) := ⟨alpha, halpha⟩
  have hbasis : ∀ j : ClassicalHodgeBasisIndex V H (p + 1),
      (classicalHodgeBasis V H (p + 1) j).1 ∈
        LinearMap.range (H.cycleClass (p + 1)) := by
    intro j
    exact (R j).target_mem_cycleClass_range
  rw [show alphaH =
      ∑ j ∈ ((classicalHodgeBasis V H (p + 1)).repr alphaH).support,
        ((classicalHodgeBasis V H (p + 1)).repr alphaH j) •
          classicalHodgeBasis V H (p + 1) j by
    exact (classicalHodgeBasis V H (p + 1)).sum_repr alphaH]
  simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower]
  apply Submodule.sum_mem
  intro j hj
  exact (LinearMap.range (H.cycleClass (p + 1))).smul_mem
    ((classicalHodgeBasis V H (p + 1)).repr alphaH j) (hbasis j)

#check degreeCertifiedSuccessorSeed
#check degreeCertifiedAddress
#check degreeCertifiedSourceSheet
#check degreeCertifiedSourceProbe_ne_zero
#check DegreeCertifiedGSTProgram
#check degreeCertifiedProgram_targetCycle
#check degreeCertifiedProgram_no_separator
#check hodge_weight_of_degreeCertifiedPrograms

#print axioms degreeCertifiedSourceProbe_ne_zero
#print axioms degreeCertifiedProgram_targetCycle
#print axioms degreeCertifiedProgram_no_separator
#print axioms hodge_weight_of_degreeCertifiedPrograms

end GSTClassicalHodgeGSTDegreeCertifiedSource
