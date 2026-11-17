import GSTClassicalHodgeOpenAIGeometricPeriodCertificates
import GSTClassicalHodgeSingleSheetCrown
import GSTClassicalHodgeAtomicAnnihilator

/-!
# Semantic noncircularity audit for OpenAI-to-GST geometric certificates

An arbitrary existential source carrier permits the IDENTITY correspondence
on the target carrier.  Therefore the existence of a generic
`GeometricSourcePeriodCertificate` is logically equivalent to a native
basis-cycle witness; it is NOT, by itself, a discovery of missing geometry.

This file proves that fact within Lean, and also proves:
* any independently constructed certificate destroys the corresponding
  single-sheet algebraic separator;
* any surviving separator forbids such a certificate;
* the abstract universal certificate property is equivalent to Hodge, so
  it MUST NOT be made into a new axiom as a way to announce a solution.

The actual geometric work is to build the CM surface/divisor kernels and
Kuga--Satake/Gale cycles without using the identity/basis-cycle direction
of this equivalence.  This audit prevents a logical cycle in the proof graph.

NEEDS CI RUN LATER.
-/

set_option maxHeartbeats 30000000
set_option maxRecDepth 800000

noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeNativeExecutablePlane
open GSTClassicalHodgeCrossCarrierGeometricTransfer
open GSTClassicalHodgeOpenAIGeometricPeriodCertificates
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeAtomicAnnihilator
open GSTClassicalHodgeSingleSheetCrown

namespace GSTClassicalHodgeOpenAIGeometryNoncircularityAudit

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {q : Nat}
variable {j : ClassicalHodgeBasisIndex V H q}

/-- A rational native cycle for one sheet supplies a trivial certificate via
the diagonal.  Thus the abstract certificate notion does not evade the
original Hodge obstruction. -/
noncomputable def certificateOfAlreadyAlgebraicBasis
    (Z : codimensionCycles V.X q)
    (hZ : H.cycleClass q Z = (classicalHodgeBasis V H q j).1) :
    GeometricSourcePeriodCertificate V H q j where
  source := V
  sourceData := H
  sourceCodimension := q
  geometricTransfer := CrossCarrierTransfer.identity V H q
  sourceNativeCycle := Z
  period := 1
  nonzero_period := one_ne_zero
  exact_period_formula := by
    simpa [CrossCarrierTransfer.identity] using hZ

/-- Conversely any truly certified period constructs an algebraic cycle.
The two statements are equivalent when the source class is unrestricted. -/
theorem geometricCertificate_iff_basisCycle
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (q : Nat) (j : ClassicalHodgeBasisIndex V H q) :
    Nonempty (GeometricSourcePeriodCertificate V H q j) ↔
      ∃ Z : codimensionCycles V.X q,
        H.cycleClass q Z = (classicalHodgeBasis V H q j).1 := by
  constructor
  · rintro ⟨C⟩
    exact ⟨C.normalizedNativeCycle, C.normalizedNativeCycle_spec⟩
  · rintro ⟨Z, hZ⟩
    exact ⟨certificateOfAlreadyAlgebraicBasis Z hZ⟩

/-- The universal abstract existence of a geometric source certificate
is EXACTLY the original basis-cycle supply statement.  It is not a new
unconditional geometric theorem. -/
theorem completeCertificates_iff_basisCycleSupply
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V) :
    (∀ q : Nat, ∀ j : ClassicalHodgeBasisIndex V H q,
        Nonempty (GeometricSourcePeriodCertificate V H q j)) ↔
      HodgeBasisCycleSupply (V := V) (H := H) := by
  constructor
  · intro h q j
    exact
      (geometricCertificate_iff_basisCycle V H q j).mp (h q j)
  · intro h q j
    exact
      (geometricCertificate_iff_basisCycle V H q j).mpr (h q j)

/-- The unrestricted complete-certificate statement is therefore
EQUIVALENT to the exact rational Hodge conjecture at the current
Stage-2G semantic carrier. -/
theorem completeCertificates_iff_exactHodge
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V) :
    (∀ q : Nat, ∀ j : ClassicalHodgeBasisIndex V H q,
      Nonempty (GeometricSourcePeriodCertificate V H q j)) ↔
        BigradedBettiHodgeStatement V H := by
  exact (completeCertificates_iff_basisCycleSupply V H).trans
    (basisCycleSupply_iff_hodge (V := V) (H := H))

/-- A genuine algebraic point-cycle annihilator annihilates every full
rational native cycle class.  The existing finite-support theorem identifies
the atomic span with the entire native-cycle range. -/
theorem basisSeparator_annihilates_all_native_cycles
    (S : BasisAtomicSeparator V H q j)
    (Z : codimensionCycles V.X q) :
    S.detector (H.cycleClass q Z) = 0 := by
  have hker :
      pointCycleClassSpan q (H.cycleClass q) ≤
        LinearMap.ker S.detector :=
    (annihilatesPointCycles_iff_atomicSpan_le_ker
      q (H.cycleClass q) S.detector).mp S.annihilates_atoms
  have hmem : H.cycleClass q Z ∈
      pointCycleClassSpan q (H.cycleClass q) := by
    rw [← smoothProjective_cycleClass_range_eq_atomic_span V H q]
    exact ⟨Z, rfl⟩
  exact hker hmem

/-- A geometric source certificate and a detector of the same allegedly
nonalgebraic Hodge sheet cannot coexist.  Crucially this applies even when
the source is a DIFFERENT variety or a long sandwich of correspondences. -/
theorem separator_forbids_geometricCertificate
    (S : BasisAtomicSeparator V H q j) :
    IsEmpty (GeometricSourcePeriodCertificate V H q j) := by
  refine ⟨fun C => ?_⟩
  have hzero :
      S.detector (classicalHodgeBasis V H q j).1 = 0 := by
    rw [← C.normalizedNativeCycle_spec]
    exact basisSeparator_annihilates_all_native_cycles S _
  exact S.detects_basis hzero

/-- A single genuine period certificate eliminates the corresponding
atomic separator, regardless of the auxiliary carrier geometry used. -/
theorem geometricCertificate_eliminates_separator
    (C : GeometricSourcePeriodCertificate V H q j) :
    IsEmpty (BasisAtomicSeparator V H q j) := by
  refine ⟨?_⟩
  intro S
  exact isEmpty_iff.mp (separator_forbids_geometricCertificate S) C

#check geometricCertificate_iff_basisCycle
#check completeCertificates_iff_exactHodge
#check separator_forbids_geometricCertificate
#print axioms completeCertificates_iff_exactHodge

end GSTClassicalHodgeOpenAIGeometryNoncircularityAudit
