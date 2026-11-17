import GSTClassicalHodgeCrossCarrierGSTProgramFusion
import GSTClassicalHodgeNativeExecutablePlane
import GSTClassicalHodgeExactClayStatement

/-!
# Inter-variety surface-period certificates for rational Hodge basis sheets

This module integrates the CM surface-switch route, Kuga--Satake geometric
correspondence route and Gale correspondence route with the existing
`ClassicalHodgeBasis` and exact Stage-2G rational Hodge statement.

A `GeometricSourcePeriodCertificate` contains:
1. a possibly DIFFERENT smooth projective source;
2. its genuine supplied Hodge/Betti cycle-class semantics;
3. a native codimension-s source cycle;
4. a cycle-class-natural algebraic transfer to the target variety;
5. a NONZERO rational period identity for one specified Hodge basis sheet.

Theorems build target native cycles explicitly by rational normalization and
finite basis support.  The FINAL implication to the Hodge conjecture remains
CONDITIONAL on real geometric certificates for every target sheet.
That condition is never manufactured by choosing a cycle-class preimage.

Important mathematical distinction from the upstream OpenAI paper:
the actual period in its CM surface construction can lie in Qbar, and
algebraic coefficient descent is indispensable.  Certificates in this file
work over rational Betti cohomology with a scalar k in Q^×.  They are not
misrepresented as a full formalization of the Qbar/CM geometric case.

NEEDS CI RUN LATER.
-/

set_option maxHeartbeats 40000000
set_option maxRecDepth 800000

noncomputable section

open scoped BigOperators
open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeExactClayStatement
open GSTClassicalHodgeNativeExecutablePlane
open GSTClassicalHodgeCrossCarrierGeometricTransfer

namespace GSTClassicalHodgeOpenAIGeometricPeriodCertificates

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- A concrete rational cohomology state on a destination variety that
arises by a REAL cross-carrier cycle-class-natural geometric transfer from
an actual native cycle on a source variety. -/
def GeometricTransferOutputSet
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (q : Nat) :
    Set (RationalSingularCohomology H.analytification (2 * q)) :=
  { alpha | ∃ (S : SmoothProjectiveComplexScheme)
      (D : HodgeBigradedBettiData S)
      (s : Nat)
      (R : CrossCarrierTransfer S V D H s q)
      (Z : codimensionCycles S.X s),
      alpha = R.betti (D.cycleClass s Z) }

/-- The linear hull of REALIZED geometric outputs from arbitrary auxiliary
smooth projective algebraic carriers. -/
noncomputable def GeometricTransferOutputSpan
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (q : Nat) :
    Submodule ℚ (RationalSingularCohomology H.analytification (2 * q)) :=
  Submodule.span ℚ (GeometricTransferOutputSet V H q)

/-- Every already-supplied actual geometric transfer lies in the native
cycle-class range on the destination variety.  No Hodge conjecture assumed. -/
theorem geometricTransferOutputSet_algebraic
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (q : Nat)
    {alpha : RationalSingularCohomology H.analytification (2 * q)}
    (h : alpha ∈ GeometricTransferOutputSet V H q) :
    alpha ∈ LinearMap.range (H.cycleClass q) := by
  rcases h with ⟨S, D, s, R, Z, hZ⟩
  rw [hZ]
  exact R.native_range_preserved Z

/-- The geometric output span is an actual subspace of algebraic-cycle
classes even after arbitrary finite rational linear combinations. -/
theorem geometricTransferOutputSpan_le_algebraic
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (q : Nat) :
    GeometricTransferOutputSpan V H q ≤
      LinearMap.range (H.cycleClass q) := by
  apply Submodule.span_le.mpr
  intro alpha h
  exact geometricTransferOutputSet_algebraic V H q h

/-- An explicit period certificate for one Hodge sheet.  An inhabitant
requires genuine native and cohomological maps with their own naturality
proof, as well as a separately PROVED nonzero period identity. -/
structure GeometricSourcePeriodCertificate
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (q : Nat)
    (j : ClassicalHodgeBasisIndex V H q) where
  source : SmoothProjectiveComplexScheme
  sourceData : HodgeBigradedBettiData source
  sourceCodimension : Nat
  geometricTransfer :
    CrossCarrierTransfer source V sourceData H sourceCodimension q
  sourceNativeCycle :
    codimensionCycles source.X sourceCodimension
  period : ℚ
  nonzero_period : period ≠ 0
  exact_period_formula :
    geometricTransfer.betti
      (sourceData.cycleClass sourceCodimension sourceNativeCycle) =
      period • (classicalHodgeBasis V H q j).1

namespace GeometricSourcePeriodCertificate

variable {q : Nat} {j : ClassicalHodgeBasisIndex V H q}

/-- This is a genuinely CONSTRUCTED normalized native algebraic cycle,
built by transporting the stated source cycle through the geometric
correspondence and dividing by the independently supplied period. -/
noncomputable def normalizedNativeCycle
    (C : GeometricSourcePeriodCertificate V H q j) :
    codimensionCycles V.X q :=
  C.period⁻¹ • C.geometricTransfer.native C.sourceNativeCycle

/-- The normalized native cycle has precisely the selected Hodge basis
class as its rational cycle class. -/
theorem normalizedNativeCycle_spec
    (C : GeometricSourcePeriodCertificate V H q j) :
    H.cycleClass q C.normalizedNativeCycle =
      (classicalHodgeBasis V H q j).1 := by
  unfold normalizedNativeCycle
  rw [map_smul, C.geometricTransfer.naturality,
    C.exact_period_formula, smul_smul]
  simp [C.nonzero_period]

end GeometricSourcePeriodCertificate

/-- Pointwise existence of independently certified surface / auxiliary
variety transfers gives the BASIS normal form of rational algebraicity.
This is explicitly a premise, not a previously established theorem. -/
theorem basisCycleSupply_of_geometricCertificates
    (h : ∀ q : Nat, ∀ j : ClassicalHodgeBasisIndex V H q,
      Nonempty (GeometricSourcePeriodCertificate V H q j)) :
    HodgeBasisCycleSupply (V := V) (H := H) := by
  intro q j
  rcases h q j with ⟨C⟩
  exact ⟨C.normalizedNativeCycle, C.normalizedNativeCycle_spec⟩

/-- Finite-support assembly constructs a genuine rational algebraic cycle
for every rational Hodge state once real geometric certificates are given
for its basis directions. -/
noncomputable def classCycleOfGeometricCertificates
    (h : ∀ q : Nat, ∀ j : ClassicalHodgeBasisIndex V H q,
      Nonempty (GeometricSourcePeriodCertificate V H q j))
    (q : Nat) (alpha : ClassicalHodgeFiber V H q) :
    codimensionCycles V.X q :=
  ∑ j ∈ ((classicalHodgeBasis V H q).repr alpha).support,
    ((classicalHodgeBasis V H q).repr alpha j) •
      (Classical.choice (h q j)).normalizedNativeCycle

/-- EXACT reconstruction, with the actual native cycle supplied by the
finite support of the GST fibered Hodge address. -/
theorem classCycleOfGeometricCertificates_spec
    (h : ∀ q : Nat, ∀ j : ClassicalHodgeBasisIndex V H q,
      Nonempty (GeometricSourcePeriodCertificate V H q j))
    (q : Nat) (alpha : ClassicalHodgeFiber V H q) :
    H.cycleClass q (classCycleOfGeometricCertificates h q alpha) =
      alpha.1 := by
  unfold classCycleOfGeometricCertificates
  rw [map_sum]
  simp only [LinearMap.map_smul]
  have hexp : (alpha : RationalSingularCohomology H.analytification (2 * q)) =
      ∑ j ∈ ((classicalHodgeBasis V H q).repr alpha).support,
        ((classicalHodgeBasis V H q).repr alpha j) •
          ((classicalHodgeBasis V H q j).1 :
            RationalSingularCohomology H.analytification (2 * q)) := by
    have hrepr := ((classicalHodgeBasis V H q).linearCombination_repr alpha).symm
    rw [Finsupp.linearCombination_apply] at hrepr
    conv_lhs => rw [hrepr]
    simp [Finsupp.sum, Submodule.coe_sum, Submodule.coe_smul_of_tower]
  rw [hexp]
  apply Finset.sum_congr rfl
  intro j hj
  rw [(Classical.choice (h q j)).normalizedNativeCycle_spec]

/-- Full Hodge conclusion FROM full, independent, real geometric period
certificates.  This is not asserted unconditionally, since producing all
these certificates is the genuinely difficult geometric problem. -/
theorem exactHodge_of_completeGeometricCertificates
    (h : ∀ q : Nat, ∀ j : ClassicalHodgeBasisIndex V H q,
      Nonempty (GeometricSourcePeriodCertificate V H q j)) :
    BigradedBettiHodgeStatement V H := by
  exact hodge_of_basisCycleSupply
    (basisCycleSupply_of_geometricCertificates h)

/-- Source-level geometric span coverage, rather than basis-by-basis
normalization, gives a second exact realization criterion.
The substantive premise is coverage by genuine geometric transfers. -/
theorem exactHodge_of_geometricSpanCoversHodge
    (h : ∀ q : Nat,
      rationalHodgeSubspace (H.hodgeBigrading q) ≤
        GeometricTransferOutputSpan V H q) :
    BigradedBettiHodgeStatement V H := by
  intro q alpha halpha
  exact geometricTransferOutputSpan_le_algebraic V H q (h q halpha)

#check geometricTransferOutputSpan_le_algebraic
#check GeometricSourcePeriodCertificate.normalizedNativeCycle_spec
#check classCycleOfGeometricCertificates_spec
#check exactHodge_of_completeGeometricCertificates
#print axioms exactHodge_of_completeGeometricCertificates

end GSTClassicalHodgeOpenAIGeometricPeriodCertificates
