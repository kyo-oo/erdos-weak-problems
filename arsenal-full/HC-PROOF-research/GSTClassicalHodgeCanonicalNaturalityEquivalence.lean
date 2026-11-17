import GSTClassicalHodgeCanonicalLimitlessNaturalityCrown
import GSTClassicalHodgeArsenalNonCircularity
import GSTClassicalHodgeFiberedTransferCompletion
import GSTClassicalHodgeNativeCycleCosmicShadow

/-!
# GST CLASSICAL HODGE — CANONICAL NATURALITY / SATURATION EQUIVALENCE

The unrestricted GST cosmos completely controls the weight axis.  Native
codimension-p point cycles have an unconditional cosmic shadow supported at the
single weight p.  The fibered completion restores the independent multiplicity
sheets of the genuine classical Hodge fiber.

The remaining fixed-weight issue is therefore exact and unavoidable: does the
canonical cosmic read/write action between two multiplicity sheets preserve the
actual algebraic cycle-class range?

This file proves that, once a single nonzero algebraic Hodge seed exists in a
weight, the answer to that one naturality question is equivalent to complete
algebraic saturation of the Hodge fiber.  Thus it is not legitimate to insert
canonical cosmic naturality as an unexplained formal assumption and call the
Hodge proof complete.  It must be derived from the native/fibered geometry.

Conversely, this equivalence is useful positively: it shows that deriving the
single canonical no-escape law is sufficient—there are no additional hidden
basis-cycle obligations after it.
-/

set_option maxHeartbeats 50000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeCanonicalNaturalityEquivalence

open GSTProjectiveOverC
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgeLimitlessTwoSlotFailureDichotomy
open GSTClassicalHodgeCanonicalLimitlessNaturalityCrown
open GSTClassicalHodgeFiberedTransferCompletion
open GSTClassicalHodgeNativeCycleCosmicShadow
open GSTClassicalHodgeConcreteFailureDichotomy

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- If the algebraic Hodge fiber is already the whole Hodge fiber, canonical
cosmic naturality is automatic. -/
theorem canonicalCosmicNaturality_of_eq_top
    (htop : AlgebraicFiber (V := V) (H := H) (p := p) = ⊤) :
    CanonicalCosmicNaturality (V := V) (H := H) p := by
  intro i j alpha halpha
  rw [htop]
  trivial

/-- **FIXED-WEIGHT EQUIVALENCE.**  In the presence of one nonzero algebraic
Hodge seed, preservation by the one true limitless cosmic read/write operator
is equivalent to complete algebraic saturation of the weight-p Hodge fiber. -/
theorem canonicalCosmicNaturality_iff_algebraicFiber_eq_top
    (hseed : AlgebraicFiber (V := V) (H := H) (p := p) ≠ ⊥) :
    CanonicalCosmicNaturality (V := V) (H := H) p ↔
      AlgebraicFiber (V := V) (H := H) (p := p) = ⊤ := by
  constructor
  · intro hcosmic
    exact algebraicFiber_eq_top hseed hcosmic
  · exact canonicalCosmicNaturality_of_eq_top

/-- The exact Stage-2G weight statement is equivalent to topness of the
algebraic Hodge fiber. -/
theorem hodgeWeight_iff_algebraicFiber_eq_top :
    (rationalHodgeSubspace (H.hodgeBigrading p) ≤
      LinearMap.range (H.cycleClass p)) ↔
      AlgebraicFiber (V := V) (H := H) (p := p) = ⊤ := by
  constructor
  · intro h
    apply top_unique
    intro alpha _
    have hrange : alpha.1 ∈ LinearMap.range (H.cycleClass p) :=
      h alpha.2
    rw [smoothProjective_cycleClass_range_eq_atomic_span V H p] at hrange
    exact hrange
  · intro htop alpha halpha
    let alphaH : ClassicalHodgeFiber V H p := ⟨alpha, halpha⟩
    have halg : alphaH ∈ AlgebraicFiber (V := V) (H := H) (p := p) := by
      rw [htop]
      trivial
    rw [smoothProjective_cycleClass_range_eq_atomic_span V H p]
    exact halg

/-- With a seed, the one canonical limitless naturality law is therefore
literally equivalent to the exact weight-p Hodge target. -/
theorem canonicalCosmicNaturality_iff_hodgeWeight
    (hseed : AlgebraicFiber (V := V) (H := H) (p := p) ≠ ⊥) :
    CanonicalCosmicNaturality (V := V) (H := H) p ↔
      rationalHodgeSubspace (H.hodgeBigrading p) ≤
        LinearMap.range (H.cycleClass p) := by
  exact (canonicalCosmicNaturality_iff_algebraicFiber_eq_top hseed).trans
    hodgeWeight_iff_algebraicFiber_eq_top.symm

/-! ## Why the base cosmic address does not by itself resolve multiplicity -/

/-- Every classical multiplicity sheet over the same weight projects to the
same base limitless GST generator. -/
theorem all_multiplicity_sheets_have_same_base_shadow
    (i j : ClassicalHodgeBasisIndex V H p) :
    forgetMultiplicityToGST (fiberedSheetGenerator V H ⟨p,i⟩) =
      forgetMultiplicityToGST (fiberedSheetGenerator V H ⟨p,j⟩) := by
  rw [fiberedSheet_projects_to_cosmicGenerator]
  rw [fiberedSheet_projects_to_cosmicGenerator]

/-- Likewise every genuine unit native point cycle in codimension p has the
same base cosmic shadow.  Thus native projective support and Hodge
multiplicity both require the richer fibered/native refinement before the
final no-escape theorem can distinguish them. -/
theorem all_native_point_cycles_have_same_base_shadow
    (x y : GSTNativeCodimensionCyclePresentation.CodimensionPoint V.X p) :
    nativeCycleCosmicShadow V p
        (GSTNativeCodimensionCyclePresentation.codimensionPointCycle V.X p x) =
      nativeCycleCosmicShadow V p
        (GSTNativeCodimensionCyclePresentation.codimensionPointCycle V.X p y) := by
  rw [nativeCycleCosmicShadow_point]
  rw [nativeCycleCosmicShadow_point]

/-- Crown: the base limitless address theorem is complete on the weight axis,
while the sole fixed-weight completion target is canonical multiplicity
naturality. -/
theorem canonical_naturality_equivalence_crown
    (hseed : AlgebraicFiber (V := V) (H := H) (p := p) ≠ ⊥) :
    (CanonicalCosmicNaturality (V := V) (H := H) p ↔
      rationalHodgeSubspace (H.hodgeBigrading p) ≤
        LinearMap.range (H.cycleClass p))
    ∧ (∀ i j : ClassicalHodgeBasisIndex V H p,
      forgetMultiplicityToGST (fiberedSheetGenerator V H ⟨p,i⟩) =
        forgetMultiplicityToGST (fiberedSheetGenerator V H ⟨p,j⟩)) := by
  exact ⟨canonicalCosmicNaturality_iff_hodgeWeight hseed,
    all_multiplicity_sheets_have_same_base_shadow⟩

#check canonicalCosmicNaturality_of_eq_top
#check canonicalCosmicNaturality_iff_algebraicFiber_eq_top
#check hodgeWeight_iff_algebraicFiber_eq_top
#check canonicalCosmicNaturality_iff_hodgeWeight
#check all_multiplicity_sheets_have_same_base_shadow
#check all_native_point_cycles_have_same_base_shadow
#check canonical_naturality_equivalence_crown

#print axioms canonicalCosmicNaturality_iff_algebraicFiber_eq_top
#print axioms hodgeWeight_iff_algebraicFiber_eq_top
#print axioms canonicalCosmicNaturality_iff_hodgeWeight
#print axioms canonical_naturality_equivalence_crown

end GSTClassicalHodgeCanonicalNaturalityEquivalence
