import GSTClassicalHodgeLimitlessTwoSlotFailureDichotomy
import GSTClassicalHodgeLimitlessProjectiveLefschetzTower
import GSTClassicalHodgeCrossWeightNativePropagation
import GSTClassicalHodgeAtomicSpan

/-!
# GST CLASSICAL HODGE — CANONICAL LIMITLESS NATURALITY CROWN

The rank-free failure theorem reduces fixed-weight Hodge algebraicity to one
canonical operation: the true limitless cosmic matrix unit, observed through
an arbitrary two-sheet chart.  It is unnecessary, and mathematically too
strong, to postulate unrelated projective self-maps realizing every abstract
basis matrix unit.

This module records the minimal geometric naturality statement for the single
canonical limitless operator and proves that it is exactly enough to eliminate
the escape alternative produced by `proper_algebraicFiber_zero_or_limitlessCosmicEscape`.

The second artery is cross-weight propagation.  Once one nonzero algebraic
Hodge seed is available in weight zero, the already constructed native
projective successor tower transports algebraicity to every weight.  Therefore
one canonical fixed-weight naturality law plus one canonical graded successor
naturality law are sufficient for the complete Stage-2G statement.

Neither law states cycle-class surjectivity or supplies basis-cycle witnesses.
They are operator compatibility laws for independently constructed GST/native
operators.
-/

set_option maxHeartbeats 70000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeCanonicalLimitlessNaturalityCrown

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgeLimitlessTwoSlotFailureDichotomy
open GSTClassicalHodgeLimitlessCosmicMatrixUnits
open GSTClassicalHodgeCrossWeightNativePropagation
open GSTClassicalHodgeConcreteFailureDichotomy
open GSTClassicalHodgeRankFreePrimitiveGeneration

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- The one canonical fixed-weight naturality law demanded by the limitless
failure dichotomy.  It says that the true cosmic read/write operator preserves
the actual algebraic Hodge subspace in every finite two-sheet observation.

This is deliberately about the already-defined cosmic operator itself, not an
arbitrary matrix-unit family. -/
def CanonicalCosmicNaturality (p : Nat) : Prop :=
  ∀ i j : ClassicalHodgeBasisIndex V H p,
    ∀ alpha : ClassicalHodgeFiber V H p,
      alpha ∈ AlgebraicFiber (V := V) (H := H) (p := p) →
      liftCosmicWindowOperator (pairBasisIndex i j)
          (rationalCosmicMatrixUnit sourceSlot.1 targetSlot.1) alpha ∈
        AlgebraicFiber (V := V) (H := H) (p := p)

/-- The canonical naturality law rules out every limitless cosmic escape. -/
theorem not_limitlessCosmicEscape
    {p : Nat}
    (hcosmic : CanonicalCosmicNaturality (V := V) (H := H) p) :
    ¬ Nonempty (LimitlessCosmicEscape (V := V) (H := H) (p := p)) := by
  rintro ⟨E⟩
  exact E.escapes (hcosmic E.source E.target E.alpha E.alpha_algebraic)

/-- **FIXED-WEIGHT LIMITLESS SATURATION.**
One nonzero algebraic Hodge state and canonical cosmic naturality force the
whole Hodge fiber to be algebraic. -/
theorem algebraicFiber_eq_top
    {p : Nat}
    (hseed : AlgebraicFiber (V := V) (H := H) (p := p) ≠ ⊥)
    (hcosmic : CanonicalCosmicNaturality (V := V) (H := H) p) :
    AlgebraicFiber (V := V) (H := H) (p := p) = ⊤ := by
  by_contra hproper
  rcases proper_algebraicFiber_zero_or_limitlessCosmicEscape
      (V := V) (H := H) (p := p) hproper with hzero | hescape
  · exact hseed hzero
  · exact (not_limitlessCosmicEscape hcosmic) hescape

/-- Fixed-weight exact Stage-2G range statement. -/
theorem hodge_weight
    {p : Nat}
    (hseed : AlgebraicFiber (V := V) (H := H) (p := p) ≠ ⊥)
    (hcosmic : CanonicalCosmicNaturality (V := V) (H := H) p) :
    rationalHodgeSubspace (H.hodgeBigrading p) ≤
      LinearMap.range (H.cycleClass p) := by
  have htop := algebraicFiber_eq_top hseed hcosmic
  intro alpha halpha
  let alphaH : ClassicalHodgeFiber V H p := ⟨alpha, halpha⟩
  have halg : alphaH ∈ AlgebraicFiber (V := V) (H := H) (p := p) := by
    rw [htop]
    trivial
  rw [smoothProjective_cycleClass_range_eq_atomic_span V H p]
  exact halg

/-- Cross-weight seed propagation supplies the nonzero algebraic seed at every
weight from the single base seed. -/
theorem propagatedSeed_ne_bot
    (F : SeedPropagationFamily V H)
    (h0 : F.seed 0 ∈ AlgebraicHodgeSubspace V H 0)
    (h0ne : F.seed 0 ≠ 0)
    (p : Nat) :
    AlgebraicFiber (V := V) (H := H) (p := p) ≠ ⊥ := by
  have hpAlg : F.seed p ∈ AlgebraicHodgeSubspace V H p :=
    F.algebraic_of_zero_seed h0 p
  have hpNe : F.seed p ≠ 0 := F.seed_ne_zero p
  intro hbot
  have : F.seed p = 0 := by
    have hm : F.seed p ∈ (⊥ : Submodule ℚ (ClassicalHodgeFiber V H p)) := by
      rw [← hbot]
      exact hpAlg
    simpa using hm
  exact hpNe this

/-- **CANONICAL LIMITLESS GLOBAL CROWN.**
A single nonzero algebraic seed at weight zero, genuine cross-weight native
propagation, and naturality of the one true cosmic read/write operator in every
weight imply the exact Stage-2G Hodge statement. -/
theorem bigradedBettiHodge
    (F : SeedPropagationFamily V H)
    (h0 : F.seed 0 ∈ AlgebraicHodgeSubspace V H 0)
    (h0ne : F.seed 0 ≠ 0)
    (hcosmic : ∀ p : Nat,
      CanonicalCosmicNaturality (V := V) (H := H) p) :
    BigradedBettiHodgeStatement V H := by
  intro p alpha halpha
  exact hodge_weight
    (propagatedSeed_ne_bot F h0 h0ne p)
    (hcosmic p)
    halpha

#check CanonicalCosmicNaturality
#check not_limitlessCosmicEscape
#check algebraicFiber_eq_top
#check hodge_weight
#check propagatedSeed_ne_bot
#check bigradedBettiHodge

#print axioms not_limitlessCosmicEscape
#print axioms algebraicFiber_eq_top
#print axioms hodge_weight
#print axioms bigradedBettiHodge

end GSTClassicalHodgeCanonicalLimitlessNaturalityCrown
