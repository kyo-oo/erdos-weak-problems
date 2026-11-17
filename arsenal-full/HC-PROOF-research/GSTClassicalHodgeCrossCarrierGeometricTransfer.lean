import GSTClassicalHodgeExactClayStatement
import GSTClassicalHodgeFiberedCosmology

/-!
# GST cross-carrier geometric correspondence calculus

Research integration of OpenAI/math (2026), family 032:
* `The rational Hodge conjecture for CM abelian varieties`, section 3
  ("A surface criterion for the switch").
* `Algebraic Kuga--Satake correspondences and Hodge conjectures on a
  K3 quadratic locus`, section 1.
* `Abelian covers, Gale correspondences, and the Hodge conjecture for
  powers`, section "The perfect Gale correspondence".

The cited papers pass between DISTINCT smooth projective carriers (a surface,
products of CM abelian varieties, and auxiliary varieties).  Earlier GST
`FiniteClosedCorrespondence` engines chiefly work with self-correspondences.

The purpose of this file is to construct, and prove closed under identity,
composition, addition and rational rescaling, the *cross-carrier*
cycle-class naturality square.  The surface-switch extraction lemma calculates
the actual native target cycle when a genuine geometric correspondence has
nonzero period on a target Hodge state.

IMPORTANT SCOPE:
- The carrier `CrossCarrierTransfer` is a geometric realization INTERFACE.
  An inhabitant needs an actual native map, a Betti map, and their commuting
  square; this file does not postulate that those exist universally.
- The extraction theorem neither assumes nor concludes that an arbitrary
  Hodge class has an appropriate period witness.
- No Hodge conjecture, CM-paper claim, or ghost-extinction statement is
  asserted unconditionally here.
- No axioms or sorry placeholders are introduced.
-/

set_option maxHeartbeats 2000000

noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology

namespace GSTClassicalHodgeCrossCarrierGeometricTransfer

/-- An actual algebraic-cycle/Betti realization BETWEEN TWO CARRIERS.

For a correspondence built from a surface, a divisor kernel or a Gale
construction, `native` is the induced push/pull action on native rational
algebraic cycles; `betti` is the same geometric action on rational singular
cohomology.  The condition `naturality` must be proved from geometry. -/
structure CrossCarrierTransfer
    (V W : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (J : HodgeBigradedBettiData W)
    (p q : Nat) where
  native :
    codimensionCycles V.X p →ₗ[ℚ] codimensionCycles W.X q
  betti :
    RationalSingularCohomology H.analytification (2 * p) →ₗ[ℚ]
      RationalSingularCohomology J.analytification (2 * q)
  naturality :
    ∀ Z : codimensionCycles V.X p,
      J.cycleClass q (native Z) = betti (H.cycleClass p Z)

variable {V W U : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {J : HodgeBigradedBettiData W}
variable {K : HodgeBigradedBettiData U}
variable {p q r : Nat}

namespace CrossCarrierTransfer

/-- The diagonal correspondence acts by the identity on both sides. -/
def identity
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V) (p : Nat) :
    CrossCarrierTransfer V V H H p p where
  native := LinearMap.id
  betti := LinearMap.id
  naturality := by
    intro Z
    rfl

/-- Composition of two genuine cross-carrier transfers.  This is the
mathematical operation used to connect surface, CM and target carriers
without falsely identifying their respective cycle spaces. -/
def compose
    (S : CrossCarrierTransfer W U J K q r)
    (R : CrossCarrierTransfer V W H J p q) :
    CrossCarrierTransfer V U H K p r where
  native := S.native.comp R.native
  betti := S.betti.comp R.betti
  naturality := by
    intro Z
    change K.cycleClass r (S.native (R.native Z)) =
      S.betti (R.betti (H.cycleClass p Z))
    rw [S.naturality, R.naturality]

/-- Rational linear combination of correspondences on a fixed carrier pair. -/
def add
    (R S : CrossCarrierTransfer V W H J p q) :
    CrossCarrierTransfer V W H J p q where
  native := R.native + S.native
  betti := R.betti + S.betti
  naturality := by
    intro Z
    change J.cycleClass q (R.native Z + S.native Z) =
      R.betti (H.cycleClass p Z) + S.betti (H.cycleClass p Z)
    rw [map_add, R.naturality, S.naturality]

/-- Rescaling a genuine cycle correspondence rescales its Betti action. -/
def rescale
    (a : ℚ) (R : CrossCarrierTransfer V W H J p q) :
    CrossCarrierTransfer V W H J p q where
  native := a • R.native
  betti := a • R.betti
  naturality := by
    intro Z
    change J.cycleClass q (a • R.native Z) =
      a • R.betti (H.cycleClass p Z)
    rw [map_smul, R.naturality]

/-- Every image of a genuine source cycle under a geometric transfer
remains in the NATIVE cycle-class range on the destination carrier. -/
theorem native_range_preserved
    (R : CrossCarrierTransfer V W H J p q)
    (Z : codimensionCycles V.X p) :
    R.betti (H.cycleClass p Z) ∈ LinearMap.range (J.cycleClass q) :=
  ⟨R.native Z, R.naturality Z⟩

/-- SURFACE-SWITCH EXTRACTION.

In the cited CM construction an algebraic surface image is paired against a
four-factor Hodge line and then transported by algebraic divisor kernels.
When the mixed period is k != 0, the transported native cycle has class
k times the target vector.  Dividing that actual native cycle by k gives
the required target cycle, rather than merely a numerical functional.

This abstract lemma proves the normalization and the native conclusion for
ANY geometrically realized cross-carrier action.  Constructing the concrete
surface/divisor kernels and proving the period identity are separate
nontrivial geometric problems, not hidden in this lemma. -/
theorem native_target_of_nonzero_geometric_period
    (R : CrossCarrierTransfer V W H J p q)
    (sourceCycle : codimensionCycles V.X p)
    (target : ClassicalHodgeFiber W J q)
    (k : ℚ) (hk : k ≠ 0)
    (hperiod :
      R.betti (H.cycleClass p sourceCycle) = k • target.1) :
    ∃ targetCycle : codimensionCycles W.X q,
      J.cycleClass q targetCycle = target.1 := by
  refine ⟨k⁻¹ • R.native sourceCycle, ?_⟩
  rw [map_smul, R.naturality, hperiod, smul_smul]
  simp [hk]

/-- The same extraction survives MULTIPLE geometric carriers: first
transfer onto an auxiliary variety, then use a second correspondence
into the final target variety.  This is the required pattern for
surface -> auxiliary abelian product -> destination. -/
theorem native_target_of_composed_period
    (R : CrossCarrierTransfer V W H J p q)
    (S : CrossCarrierTransfer W U J K q r)
    (sourceCycle : codimensionCycles V.X p)
    (target : ClassicalHodgeFiber U K r)
    (k : ℚ) (hk : k ≠ 0)
    (hperiod :
      S.betti (R.betti (H.cycleClass p sourceCycle)) = k • target.1) :
    ∃ targetCycle : codimensionCycles U.X r,
      K.cycleClass r targetCycle = target.1 := by
  exact native_target_of_nonzero_geometric_period
    (S.compose R) sourceCycle target k hk hperiod

end CrossCarrierTransfer

#check CrossCarrierTransfer.identity
#check CrossCarrierTransfer.compose
#check CrossCarrierTransfer.add
#check CrossCarrierTransfer.rescale
#check CrossCarrierTransfer.native_range_preserved
#check CrossCarrierTransfer.native_target_of_nonzero_geometric_period
#check CrossCarrierTransfer.native_target_of_composed_period

#print axioms CrossCarrierTransfer.native_target_of_nonzero_geometric_period
#print axioms CrossCarrierTransfer.native_target_of_composed_period

end GSTClassicalHodgeCrossCarrierGeometricTransfer
