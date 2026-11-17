import GSTClassicalHodgeSingleExactSuccessorSurvival
import GSTClassicalHodgeGeometricCycleClassSpine
import GSTClassicalHodgeSynchronizedDefectOrbit
import GSTClassicalHodgeNativeTransferAddressIdentification

/-!
# GST CLASSICAL HODGE — SUCCESSOR SEED / HOMOLOGY-ESCAPE DICHOTOMY

The projective separator machinery constructs a genuine relative height-one
successor.  The single-survivor theorem shows that one exact ambient
codimension-(p+1) successor already forces the native principal-cut image of a
point atom to have nonzero rational mass.

This file pushes that fact simultaneously into the three relevant universes:

* genuine native algebraic cycles;
* genuine Betti cycle classes and the rational (p+1,p+1) Hodge sector;
* the limitless GST pure-Hodge / transfer universe.

There are then only two possibilities.

1. The successor cycle class is nonzero.  Because every algebraic cycle has
   Hodge type under the geometric cycle-class spine, the successor itself is a
   `NativeHodgeOrbitSeed`, exactly the seed consumed by the synchronized
   limitless orbit theorem.
2. The successor cycle class vanishes.  Then the actual projective geometry
   has produced a cycle with nonzero native mass and nonzero limitless GST
   shadow which is killed by Betti cycle class.  We isolate this as a
   `PositiveCosmicHomologyEscape`.

Thus seed nonvanishing is reduced to exclusion of one concrete geometric
escape.  No Hodge-surjectivity statement, basis-cycle representative, or
matrix-unit naturality is assumed here.
-/

set_option maxHeartbeats 60000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeSuccessorSeedEscapeDichotomy

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2G
open GSTNativeCodimensionCyclePresentation
open GSTClassicalHodgePointClosureRelativeCut
open GSTClassicalHodgePrincipalCutSuccessorOperator
open GSTClassicalHodgeNativeCycleCosmicShadow
open GSTClassicalHodgeSingleExactSuccessorSurvival
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeSynchronizedDefectOrbit
open GSTClassicalHodgeNativeTransferAddressIdentification
open GSTClassicalHodgeLimitlessCosmicMatrixUnits
open GSTClassicalHodgeHeightOneProjectiveRelevance
open GSTClassicalHodgeRelativeSuccessorNonempty
open GSTClassicalHodgeSeparatorRelativeCoheightOne
open GSTClassicalHodgeFiberedCosmology

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- A genuine native algebraic cycle whose projective/native content survives
in the limitless GST transfer universe although its genuine Betti cycle class
vanishes.  This is the exact escape that a projective degree/Poincare
compatibility theorem must exclude. -/
structure PositiveCosmicHomologyEscape
    (q : Nat) where
  cycle : codimensionCycles V.X q
  mass_ne_zero : nativeCycleMass V q cycle ≠ 0
  shadow_ne_zero : nativeCycleCosmicShadow V q cycle ≠ 0
  class_zero : H.cycleClass q cycle = 0

/-- Nonzero native mass is already visible as the coefficient at the cycle's
own limitless Hodge weight. -/
theorem nativeCycleCosmicShadow_self_ne_zero_of_mass
    (q : Nat)
    (Z : codimensionCycles V.X q)
    (hmass : nativeCycleMass V q Z ≠ 0) :
    nativeCycleCosmicShadow V q Z ≠ 0 := by
  intro hzero
  have hcoord := congrArg (fun f : RationalPureCosmos => f q) hzero
  simp [nativeCycleCosmicShadow, hmass] at hcoord

/-- Exact self-coordinate formula for the geometry-built successor shadow. -/
theorem successor_shadow_self_coordinate
    (p : Nat)
    (x : CodimensionPoint V.X p) :
    nativeCycleCosmicShadow V (p + 1)
        (successorNativeOperator V p
          (codimensionPointCycle V.X p x)) (p + 1) =
      successorMass V p x := by
  rw [successorNativeOperator_cosmicShadow_point]
  simp [rationalCosmicBasis]

/-- One exact separator successor produces a nonzero limitless GST shadow on
weight p+1. -/
theorem separator_successor_shadow_ne_zero_of_ambient_exact
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (hlive : ProjectivelyLiveSource V.projective.n
      (V.projective.immersion x.1))
    (hExact :
      Order.coheight
        (ambientSuccessorPoint V x.1
          (relativeHeightOneSeparatorSuccessor V x.1 hlive)) = p + 1) :
    nativeCycleCosmicShadow V (p + 1)
      (successorNativeOperator V p
        (codimensionPointCycle V.X p x)) ≠ 0 := by
  have hsurvive := separator_successor_survives_of_ambient_exact
    V p x hlive hExact
  have hmass : (nativeCycleMass V (p + 1))
      (successorNativeOperator V p (codimensionPointCycle V.X p x)) ≠ 0 := by
    rw [nativeCycleMass_successor_point]
    exact hsurvive.1
  exact nativeCycleCosmicShadow_self_ne_zero_of_mass
    (V := V) (p + 1)
    (successorNativeOperator V p (codimensionPointCycle V.X p x))
    hmass

/-- **SUCCESSOR SEED / HOMOLOGY-ESCAPE DICHOTOMY.**
Once the single canonical separator successor is known to occupy the exact
ambient codimension p+1, either it already gives the nonzero algebraic Hodge
seed needed by synchronized limitless saturation, or it is an explicit
positive cosmic homology escape. -/
theorem separator_successor_seed_or_escape
    (G : GeometricCycleClassSpine V H)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (hlive : ProjectivelyLiveSource V.projective.n
      (V.projective.immersion x.1))
    (hExact :
      Order.coheight
        (ambientSuccessorPoint V x.1
          (relativeHeightOneSeparatorSuccessor V x.1 hlive)) = p + 1) :
    Nonempty (NativeHodgeOrbitSeed (V := V) (H := H) (p := p + 1))
      ∨ Nonempty (PositiveCosmicHomologyEscape (V := V) (H := H) (p + 1)) := by
  let Z : codimensionCycles V.X (p + 1) :=
    successorNativeOperator V p (codimensionPointCycle V.X p x)
  have hsurvive := separator_successor_survives_of_ambient_exact
    V p x hlive hExact
  have hmass : nativeCycleMass V (p + 1) Z ≠ 0 := by
    show nativeCycleMass V (p + 1)
        (successorNativeOperator V p (codimensionPointCycle V.X p x)) ≠ 0
    rw [nativeCycleMass_successor_point]
    exact hsurvive.1
  have hshadow : nativeCycleCosmicShadow V (p + 1) Z ≠ 0 :=
    nativeCycleCosmicShadow_self_ne_zero_of_mass
      (V := V) (p + 1) Z hmass
  have hHodge : H.cycleClass (p + 1) Z ∈
      rationalHodgeSubspace (H.hodgeBigrading (p + 1)) :=
    G.algebraic_is_hodge (p + 1) Z
  by_cases hclass : H.cycleClass (p + 1) Z = 0
  · right
    exact ⟨{
      cycle := Z
      mass_ne_zero := hmass
      shadow_ne_zero := hshadow
      class_zero := hclass
    }⟩
  · left
    let alpha : ClassicalHodgeFiber V H (p + 1) :=
      ⟨H.cycleClass (p + 1) Z, hHodge⟩
    have halpha : alpha ≠ 0 := by
      intro hz
      apply hclass
      exact congrArg Subtype.val hz
    exact ⟨{
      cycle := Z
      hodge := alpha
      hodge_ne_zero := halpha
      class_eq := rfl
    }⟩

/-- The escape branch lies on the same established limitless transfer ray as
all genuine codimension-q projective cycles, with nonzero coefficient. -/
theorem escape_transfer_ray
    {q : Nat}
    (E : PositiveCosmicHomologyEscape (V := V) (H := H) q) :
    pureWeightToUniversalAddress (nativeCycleCosmicShadow V q E.cycle) =
      nativeCycleMass V q E.cycle •
        rationalizeCompactAddress
          (GSTTransferBridgeV2.compactClMono q) := by
  exact nativeCycle_shadow_eq_mass_transfer V q E.cycle

/-- If positive cosmic homology escapes are excluded, the exact separator
successor automatically supplies a synchronized native Hodge orbit seed. -/
theorem separator_successor_seed_of_no_escape
    (G : GeometricCycleClassSpine V H)
    (hNoEscape : ∀ q : Nat,
      IsEmpty (PositiveCosmicHomologyEscape (V := V) (H := H) q))
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (hlive : ProjectivelyLiveSource V.projective.n
      (V.projective.immersion x.1))
    (hExact :
      Order.coheight
        (ambientSuccessorPoint V x.1
          (relativeHeightOneSeparatorSuccessor V x.1 hlive)) = p + 1) :
    Nonempty (NativeHodgeOrbitSeed (V := V) (H := H) (p := p + 1)) := by
  rcases separator_successor_seed_or_escape G p x hlive hExact with hseed | hescape
  · exact hseed
  · exact False.elim (isEmpty_iff.mp (hNoEscape (p + 1)) (Classical.choice hescape))

#check PositiveCosmicHomologyEscape
#check nativeCycleCosmicShadow_self_ne_zero_of_mass
#check successor_shadow_self_coordinate
#check separator_successor_shadow_ne_zero_of_ambient_exact
#check separator_successor_seed_or_escape
#check escape_transfer_ray
#check separator_successor_seed_of_no_escape

#print axioms nativeCycleCosmicShadow_self_ne_zero_of_mass
#print axioms separator_successor_shadow_ne_zero_of_ambient_exact
#print axioms separator_successor_seed_or_escape
#print axioms separator_successor_seed_of_no_escape

end GSTClassicalHodgeSuccessorSeedEscapeDichotomy
