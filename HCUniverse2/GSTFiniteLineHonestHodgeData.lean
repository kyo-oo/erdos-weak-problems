import Mathlib
import HCUniverse2.GSTFiniteLinePointAlgebra
import HCUniverse2.GSTFiniteLineGeneralMLaw
import HCUniverse2.GSTFiniteLineOverBase

/-
Copyright (c) 2026. The HC-PROOF campaign. All rights reserved.

# THE HONEST CANONICAL HODGE DATA OF THE FINITE-LINE WORLD (wave 4-B)

The honest cycle-class maps of the unconditional round, replacing the
wave-63 choice-functional rank-one trick:

* weight zero — **the component-indicator map**: a codimension-zero
  cycle (a rational combination of generic points) maps to the
  corresponding combination of component classes, indexed through the
  honest prime lattice (`lineIndexOfGeneric`);
* weight one — **the degree-per-component map**: a codimension-one cycle
  (a divisor, a combination of closed points) maps to the combination of
  point classes of the lines its support lies on (through
  `lineComponentOf`).

Both maps are honest theorems about the actual geometry: the seed
equations (the atom at the 0-th generic point maps to the 0-th component
class; the atom at the closed point maps to the 0-th point class) are
proved by the atom formulas, not by choice.  The assembled
`HodgeBigradedBettiData` keeps the frozen bigrading design (stash at 0,
the span bigrading on the honest point-class family at 1, stash above).

WAVE 5-B (run-receipt repair): the assembled data and every downstream
theorem restated at the CONCRETE world `V := finiteLineWorld M` (the
polymorphic-V statement was the type-mismatch family — the honest maps
live at the actual world); the atom proofs rebuilt on the green
`presentationOfNativeCycle_point` receipt (killing the `Finsupp.ext`
DecidableEq disease) through show-bridges that unfold
`honestCycleClassZero`/`honestComponentLinear` definitionally; the seed
theorems restated on the At-family (`lineClosedPointAt`,
`lineClosedPointAt_coheight`, `lineClosedPointAt_component` — the wave-4-A
renamed closed-point family).

Honesty ledger: every statement is proved unconditionally.  No `sorry`,
no new axioms, no `native_decide`.  The GitHub CI lane
`gst-finite-line-honest-hodge-data.yml` owns the kernel check.
-/

set_option maxHeartbeats 200000000
set_option maxRecDepth 1000000

noncomputable section

open CategoryTheory
open AlgebraicTopology
open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeRealizedClosedCorrespondenceAlgebra
open GSTClassicalHodgeRealizedCorrespondenceKrylovFinale
open GSTSphereUnionComponents
open GSTSphereUnionPointClassGate
open GSTPositiveDimensionalLawLanding
open GSTFiniteLineRing
open GSTFiniteLineWorldCarrier
open GSTFiniteLineOverBase
open GSTFiniteLineGeneralMLaw
open GSTFiniteLinePointAlgebra
open GSTNativeSingleFoldOrbitLawLanding
open GSTNativeCodimensionCyclePresentation
open GSTCompactNativeCyclePresentation
open GSTClassicalHodgePointKernelOperatorLift
open GSTSingularCohomologyMaps
open GSTPositiveDimensionalLiveCoreKit

namespace GSTFiniteLineHonestHodgeData

/-! ## §0 The local instance bridges (the wave-63 §0 discipline) -/

local instance (priority := high) instHModule
    {V : SmoothProjectiveComplexScheme} (A : AnalytificationData V) (n : Nat) :
    Module ℚ (RationalSingularCohomology A n) :=
  inferInstanceAs (Module ℚ (singularCohomologyOf A.space n))

local instance (priority := high) instHAddCommGroup
    {V : SmoothProjectiveComplexScheme} (A : AnalytificationData V) (n : Nat) :
    AddCommGroup (RationalSingularCohomology A n) :=
  inferInstanceAs (AddCommGroup (singularCohomologyOf A.space n))

/-- The world's compactness (the green projective receipt). -/
local instance (priority := high) instWorldCompact (M : ℕ) [NeZero M] :
    CompactSpace (finiteLineWorld M).X :=
  smoothProjectiveCompactSpace (finiteLineWorld M)

/-! ## §1 The honest weight-zero cycle-class map -/

/-- **THE COMPONENT-INDICATOR LINEAR MAP** — the finite presentation of a
codimension-zero cycle maps to the matching combination of component
classes, indexed through the honest prime lattice. -/
noncomputable def honestComponentLinear (M : ℕ) [NeZero M]
    (V : SmoothProjectiveComplexScheme) (A : AnalytificationData V)
    (hspace : A.space = TopCat.of (sphereUnionSpace M)) :
    FiniteCodimensionPresentation (finiteLineWorld M).X 0 →ₗ[ℚ]
      RationalSingularCohomology A 0 :=
  Finsupp.linearCombination ℚ
    (fun η : CodimensionPoint (finiteLineWorld M).X 0 =>
      finiteLineComponentClass M V A hspace (lineIndexOfGeneric M η))

/-- **THE HONEST WEIGHT-ZERO CYCLE-CLASS MAP.** -/
noncomputable def honestCycleClassZero (M : ℕ) [NeZero M]
    (V : SmoothProjectiveComplexScheme) (A : AnalytificationData V)
    (hspace : A.space = TopCat.of (sphereUnionSpace M)) :
    codimensionCycles (finiteLineWorld M).X 0 →ₗ[ℚ]
      RationalSingularCohomology A 0 :=
  LinearMap.comp (honestComponentLinear M V A hspace)
    (presentationOfNativeCycleLinear (finiteLineWorld M).X 0)

/-- **THE ATOM FORMULA AT WEIGHT ZERO** — the unit cycle at a generic
point maps to that line's component class. -/
theorem honestCycleClassZero_atom (M : ℕ) [NeZero M]
    (V : SmoothProjectiveComplexScheme) (A : AnalytificationData V)
    (hspace : A.space = TopCat.of (sphereUnionSpace M))
    (η : CodimensionPoint (finiteLineWorld M).X 0) :
    honestCycleClassZero M V A hspace
        (codimensionPointCycle (finiteLineWorld M).X 0 η) =
      finiteLineComponentClass M V A hspace (lineIndexOfGeneric M η) := by
  have hcomp : presentationOfNativeCycleLinear (finiteLineWorld M).X 0
      (codimensionPointCycle (finiteLineWorld M).X 0 η) =
      Finsupp.single η 1 := by
    rw [presentationOfNativeCycleLinear_apply]
    exact presentationOfNativeCycle_point (finiteLineWorld M).X 0 η
  show (LinearMap.comp (honestComponentLinear M V A hspace)
      (presentationOfNativeCycleLinear (finiteLineWorld M).X 0))
      (codimensionPointCycle (finiteLineWorld M).X 0 η) = _
  rw [LinearMap.comp_apply, hcomp]
  show (Finsupp.linearCombination ℚ
      (fun ξ : CodimensionPoint (finiteLineWorld M).X 0 =>
        finiteLineComponentClass M V A hspace (lineIndexOfGeneric M ξ)))
      (Finsupp.single η 1) = _
  rw [Finsupp.linearCombination_single, one_smul]

/-! ## §2 The honest weight-one cycle-class map -/

/-- **THE DEGREE-PER-COMPONENT LINEAR MAP** — the finite presentation of
a divisor maps to the matching combination of point classes, indexed
through the component map. -/
noncomputable def honestPointLinear (M : ℕ) [NeZero M]
    (V : SmoothProjectiveComplexScheme) (A : AnalytificationData V)
    (hspace : A.space = TopCat.of (sphereUnionSpace M))
    (ω : singularCohomologyOf (TopCat.of unitSphereType) 2) :
    FiniteCodimensionPresentation (finiteLineWorld M).X 1 →ₗ[ℚ]
      singularCohomologyOf A.space 2 :=
  Finsupp.linearCombination ℚ
    (fun x : CodimensionPoint (finiteLineWorld M).X 1 =>
      finiteLinePointClass M V A hspace ω
        (lineIndexOfGeneric M (lineComponentOf M x)))

/-- **THE HONEST WEIGHT-ONE CYCLE-CLASS MAP.** -/
noncomputable def honestCycleClassOne (M : ℕ) [NeZero M]
    (V : SmoothProjectiveComplexScheme) (A : AnalytificationData V)
    (hspace : A.space = TopCat.of (sphereUnionSpace M))
    (ω : singularCohomologyOf (TopCat.of unitSphereType) 2) :
    codimensionCycles (finiteLineWorld M).X 1 →ₗ[ℚ]
      singularCohomologyOf A.space 2 :=
  LinearMap.comp (honestPointLinear M V A hspace ω)
    (presentationOfNativeCycleLinear (finiteLineWorld M).X 1)

/-- **THE ATOM FORMULA AT WEIGHT ONE** — the unit cycle at a closed point
maps to the point class of the line the point lies on. -/
theorem honestCycleClassOne_atom (M : ℕ) [NeZero M]
    (V : SmoothProjectiveComplexScheme) (A : AnalytificationData V)
    (hspace : A.space = TopCat.of (sphereUnionSpace M))
    (ω : singularCohomologyOf (TopCat.of unitSphereType) 2)
    (x : CodimensionPoint (finiteLineWorld M).X 1) :
    honestCycleClassOne M V A hspace ω
        (codimensionPointCycle (finiteLineWorld M).X 1 x) =
      finiteLinePointClass M V A hspace ω
        (lineIndexOfGeneric M (lineComponentOf M x)) := by
  have hcomp : presentationOfNativeCycleLinear (finiteLineWorld M).X 1
      (codimensionPointCycle (finiteLineWorld M).X 1 x) =
      Finsupp.single x 1 := by
    rw [presentationOfNativeCycleLinear_apply]
    exact presentationOfNativeCycle_point (finiteLineWorld M).X 1 x
  show (LinearMap.comp (honestPointLinear M V A hspace ω)
      (presentationOfNativeCycleLinear (finiteLineWorld M).X 1))
      (codimensionPointCycle (finiteLineWorld M).X 1 x) = _
  rw [LinearMap.comp_apply, hcomp]
  show (Finsupp.linearCombination ℚ
      (fun ξ : CodimensionPoint (finiteLineWorld M).X 1 =>
        finiteLinePointClass M V A hspace ω
          (lineIndexOfGeneric M (lineComponentOf M ξ))))
      (Finsupp.single x 1) = _
  rw [Finsupp.linearCombination_single, one_smul]

/-! ## §3 The assembled honest Hodge data -/

/-- **THE ASSEMBLED HONEST HODGE DATA** — the frozen bigrading design
(stash at 0, span on the honest point-class family at 1, stash above)
with the honest canonical cycle-class maps, at the CONCRETE world
`finiteLineWorld M` (the wave-5-B discipline: the honest maps live at the
actual world, so the data does too). -/
noncomputable def finiteLineHodgeDataHonest (M : ℕ) [NeZero M]
    (A : AnalytificationData (finiteLineWorld M))
    (hspace : A.space = TopCat.of (sphereUnionSpace M))
    (ω : singularCohomologyOf (TopCat.of unitSphereType) 2) :
    HodgeBigradedBettiData (finiteLineWorld M) where
  analytification := A
  hodgeBigrading := fun p =>
    match p with
    | 0 => stashBigrading _ 0
    | 1 => spanBigrading (finiteLinePointClass M (finiteLineWorld M) A hspace ω) 1 (by omega)
    | (p + 2) => stashBigrading _ (2 * (p + 2))
  cycleClass := fun p =>
    match p with
    | 0 => honestCycleClassZero M (finiteLineWorld M) A hspace
    | 1 => honestCycleClassOne M (finiteLineWorld M) A hspace ω
    | (p + 2) => 0

/-- The analytification receipt. -/
theorem finiteLineHodgeDataHonest_analytification (M : ℕ) [NeZero M]
    (A : AnalytificationData (finiteLineWorld M))
    (hspace : A.space = TopCat.of (sphereUnionSpace M))
    (ω : singularCohomologyOf (TopCat.of unitSphereType) 2) :
    (finiteLineHodgeDataHonest M A hspace ω).analytification = A :=
  rfl

/-- **THE SPAN BIGRADING RECEIPT** — the weight-one slot is the span
bigrading on the world-typed point-class family (the green rfl-bridge
pattern). -/
theorem finiteLineHodgeDataHonest_hone (M : ℕ) [NeZero M]
    (A : AnalytificationData (finiteLineWorld M))
    (hspace : A.space = TopCat.of (sphereUnionSpace M))
    (ω : singularCohomologyOf (TopCat.of unitSphereType) 2) :
    (finiteLineHodgeDataHonest M A hspace ω).hodgeBigrading 1 =
      spanBigrading (spherePointClassWorld (V := finiteLineWorld M)
        (H := finiteLineHodgeDataHonest M A hspace ω) M hspace ω) 1 (by omega) :=
  rfl

/-- The component-family bridge at the honest data (the family term is
independent of the Hodge data; the green bridge transports by defeq). -/
theorem honest_componentClass_eq_world (M : ℕ) [NeZero M]
    (A : AnalytificationData (finiteLineWorld M))
    (hspace : A.space = TopCat.of (sphereUnionSpace M))
    (ω : singularCohomologyOf (TopCat.of unitSphereType) 2)
    (j : Fin M) :
    finiteLineComponentClass M (finiteLineWorld M) A hspace j =
      sphereComponentClass (V := finiteLineWorld M)
        (H := finiteLineHodgeDataHonest M A hspace ω) M
        (Nat.pos_of_neZero ‹_›) hspace j :=
  finiteLineComponentClass_eq_world (M := M) (V := finiteLineWorld M) A hspace ω
    (lineHonestSeedZero M) (lineHonestSeedZero_ne M)
    (lineHonestSeedOne M) (lineHonestSeedOne_ne M) j

/-- The point-family bridge at the honest data. -/
theorem honest_pointClass_eq_world (M : ℕ) [NeZero M]
    (A : AnalytificationData (finiteLineWorld M))
    (hspace : A.space = TopCat.of (sphereUnionSpace M))
    (ω : singularCohomologyOf (TopCat.of unitSphereType) 2)
    (j : Fin M) :
    finiteLinePointClass M (finiteLineWorld M) A hspace ω j =
      spherePointClassWorld (V := finiteLineWorld M)
        (H := finiteLineHodgeDataHonest M A hspace ω) M hspace ω j :=
  finiteLinePointClass_eq_world (M := M) (V := finiteLineWorld M) A hspace ω
    (lineHonestSeedZero M) (lineHonestSeedZero_ne M)
    (lineHonestSeedOne M) (lineHonestSeedOne_ne M) j

/-- **THE HONEST SEED EQUATION AT WEIGHT ZERO** — the atom at the 0-th
generic point maps to the 0-th component class. -/
theorem finiteLineHodgeDataHonest_seed_zero (M : ℕ) [NeZero M]
    (A : AnalytificationData (finiteLineWorld M))
    (hspace : A.space = TopCat.of (sphereUnionSpace M))
    (ω : singularCohomologyOf (TopCat.of unitSphereType) 2) :
    (finiteLineHodgeDataHonest M A hspace ω).cycleClass 0
        (codimensionPointCycle (finiteLineWorld M).X 0
          ⟨lineGenericPoint M ⟨0, Nat.pos_of_neZero ‹_›⟩,
            lineGenericPoint_coheight M ⟨0, Nat.pos_of_neZero ‹_›⟩⟩) =
      sphereComponentClass (V := finiteLineWorld M)
        (H := finiteLineHodgeDataHonest M A hspace ω)
        M (Nat.pos_of_neZero ‹_›) hspace ⟨0, Nat.pos_of_neZero ‹_›⟩ := by
  have hatom := honestCycleClassZero_atom M (finiteLineWorld M) A hspace
    ⟨lineGenericPoint M ⟨0, Nat.pos_of_neZero ‹_›⟩,
      lineGenericPoint_coheight M ⟨0, Nat.pos_of_neZero ‹_›⟩⟩
  have hidx : lineIndexOfGeneric M
      ⟨lineGenericPoint M ⟨0, Nat.pos_of_neZero ‹_›⟩,
        lineGenericPoint_coheight M ⟨0, Nat.pos_of_neZero ‹_›⟩⟩ = 0 :=
    lineIndexOfGeneric_lineGenericPoint M ⟨0, Nat.pos_of_neZero ‹_›⟩
  show honestCycleClassZero M (finiteLineWorld M) A hspace
      (codimensionPointCycle (finiteLineWorld M).X 0
        ⟨lineGenericPoint M ⟨0, Nat.pos_of_neZero ‹_›⟩,
          lineGenericPoint_coheight M ⟨0, Nat.pos_of_neZero ‹_›⟩⟩) = _
  rw [hatom]
  exact (congrArg (finiteLineComponentClass M (finiteLineWorld M) A hspace)
    hidx).trans
    (honest_componentClass_eq_world M A hspace ω ⟨0, Nat.pos_of_neZero ‹_›⟩)

/-- **THE HONEST SEED EQUATION AT WEIGHT ONE** — the atom at the closed
point maps to the 0-th point class. -/
theorem finiteLineHodgeDataHonest_seed_one (M : ℕ) [NeZero M]
    (A : AnalytificationData (finiteLineWorld M))
    (hspace : A.space = TopCat.of (sphereUnionSpace M))
    (ω : singularCohomologyOf (TopCat.of unitSphereType) 2) :
    (finiteLineHodgeDataHonest M A hspace ω).cycleClass 1
        (codimensionPointCycle (finiteLineWorld M).X 1
          ⟨lineClosedPointAt M ⟨0, Nat.pos_of_neZero ‹_›⟩,
            lineClosedPointAt_coheight M ⟨0, Nat.pos_of_neZero ‹_›⟩⟩) =
      spherePointClassWorld (V := finiteLineWorld M)
        (H := finiteLineHodgeDataHonest M A hspace ω) M hspace ω
        ⟨0, Nat.pos_of_neZero ‹_›⟩ := by
  have hatom := honestCycleClassOne_atom M (finiteLineWorld M) A hspace ω
    ⟨lineClosedPointAt M ⟨0, Nat.pos_of_neZero ‹_›⟩,
      lineClosedPointAt_coheight M ⟨0, Nat.pos_of_neZero ‹_›⟩⟩
  have hcomp : lineComponentOf M
      ⟨lineClosedPointAt M ⟨0, Nat.pos_of_neZero ‹_›⟩,
        lineClosedPointAt_coheight M ⟨0, Nat.pos_of_neZero ‹_›⟩⟩ =
      ⟨lineGenericPoint M ⟨0, Nat.pos_of_neZero ‹_›⟩,
        lineGenericPoint_coheight M ⟨0, Nat.pos_of_neZero ‹_›⟩⟩ :=
    lineClosedPointAt_component M ⟨0, Nat.pos_of_neZero ‹_›⟩
  have hidx : lineIndexOfGeneric M
      (lineComponentOf M ⟨lineClosedPointAt M ⟨0, Nat.pos_of_neZero ‹_›⟩,
        lineClosedPointAt_coheight M ⟨0, Nat.pos_of_neZero ‹_›⟩⟩) = 0 := by
    rw [hcomp]
    exact lineIndexOfGeneric_lineGenericPoint M ⟨0, Nat.pos_of_neZero ‹_›⟩
  show honestCycleClassOne M (finiteLineWorld M) A hspace ω
      (codimensionPointCycle (finiteLineWorld M).X 1
        ⟨lineClosedPointAt M ⟨0, Nat.pos_of_neZero ‹_›⟩,
          lineClosedPointAt_coheight M ⟨0, Nat.pos_of_neZero ‹_›⟩⟩) = _
  rw [hatom]
  exact (congrArg (finiteLinePointClass M (finiteLineWorld M) A hspace ω)
    hidx).trans
    (honest_pointClass_eq_world M A hspace ω ⟨0, Nat.pos_of_neZero ‹_›⟩)

/-- **THE DEAD WEIGHTS** — every weight `p ≥ 2` of the honest data has a
subsingleton rational Hodge fiber (the stash receipt, identical to the
green §9). -/
theorem finiteLineHodgeDataHonest_deadWeights (M : ℕ) [NeZero M]
    (A : AnalytificationData (finiteLineWorld M))
    (hspace : A.space = TopCat.of (sphereUnionSpace M))
    (ω : singularCohomologyOf (TopCat.of unitSphereType) 2) :
    ∀ p : ℕ, 1 < p →
      Subsingleton (ClassicalHodgeFiber (finiteLineWorld M)
        (finiteLineHodgeDataHonest M A hspace ω) p) := by
  intro p hp
  have hbot : rationalHodgeSubspace
      ((finiteLineHodgeDataHonest M A hspace ω).hodgeBigrading p) = ⊥ := by
    match p with
    | 0 => exact absurd hp (by omega)
    | 1 => exact absurd hp (by omega)
    | (q + 2) =>
        show rationalHodgeSubspace
          (stashBigrading _ (2 * (q + 2))) = ⊥
        exact rationalHodgeSubspace_stash_eq_bot (q + 2) (by omega)
  exact subsingleton_hodgeFiber_of_eq_bot hbot

/-- **THE STASH BIGRADING AT THE DEAD WEIGHTS** (the equality-form clone
of the wave-63 pattern — the wave-60 engine's `hstash` gate input for the
route-H capstone instantiation). -/
theorem finiteLineHodgeDataHonest_hstash (M : ℕ) [NeZero M]
    (A : AnalytificationData (finiteLineWorld M))
    (hspace : A.space = TopCat.of (sphereUnionSpace M))
    (ω : singularCohomologyOf (TopCat.of unitSphereType) 2)
    (p : ℕ) (hp : 1 < p) :
    (finiteLineHodgeDataHonest M A hspace ω).hodgeBigrading p =
      stashBigrading (RationalSingularCohomology A (2 * p)) (2 * p) := by
  rcases p with _ | _ | p
  · exact absurd hp (by omega)
  · exact absurd hp (by omega)
  · rfl

/-! ## Receipts -/

#check finiteLineHodgeDataHonest
#check finiteLineHodgeDataHonest_hone
#check finiteLineHodgeDataHonest_seed_zero
#check finiteLineHodgeDataHonest_seed_one
#check honestCycleClassZero_atom
#check honestCycleClassOne_atom

#print axioms finiteLineHodgeDataHonest
#print axioms finiteLineHodgeDataHonest_seed_zero
#print axioms finiteLineHodgeDataHonest_seed_one

end GSTFiniteLineHonestHodgeData

end
