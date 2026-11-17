import GSTClassicalHodgeProjectiveWordOrbit
import GSTClassicalHodgeLimitlessSpinePropagation

/-!
# GST CLASSICAL HODGE — GRADED GEOMETRIC PROGRAM ORBIT

The previous crowns treated two geometric motions separately:

* horizontal motion inside one codimension by genuine projective operator
  words;
* vertical motion between consecutive codimensions by the genuine principal
  cut.

That separation is artificial.  The geometry cosmology is stronger when both
motions live in one graded noncommutative program algebra.

A `GradedGeometricProgram V p q` is built only from operations already earned
by the native geometry:

* identity;
* a finite projective self-transport word at one weight;
* the genuine principal-cut successor;
* rational scaling and addition;
* ordered composition across matching weights.

Every constructor has an actual native-cycle interpretation.  The genuine
cycle-class spine gives the cohomological face of every primitive, and the
linear/noncommutative closure laws propagate the exact cycle-class square
through every finite program.  Thus a complete mixed horizontal/vertical GST
program can never leave the genuine algebraic range.

The canonical codimension-zero fundamental cycle is then used as the geometric
origin.  At weight `q`, the graded program orbit is the rational span of all
cohomology states reached from that origin by finite programs `0 -> q`.
Every orbit state is proved algebraic *by construction*.  Therefore the whole
Hodge problem is compressed to one pure reachability statement:

  every rational `(q,q)` Hodge state lies in the graded geometric program
  orbit.

Under that reachability law, the Stage-2G Hodge statement follows immediately.
No separate all-weight nonvanishing family, matrix-unit externalization,
projective two-generator package, kernel-mass law, or per-sheet cycle witness
is needed.

The old normalized principal-cut spine is also compiled into this program
algebra, proving that the new cosmology strictly contains the earlier tower
route rather than replacing it.
-/

set_option maxHeartbeats 90000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeGradedGeometricProgramOrbit

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeCrossWeightNativePropagation
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeCodimensionZeroFundamentalCycle
open GSTClassicalHodgePrincipalCutSuccessorOperator
open GSTClassicalHodgeLimitlessTowerOrbitCrown
open GSTClassicalHodgeLimitlessSpinePropagation
open GSTClassicalHodgeProjectiveWordOrbit

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-! ## Algebra of graded cycle-natural pairs -/

namespace GradedCycleClassOperatorPair

/-- Identity graded pair. -/
noncomputable def idPair
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat) :
    GradedCycleClassOperatorPair V H p p where
  cycleOperator := LinearMap.id
  cohomologyOperator := LinearMap.id
  cycleClass_natural := by
    intro Z
    rfl

/-- Add two graded cycle-natural pairs with the same source and target. -/
noncomputable def addPair
    {p q : Nat}
    (A B : GradedCycleClassOperatorPair V H p q) :
    GradedCycleClassOperatorPair V H p q where
  cycleOperator := A.cycleOperator + B.cycleOperator
  cohomologyOperator := A.cohomologyOperator + B.cohomologyOperator
  cycleClass_natural := by
    intro Z
    simp [A.cycleClass_natural Z, B.cycleClass_natural Z]

/-- Rationally scale one graded cycle-natural pair. -/
noncomputable def smulPair
    {p q : Nat}
    (a : ℚ)
    (A : GradedCycleClassOperatorPair V H p q) :
    GradedCycleClassOperatorPair V H p q where
  cycleOperator := a • A.cycleOperator
  cohomologyOperator := a • A.cohomologyOperator
  cycleClass_natural := by
    intro Z
    simp [A.cycleClass_natural Z]

/-- Ordered composition of graded cycle-natural pairs. -/
noncomputable def compPair
    {p q r : Nat}
    (A : GradedCycleClassOperatorPair V H p q)
    (B : GradedCycleClassOperatorPair V H q r) :
    GradedCycleClassOperatorPair V H p r where
  cycleOperator := B.cycleOperator.comp A.cycleOperator
  cohomologyOperator := B.cohomologyOperator.comp A.cohomologyOperator
  cycleClass_natural := by
    intro Z
    rw [LinearMap.comp_apply, LinearMap.comp_apply]
    rw [B.cycleClass_natural, A.cycleClass_natural]

end GradedCycleClassOperatorPair

/-! ## Mixed horizontal/vertical geometry programs -/

/-- Finite graded noncommutative programs generated entirely by genuine
projective self-transport and genuine principal cuts. -/
inductive GradedGeometricProgram
    (V : SmoothProjectiveComplexScheme) : Nat → Nat → Type
  | id (p : Nat) : GradedGeometricProgram V p p
  | word {p : Nat} (W : ProjectiveOperatorWord V p) :
      GradedGeometricProgram V p p
  | cut (p : Nat) : GradedGeometricProgram V p (p + 1)
  | add {p q : Nat}
      (A B : GradedGeometricProgram V p q) :
      GradedGeometricProgram V p q
  | smul {p q : Nat}
      (a : ℚ) (A : GradedGeometricProgram V p q) :
      GradedGeometricProgram V p q
  | comp {p q r : Nat}
      (A : GradedGeometricProgram V p q)
      (B : GradedGeometricProgram V q r) :
      GradedGeometricProgram V p r

namespace GradedGeometricProgram

/-- Interpret a mixed geometric program as one exact graded
cycle/cohomology-natural pair. -/
noncomputable def toPair
    (G : GeometricCycleClassSpine V H) :
    {p q : Nat} → GradedGeometricProgram V p q →
      GradedCycleClassOperatorPair V H p q
  | _, _, .id p => GradedCycleClassOperatorPair.idPair V H p
  | _, _, .word W =>
      { cycleOperator := W.eval
        cohomologyOperator := (W.operatorPair G).cohomologyOperator
        cycleClass_natural := fun Z => W.cycleClass_eval G Z }
  | _, _, .cut p => G.principalCutPair p
  | _, _, .add A B =>
      GradedCycleClassOperatorPair.addPair (toPair G A) (toPair G B)
  | _, _, .smul a A =>
      GradedCycleClassOperatorPair.smulPair a (toPair G A)
  | _, _, .comp A B =>
      GradedCycleClassOperatorPair.compPair (toPair G A) (toPair G B)

/-- Native-cycle execution. -/
noncomputable def cycleEval
    (G : GeometricCycleClassSpine V H)
    {p q : Nat}
    (P : GradedGeometricProgram V p q) :
    codimensionCycles V.X p →ₗ[ℚ] codimensionCycles V.X q :=
  (P.toPair G).cycleOperator

/-- Cohomological execution. -/
noncomputable def cohomologyEval
    (G : GeometricCycleClassSpine V H)
    {p q : Nat}
    (P : GradedGeometricProgram V p q) :
    RationalSingularCohomology H.analytification (2 * p) →ₗ[ℚ]
      RationalSingularCohomology H.analytification (2 * q) :=
  (P.toPair G).cohomologyOperator

/-- **MASTER PROGRAM NATURALITY LAW.**
Every finite mixed GST geometry program carries an exact genuine cycle-class
commuting square. -/
theorem cycleClass_cycleEval
    (G : GeometricCycleClassSpine V H)
    {p q : Nat}
    (P : GradedGeometricProgram V p q)
    (Z : codimensionCycles V.X p) :
    H.cycleClass q (P.cycleEval G Z) =
      P.cohomologyEval G (H.cycleClass p Z) := by
  exact (P.toPair G).cycleClass_natural Z

/-- Every program image of an actual native cycle is automatically in the
actual target cycle-class range. -/
theorem cohomologyEval_mem_cycleClass_range
    (G : GeometricCycleClassSpine V H)
    {p q : Nat}
    (P : GradedGeometricProgram V p q)
    (Z : codimensionCycles V.X p) :
    P.cohomologyEval G (H.cycleClass p Z) ∈
      LinearMap.range (H.cycleClass q) := by
  refine ⟨P.cycleEval G Z, ?_⟩
  exact P.cycleClass_cycleEval G Z

/-- Every program image of a genuine cycle class has true `(q,q)` Hodge type. -/
theorem cohomologyEval_mem_hodge
    (G : GeometricCycleClassSpine V H)
    {p q : Nat}
    (P : GradedGeometricProgram V p q)
    (Z : codimensionCycles V.X p) :
    P.cohomologyEval G (H.cycleClass p Z) ∈
      rationalHodgeSubspace (H.hodgeBigrading q) := by
  rw [← P.cycleClass_cycleEval G Z]
  exact G.algebraic_is_hodge q (P.cycleEval G Z)

end GradedGeometricProgram

/-! ## Canonical geometric origin and its full graded orbit -/

/-- Genuine cohomological origin carried by the canonical codimension-zero
fundamental cycle. -/
noncomputable def geometricOriginClass
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V) :
    RationalSingularCohomology H.analytification 0 :=
  H.cycleClass 0 (codimensionZeroFundamentalCycle V)

/-- States reachable at weight `q` from the canonical geometric origin by one
finite mixed geometry program. -/
def geometricProgramOrbitSet
    (G : GeometricCycleClassSpine V H)
    (q : Nat) :
    Set (RationalSingularCohomology H.analytification (2 * q)) :=
  { alpha | ∃ P : GradedGeometricProgram V 0 q,
      alpha = P.cohomologyEval G (geometricOriginClass V H) }

/-- Rational linear hull of the full mixed geometric orbit. -/
noncomputable def geometricProgramOrbitSubspace
    (G : GeometricCycleClassSpine V H)
    (q : Nat) :
    Submodule ℚ (RationalSingularCohomology H.analytification (2 * q)) :=
  Submodule.span ℚ (geometricProgramOrbitSet G q)

/-- Every one-program orbit generator is the actual class of the native cycle
obtained by executing the same program on the fundamental cycle. -/
theorem orbitGenerator_mem_cycleClass_range
    (G : GeometricCycleClassSpine V H)
    (q : Nat)
    {alpha : RationalSingularCohomology H.analytification (2 * q)}
    (halpha : alpha ∈ geometricProgramOrbitSet G q) :
    alpha ∈ LinearMap.range (H.cycleClass q) := by
  rcases halpha with ⟨P, rfl⟩
  exact P.cohomologyEval_mem_cycleClass_range G
    (codimensionZeroFundamentalCycle V)

/-- **GEOMETRIC ORBIT ALGEBRAICITY.**
The entire rational span of all mixed projective/cut programs stays inside the
genuine cycle-class range. -/
theorem geometricProgramOrbitSubspace_le_cycleClass_range
    (G : GeometricCycleClassSpine V H)
    (q : Nat) :
    geometricProgramOrbitSubspace G q ≤
      LinearMap.range (H.cycleClass q) := by
  apply Submodule.span_le.2
  intro alpha halpha
  exact orbitGenerator_mem_cycleClass_range G q halpha

/-- The full program orbit also lies in the genuine Hodge `(q,q)` sector. -/
theorem geometricProgramOrbitSubspace_le_hodge
    (G : GeometricCycleClassSpine V H)
    (q : Nat) :
    geometricProgramOrbitSubspace G q ≤
      rationalHodgeSubspace (H.hodgeBigrading q) := by
  intro alpha halpha
  have hrange := geometricProgramOrbitSubspace_le_cycleClass_range G q halpha
  rcases hrange with ⟨Z, rfl⟩
  exact G.algebraic_is_hodge q Z

/-- Pure reachability/cyclicity statement for the upgraded geometry cosmology:
every true Hodge state is generated from the canonical geometric origin by the
rational span of finite mixed projective/cut programs. -/
def GradedGeometricOrbitCyclic
    (G : GeometricCycleClassSpine V H) : Prop :=
  ∀ q : Nat,
    rationalHodgeSubspace (H.hodgeBigrading q) ≤
      geometricProgramOrbitSubspace G q

/-- **GRADED GEOMETRIC ORBIT HODGE CROWN.**
Once the Hodge sector is cyclic for the verified mixed geometry orbit, the
exact Stage-2G Hodge conclusion follows with no separate tower-survival or
externalization package. -/
theorem bigradedBettiHodge_of_gradedGeometricOrbitCyclic
    (G : GeometricCycleClassSpine V H)
    (hcyclic : GradedGeometricOrbitCyclic G) :
    BigradedBettiHodgeStatement V H := by
  intro q alpha halpha
  exact geometricProgramOrbitSubspace_le_cycleClass_range G q
    (hcyclic q halpha)

/-- Elementwise native-cycle witness obtained from graded geometric
reachability. -/
theorem every_hodge_class_has_native_cycle_of_gradedGeometricOrbitCyclic
    (G : GeometricCycleClassSpine V H)
    (hcyclic : GradedGeometricOrbitCyclic G)
    (q : Nat)
    (alpha : RationalSingularCohomology H.analytification (2 * q))
    (halpha : alpha ∈ rationalHodgeSubspace (H.hodgeBigrading q)) :
    ∃ Z : codimensionCycles V.X q,
      H.cycleClass q Z = alpha := by
  exact geometricProgramOrbitSubspace_le_cycleClass_range G q
    (hcyclic q halpha)

/-! ## The old normalized projective spine is internal to the new orbit -/

/-- Compile the recursively normalized principal-cut tower into one mixed
geometric program from weight zero to weight `q`. -/
noncomputable def normalizedSpineProgram
    (V : SmoothProjectiveComplexScheme) :
    (q : Nat) → GradedGeometricProgram V 0 q
  | 0 => .id 0
  | q + 1 =>
      .smul (successorScalar q)⁻¹
        (.comp (normalizedSpineProgram V q) (.cut q))

/-- Native execution of the compiled program is exactly the earlier normalized
spine tower. -/
theorem normalizedSpineProgram_cycleEval
    (G : GeometricCycleClassSpine V H) :
    ∀ q : Nat,
      (normalizedSpineProgram V q).cycleEval G
          (codimensionZeroFundamentalCycle V) =
        spineNativeTower G q := by
  intro q
  induction q with
  | zero => rfl
  | succ q ih =>
      show (successorScalar q)⁻¹ •
          ((G.principalCutPair q).cycleOperator.comp
            ((normalizedSpineProgram V q).cycleEval G))
            (codimensionZeroFundamentalCycle V) =
          spineNativeTower G (q + 1)
      rw [G.principalCutPair_native q]
      simp only [LinearMap.smul_apply, LinearMap.comp_apply]
      rw [ih]
      exact (spineNativeTower_succ G q).symm

/-- Cohomological execution of the same program is exactly the earlier
normalized spine Hodge state. -/
theorem normalizedSpineProgram_cohomologyEval
    (G : GeometricCycleClassSpine V H)
    (q : Nat) :
    (normalizedSpineProgram V q).cohomologyEval G
        (geometricOriginClass V H) =
      (spineHodgeSeed G q).1 := by
  calc
    (normalizedSpineProgram V q).cohomologyEval G
        (geometricOriginClass V H) =
      H.cycleClass q
        ((normalizedSpineProgram V q).cycleEval G
          (codimensionZeroFundamentalCycle V)) := by
            exact ((normalizedSpineProgram V q).cycleClass_cycleEval G
              (codimensionZeroFundamentalCycle V)).symm
    _ = H.cycleClass q (spineNativeTower G q) := by
          rw [normalizedSpineProgram_cycleEval G q]
    _ = (spineHodgeSeed G q).1 := spineNativeTower_cycleClass G q

/-- Every old canonical spine seed is therefore literally a generator of the
new graded geometric orbit. -/
theorem spineHodgeSeed_mem_geometricProgramOrbitSet
    (G : GeometricCycleClassSpine V H)
    (q : Nat) :
    (spineHodgeSeed G q).1 ∈ geometricProgramOrbitSet G q := by
  refine ⟨normalizedSpineProgram V q, ?_⟩
  exact (normalizedSpineProgram_cohomologyEval G q).symm

/-- In particular every old spine seed belongs to the new orbit subspace. -/
theorem spineHodgeSeed_mem_geometricProgramOrbitSubspace
    (G : GeometricCycleClassSpine V H)
    (q : Nat) :
    (spineHodgeSeed G q).1 ∈ geometricProgramOrbitSubspace G q := by
  exact Submodule.subset_span
    (spineHodgeSeed_mem_geometricProgramOrbitSet G q)

#check GradedGeometricProgram
#check GradedGeometricProgram.toPair
#check GradedGeometricProgram.cycleClass_cycleEval
#check geometricProgramOrbitSet
#check geometricProgramOrbitSubspace
#check geometricProgramOrbitSubspace_le_cycleClass_range
#check geometricProgramOrbitSubspace_le_hodge
#check GradedGeometricOrbitCyclic
#check bigradedBettiHodge_of_gradedGeometricOrbitCyclic
#check normalizedSpineProgram
#check normalizedSpineProgram_cycleEval
#check normalizedSpineProgram_cohomologyEval
#check spineHodgeSeed_mem_geometricProgramOrbitSubspace

#print axioms GradedGeometricProgram.cycleClass_cycleEval
#print axioms geometricProgramOrbitSubspace_le_cycleClass_range
#print axioms geometricProgramOrbitSubspace_le_hodge
#print axioms bigradedBettiHodge_of_gradedGeometricOrbitCyclic
#print axioms normalizedSpineProgram_cycleEval
#print axioms normalizedSpineProgram_cohomologyEval

end GSTClassicalHodgeGradedGeometricProgramOrbit