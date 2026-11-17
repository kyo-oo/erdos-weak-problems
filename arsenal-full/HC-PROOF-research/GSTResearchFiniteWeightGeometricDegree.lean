import GSTClassicalHodgeLimitlessSpinePropagation

/-!
# GST finite-weight geometric degree conservation law

This is a VALID replacement for an unlimited unweighted native-mass
bridge. Actual smooth projective varieties have finite dimension.
Codimension-p algebraic cycles vanish for p above that dimension, so
a universally nonzero algebraic spine for ALL p cannot be correct.

Define a projective-geometric DEGREE charge only on a certified
finite codimension range 0<=p<=d. Require:
1. a genuine native rational linear degree at each weight;
2. an ambient rational cohomological degree readout;
3. compatibility of the two through ACTUAL cycle-class maps;
4. nonzero degree of the canonical codimension-zero fundamental cycle;
5. the projective principal-cut successor degree transport for p<d.

Unlike unweighted coefficient-count mass, a cohomology-compatible
intersection/degree charge is allowed to annihilate homologically
trivial cycles. There is NO assertion of nonzero cycles for p>d.

The theorem derives conservation and nonzero genuine algebraic
Hodge spine classes at EACH p<=d. This constructs a consistent
finite-window geometric source law, without ANY assertion that
its structural hypotheses have been proved for all varieties.
The independent verification of the geometric degree fields is a
substantive next obligation (cup/Gysin/projective intersection).
-/

set_option maxHeartbeats 20000000
noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeLimitlessSpinePropagation
open GSTClassicalHodgeCodimensionZeroFundamentalCycle
open GSTClassicalHodgePrincipalCutSuccessorOperator
open GSTClassicalHodgeLimitlessTowerOrbitCrown

namespace GSTResearchFiniteWeightGeometricDegree

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- Dimension-bounded true-cohomological degree law, with neither
unweighted native mass nor any p>d nonvanishing requirement. -/
structure BoundedGeometricDegreeCharge
    (G : GeometricCycleClassSpine V H) (d : Nat) where
  nativeDegree : ∀ p : Nat, codimensionCycles V.X p →ₗ[ℚ] ℚ
  bettiDegree : ∀ p : Nat,
    RationalSingularCohomology H.analytification (2 * p) →ₗ[ℚ] ℚ
  class_degree :
    ∀ p : Nat, p ≤ d → ∀ Z : codimensionCycles V.X p,
      bettiDegree p (H.cycleClass p Z) = nativeDegree p Z
  base_degree_ne_zero :
    nativeDegree 0 (codimensionZeroFundamentalCycle V) ≠ 0
  successor_degree :
    ∀ p : Nat, p < d → ∀ Z : codimensionCycles V.X p,
      nativeDegree (p+1) (successorNativeOperator V p Z) =
        successorScalar p * nativeDegree p Z

namespace BoundedGeometricDegreeCharge

variable {G : GeometricCycleClassSpine V H}
variable {d : Nat}

/-- The genuine native projective spine has constant degree INSIDE
the certified finite window. No statement is made for p>d. -/
theorem degree_spineNativeTower
    (C : BoundedGeometricDegreeCharge G d)
    (p : Nat) (hp : p ≤ d) :
    C.nativeDegree p (spineNativeTower G p) =
      C.nativeDegree 0 (codimensionZeroFundamentalCycle V) := by
  induction p with
  | zero =>
      rfl
  | succ p ih =>
      have hprev : p ≤ d := by omega
      have hnext : p < d := by omega
      rw [spineNativeTower_succ]
      rw [LinearMap.map_smul]
      rw [C.successor_degree p hnext (spineNativeTower G p)]
      simp [successorScalar_ne_zero, ih hprev]

/-- Nonzero geometric native degree is DERIVED for all p<=d. -/
theorem native_spine_degree_nonzero
    (C : BoundedGeometricDegreeCharge G d)
    (p : Nat) (hp : p ≤ d) :
    C.nativeDegree p (spineNativeTower G p) ≠ 0 := by
  rw [C.degree_spineNativeTower p hp]
  exact C.base_degree_ne_zero

/-- The native degree and true cycle class commute, so the bounded
native spine class cannot vanish in rational Betti cohomology. -/
theorem cohomological_spine_nonzero
    (C : BoundedGeometricDegreeCharge G d)
    (p : Nat) (hp : p ≤ d) :
    H.cycleClass p (spineNativeTower G p) ≠ 0 := by
  intro hz
  have hc := C.class_degree p hp (spineNativeTower G p)
  rw [hz] at hc
  simp only [map_zero] at hc
  exact (C.native_spine_degree_nonzero p hp) hc.symm

/-- Thus every ACTIVE certified weight contains an actually
constructed nonzero rational algebraic Hodge class. -/
theorem hodge_spine_nonzero
    (C : BoundedGeometricDegreeCharge G d)
    (p : Nat) (hp : p ≤ d) :
    spineHodgeSeed G p ≠ 0 := by
  exact (spineHodgeSeed_ne_zero_iff_cycleClass_ne_zero G p).2
    (C.cohomological_spine_nonzero p hp)

end BoundedGeometricDegreeCharge

#check BoundedGeometricDegreeCharge
#check BoundedGeometricDegreeCharge.degree_spineNativeTower
#check BoundedGeometricDegreeCharge.native_spine_degree_nonzero
#check BoundedGeometricDegreeCharge.cohomological_spine_nonzero
#check BoundedGeometricDegreeCharge.hodge_spine_nonzero

#print axioms BoundedGeometricDegreeCharge.degree_spineNativeTower
#print axioms BoundedGeometricDegreeCharge.cohomological_spine_nonzero
#print axioms BoundedGeometricDegreeCharge.hodge_spine_nonzero

end GSTResearchFiniteWeightGeometricDegree
