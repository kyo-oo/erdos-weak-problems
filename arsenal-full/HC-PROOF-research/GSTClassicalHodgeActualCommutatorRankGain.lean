import GSTClassicalHodgeActualNoncommutativeNativeFrame
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# Strict geometric rank-gain certificate from noncommutative GST cycles

The actual geometric projective spine carries a NONZERO conserved charge.
A genuine geometric correspondence E can act as a scalar on that charge
functional even while acting nontrivially on the Hodge fiber.

If E and F each act by scalars on the same charge, their commutator has
exactly ZERO charge. When the constructed commutator Betti class is NONZERO,
it is automatically linearly independent from the actual nonzero-charge
native spine. Hence actual geometric noncommutativity opens a SECOND
algebraic Hodge direction, not just another formula for the same class.

The nonzero commutator is an independently testable geometric requirement.
This file does not assume the Hodge conjecture or target-cycle preimages,
nor does it prove such a nonzero commutator exists on every variety.
-/

set_option maxHeartbeats 12000000

noncomputable section

open scoped BigOperators
open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeLimitlessSpinePropagation
open GSTClassicalHodgeRealizedCorrespondenceExpressionAlgebra
open GSTClassicalHodgeActualNoncommutativeNativeFrame
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgeAtomicSpan

namespace GSTClassicalHodgeActualCommutatorRankGain

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- The recursively manufactured projective spine has a genuine nonzero
cohomological charge, derived from the native charge law and exact naturality. -/
theorem actualSpine_betti_charge_nonzero
    (G : GeometricCycleClassSpine V H)
    (D : SpineTowerConservedCharge G) :
    D.cohomologyRead p (spineHodgeSeed G p).1 ≠ 0 := by
  rw [← spineNativeTower_cycleClass G p]
  rw [D.cycleClass_read p (spineNativeTower G p)]
  exact D.nativeRead_spineNativeTower_ne_zero p

/-- Two REALIZED geometric actions preserving the charge line necessarily
have a zero-charge commutator, even if the cohomological commutator itself
is a new nonzero algebraic Hodge direction. -/
theorem geometric_commutator_charge_zero
    (G : GeometricCycleClassSpine V H)
    (D : SpineTowerConservedCharge G)
    (E F : RealizedCorrespondenceExpr V H p)
    (a b : ℚ)
    (hE : ∀ x : RationalSingularCohomology H.analytification (2 * p),
      D.cohomologyRead p (E.cohomologyOperator x) =
        a * D.cohomologyRead p x)
    (hF : ∀ x : RationalSingularCohomology H.analytification (2 * p),
      D.cohomologyRead p (F.cohomologyOperator x) =
        b * D.cohomologyRead p x) :
    D.cohomologyRead p (bettiGeometricCommutator G E F) = 0 := by
  unfold bettiGeometricCommutator
  rw [map_sub, hE, hF, hF, hE]
  ring

/-- A charge-zero NONZERO native geometric commutator is automatically
independent from the original nonzero-charge native spine.

This is an exact algebraic two-vector independence proof; the target
Hodge space and any desired target class are not supplied as premises. -/
theorem geometric_spine_commutator_coefficient_rigidity
    (G : GeometricCycleClassSpine V H)
    (D : SpineTowerConservedCharge G)
    (E F : RealizedCorrespondenceExpr V H p)
    (hcomm : bettiGeometricCommutator G E F ≠ 0)
    (hcommcharge : D.cohomologyRead p
      (bettiGeometricCommutator G E F) = 0) :
    ∀ a b : ℚ,
      a • (spineHodgeSeed G p).1 +
        b • bettiGeometricCommutator G E F = 0 →
      a = 0 ∧ b = 0 := by
  intro a b hab
  have hread :
      a * D.cohomologyRead p (spineHodgeSeed G p).1 +
        b * D.cohomologyRead p (bettiGeometricCommutator G E F) = 0 := by
    have h := congrArg (D.cohomologyRead p) hab
    simpa only [map_add, map_smul, map_zero, smul_eq_mul] using h
  have hamul : a * D.cohomologyRead p (spineHodgeSeed G p).1 = 0 := by
    simpa [hcommcharge] using hread
  have ha : a = 0 :=
    (mul_eq_zero.mp hamul).resolve_right
      (actualSpine_betti_charge_nonzero G D)
  subst a
  have hbsmul : b • bettiGeometricCommutator G E F = 0 := by
    simpa using hab
  have hb : b = 0 := (smul_eq_zero.mp hbsmul).resolve_right hcomm
  exact ⟨rfl, hb⟩

/-- The original projective spine and the *ACTUAL* geometric commutator
have two linearly independent Betti classes when the conserved charge
separates them. This certifies a strict rank gain from genuine geometry. -/
theorem actual_spine_and_commutator_linearIndependent
    (G : GeometricCycleClassSpine V H)
    (D : SpineTowerConservedCharge G)
    (E F : RealizedCorrespondenceExpr V H p)
    (hcomm : bettiGeometricCommutator G E F ≠ 0)
    (hcommcharge : D.cohomologyRead p
      (bettiGeometricCommutator G E F) = 0) :
    LinearIndependent ℚ
      ![(spineHodgeSeed G p).1, bettiGeometricCommutator G E F] := by
  exact (LinearIndependent.pair_iff).2
    (geometric_spine_commutator_coefficient_rigidity
      G D E F hcomm hcommcharge)

/-- Charge-eigenfunctional geometry removes the zero-charge condition:
nonvanishing of the actual commutator is now the ONLY additional condition
needed for a second independent algebraic Hodge class. -/
theorem actual_rank_gain_of_geometric_charge_eigenoperators
    (G : GeometricCycleClassSpine V H)
    (D : SpineTowerConservedCharge G)
    (E F : RealizedCorrespondenceExpr V H p)
    (a b : ℚ)
    (hE : ∀ x : RationalSingularCohomology H.analytification (2 * p),
      D.cohomologyRead p (E.cohomologyOperator x) =
        a * D.cohomologyRead p x)
    (hF : ∀ x : RationalSingularCohomology H.analytification (2 * p),
      D.cohomologyRead p (F.cohomologyOperator x) =
        b * D.cohomologyRead p x)
    (hcomm : bettiGeometricCommutator G E F ≠ 0) :
    LinearIndependent ℚ
      ![(spineHodgeSeed G p).1, bettiGeometricCommutator G E F] :=
  actual_spine_and_commutator_linearIndependent G D E F hcomm
    (geometric_commutator_charge_zero G D E F a b hE hF)

/-! ## Rank-two completion by ACTUAL geometric commutator classes

If the rational Hodge fiber has dimension precisely two, the two
independently constructed cycle classes span the entire Hodge fiber.
The only nontrivial geometry required beyond the spine and conserved
charge is that one actual commutator remains nonzero in Betti.
No target-cycle existence, Hodge surjectivity, or matrix determinant
is supplied as an assumption. -/

/-- Native algebraicity of every rational Hodge class in an actual
two-dimensional fiber, proved from the GST spine plus one nonzero
genuine correspondence commutator that is charge-orthogonal to the spine. -/
theorem every_rank_two_hodge_class_of_nonzero_geometric_commutator
    (G : GeometricCycleClassSpine V H)
    (D : SpineTowerConservedCharge G)
    (E F : RealizedCorrespondenceExpr V H p)
    (hcomm : bettiGeometricCommutator G E F ≠ 0)
    (hcommcharge : D.cohomologyRead p
      (bettiGeometricCommutator G E F) = 0)
    [FiniteDimensional ℚ (ClassicalHodgeFiber V H p)]
    (hrank : Module.finrank ℚ (ClassicalHodgeFiber V H p) = 2)
    (alpha : RationalSingularCohomology H.analytification (2 * p))
    (halpha : alpha ∈ rationalHodgeSubspace (H.hodgeBigrading p)) :
    ∃ Z : codimensionCycles V.X p, H.cycleClass p Z = alpha := by
  let t : ClassicalHodgeFiber V H p :=
    ⟨bettiGeometricCommutator G E F,
      bettiGeometricCommutator_is_hodge G E F⟩
  have hLI :
      LinearIndependent ℚ ![spineHodgeSeed G p, t] := by
    apply (LinearIndependent.pair_iff).2
    intro a b hab
    have hval : a • (spineHodgeSeed G p).1 +
        b • bettiGeometricCommutator G E F = 0 := by
      have h := congrArg Subtype.val hab
      simpa [t, Submodule.coe_add, Submodule.coe_smul_of_tower] using h
    exact (LinearIndependent.pair_iff.mp
      (actual_spine_and_commutator_linearIndependent
        G D E F hcomm hcommcharge)) a b hval
  have hspan :
      Submodule.span ℚ
        (Set.range (![spineHodgeSeed G p, t] :
          Fin 2 → ClassicalHodgeFiber V H p)) = ⊤ :=
    hLI.span_eq_top_of_card_eq_finrank' (by simpa [hrank])
  let S := AlgebraicHodgeSubspace V H p
  have hseed : spineHodgeSeed G p ∈ S :=
    spineHodgeSeed_algebraic G p
  have htarget : t ∈ S := by
    change bettiGeometricCommutator G E F ∈
      pointCycleClassSpan p (H.cycleClass p)
    rw [← smoothProjective_cycleClass_range_eq_atomic_span V H p]
    exact ⟨nativeGeometricCommutator G E F,
      nativeGeometricCommutator_cycleClass G E F⟩
  have hS : S = ⊤ := by
    apply top_unique
    rw [← hspan]
    apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    fin_cases i
    · simpa using hseed
    · simpa using htarget
  have hmem : (⟨alpha, halpha⟩ :
      ClassicalHodgeFiber V H p) ∈ S := by
    rw [hS]
    trivial
  change alpha ∈ pointCycleClassSpan p (H.cycleClass p) at hmem
  rw [← smoothProjective_cycleClass_range_eq_atomic_span V H p] at hmem
  exact hmem

/-- Charge-eigenrealized geometric correspondences produce the required
zero-charge commutator automatically; no independent charge-zero
hypothesis remains in the rank-two Hodge conclusion. -/
theorem rank_two_hodge_of_charge_eigen_geometric_commutator
    (G : GeometricCycleClassSpine V H)
    (D : SpineTowerConservedCharge G)
    (E F : RealizedCorrespondenceExpr V H p)
    (a b : ℚ)
    (hE : ∀ x : RationalSingularCohomology H.analytification (2 * p),
      D.cohomologyRead p (E.cohomologyOperator x) =
        a * D.cohomologyRead p x)
    (hF : ∀ x : RationalSingularCohomology H.analytification (2 * p),
      D.cohomologyRead p (F.cohomologyOperator x) =
        b * D.cohomologyRead p x)
    (hcomm : bettiGeometricCommutator G E F ≠ 0)
    [FiniteDimensional ℚ (ClassicalHodgeFiber V H p)]
    (hrank : Module.finrank ℚ (ClassicalHodgeFiber V H p) = 2)
    (alpha : RationalSingularCohomology H.analytification (2 * p))
    (halpha : alpha ∈ rationalHodgeSubspace (H.hodgeBigrading p)) :
    ∃ Z : codimensionCycles V.X p, H.cycleClass p Z = alpha :=
  every_rank_two_hodge_class_of_nonzero_geometric_commutator
    G D E F hcomm
    (geometric_commutator_charge_zero G D E F a b hE hF)
    hrank alpha halpha


/-! ## Exact four-coordinate GST graph audit (Mathbox + Wolfram)

The rank-two commutator theorem above is genuine under its hypotheses,
but *noncommutativity plus a conserved source charge* does not force a
full Hodge-basis orbit in arbitrary rank. We construct a four-dimensional
RATIONAL representation with two noncommuting, charge-preserving operators.
Every finite graph word, rational combination, and scaled path beginning
at its native-style seed remains in the hyperplane x₃=0. The commutator
is nonzero and creates a new direction, but the fourth direction is not
reachable. This is a countermodel to an ABSTRACT rank-completion
inference, NOT a counterexample on an actual projective variety. -/

namespace FourCoordinateGSTGraphAudit

def graphSeed : Fin 4 → ℚ :=
  fun i => if i = 0 ∨ i = 1 then 1 else 0

/-- Swap the middle two rational graph channels, preserving the first charge. -/
def graphSwap (v : Fin 4 → ℚ) : Fin 4 → ℚ :=
  fun i => if i = 1 then v 2 else if i = 2 then v 1 else v i

/-- A genuinely distinct diagonal CM/NM-style rational graph action. -/
def graphDiagonal (v : Fin 4 → ℚ) : Fin 4 → ℚ :=
  fun i => if i = 1 then 2 * v i else
    if i = 2 then 3 * v i else
    if i = 3 then 5 * v i else v i

theorem graphSwap_conserves_charge (v : Fin 4 → ℚ) :
    graphSwap v 0 = v 0 := by
  simp [graphSwap]

theorem graphDiagonal_conserves_charge (v : Fin 4 → ℚ) :
    graphDiagonal v 0 = v 0 := by
  simp [graphDiagonal]

theorem graphSeed_charge_nonzero : graphSeed 0 ≠ 0 := by
  norm_num [graphSeed]

/-- The two charge-preserving operators genuinely fail to commute on seed. -/
theorem graph_commutator_nonzero :
    graphSwap (graphDiagonal graphSeed) -
      graphDiagonal (graphSwap graphSeed) ≠ 0 := by
  intro h
  have h2 := congrArg (fun v : Fin 4 → ℚ => v 2) h
  simp [graphSwap, graphDiagonal, graphSeed] at h2
  norm_num at h2

/-- Every finite GST graph expression built from these two actions and
rational linear combinations; arbitrary nesting and word length allowed. -/
inductive GraphProgram where
  | seed
  | swap (P : GraphProgram)
  | diagonal (P : GraphProgram)
  | add (P Q : GraphProgram)
  | scale (a : ℚ) (P : GraphProgram)

def GraphProgram.eval : GraphProgram → (Fin 4 → ℚ)
  | .seed => graphSeed
  | .swap P => graphSwap P.eval
  | .diagonal P => graphDiagonal P.eval
  | .add P Q => P.eval + Q.eval
  | .scale a P => a • P.eval

/-- Graph closure has a genuine missing rational direction at ANY
finite depth, notwithstanding nonzero commutators and a conserved charge. -/
theorem every_graph_program_fourth_coordinate_zero
    (P : GraphProgram) : P.eval 3 = 0 := by
  induction P with
  | seed => simp [GraphProgram.eval, graphSeed]
  | swap P ih => simpa [GraphProgram.eval, graphSwap] using ih
  | diagonal P ih => simpa [GraphProgram.eval, graphDiagonal] using ih
  | add P Q hP hQ => simp [GraphProgram.eval, hP, hQ]
  | scale a P ih => simp [GraphProgram.eval, ih]

/-- The fourth basis class is NOT produced by any amount of these
graph operators. This refutes only the abstract claim that the stated
operators FORCE full rank, not the classical Hodge conjecture. -/
theorem fourth_basis_direction_unreachable (P : GraphProgram) :
    P.eval ≠ (fun i : Fin 4 => if i = 3 then (1 : ℚ) else 0) := by
  intro h
  have h3 := congrArg (fun v : Fin 4 → ℚ => v 3) h
  have hz := every_graph_program_fourth_coordinate_zero P
  simp [hz] at h3

/-- Noncommutativity is witnessed by two concrete executable graph words. -/
theorem executable_graph_words_do_not_commute :
    (GraphProgram.swap (GraphProgram.diagonal .seed)).eval -
      (GraphProgram.diagonal (GraphProgram.swap .seed)).eval ≠ 0 := by
  exact graph_commutator_nonzero

#print axioms graph_commutator_nonzero
#print axioms fourth_basis_direction_unreachable
end FourCoordinateGSTGraphAudit

#check actualSpine_betti_charge_nonzero
#check geometric_commutator_charge_zero
#check actual_spine_and_commutator_linearIndependent
#check actual_rank_gain_of_geometric_charge_eigenoperators
#check every_rank_two_hodge_class_of_nonzero_geometric_commutator
#check rank_two_hodge_of_charge_eigen_geometric_commutator

#print axioms actualSpine_betti_charge_nonzero
#print axioms geometric_commutator_charge_zero
#print axioms actual_rank_gain_of_geometric_charge_eigenoperators
#print axioms rank_two_hodge_of_charge_eigen_geometric_commutator

end GSTClassicalHodgeActualCommutatorRankGain
