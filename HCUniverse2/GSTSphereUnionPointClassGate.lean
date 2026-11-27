import HCUniverse2.GSTSphereCycleLegs
import HCUniverse2.GSTSpherePointSpaceCohomology

/-
Copyright (c) 2026. The HC-PROOF campaign. All rights reserved.

# GST SPHERE-UNION POINT-CLASS GATE (Wave 59, file F3)

THE WEIGHT-1 GATE CALCULUS of the positive-dimensional lane — the
carrier-free module the frozen design demanded:

* `spherePointClass M ω i` — the honest point class of the i-th line:
  the pullback of ONE honest degree-two sphere class `ω` along the i-th
  collapse;
* `incl_pointClass_self` — the on-slice restriction is `ω` itself (the
  wave-57 restriction-section calculus);
* `incl_pointClass_ne` — the off-slice restriction is ZERO (the
  const-factorization through the point space, whose H² vanishes — file
  F2);
* `spherePointClass_ne_zero` + `spherePointClass_indep` — the family is
  nonzero and linearly independent (the gate's first two fields);
* `cycle_pointClass` — the M-cycle letter's operator equation: the cycle
  permutes the family along `cyclicPred` (the gate's cycle-equivariance
  field, the input the Krylov orbit of the planned law-landing consumes).

Everything is stated on the RAW sphere-union space; the carrier-side gate
structure (`FiniteLinePointClassData`) is assembled once the scheme
carrier lands, by composing with the analytification's space
identification.

Honesty ledger: every statement is proved unconditionally.  The single
input is the honest sphere class `ω` with `ω ≠ 0` — the fenced
sphere-machine core, an explicit hypothesis here.  No `sorry`, no new
axioms, no `native_decide`.  The GitHub CI lane
`gst-sphere-point-class-gate.yml` owns the kernel check.
-/

set_option maxHeartbeats 200000000
set_option maxRecDepth 1000000

noncomputable section

open CategoryTheory
open GSTSphereUnionComponents
open GSTSingularCohomologyMaps
open GSTSphereCycleLegs
open GSTSpherePointSpaceCohomology

namespace GSTSphereUnionPointClassGate

/-! ## §0 The composite-restriction helper -/

/-- The pair-pullback: pulling back along `g` then along `f` is pulling
back along the composite (the applied form of the wave-57 contravariant
composition law). -/
theorem pullback_pair {X Y Z : TopCat} (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ)
    (ω : singularCohomologyOf Z n) :
    (cohomologyPullbackOf f n) ((cohomologyPullbackOf g n) ω) =
      (cohomologyPullbackOf (f ≫ g) n) ω := by
  rw [cohomologyPullbackOf_comp f g n]
  rfl

/-! ## §1 The honest point-class family -/

/-- **THE HONEST POINT CLASS OF THE i-TH LINE.**  The pullback of the
honest degree-two sphere class along the i-th collapse. -/
def spherePointClass (M : ℕ)
    (ω : singularCohomologyOf (TopCat.of unitSphereType) 2)
    (i : Fin M) :
    singularCohomologyOf (TopCat.of (sphereUnionSpace M)) 2 :=
  (cohomologyPullbackOf (sphereCollapse M i) 2) ω

/-! ## §2 The restriction calculus -/

/-- **THE ON-SLICE RESTRICTION.**  Restricting the i-th point class to
the i-th slice returns the sphere class itself: the collapse is a section
of the inclusion. -/
theorem incl_pointClass_self (M : ℕ)
    (ω : singularCohomologyOf (TopCat.of unitSphereType) 2) (i : Fin M) :
    (cohomologyPullbackOf (sphereIncl M i) 2) (spherePointClass M ω i) = ω := by
  rw [show spherePointClass M ω i =
      (cohomologyPullbackOf (sphereCollapse M i) 2) ω from rfl,
    pullback_pair (sphereIncl M i) (sphereCollapse M i) 2 ω,
    incl_comp_collapse M i, cohomologyPullbackOf_id]
  rfl

/-- **THE OFF-SLICE RESTRICTION.**  Restricting the i-th point class to a
different slice is ZERO: the off-slice composite is the constant map,
which factors through the point space, whose H² vanishes. -/
theorem incl_pointClass_ne (M : ℕ)
    (ω : singularCohomologyOf (TopCat.of unitSphereType) 2)
    (i j : Fin M) (hji : j ≠ i) :
    (cohomologyPullbackOf (sphereIncl M j) 2) (spherePointClass M ω i) = 0 := by
  rw [show spherePointClass M ω i =
      (cohomologyPullbackOf (sphereCollapse M i) 2) ω from rfl,
    pullback_pair (sphereIncl M j) (sphereCollapse M i) 2 ω,
    incl_comp_collapse_const M i j hji]
  exact constSphere_pullback_two M ω

/-! ## §3 Nonzero and independence -/

/-- **THE POINT CLASSES ARE NONZERO** (given the sphere class is). -/
theorem spherePointClass_ne_zero (M : ℕ)
    (ω : singularCohomologyOf (TopCat.of unitSphereType) 2) (hω : ω ≠ 0)
    (i : Fin M) :
    spherePointClass M ω i ≠ 0 := by
  intro h
  exact hω (by
    rw [← incl_pointClass_self M ω i, h, map_zero])

/-- **THE POINT CLASSES ARE LINEARLY INDEPENDENT.**  A relation, restricted
to the j-th slice, leaves only the j-th coefficient times the sphere
class. -/
theorem spherePointClass_indep (M : ℕ)
    (ω : singularCohomologyOf (TopCat.of unitSphereType) 2) (hω : ω ≠ 0) :
    LinearIndependent ℚ (spherePointClass M ω) := by
  rw [linearIndependent_iff']
  intro s g hg j hj
  have hsum : (cohomologyPullbackOf (sphereIncl M j) 2)
      (∑ i ∈ s, g i • spherePointClass M ω i) = 0 := by
    rw [hg, map_zero]
  rw [map_sum] at hsum
  simp only [map_smul] at hsum
  have hsingle : ∑ i ∈ s, g i • (cohomologyPullbackOf (sphereIncl M j) 2)
      (spherePointClass M ω i) = g j • ω := by
    rw [Finset.sum_eq_single_of_mem j hj]
    · rw [incl_pointClass_self M ω j]
    · intro i _hi hij
      rw [incl_pointClass_ne M ω i j (Ne.symm hij), smul_zero]
  rw [hsingle] at hsum
  rcases (smul_eq_zero (R := ℚ)).mp hsum with h | h
  · exact h
  · exact absurd h hω

/-! ## §4 The cycle action -/

/-- **THE CYCLE-EQUIVARIANCE EQUATION.**  The M-cycle letter's cohomology
operator sends the j-th point class to the predecessor-slice point class:
the Krylov orbit of the 0-th class under the letter visits every line. -/
theorem cycle_pointClass (M : ℕ)
    (ω : singularCohomologyOf (TopCat.of unitSphereType) 2) (j : Fin M) :
    (cohomologyPullbackOf (sphereCycle M) 2) (spherePointClass M ω j) =
      spherePointClass M ω (cyclicPred M j) := by
  rw [show spherePointClass M ω j =
      (cohomologyPullbackOf (sphereCollapse M j) 2) ω from rfl,
    pullback_pair (sphereCycle M) (sphereCollapse M j) 2 ω,
    cycle_comp_collapse M j]
  rfl

/-! ## §5 The gate bundle -/

/-- **THE RAW-SPACE POINT-CLASS GATE.**  Given ONE honest nonzero
degree-two class on the sphere, the collapse family is nonzero at the
0-th line, linearly independent, and cycle-equivariant — the gate fields
of the frozen design, on the raw sphere-union space. -/
theorem spherePointClass_gate (M : ℕ) (hM : 0 < M)
    (ω : singularCohomologyOf (TopCat.of unitSphereType) 2) (hω : ω ≠ 0) :
    spherePointClass M ω ⟨0, hM⟩ ≠ 0 ∧
    LinearIndependent ℚ (spherePointClass M ω) ∧
    ∀ j : Fin M, (cohomologyPullbackOf (sphereCycle M) 2)
        (spherePointClass M ω j) = spherePointClass M ω (cyclicPred M j) :=
  ⟨spherePointClass_ne_zero M ω hω _, spherePointClass_indep M ω hω,
    fun j => cycle_pointClass M ω j⟩

end GSTSphereUnionPointClassGate
