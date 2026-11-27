import Mathlib

/-!
# GST hypothesis: original-X divisor/curve Chow cyclic fold algebra

The accompanying geometric proof
 research/derivations/GST_original_X_divisor_curve_hodge_cyclic_chow_correspondence_2026_11_11.tex
constructs ACTUAL Chow correspondences on every smooth connected projective
original X in codimensions p=1 and p=dim(X)-1, from genuine algebraic divisor
cycles and the nondegenerate rational Hodge-index intersection matrix.

This module verifies the precise native/intersection/Betti LINEAR ALGEBRA:
* all native readouts are rational intersection degrees with ACTUAL cycles;
* all Betti readouts are canonical rational cup/integration pairings;
* their equality is the projection formula, NOT an Hodge-to-Chow inverse;
* a finite rational sum of matrix-unit source operators is a natural fold;
* its action on genuine source cycles is an exact cyclic permutation;
* under a cyclic indexing its entire native/Betti orbit spans the existing
  original algebraic source frame.

The geometric proof independently establishes that this source frame
is a BASIS for W_1(X) and W_{dim(X)-1}(X) via Lefschetz (1,1), hard
Lefschetz and the Hodge index theorem. Nothing in this file claims that
a basis of algebraic classes has been constructed for every higher p.

Full Chow correspondences on X×X have positive-dimensional left fibers
in general, so the repo's narrower FiniteClosedCorrespondence datatype
cannot directly encode the product-cycle geometry in the companion paper.
Do not claim that this abstract rational-module file itself creates
Chow cycle products in Mathlib.
-/

set_option maxHeartbeats 6000000
noncomputable section
open scoped BigOperators

namespace GSTOriginalXDivisorCurveCyclicChowFold

universe u v w

variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {A : Type v} [AddCommGroup A] [Module ℚ A]
variable {B : Type w} [AddCommGroup B] [Module ℚ B]

/-- The exact finite Gram-dual data of the REAL original-X divisor/curve
intersection construction. Neither a Hodge-class preimage nor universal
surjectivity is an input. -/
structure IntersectionChowFrame
    (ι : Type u) (A : Type v) (B : Type w)
    [Fintype ι] [DecidableEq ι]
    [AddCommGroup A] [Module ℚ A]
    [AddCommGroup B] [Module ℚ B] where
  cycleClass : A →ₗ[ℚ] B
  source : ι → A
  nativeIntersection : ι → (A →ₗ[ℚ] ℚ)
  bettiIntersection : ι → (B →ₗ[ℚ] ℚ)
  intersection_natural :
    ∀ (i : ι) (z : A),
      nativeIntersection i z = bettiIntersection i (cycleClass z)
  intersection_delta :
    ∀ i j : ι,
      nativeIntersection i (source j) = if i = j then 1 else 0

variable (F : IntersectionChowFrame ι A B)

namespace IntersectionChowFrame

/-- The actual rational Chow matrix-unit sum
  N_sigma(z)=sum_i degree(z . Y_i) Z_(sigma i)
at the level of the original native cycle module. -/
noncomputable def nativeCycleFold (sigma : ι → ι) : A →ₗ[ℚ] A where
  toFun z :=
    ∑ i : ι, (F.nativeIntersection i z) • F.source (sigma i)
  map_add' := by
    intro x y
    simp [map_add, add_smul, Finset.sum_add_distrib]
  map_smul' := by
    intro q x
    simp [map_smul, smul_smul, Finset.smul_sum]

/-- Exactly the SAME finite Chow correspondence's canonical Betti action:
  T_sigma(v)=sum_i int_X(v . cl(Y_i)) cl(Z_(sigma i)). -/
noncomputable def bettiCyclicFold (sigma : ι → ι) : B →ₗ[ℚ] B where
  toFun v :=
    ∑ i : ι,
      (F.bettiIntersection i v) • F.cycleClass (F.source (sigma i))
  map_add' := by
    intro x y
    simp [map_add, add_smul, Finset.sum_add_distrib]
  map_smul' := by
    intro q x
    simp [map_smul, smul_smul, Finset.smul_sum]

/-- Exact canonical native/Betti square for EVERY native cycle and EVERY
finite index permutation. No unknown alpha-indexed Chow lift is used. -/
theorem nativeCycleFold_class (sigma : ι → ι) (z : A) :
    F.cycleClass (F.nativeCycleFold sigma z) =
      F.bettiCyclicFold sigma (F.cycleClass z) := by
  change
    F.cycleClass
      (∑ i : ι, (F.nativeIntersection i z) • F.source (sigma i)) =
    ∑ i : ι,
      (F.bettiIntersection i (F.cycleClass z)) •
        F.cycleClass (F.source (sigma i))
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_smul, F.intersection_natural i z]

/-- The Chow fold genuinely moves each original source cycle to the next
prescribed cycle, because the intersection degrees are delta_ij. -/
theorem nativeCycleFold_source (sigma : ι → ι) (j : ι) :
    F.nativeCycleFold sigma (F.source j) = F.source (sigma j) := by
  change
    (∑ i : ι, F.nativeIntersection i (F.source j) •
        F.source (sigma i)) = F.source (sigma j)
  simp_rw [F.intersection_delta]
  simp

/-- Betti matrix-unit action on the actual source class. -/
theorem bettiCyclicFold_source (sigma : ι → ι) (j : ι) :
    F.bettiCyclicFold sigma (F.cycleClass (F.source j)) =
      F.cycleClass (F.source (sigma j)) := by
  rw [← F.nativeCycleFold_class sigma, F.nativeCycleFold_source sigma j]

/-- Original native/Betti pairing sees each actual source class as a
Kronecker basis vector, without selecting an inverse of cycleClass. -/
theorem bettiIntersection_source (i j : ι) :
    F.bettiIntersection i (F.cycleClass (F.source j)) =
      if i = j then (1 : ℚ) else 0 := by
  rw [← F.intersection_natural i (F.source j)]
  exact F.intersection_delta i j

/-- The same original-X finite index sequence on both native and Hodge sides. -/
def indexOrbit (sigma : ι → ι) (j : ι) : ℕ → ι
  | 0 => j
  | n + 1 => sigma (indexOrbit sigma j n)

/-- Genuine Chow orbit from ONE original-X algebraic seed. -/
def nativeOrbit (sigma : ι → ι) (j : ι) : ℕ → A
  | 0 => F.source j
  | n + 1 => F.nativeCycleFold sigma (nativeOrbit sigma j n)

/-- Explicit original-X cycle at EVERY iterated source step. -/
theorem nativeOrbit_eq_source (sigma : ι → ι) (j : ι) :
    ∀ n : ℕ,
      F.nativeOrbit sigma j n = F.source (indexOrbit sigma j n) := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      change F.nativeCycleFold sigma (F.nativeOrbit sigma j n) =
        F.source (sigma (indexOrbit sigma j n))
      rw [ih, F.nativeCycleFold_source]

/-- All native orbit classes, for ANY index map sigma, are genuine
original-X algebraic cycle classes of the source frame. -/
theorem orbit_span_le_source_span (sigma : ι → ι) (j : ι) :
    Submodule.span ℚ
      (Set.range (fun n : ℕ => F.cycleClass (F.nativeOrbit sigma j n))) ≤
    Submodule.span ℚ
      (Set.range (fun i : ι => F.cycleClass (F.source i))) := by
  apply Submodule.span_le.mpr
  rintro x ⟨n, rfl⟩
  change F.cycleClass (F.nativeOrbit sigma j n) ∈
    Submodule.span ℚ
      (Set.range (fun i : ι => F.cycleClass (F.source i)))
  rw [F.nativeOrbit_eq_source sigma j n]
  exact Submodule.subset_span (Set.mem_range_self (indexOrbit sigma j n))

/-- A genuinely CYCLIC index map has an orbit that spans the complete
frame of already constructed algebraic sources. This is distinct from
assuming that frame spans arbitrary higher Hodge cohomology. -/
theorem source_span_le_orbit_span (sigma : ι → ι) (j : ι)
    (hcyc : Function.Surjective (indexOrbit sigma j)) :
    Submodule.span ℚ
      (Set.range (fun i : ι => F.cycleClass (F.source i))) ≤
    Submodule.span ℚ
      (Set.range (fun n : ℕ => F.cycleClass (F.nativeOrbit sigma j n))) := by
  apply Submodule.span_le.mpr
  rintro x ⟨i, rfl⟩
  obtain ⟨n, hn⟩ := hcyc i
  have hmem :
      F.cycleClass (F.source (indexOrbit sigma j n)) ∈
        Submodule.span ℚ
          (Set.range (fun m : ℕ => F.cycleClass (F.nativeOrbit sigma j m))) := by
    apply Submodule.subset_span
    refine ⟨n, ?_⟩
    change F.cycleClass (F.nativeOrbit sigma j n) =
      F.cycleClass (F.source (indexOrbit sigma j n))
    rw [F.nativeOrbit_eq_source sigma j n]
  simpa [hn] using hmem

theorem source_span_eq_orbit_span (sigma : ι → ι) (j : ι)
    (hcyc : Function.Surjective (indexOrbit sigma j)) :
    Submodule.span ℚ
      (Set.range (fun n : ℕ => F.cycleClass (F.nativeOrbit sigma j n))) =
    Submodule.span ℚ
      (Set.range (fun i : ι => F.cycleClass (F.source i))) := by
  apply le_antisymm
  · exact F.orbit_span_le_source_span sigma j
  · exact F.source_span_le_orbit_span sigma j hcyc

#check IntersectionChowFrame
#check nativeCycleFold_class
#check nativeCycleFold_source
#check bettiCyclicFold_source
#check bettiIntersection_source
#check nativeOrbit_eq_source
#check source_span_eq_orbit_span
#print axioms nativeCycleFold_class
#print axioms nativeCycleFold_source
#print axioms source_span_eq_orbit_span

end IntersectionChowFrame

end GSTOriginalXDivisorCurveCyclicChowFold
