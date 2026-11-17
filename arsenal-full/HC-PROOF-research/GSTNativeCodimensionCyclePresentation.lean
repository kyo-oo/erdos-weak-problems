import Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic
import GSTGeometricRealizationStage2D

/-!
# GST NATIVE CODIMENSION CYCLE PRESENTATIONS

This module removes an avoidable abstraction from the classical Hodge landing.
A rational algebraic cycle is built explicitly from genuine scheme points of
the required coheight.  Finite rational combinations are then formed inside
`codimensionCycles X p`, so every object produced here is a native Mathlib
`AlgebraicCycle` with the codimension condition proved by construction.

No cohomological cycle-class surjectivity statement is asserted in this file.
The final section instead proves the exact linear formula for the image of a
finite presentation under any supplied rational cycle-class map.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry
open GSTGeometricRealizationStage2D

namespace GSTNativeCodimensionCyclePresentation

universe u

/-- A genuine point of `X` lying in codimension `p`.  In the algebraic-cycle
model this is the generic-point coordinate of an irreducible codimension-p
subvariety. -/
abbrev CodimensionPoint (X : Scheme.{u}) (p : Nat) :=
  {x : X // Order.coheight x = p}

/-- The unit algebraic cycle concentrated at one genuine codimension-p point. -/
noncomputable def codimensionPointCycle
    (X : Scheme.{u}) (p : Nat) (x : CodimensionPoint X p) :
    codimensionCycles X p := by
  classical
  refine ⟨Function.locallyFinsuppWithin.single x.1 (1 : ℚ), ?_⟩
  intro y hy
  have hyx : y = x.1 := by
    by_contra hne
    apply hy
    simp [Function.locallyFinsuppWithin.single_apply, hne]
  subst y
  exact x.2

/-- A finite rational presentation by genuine codimension-p points. -/
abbrev FiniteCodimensionPresentation (X : Scheme.{u}) (p : Nat) :=
  CodimensionPoint X p →₀ ℚ

/-- Realize a finite rational presentation as an actual native
codimension-p algebraic cycle.  Codimension support is preserved because the
sum is performed inside the submodule `codimensionCycles X p`. -/
noncomputable def realizeFiniteCodimensionPresentation
    (X : Scheme.{u}) (p : Nat)
    (φ : FiniteCodimensionPresentation X p) :
    codimensionCycles X p :=
  φ.sum fun x q => q • codimensionPointCycle X p x

@[simp]
theorem realizeFiniteCodimensionPresentation_zero
    (X : Scheme.{u}) (p : Nat) :
    realizeFiniteCodimensionPresentation X p 0 = 0 := by
  simp [realizeFiniteCodimensionPresentation]

/-- Additivity of the realization map, at the presentation level. -/
theorem realizeFiniteCodimensionPresentation_add
    (X : Scheme.{u}) (p : Nat)
    (φ ψ : FiniteCodimensionPresentation X p) :
    realizeFiniteCodimensionPresentation X p (φ + ψ) =
      realizeFiniteCodimensionPresentation X p φ +
        realizeFiniteCodimensionPresentation X p ψ := by
  classical
  simp only [realizeFiniteCodimensionPresentation]
  rw [Finsupp.sum_add_index']
  · intro i; simp
  · intro i b₁ b₂; simp [add_smul]

/-- Scalar homogeneity of the realization map, at the presentation level. -/
theorem realizeFiniteCodimensionPresentation_smul
    (X : Scheme.{u}) (p : Nat)
    (q : ℚ) (φ : FiniteCodimensionPresentation X p) :
    realizeFiniteCodimensionPresentation X p (q • φ) =
      q • realizeFiniteCodimensionPresentation X p φ := by
  classical
  first
  | simp only [realizeFiniteCodimensionPresentation]
    rw [Finsupp.sum_smul_index]
    all_goals first
      | intro i
        simp
      | rfl
      | simp [Finset.smul_sum, smul_smul]
  | by_cases hq : q = 0
    · subst q
      simp
    · have hsup : (q • φ).support = φ.support := by
        ext a
        simp [Finsupp.mem_support_iff, mul_ne_zero_iff, hq]
      simp only [realizeFiniteCodimensionPresentation, Finsupp.sum,
        Finsupp.smul_apply, smul_eq_mul]
      rw [hsup]
      simp [Finset.smul_sum, smul_smul]

@[simp]
theorem realizeFiniteCodimensionPresentation_single
    (X : Scheme.{u}) (p : Nat)
    (x : CodimensionPoint X p) (q : ℚ) :
    realizeFiniteCodimensionPresentation X p (Finsupp.single x q) =
      q • codimensionPointCycle X p x := by
  classical
  by_cases hq : q = 0
  · subst q
    simp
  · simp [realizeFiniteCodimensionPresentation]

/-- Native-cycle receipt: every finite presentation lands in the exact
Stage-2D codimension-p cycle submodule. -/
theorem finite_presentation_is_native_codimension_cycle
    (X : Scheme.{u}) (p : Nat)
    (φ : FiniteCodimensionPresentation X p) :
    (realizeFiniteCodimensionPresentation X p φ : AlgebraicCycle X ℚ) ∈
      codimensionCycles X p :=
  (realizeFiniteCodimensionPresentation X p φ).2

/-! ## Exact image under an arbitrary rational cycle-class map -/

/-- Applying any rational-linear map to a finite codimension presentation is
exactly the finite linear combination of the images of its genuine point
cycles.  For the Stage-2G classical landing, instantiate `cl` with the actual
supplied cycle-class map. -/
theorem linearMap_realizeFiniteCodimensionPresentation
    {Coh : Type*} [AddCommGroup Coh] [Module ℚ Coh]
    (X : Scheme.{u}) (p : Nat)
    (cl : codimensionCycles X p →ₗ[ℚ] Coh)
    (φ : FiniteCodimensionPresentation X p) :
    cl (realizeFiniteCodimensionPresentation X p φ) =
      φ.sum (fun x q => q • cl (codimensionPointCycle X p x)) := by
  classical
  simpa [realizeFiniteCodimensionPresentation] using
    (map_finsuppSum cl φ
      (fun x q => q • codimensionPointCycle X p x))

/-- Singleton specialization: the class of one weighted codimension point is
the same scalar multiple of the class of its unit point cycle. -/
@[simp]
theorem linearMap_realizeFiniteCodimensionPresentation_single
    {Coh : Type*} [AddCommGroup Coh] [Module ℚ Coh]
    (X : Scheme.{u}) (p : Nat)
    (cl : codimensionCycles X p →ₗ[ℚ] Coh)
    (x : CodimensionPoint X p) (q : ℚ) :
    cl (realizeFiniteCodimensionPresentation X p (Finsupp.single x q)) =
      q • cl (codimensionPointCycle X p x) := by
  rw [realizeFiniteCodimensionPresentation_single]
  exact cl.map_smul q (codimensionPointCycle X p x)

#check CodimensionPoint
#check codimensionPointCycle
#check FiniteCodimensionPresentation
#check realizeFiniteCodimensionPresentation
#check realizeFiniteCodimensionPresentation_zero
#check realizeFiniteCodimensionPresentation_single
#check finite_presentation_is_native_codimension_cycle
#check linearMap_realizeFiniteCodimensionPresentation
#check linearMap_realizeFiniteCodimensionPresentation_single

#print axioms codimensionPointCycle
#print axioms realizeFiniteCodimensionPresentation_single
#print axioms finite_presentation_is_native_codimension_cycle
#print axioms linearMap_realizeFiniteCodimensionPresentation
#print axioms linearMap_realizeFiniteCodimensionPresentation_single

end GSTNativeCodimensionCyclePresentation