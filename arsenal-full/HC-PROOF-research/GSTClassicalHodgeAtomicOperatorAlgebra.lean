import GSTClassicalHodgeNativeGeneratorNaturality

/-!
# GST CLASSICAL HODGE — ATOMIC-NATURAL OPERATOR ALGEBRA

The operator-natural part of the classical Hodge attack is stable under the
same algebraic constructions used throughout the GST cosmology.

Once primitive cohomological operators preserve the genuine point-cycle
atomic span, so do:

* zero and identity;
* rational scalar multiples;
* sums and differences;
* compositions;
* natural powers;
* every finite polynomial expression.

On smooth projective carriers these closure laws immediately transport back
to generatorwise native-cycle lifts and finite point-transition kernels.
Consequently a complicated Lefschetz/projector observable only needs to be
factored into primitive atomic-natural generators; atomic naturality of the
full operator is then automatic.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeCyclicSpectralGeneration
open GSTClassicalHodgeGeneratorwiseAtomicStability
open GSTClassicalHodgePolynomialTransitionClosure
open GSTClassicalHodgeNativeGeneratorNaturality

namespace GSTClassicalHodgeAtomicOperatorAlgebra

universe u v

variable {X : Scheme.{u}}
variable {Coh : Type v} [AddCommGroup Coh] [Module ℚ Coh]
variable {p : Nat}
variable {cl : codimensionCycles X p →ₗ[ℚ] Coh}

/-- Zero preserves every atomic span. -/
theorem atomicSpanStable_zero :
    AtomicSpanStable (p := p) (cl := cl) (0 : Coh →ₗ[ℚ] Coh) := by
  intro x hx
  simpa using (pointCycleClassSpan p cl).zero_mem

/-- Identity preserves every atomic span. -/
theorem atomicSpanStable_id :
    AtomicSpanStable (p := p) (cl := cl) (LinearMap.id : Coh →ₗ[ℚ] Coh) := by
  intro x hx
  simpa using hx

/-- Rational scaling preserves atomic naturality. -/
theorem atomicSpanStable_smul
    (q : ℚ) {T : Coh →ₗ[ℚ] Coh}
    (hT : AtomicSpanStable (p := p) (cl := cl) T) :
    AtomicSpanStable (p := p) (cl := cl) (q • T) := by
  intro x hx
  simpa using (pointCycleClassSpan p cl).smul_mem q (hT x hx)

/-- Sums of atomic-natural operators remain atomic-natural. -/
theorem atomicSpanStable_add
    {T U : Coh →ₗ[ℚ] Coh}
    (hT : AtomicSpanStable (p := p) (cl := cl) T)
    (hU : AtomicSpanStable (p := p) (cl := cl) U) :
    AtomicSpanStable (p := p) (cl := cl) (T + U) := by
  intro x hx
  simpa using (pointCycleClassSpan p cl).add_mem (hT x hx) (hU x hx)

/-- Negation preserves atomic naturality. -/
theorem atomicSpanStable_neg
    {T : Coh →ₗ[ℚ] Coh}
    (hT : AtomicSpanStable (p := p) (cl := cl) T) :
    AtomicSpanStable (p := p) (cl := cl) (-T) := by
  intro x hx
  simpa using (pointCycleClassSpan p cl).neg_mem (hT x hx)

/-- Differences of atomic-natural operators remain atomic-natural. -/
theorem atomicSpanStable_sub
    {T U : Coh →ₗ[ℚ] Coh}
    (hT : AtomicSpanStable (p := p) (cl := cl) T)
    (hU : AtomicSpanStable (p := p) (cl := cl) U) :
    AtomicSpanStable (p := p) (cl := cl) (T - U) := by
  intro x hx
  simpa using (pointCycleClassSpan p cl).sub_mem (hT x hx) (hU x hx)

/-- Composition preserves atomic naturality. -/
theorem atomicSpanStable_comp
    {T U : Coh →ₗ[ℚ] Coh}
    (hT : AtomicSpanStable (p := p) (cl := cl) T)
    (hU : AtomicSpanStable (p := p) (cl := cl) U) :
    AtomicSpanStable (p := p) (cl := cl) (T.comp U) := by
  intro x hx
  exact hT _ (hU x hx)

/-- Natural powers of one atomic-natural operator remain atomic-natural. -/
theorem atomicSpanStable_pow
    {T : Coh →ₗ[ℚ] Coh}
    (hT : AtomicSpanStable (p := p) (cl := cl) T) :
    ∀ n : Nat,
      AtomicSpanStable (p := p) (cl := cl) (T ^ n) := by
  intro n
  induction n with
  | zero =>
      exact atomicSpanStable_id (p := p) (cl := cl)
  | succ n ih =>
      rw [pow_succ]
      exact atomicSpanStable_comp ih hT

/-- Polynomial closure, restated as the algebraic crown of the operator
closure package. -/
theorem atomicSpanStable_polynomial
    {T : Coh →ₗ[ℚ] Coh}
    (hT : AtomicSpanStable (p := p) (cl := cl) T)
    (P : Polynomial ℚ) :
    AtomicSpanStable (p := p) (cl := cl) (linearPolyEval T P) :=
  atomicSpanStable_linearPolyEval hT P

/-! ## Smooth-projective native-lift closure -/

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- Native generatorwise naturality is closed under addition on a smooth
projective carrier. -/
theorem nativePointLifts_add
    {T U : RationalSingularCohomology H.analytification (2 * p) →ₗ[ℚ]
      RationalSingularCohomology H.analytification (2 * p)}
    (hT : HasNativePointLifts (p := p) (cl := H.cycleClass p) T)
    (hU : HasNativePointLifts (p := p) (cl := H.cycleClass p) U) :
    HasNativePointLifts (p := p) (cl := H.cycleClass p) (T + U) := by
  rw [← smoothProjective_atomicStable_iff_nativePointLifts] at hT hU ⊢
  exact atomicSpanStable_add hT hU

/-- Native generatorwise naturality is closed under composition. -/
theorem nativePointLifts_comp
    {T U : RationalSingularCohomology H.analytification (2 * p) →ₗ[ℚ]
      RationalSingularCohomology H.analytification (2 * p)}
    (hT : HasNativePointLifts (p := p) (cl := H.cycleClass p) T)
    (hU : HasNativePointLifts (p := p) (cl := H.cycleClass p) U) :
    HasNativePointLifts (p := p) (cl := H.cycleClass p) (T.comp U) := by
  rw [← smoothProjective_atomicStable_iff_nativePointLifts] at hT hU ⊢
  exact atomicSpanStable_comp hT hU

/-- Native generatorwise naturality is closed under every rational polynomial
in a single observable. -/
theorem nativePointLifts_polynomial
    {T : RationalSingularCohomology H.analytification (2 * p) →ₗ[ℚ]
      RationalSingularCohomology H.analytification (2 * p)}
    (hT : HasNativePointLifts (p := p) (cl := H.cycleClass p) T)
    (P : Polynomial ℚ) :
    HasNativePointLifts (p := p) (cl := H.cycleClass p)
      (linearPolyEval T P) := by
  rw [← smoothProjective_atomicStable_iff_nativePointLifts] at hT ⊢
  exact atomicSpanStable_polynomial hT P

/-- **LEFSCHETZ-ASSEMBLY FORM.**  If two primitive axis operators are
native-natural on point classes, then their sum is native-natural, and every
spectral polynomial in that sum is native-natural as well. -/
theorem nativePointLifts_polynomial_of_axis_sum
    {A B : RationalSingularCohomology H.analytification (2 * p) →ₗ[ℚ]
      RationalSingularCohomology H.analytification (2 * p)}
    (hA : HasNativePointLifts (p := p) (cl := H.cycleClass p) A)
    (hB : HasNativePointLifts (p := p) (cl := H.cycleClass p) B)
    (P : Polynomial ℚ) :
    HasNativePointLifts (p := p) (cl := H.cycleClass p)
      (linearPolyEval (A + B) P) := by
  exact nativePointLifts_polynomial (nativePointLifts_add hA hB) P

#check atomicSpanStable_zero
#check atomicSpanStable_id
#check atomicSpanStable_smul
#check atomicSpanStable_add
#check atomicSpanStable_neg
#check atomicSpanStable_sub
#check atomicSpanStable_comp
#check atomicSpanStable_pow
#check atomicSpanStable_polynomial
#check nativePointLifts_add
#check nativePointLifts_comp
#check nativePointLifts_polynomial
#check nativePointLifts_polynomial_of_axis_sum

#print axioms atomicSpanStable_add
#print axioms atomicSpanStable_comp
#print axioms atomicSpanStable_pow
#print axioms atomicSpanStable_polynomial
#print axioms nativePointLifts_add
#print axioms nativePointLifts_comp
#print axioms nativePointLifts_polynomial
#print axioms nativePointLifts_polynomial_of_axis_sum

end GSTClassicalHodgeAtomicOperatorAlgebra
