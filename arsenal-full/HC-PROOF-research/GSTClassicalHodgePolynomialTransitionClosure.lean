import GSTClassicalHodgeGeneratorwiseAtomicStability

/-!
# GST CLASSICAL HODGE — POLYNOMIAL TRANSITION CLOSURE

A single generatorwise transition law for one rational cohomological
observable propagates automatically through the entire polynomial functional
calculus used by the GST spectral machinery.

If T sends every genuine codimension-p point-cycle class into the atomic span,
then the whole atomic span is T-invariant.  The cyclic-spectral engine already
proves that T-invariance implies invariance under every polynomial P(T).
Combining that theorem with the exact finite-transition normal form gives:

  every polynomial P(T) sends every genuine point-cycle class to an explicit
  finite rational point-cycle presentation.

Thus once one base GST/Lefschetz observable is shown generatorwise algebraic,
all of its Lagrange isolators, code-sector projectors and spectral extraction
operators inherit classical atomic naturality automatically.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000000

noncomputable section

open scoped BigOperators
open AlgebraicGeometry
open GSTGeometricRealizationStage2D
open GSTNativeCodimensionCyclePresentation
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeCyclicSpectralGeneration
open GSTClassicalHodgeGeneratorwiseAtomicStability

namespace GSTClassicalHodgePolynomialTransitionClosure

universe u v

variable {X : Scheme.{u}}
variable {Coh : Type v} [AddCommGroup Coh] [Module ℚ Coh]
variable {p : Nat}
variable {cl : codimensionCycles X p →ₗ[ℚ] Coh}
variable {T : Coh →ₗ[ℚ] Coh}

/-- Atomic stability propagates through the complete rational polynomial
functional calculus of an atomic-stable observable. -/
theorem atomicSpanStable_linearPolyEval
    (hT : AtomicSpanStable (p := p) (cl := cl) T)
    (P : Polynomial ℚ) :
    AtomicSpanStable (p := p) (cl := cl) (linearPolyEval T P) := by
  intro y hy
  exact polynomialStable_of_operatorStable
    (pointCycleClassSpan p cl) T hT P y hy

/-- A point-transition kernel for T therefore gives finite point transitions
for every polynomial P(T). -/
theorem finitePointTransitions_linearPolyEval
    (K : PointClassTransitionKernel (p := p) (cl := cl) T)
    (P : Polynomial ℚ) :
    HasFinitePointTransitions
      (p := p) (cl := cl) (linearPolyEval T P) := by
  apply (atomicSpanStable_iff_finitePointTransitions
    (p := p) (cl := cl) (linearPolyEval T P)).mp
  exact atomicSpanStable_linearPolyEval K.atomicSpanStable P

/-- Choose the induced finite point-transition kernel for P(T).  The theorem
above guarantees existence; this definition packages those finite geometric
transitions for downstream spectral projector arguments. -/
noncomputable def polynomialPointTransitionKernel
    (K : PointClassTransitionKernel (p := p) (cl := cl) T)
    (P : Polynomial ℚ) :
    PointClassTransitionKernel
      (p := p) (cl := cl) (linearPolyEval T P) where
  transition x :=
    Classical.choose (finitePointTransitions_linearPolyEval K P x)
  transition_spec x :=
    Classical.choose_spec (finitePointTransitions_linearPolyEval K P x)

/-- Every polynomially extracted point class has an actual native
codimension-p cycle representative, obtained by realizing its finite point
presentation. -/
theorem exists_native_cycle_for_polynomial_point_image
    (K : PointClassTransitionKernel (p := p) (cl := cl) T)
    (P : Polynomial ℚ)
    (x : CodimensionPoint X p) :
    ∃ Z : codimensionCycles X p,
      cl Z = linearPolyEval T P
        (cl (codimensionPointCycle X p x)) := by
  let KP := polynomialPointTransitionKernel K P
  refine ⟨realizeFiniteCodimensionPresentation X p (KP.transition x), ?_⟩
  rw [← finitePointCycleClassMap_eq_cycleClass_realize]
  exact KP.transition_spec x

/-! ## Spectral isolator specialization -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- If the base observable of a finite spectral family has a point-transition
kernel, then every Lagrange isolator used to select an individual spectral
sheet also has a point-transition kernel. -/
noncomputable def FiniteSpectralFamily.isolatorPointTransitionKernel
    (S : FiniteSpectralFamily ι Coh)
    (K : PointClassTransitionKernel
      (p := p) (cl := cl) S.observable)
    (i : ι) :
    PointClassTransitionKernel
      (p := p) (cl := cl)
      (linearPolyEval S.observable (S.isolatorPolynomial i)) :=
  polynomialPointTransitionKernel K (S.isolatorPolynomial i)

/-- In particular, each Lagrange-isolated image of a genuine point-cycle class
is again the class of an actual native codimension-p cycle. -/
theorem FiniteSpectralFamily.exists_native_cycle_for_isolated_point
    (S : FiniteSpectralFamily ι Coh)
    (K : PointClassTransitionKernel
      (p := p) (cl := cl) S.observable)
    (i : ι)
    (x : CodimensionPoint X p) :
    ∃ Z : codimensionCycles X p,
      cl Z =
        linearPolyEval S.observable (S.isolatorPolynomial i)
          (cl (codimensionPointCycle X p x)) :=
  exists_native_cycle_for_polynomial_point_image
    K (S.isolatorPolynomial i) x

#check atomicSpanStable_linearPolyEval
#check finitePointTransitions_linearPolyEval
#check polynomialPointTransitionKernel
#check exists_native_cycle_for_polynomial_point_image
#check FiniteSpectralFamily.isolatorPointTransitionKernel
#check FiniteSpectralFamily.exists_native_cycle_for_isolated_point

#print axioms atomicSpanStable_linearPolyEval
#print axioms finitePointTransitions_linearPolyEval
#print axioms polynomialPointTransitionKernel
#print axioms exists_native_cycle_for_polynomial_point_image
#print axioms FiniteSpectralFamily.isolatorPointTransitionKernel
#print axioms FiniteSpectralFamily.exists_native_cycle_for_isolated_point

end GSTClassicalHodgePolynomialTransitionClosure
