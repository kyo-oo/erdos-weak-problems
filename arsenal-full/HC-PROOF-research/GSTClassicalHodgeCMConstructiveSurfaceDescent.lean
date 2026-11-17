import GSTClassicalHodgeCrossCarrierExplicitPointKernel
import GSTClassicalHodgeCMNativeRationalDescent

/-!
# CM surface/Gale route: finite incidence and algebraic coefficients -> Q-cycles

This is a concrete composition of the two independent upgrades:
(1) geometric incidence data at source points creates a native
    rational-cycle operator on TWO DIFFERENT projective varieties;
(2) a finite K-linear Betti representation of a rational target by
    these explicit images descends to a finite Q-linear representation.

A source cycle is never chosen as a preimage of the target.  The sources,
point incidence kernel and Betti action are explicit independent inputs.
The theorem CONSTRUCTS the rational target algebraic cycle.

The coefficient field K can be Qbar or any other field extension of Q;
we do not assume the crucial surface period lies in Q. This is the correct
coefficient shape for the CM paper's surface-switch correspondence route,
and for Gale sources after Tate-twist and codimension bookkeeping.

The one geometric obligation is the pointwise Betti action of the chosen
finite incidence kernel. This is not equivalent to the claim that every
Hodge class is algebraic unless sufficient geometric source data is supplied
from an independent construction.

NEEDS CI RUN LATER.
-/

set_option maxHeartbeats 55000000
set_option maxRecDepth 1000000

noncomputable section

open scoped BigOperators
open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeCrossCarrierPointIncidence
open GSTClassicalHodgeCrossCarrierExplicitPointKernel
open GSTClassicalHodgeCMNativeRationalDescent

namespace GSTClassicalHodgeCMConstructiveSurfaceDescent

variable {K : Type*} [Field K] [Algebra ℚ K]
variable {I : Type*}
variable {S V : SmoothProjectiveComplexScheme}
variable {D : HodgeBigradedBettiData S}
variable {H : HodgeBigradedBettiData V}
variable {p q : Nat}

/-- An actual finite point-incidence kernel (not a free Betti operator)
acting on independently provided algebraic source cycles, with an exact
K-coefficient equality of the target and the geometrically induced
Betti images. -/
theorem rational_target_of_finite_surface_kernel
    (pointKernel : FiniteCrossCarrierPointKernel S V p q)
    (betti :
      RationalSingularCohomology D.analytification (2 * p) →ₗ[ℚ]
        RationalSingularCohomology H.analytification (2 * q))
    (hIncidence :
      RealizesFinitePointKernelOnBetti (H := D) (J := H)
        pointKernel betti)
    (s : Finset I)
    (sourceCycles : I → codimensionCycles S.X p)
    (coeff : I → K)
    (target : RationalSingularCohomology H.analytification (2 * q))
    (hBettiExpansion :
      let b := Module.Free.chooseBasis ℚ
        (RationalSingularCohomology H.analytification (2 * q))
      ∀ i : Module.Free.ChooseBasisIndex ℚ
        (RationalSingularCohomology H.analytification (2 * q)),
        algebraMap ℚ K ((b.repr target) i) =
          ∑ j ∈ s,
            coeff j * algebraMap ℚ K
              ((b.repr (betti (D.cycleClass p (sourceCycles j)))) i)) :
    ∃ Z : codimensionCycles V.X q, H.cycleClass q Z = target := by
  have hNativeExpansion :
      let b := Module.Free.chooseBasis ℚ
        (RationalSingularCohomology H.analytification (2 * q))
      ∀ i : Module.Free.ChooseBasisIndex ℚ
        (RationalSingularCohomology H.analytification (2 * q)),
        algebraMap ℚ K ((b.repr target) i) =
          ∑ j ∈ s,
            coeff j * algebraMap ℚ K
              ((b.repr (H.cycleClass q
                (nativeOfFinitePointKernel pointKernel (sourceCycles j)))) i) := by
    intro b i
    simpa only [finitePointKernel_naturality
      pointKernel betti hIncidence] using hBettiExpansion i
  exact rational_native_cycle_of_extended_span
    s (fun j => nativeOfFinitePointKernel pointKernel (sourceCycles j))
    coeff target hNativeExpansion

/-- The exact same construction proves unconditional algebraicity of
every target RATIONAL Hodge class to which an independently certified
finite surface kernel provides such an extension-coefficient expansion.
There is no rationality restriction on the extension coefficients. -/
theorem rational_hodge_target_of_finite_surface_kernel
    (pointKernel : FiniteCrossCarrierPointKernel S V p q)
    (betti :
      RationalSingularCohomology D.analytification (2 * p) →ₗ[ℚ]
        RationalSingularCohomology H.analytification (2 * q))
    (hIncidence :
      RealizesFinitePointKernelOnBetti (H := D) (J := H)
        pointKernel betti)
    (s : Finset I)
    (sourceCycles : I → codimensionCycles S.X p)
    (coeff : I → K)
    (target : GSTClassicalHodgeFiberedCosmology.ClassicalHodgeFiber V H q)
    (hBettiExpansion :
      let b := Module.Free.chooseBasis ℚ
        (RationalSingularCohomology H.analytification (2 * q))
      ∀ i : Module.Free.ChooseBasisIndex ℚ
        (RationalSingularCohomology H.analytification (2 * q)),
        algebraMap ℚ K ((b.repr target.1) i) =
          ∑ j ∈ s,
            coeff j * algebraMap ℚ K
              ((b.repr (betti (D.cycleClass p (sourceCycles j)))) i)) :
    target.1 ∈ LinearMap.range (H.cycleClass q) := by
  exact rational_target_of_finite_surface_kernel pointKernel betti
    hIncidence s sourceCycles coeff target.1 hBettiExpansion

#check rational_target_of_finite_surface_kernel
#check rational_hodge_target_of_finite_surface_kernel
#print axioms rational_target_of_finite_surface_kernel

end GSTClassicalHodgeCMConstructiveSurfaceDescent
