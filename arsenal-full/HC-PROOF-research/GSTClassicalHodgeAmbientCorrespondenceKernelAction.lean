import GSTClassicalHodgeAmbientBettiSelfProduct
import GSTClassicalHodgeSchemeFiniteCorrespondenceFirewall
import GSTClassicalHodgeFiniteClosedCorrespondenceOperator

/-!
# GST CLASSICAL HODGE — AMBIENT CORRESPONDENCE KERNEL ACTION

For a smooth projective complex variety X of complex dimension d, the correct
Betti action of a middle-dimensional algebraic correspondence

  C ⊂ X × X

is not obtained by inverting a pullback through the (possibly singular)
carrier C.  It is the standard ambient kernel action

  alpha |-> (p₂)_* ( [C] ∪ p₁^* alpha ).

The ambient space X_an × X_an is smooth/compact even when C itself is singular.
Consequently this formula acts on the COMPLETE rational singular cohomology
carrier, including classes outside the algebraic cycle-class range.

The previous file constructs p₁^*, p₂^*, and factor swap natively from
Mathlib singular chains.  This file isolates only the two standard topological
operations still absent from the pinned Mathlib stack: the graded cup product
and Poincare/Gysin integration along a projection.  Importantly, NO arbitrary
cohomology endomorphism is supplied.  Once those ordinary topological
operations and the actual middle Betti class [C] are present, the operator is
definitionally forced by the displayed formula.

We also prove the genuine transpose formula from factor swap.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open CategoryTheory
open AlgebraicGeometry

namespace GSTClassicalHodgeAmbientCorrespondenceKernelAction

open GSTProjectiveOverC
open GSTGeometricRealizationStage2F
open GSTClassicalHodgeAmbientBettiSelfProduct
open GSTClassicalHodgeSchemeFiniteCorrespondenceFirewall

variable {V : SmoothProjectiveComplexScheme}
variable (A : AnalytificationData V)

abbrev XCoh (n : Nat) := RationalSingularCohomology A n
abbrev X2Coh (n : Nat) := ProductCohomology A n

/-- The ordinary rational intersection-theory operations on the smooth compact
ambient manifold `X_an × X_an`, in a fixed complex dimension `d`.

This is deliberately NOT a correspondence-action structure.  It stores only
cup product and the two projection Gysin maps.  The correspondence action is
constructed below from these operations and the actual class `[C]`. -/
structure AmbientBettiIntersectionCalculus (d : Nat) where
  /-- Graded cup product on the actual product singular cohomology. -/
  cup : ∀ a b : Nat,
    X2Coh A a →ₗ[ℚ] (X2Coh A b →ₗ[ℚ] X2Coh A (a + b))

  /-- Integration/Gysin along the second projection, lowering degree by the
  real fiber dimension `2*d`. -/
  sndGysin : ∀ n : Nat,
    X2Coh A (2 * d + n) →ₗ[ℚ] XCoh A n

  /-- Integration/Gysin along the first projection. -/
  fstGysin : ∀ n : Nat,
    X2Coh A (2 * d + n) →ₗ[ℚ] XCoh A n

  /-- Pullback by coordinate swap is multiplicative. -/
  swap_cup : ∀ a b (u : X2Coh A a) (v : X2Coh A b),
    swapCohomologyPullback A (a + b) (cup a b u v) =
      cup a b
        (swapCohomologyPullback A a u)
        (swapCohomologyPullback A b v)

  /-- Swapping factors converts second-projection integration into
  first-projection integration. -/
  sndGysin_swap : ∀ n (z : X2Coh A (2 * d + n)),
    sndGysin n (swapCohomologyPullback A (2 * d + n) z) =
      fstGysin n z

  /-- Symmetric companion. -/
  fstGysin_swap : ∀ n (z : X2Coh A (2 * d + n)),
    fstGysin n (swapCohomologyPullback A (2 * d + n) z) =
      sndGysin n z

namespace AmbientBettiIntersectionCalculus

/-- Cup on the left by a fixed class, as an honest linear map. -/
noncomputable def cupLeft
    {d a b : Nat}
    (P : AmbientBettiIntersectionCalculus A d)
    (u : X2Coh A a) :
    X2Coh A b →ₗ[ℚ] X2Coh A (a + b) :=
  P.cup a b u

end AmbientBettiIntersectionCalculus

/-- The actual middle Betti kernel carried by one strict scheme correspondence.
For a complex d-fold, a degree-preserving correspondence has class in
`H^(2d)(X×X,Q)`.

The transpose law is geometric: the class of the factor-swapped closed
subscheme is the pullback of `[C]` under coordinate swap. -/
structure MiddleBettiCorrespondenceKernel
    (d : Nat)
    (K : SchemeBiFiniteClosedCorrespondence V) where
  kernelClass : X2Coh A (2 * d)
  transposeClass : X2Coh A (2 * d)
  transposeClass_eq_swap :
    transposeClass = swapCohomologyPullback A (2 * d) kernelClass

namespace MiddleBettiCorrespondenceKernel

variable {d : Nat}
variable {K : SchemeBiFiniteClosedCorrespondence V}

/-- **CANONICAL AMBIENT WHOLE-BETTI ACTION.**

This is the classical correspondence formula

  T_C(alpha) = p₂_*([C] ∪ p₁^* alpha).

It is defined for every rational singular cohomology class alpha. -/
noncomputable def action
    (P : AmbientBettiIntersectionCalculus A d)
    (κ : MiddleBettiCorrespondenceKernel A d K)
    (n : Nat) :
    XCoh A n →ₗ[ℚ] XCoh A n := by
  let pull : XCoh A n →ₗ[ℚ] X2Coh A n := fstCohomologyPullback A n
  let multiply : X2Coh A n →ₗ[ℚ] X2Coh A (2 * d + n) :=
    AmbientBettiIntersectionCalculus.cupLeft A P κ.kernelClass
  exact (P.sndGysin n).comp (multiply.comp pull)

@[simp]
theorem action_apply
    (P : AmbientBettiIntersectionCalculus A d)
    (κ : MiddleBettiCorrespondenceKernel A d K)
    (n : Nat)
    (alpha : XCoh A n) :
    MiddleBettiCorrespondenceKernel.action A P κ n alpha =
      P.sndGysin n
        (P.cup (2 * d) n κ.kernelClass
          (fstCohomologyPullback A n alpha)) :=
  rfl

/-- The transpose correspondence has the swapped middle kernel. -/
noncomputable def transposeKernel
    (κ : MiddleBettiCorrespondenceKernel A d K) :
    MiddleBettiCorrespondenceKernel A d K.transpose where
  kernelClass := κ.transposeClass
  transposeClass := κ.kernelClass
  transposeClass_eq_swap := by
    rw [κ.transposeClass_eq_swap]
    have hinv := swapCohomology_involutive A (2 * d)
    have h := LinearMap.congr_fun hinv κ.kernelClass
    simpa using h.symm

/-- **EXPLICIT TRANSPOSE ACTION FORMULA.**
The action of the genuine algebraic transpose is the first-projection Gysin
of the original kernel against the second pullback.

This is the cohomological form of factor-swap/projective-incidence
compatibility; no formal coefficient transpose is inserted. -/
theorem transpose_action_apply
    (P : AmbientBettiIntersectionCalculus A d)
    (κ : MiddleBettiCorrespondenceKernel A d K)
    (n : Nat)
    (alpha : XCoh A n) :
    MiddleBettiCorrespondenceKernel.action A P (κ.transposeKernel) n alpha =
      P.fstGysin n
        (P.cup (2 * d) n κ.kernelClass
          (sndCohomologyPullback A n alpha)) := by
  rw [action_apply]
  rw [show (transposeKernel A κ).kernelClass = κ.transposeClass from rfl]
  rw [κ.transposeClass_eq_swap]
  have hpull : fstCohomologyPullback A n alpha =
      swapCohomologyPullback A n (sndCohomologyPullback A n alpha) := by
    simpa only [LinearMap.comp_apply] using
      LinearMap.congr_fun (fstPullback_eq_swap_sndPullback A n) alpha
  rw [hpull]
  rw [← P.swap_cup (2 * d) n κ.kernelClass
    (sndCohomologyPullback A n alpha)]
  exact P.sndGysin_swap n _

/-- The ambient construction is total by construction, not by a range or
surjectivity argument. -/
theorem action_total
    (P : AmbientBettiIntersectionCalculus A d)
    (κ : MiddleBettiCorrespondenceKernel A d K)
    (n : Nat) :
    ∀ alpha : XCoh A n, ∃ beta : XCoh A n,
      beta = MiddleBettiCorrespondenceKernel.action A P κ n alpha := by
  intro alpha
  exact ⟨MiddleBettiCorrespondenceKernel.action A P κ n alpha, rfl⟩

#check action
#check action_apply
#check transposeKernel
#check transpose_action_apply
#check action_total

#print axioms action_apply
#print axioms transpose_action_apply
#print axioms action_total

end MiddleBettiCorrespondenceKernel

end GSTClassicalHodgeAmbientCorrespondenceKernelAction
