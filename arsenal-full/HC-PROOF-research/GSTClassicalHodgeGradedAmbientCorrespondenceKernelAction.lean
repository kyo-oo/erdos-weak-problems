import GSTClassicalHodgeAmbientCorrespondenceKernelAction

/-!
# GST CLASSICAL HODGE — GRADED AMBIENT CORRESPONDENCE KERNEL ACTION

The middle-dimensional strict correspondence layer constructs only the
shift-zero action

  H^n(X,Q) -> H^n(X,Q).

For the Hodge derivation we also need honest cross-weight geometry.  The same
ambient formula is already graded: on a complex d-fold, a kernel class

  kappa in H^(2d+s)(X x X,Q)

acts canonically on every Betti class by

  alpha |-> (p2)_!(kappa cup p1^* alpha)

and lands in H^(n+s)(X,Q).  No extension from the algebraic range is involved.
This file exposes that latent grading directly.

Factor swap gives the corresponding action of the transposed kernel.  Notice
that transpose preserves the degree shift s; it does NOT manufacture a
Lefschetz lowering operator.  A lowering operator, when needed, must come from
Poincare adjunction rather than from a false degree-changing interpretation of
factor swap.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open CategoryTheory
open AlgebraicGeometry

namespace GSTClassicalHodgeGradedAmbientCorrespondenceKernelAction

open GSTProjectiveOverC
open GSTGeometricRealizationStage2F
open GSTClassicalHodgeAmbientBettiSelfProduct
open GSTClassicalHodgeAmbientCorrespondenceKernelAction

variable {V : SmoothProjectiveComplexScheme}
variable (A : AnalytificationData V)

abbrev XCoh (n : Nat) := RationalSingularCohomology A n
abbrev X2Coh (n : Nat) := ProductCohomology A n

/-- A genuine graded ambient Betti kernel.  `shift` is the cohomological degree
increase after integrating over one complex-d-dimensional projection fiber. -/
structure GradedBettiKernel (d shift : Nat) where
  kernelClass : X2Coh A (2 * d + shift)
  transposeClass : X2Coh A (2 * d + shift)
  transposeClass_eq_swap :
    transposeClass =
      swapCohomologyPullback A (2 * d + shift) kernelClass

namespace GradedBettiKernel

variable {d shift : Nat}

/-- Reassociate the cup-product degree into the exact domain expected by the
projection Gysin map. -/
noncomputable def reassociateDegree
    (n : Nat) :
    X2Coh A ((2 * d + shift) + n) →ₗ[ℚ]
      X2Coh A (2 * d + (shift + n)) := by
  rw [Nat.add_assoc]
  exact LinearMap.id

/-- **CANONICAL GRADED WHOLE-BETTI ACTION.**
A degree `2d+shift` kernel acts on every rational Betti class and raises degree
by exactly `shift`. -/
noncomputable def action
    (P : AmbientBettiIntersectionCalculus A d)
    (κ : GradedBettiKernel A d shift)
    (n : Nat) :
    XCoh A n →ₗ[ℚ] XCoh A (shift + n) := by
  let pull : XCoh A n →ₗ[ℚ] X2Coh A n :=
    fstCohomologyPullback A n
  let multiply : X2Coh A n →ₗ[ℚ] X2Coh A ((2 * d + shift) + n) :=
    P.cup (2 * d + shift) n κ.kernelClass
  exact (P.sndGysin (shift + n)).comp
    ((reassociateDegree (A := A) (d := d) (shift := shift) n).comp
      (multiply.comp pull))

@[simp]
theorem action_apply
    (P : AmbientBettiIntersectionCalculus A d)
    (κ : GradedBettiKernel A d shift)
    (n : Nat)
    (alpha : XCoh A n) :
    κ.action A P n alpha =
      P.sndGysin (shift + n)
        ((reassociateDegree (A := A) (d := d) (shift := shift) n)
          (P.cup (2 * d + shift) n κ.kernelClass
            (fstCohomologyPullback A n alpha))) :=
  rfl

/-- Factor swap produces the actual transposed graded kernel with the same
cohomological shift. -/
noncomputable def transposeKernel
    (κ : GradedBettiKernel A d shift) :
    GradedBettiKernel A d shift where
  kernelClass := κ.transposeClass
  transposeClass := κ.kernelClass
  transposeClass_eq_swap := by
    rw [κ.transposeClass_eq_swap]
    have hinv := swapCohomology_involutive A (2 * d + shift)
    have h := LinearMap.congr_fun hinv κ.kernelClass
    simpa using h.symm

/-- The shift-zero specialization is exactly the old middle-kernel ambient
formula, modulo the harmless `0+n=n` degree normalization carried explicitly
by `reassociateDegree`. -/
theorem action_shift_zero_apply
    (P : AmbientBettiIntersectionCalculus A d)
    (κ : GradedBettiKernel A d 0)
    (n : Nat)
    (alpha : XCoh A n) :
    κ.action A P n alpha =
      P.sndGysin (0 + n)
        ((reassociateDegree (A := A) (d := d) (shift := 0) n)
          (P.cup (2 * d + 0) n κ.kernelClass
            (fstCohomologyPullback A n alpha))) := by
  rfl

/-- A codimension-one excess kernel gives the honest degree-two action needed
for hyperplane/principal-section transport. -/
abbrev DegreeTwoKernel (d : Nat) := GradedBettiKernel A d 2

/-- Degree-two kernels act on all even Hodge-weight carriers `H^(2p)` and land
in the next even carrier `H^(2(p+1))`. -/
noncomputable def degreeTwoWeightAction
    (P : AmbientBettiIntersectionCalculus A d)
    (κ : DegreeTwoKernel A d)
    (p : Nat) :
    XCoh A (2 * p) →ₗ[ℚ] XCoh A (2 * (p + 1)) := by
  have hdeg : 2 + 2 * p = 2 * (p + 1) := by omega
  rw [← hdeg]
  exact κ.action A P (2 * p)

/-- The graded construction is total on arbitrary Betti classes, including
classes outside every algebraic cycle-class range. -/
theorem degreeTwoWeightAction_total
    (P : AmbientBettiIntersectionCalculus A d)
    (κ : DegreeTwoKernel A d)
    (p : Nat) :
    ∀ alpha : XCoh A (2 * p),
      ∃ beta : XCoh A (2 * (p + 1)),
        beta = degreeTwoWeightAction (A := A) P κ p alpha := by
  intro alpha
  exact ⟨degreeTwoWeightAction (A := A) P κ p alpha, rfl⟩

#check GradedBettiKernel
#check GradedBettiKernel.action
#check GradedBettiKernel.action_shift_zero_apply
#check DegreeTwoKernel
#check degreeTwoWeightAction
#check degreeTwoWeightAction_total

#print axioms GradedBettiKernel.action_apply
#print axioms GradedBettiKernel.action_shift_zero_apply
#print axioms degreeTwoWeightAction_total

end GradedBettiKernel

end GSTClassicalHodgeGradedAmbientCorrespondenceKernelAction
