import GSTClassicalHodgeGradedFiniteClosedCorrespondence

/-!
# GST CLASSICAL HODGE — TRANSPOSE OF A BI-FINITE CLOSED CORRESPONDENCE

The one-ghost adjoint criterion naturally asks for a geometric transpose.
The existing `FiniteClosedCorrespondence` assumes only finite fibers over the
left projection, so transposition is not automatic: after swapping the two
factors, finite left fibers are exactly finite right fibers of the original
correspondence.

This file makes that boundary explicit and geometric.

* construct the genuine swap automorphism of `X ×_C X`;
* prove it exchanges the two projections and is involutive;
* define `BiFiniteClosedCorrespondence` by adding finite right fibers;
* construct its actual transposed `FiniteClosedCorrespondence` by composing
  the closed immersion with the swap;
* prove the transpose exchanges left and right projections exactly.

No Hodge statement, pairing identity, or algebraicity conclusion enters this
layer.  It is the native correspondence geometry needed before a projection
formula can be stated honestly.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry

namespace GSTClassicalHodgeFiniteClosedCorrespondenceTranspose

open GSTProjectiveOverC
open GSTClassicalHodgeProjectiveSelfCorrespondences
open GSTClassicalHodgeFiniteClosedCorrespondence

variable {V : SmoothProjectiveComplexScheme}

/-- The genuine algebraic factor-swap on the self-product. -/
noncomputable def selfProductSwap
    (V : SmoothProjectiveComplexScheme) :
    selfProduct V ⟶ selfProduct V :=
  pullback.lift (snd V) (fst V) (by
    simpa using (fst_toBase_eq_snd_toBase V).symm)

@[simp, reassoc]
theorem selfProductSwap_fst
    (V : SmoothProjectiveComplexScheme) :
    selfProductSwap V ≫ fst V = snd V := by
  exact pullback.lift_fst _ _ _

@[simp, reassoc]
theorem selfProductSwap_snd
    (V : SmoothProjectiveComplexScheme) :
    selfProductSwap V ≫ snd V = fst V := by
  exact pullback.lift_snd _ _ _

/-- Swapping twice is literally the identity of the algebraic self-product. -/
theorem selfProductSwap_involutive
    (V : SmoothProjectiveComplexScheme) :
    selfProductSwap V ≫ selfProductSwap V = 𝟙 (selfProduct V) := by
  apply pullback.hom_ext
  · rw [Category.assoc, selfProductSwap_fst, selfProductSwap_snd]
    simp
  · rw [Category.assoc, selfProductSwap_snd, selfProductSwap_fst]
    simp

/-- The swap as an honest algebraic isomorphism. -/
noncomputable def selfProductSwapIso
    (V : SmoothProjectiveComplexScheme) :
    selfProduct V ≅ selfProduct V where
  hom := selfProductSwap V
  inv := selfProductSwap V
  hom_inv_id := selfProductSwap_involutive V
  inv_hom_id := selfProductSwap_involutive V

/-- A closed correspondence finite over both projections.  This is exactly the
extra geometry required for its transpose to remain a finite-left-fiber
correspondence. -/
structure BiFiniteClosedCorrespondence
    (V : SmoothProjectiveComplexScheme)
    extends FiniteClosedCorrespondence V where
  rightFiber_finite : ∀ x : V.X,
    ({z : toFiniteClosedCorrespondence.carrier |
      toFiniteClosedCorrespondence.right z = x} :
      Set toFiniteClosedCorrespondence.carrier).Finite

namespace BiFiniteClosedCorrespondence

/-- Right fiber as a set. -/
def rightFiber
    (K : BiFiniteClosedCorrespondence V) (x : V.X) : Set K.carrier :=
  {z | K.toFiniteClosedCorrespondence.right z = x}

/-- The right fiber is finite by the bi-finite hypothesis. -/
theorem rightFiber_finite'
    (K : BiFiniteClosedCorrespondence V) (x : V.X) :
    (K.rightFiber x).Finite := by
  simpa [rightFiber] using K.rightFiber_finite x

/-- **GENUINE TRANSPOSE CORRESPONDENCE.**
Compose the closed immersion with the actual factor-swap.  Finite left fibers
of the transpose are exactly finite right fibers of the original. -/
noncomputable def transpose
    (K : BiFiniteClosedCorrespondence V) : FiniteClosedCorrespondence V := by
  let e := selfProductSwapIso V
  letI : IsIso e.hom := e.isIso_hom
  refine {
    carrier := K.carrier
    intoProduct := K.intoProduct ≫ e.hom
    closedImmersion := ?_
    leftFiber_finite := ?_
  }
  · haveI hK : IsClosedImmersion K.intoProduct := K.closedImmersion
    infer_instance
  · intro x
    have hset :
        ({z : K.carrier |
          ((K.intoProduct ≫ e.hom) ≫ fst V) z = x} : Set K.carrier) =
          K.rightFiber x := by
      ext z
      simp [e, selfProductSwapIso, rightFiber, Category.assoc]
    rw [hset]
    exact K.rightFiber_finite x

/-- The left projection of the transpose is exactly the original right
projection. -/
theorem transpose_left
    (K : BiFiniteClosedCorrespondence V) :
    K.transpose.left = K.toFiniteClosedCorrespondence.right := by
  change (K.intoProduct ≫ selfProductSwap V) ≫ fst V =
    K.intoProduct ≫ snd V
  rw [Category.assoc, selfProductSwap_fst]

/-- The right projection of the transpose is exactly the original left
projection. -/
theorem transpose_right
    (K : BiFiniteClosedCorrespondence V) :
    K.transpose.right = K.toFiniteClosedCorrespondence.left := by
  change (K.intoProduct ≫ selfProductSwap V) ≫ snd V =
    K.intoProduct ≫ fst V
  rw [Category.assoc, selfProductSwap_snd]

/-- Underlying immersion of transpose followed by another swap recovers the
original closed immersion. -/
theorem transpose_intoProduct_swap
    (K : BiFiniteClosedCorrespondence V) :
    K.transpose.intoProduct ≫ selfProductSwap V = K.intoProduct := by
  change (K.intoProduct ≫ selfProductSwap V) ≫ selfProductSwap V =
    K.intoProduct
  rw [Category.assoc, selfProductSwap_involutive]
  simp

/-- The original finite left fibers make the transpose finite over its right
projection as well. -/
theorem transpose_rightFiber_finite
    (K : BiFiniteClosedCorrespondence V) (x : V.X) :
    ({z : K.transpose.carrier | K.transpose.right z = x} :
      Set K.transpose.carrier).Finite := by
  rw [transpose_right]
  exact K.toFiniteClosedCorrespondence.leftFiber_finite x

/-- The transpose is itself canonically bi-finite. -/
noncomputable def transposeBiFinite
    (K : BiFiniteClosedCorrespondence V) :
    BiFiniteClosedCorrespondence V where
  toFiniteClosedCorrespondence := K.transpose
  rightFiber_finite := K.transpose_rightFiber_finite

/-- Double transpose recovers both original projections. -/
theorem transpose_transpose_left
    (K : BiFiniteClosedCorrespondence V) :
    K.transposeBiFinite.transpose.left =
      K.toFiniteClosedCorrespondence.left := by
  rw [transpose_left]
  exact transpose_right K

/-- Double transpose recovers the original right projection as well. -/
theorem transpose_transpose_right
    (K : BiFiniteClosedCorrespondence V) :
    K.transposeBiFinite.transpose.right =
      K.toFiniteClosedCorrespondence.right := by
  rw [transpose_right]
  exact transpose_left K

end BiFiniteClosedCorrespondence

#check selfProductSwap
#check selfProductSwap_fst
#check selfProductSwap_snd
#check selfProductSwap_involutive
#check selfProductSwapIso
#check BiFiniteClosedCorrespondence
#check BiFiniteClosedCorrespondence.transpose
#check BiFiniteClosedCorrespondence.transpose_left
#check BiFiniteClosedCorrespondence.transpose_right
#check BiFiniteClosedCorrespondence.transposeBiFinite
#check BiFiniteClosedCorrespondence.transpose_transpose_left
#check BiFiniteClosedCorrespondence.transpose_transpose_right

#print axioms selfProductSwap_involutive
#print axioms BiFiniteClosedCorrespondence.transpose_left
#print axioms BiFiniteClosedCorrespondence.transpose_right
#print axioms BiFiniteClosedCorrespondence.transpose_transpose_left
#print axioms BiFiniteClosedCorrespondence.transpose_transpose_right

end GSTClassicalHodgeFiniteClosedCorrespondenceTranspose
