import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import GSTClassicalHodgeFiniteClosedCorrespondenceTranspose

/-!
# GST CLASSICAL HODGE — SCHEME-FINITE CORRESPONDENCE FIREWALL

The historical `FiniteClosedCorrespondence` carrier records a closed subscheme
of `X × X` and finiteness of the SET of points in each left fiber.
`BiFiniteClosedCorrespondence` adds the analogous right-fiber condition.
Those structures remain useful for the finite point-kernel calculus, but are
strictly weaker than finite morphisms of schemes.

This file installs the strict geometric layer used by the Betti-correspondence
fusion route.  A strict correspondence requires Mathlib's genuine
`AlgebraicGeometry.IsFinite` predicate on the projection morphism(s), then
forgets one-way into the older point-finite API.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry

namespace GSTClassicalHodgeSchemeFiniteCorrespondenceFirewall

open GSTProjectiveOverC
open GSTClassicalHodgeProjectiveSelfCorrespondences
open GSTClassicalHodgeFiniteClosedCorrespondence
open GSTClassicalHodgeFiniteClosedCorrespondenceTranspose

variable {V : SmoothProjectiveComplexScheme}

/-- A genuine closed self-correspondence whose left projection is a finite
morphism of schemes. -/
structure SchemeFiniteClosedCorrespondence
    (V : SmoothProjectiveComplexScheme) where
  carrier : Scheme
  intoProduct : carrier ⟶ selfProduct V
  closedImmersion : IsClosedImmersion intoProduct
  left_isFinite : IsFinite (intoProduct ≫ fst V)

namespace SchemeFiniteClosedCorrespondence

abbrev left (K : SchemeFiniteClosedCorrespondence V) : K.carrier ⟶ V.X :=
  K.intoProduct ≫ fst V

noncomputable def toFiniteClosedCorrespondence
    (K : SchemeFiniteClosedCorrespondence V) :
    FiniteClosedCorrespondence V where
  carrier := K.carrier
  intoProduct := K.intoProduct
  closedImmersion := K.closedImmersion
  leftFiber_finite := by
    intro x
    letI : IsFinite K.left := K.left_isFinite
    have h := K.left.finite_preimage_singleton x
    change ({z : K.carrier | K.left z = x} : Set K.carrier).Finite
    have heq : ({z : K.carrier | K.left z = x} : Set K.carrier) =
        K.left ⁻¹' ({x} : Set V.X) := by
      ext z
      simp
    rw [heq]
    exact h

@[simp]
theorem toFiniteClosedCorrespondence_left
    (K : SchemeFiniteClosedCorrespondence V) :
    K.toFiniteClosedCorrespondence.left = K.left := rfl

end SchemeFiniteClosedCorrespondence

/-- A genuine closed self-correspondence finite as a scheme morphism over both
projections. -/
structure SchemeBiFiniteClosedCorrespondence
    (V : SmoothProjectiveComplexScheme)
    extends SchemeFiniteClosedCorrespondence V where
  right_isFinite :
    IsFinite (toSchemeFiniteClosedCorrespondence.intoProduct ≫ snd V)

namespace SchemeBiFiniteClosedCorrespondence

abbrev right (K : SchemeBiFiniteClosedCorrespondence V) : K.carrier ⟶ V.X :=
  K.intoProduct ≫ snd V

noncomputable def toBiFiniteClosedCorrespondence
    (K : SchemeBiFiniteClosedCorrespondence V) :
    BiFiniteClosedCorrespondence V where
  toFiniteClosedCorrespondence :=
    K.toSchemeFiniteClosedCorrespondence.toFiniteClosedCorrespondence
  rightFiber_finite := by
    intro x
    letI : IsFinite K.right := K.right_isFinite
    have h := K.right.finite_preimage_singleton x
    change ({z : K.carrier | K.right z = x} : Set K.carrier).Finite
    have heq : ({z : K.carrier | K.right z = x} : Set K.carrier) =
        K.right ⁻¹' ({x} : Set V.X) := by
      ext z
      simp
    rw [heq]
    exact h

@[simp]
theorem toBiFiniteClosedCorrespondence_left
    (K : SchemeBiFiniteClosedCorrespondence V) :
    K.toBiFiniteClosedCorrespondence.toFiniteClosedCorrespondence.left =
      K.toSchemeFiniteClosedCorrespondence.left := rfl

@[simp]
theorem toBiFiniteClosedCorrespondence_right
    (K : SchemeBiFiniteClosedCorrespondence V) :
    K.toBiFiniteClosedCorrespondence.toFiniteClosedCorrespondence.right =
      K.right := rfl

/-- Genuine factor-swap transpose preserves strict bi-finiteness. -/
noncomputable def transpose
    (K : SchemeBiFiniteClosedCorrespondence V) :
    SchemeBiFiniteClosedCorrespondence V := by
  let e := selfProductSwapIso V
  letI : IsIso e.hom := e.isIso_hom
  refine {
    carrier := K.carrier
    intoProduct := K.intoProduct ≫ e.hom
    closedImmersion := ?_
    left_isFinite := ?_
    right_isFinite := ?_
  }
  · haveI hK : IsClosedImmersion K.intoProduct := K.closedImmersion
    infer_instance
  · simpa [e, selfProductSwapIso, SchemeFiniteClosedCorrespondence.left,
      right, Category.assoc] using K.right_isFinite
  · simpa [e, selfProductSwapIso, SchemeFiniteClosedCorrespondence.left,
      right, Category.assoc] using
      K.toSchemeFiniteClosedCorrespondence.left_isFinite

@[simp]
theorem transpose_left
    (K : SchemeBiFiniteClosedCorrespondence V) :
    K.transpose.toSchemeFiniteClosedCorrespondence.left = K.right := by
  change (K.intoProduct ≫ selfProductSwap V) ≫ fst V = K.intoProduct ≫ snd V
  rw [Category.assoc, selfProductSwap_fst]

@[simp]
theorem transpose_right
    (K : SchemeBiFiniteClosedCorrespondence V) :
    K.transpose.right = K.toSchemeFiniteClosedCorrespondence.left := by
  change (K.intoProduct ≫ selfProductSwap V) ≫ snd V = K.intoProduct ≫ fst V
  rw [Category.assoc, selfProductSwap_snd]

@[simp]
theorem weak_transpose_left
    (K : SchemeBiFiniteClosedCorrespondence V) :
    K.toBiFiniteClosedCorrespondence.transpose.left = K.right := by
  rw [BiFiniteClosedCorrespondence.transpose_left]
  rfl

@[simp]
theorem weak_transpose_right
    (K : SchemeBiFiniteClosedCorrespondence V) :
    K.toBiFiniteClosedCorrespondence.transpose.right =
      K.toSchemeFiniteClosedCorrespondence.left := by
  rw [BiFiniteClosedCorrespondence.transpose_right]
  rfl

end SchemeBiFiniteClosedCorrespondence

#check SchemeFiniteClosedCorrespondence
#check SchemeFiniteClosedCorrespondence.toFiniteClosedCorrespondence
#check SchemeBiFiniteClosedCorrespondence
#check SchemeBiFiniteClosedCorrespondence.toBiFiniteClosedCorrespondence
#check SchemeBiFiniteClosedCorrespondence.transpose

#print axioms SchemeFiniteClosedCorrespondence.toFiniteClosedCorrespondence
#print axioms SchemeBiFiniteClosedCorrespondence.toBiFiniteClosedCorrespondence
#print axioms SchemeBiFiniteClosedCorrespondence.transpose

end GSTClassicalHodgeSchemeFiniteCorrespondenceFirewall
