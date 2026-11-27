import Mathlib

/-!
# GST MATHLIB FINITE BASIS ADAPTER

A small adapter isolating the only Mathlib basis API needed by the Hodge
channel architecture.

For a basis B : Module.Basis (Fin N) ℚ V we expose the ordinary coordinate
function Fin N -> ℚ and the inverse finite linear superposition.  The two
operations are inverse.  Downstream Hodge files therefore reason only with
ordinary finite channel vectors and not with Finsupp implementation details.

The implementation routes through `Module.Basis.equivFun`, Mathlib's canonical
linear equivalence between a finitely-indexed basis carrier and its ordinary
coordinate functions, so every reconstruction proof is a structure law of a
genuine linear equivalence rather than a bespoke superposition computation.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000000

noncomputable section

namespace GSTMathlibFiniteBasis

variable {V : Type*} [AddCommGroup V] [Module ℚ V]
variable {N : Nat}

/-- Ordinary finite coordinate vector of x in a Fin N-indexed basis. -/
noncomputable def basisCoordinates
    (B : Module.Basis (Fin N) ℚ V) : V →ₗ[ℚ] (Fin N → ℚ) :=
  B.equivFun.toLinearMap

/-- Decode an ordinary coordinate vector by finite basis superposition. -/
noncomputable def basisDecode
    (B : Module.Basis (Fin N) ℚ V) : (Fin N → ℚ) →ₗ[ℚ] V :=
  B.equivFun.symm.toLinearMap

/-- Decoding the coordinates of a vector reconstructs it exactly. -/
theorem basisDecode_basisCoordinates
    (B : Module.Basis (Fin N) ℚ V) (x : V) :
    basisDecode B (basisCoordinates B x) = x :=
  B.equivFun.symm_apply_apply x

/-- Consequently finite basis decoding is surjective. -/
theorem basisDecode_surjective
    (B : Module.Basis (Fin N) ℚ V) :
    Function.Surjective (basisDecode B) :=
  B.equivFun.symm.toEquiv.surjective

/-- Coordinates after decoding are exactly the original finite vector. -/
theorem basisCoordinates_basisDecode
    (B : Module.Basis (Fin N) ℚ V) (a : Fin N → ℚ) :
    basisCoordinates B (basisDecode B a) = a :=
  B.equivFun.apply_symm_apply a

/-- The i-th Kronecker coordinate vector decodes to the i-th basis vector. -/
theorem basisDecode_kronecker
    (B : Module.Basis (Fin N) ℚ V) (i : Fin N) :
    basisDecode B (fun j => if j = i then 1 else 0) = B i := by
  classical
  simp [basisDecode, Module.Basis.equivFun_symm_apply]

/-- Finite basis coordinates are a linear equivalence with ordinary channel
coordinates. -/
noncomputable def basisCoordinateEquiv
    (B : Module.Basis (Fin N) ℚ V) : V ≃ₗ[ℚ] (Fin N → ℚ) :=
  B.equivFun

/-- Adapter crown. -/
theorem finite_basis_adapter_crown
    (B : Module.Basis (Fin N) ℚ V) :
    Function.Bijective (basisCoordinates B)
      ∧ Function.Bijective (basisDecode B) :=
  ⟨(basisCoordinateEquiv B).toEquiv.bijective,
    (basisCoordinateEquiv B).symm.toEquiv.bijective⟩

#check basisCoordinates
#check basisDecode
#check basisDecode_basisCoordinates
#check basisDecode_surjective
#check basisCoordinates_basisDecode
#check basisDecode_kronecker
#check basisCoordinateEquiv
#check finite_basis_adapter_crown

#print axioms basisDecode_basisCoordinates
#print axioms basisCoordinates_basisDecode
#print axioms basisDecode_kronecker
#print axioms finite_basis_adapter_crown

end GSTMathlibFiniteBasis
