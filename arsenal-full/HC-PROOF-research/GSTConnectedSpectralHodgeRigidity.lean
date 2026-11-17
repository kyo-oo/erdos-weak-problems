import Mathlib

/-!
# Connected-cover anti-divisor rigidity: the positivity core

Uncompiled proof draft. The geometric theorem is proved in the hand derivation.
Here degree is ONE scalar, as on a connected smooth projective cover. For a
split cover, taking a total degree does not provide the required definiteness.
Actual Chow and Betti classes are distinct; this file asserts no Picard triviality.
-/

namespace GSTConnectedSpectralHodgeRigidity
variable {V : Type*} [AddCommGroup V] [Module ℚ V]

theorem anti_invariant_has_degree_zero (degree : V →ₗ[ℚ] ℚ)
    (deck : Module.End ℚ V) (hdegree : ∀ v,degree (deck v)=degree v)
    (v : V) (hanti : deck v = -v) : degree v=0 := by
  have h := hdegree v
  rw [hanti,map_neg] at h
  linarith

theorem primitive_isotropic_zero (degree : V →ₗ[ℚ] ℚ)
    (energy : V → ℚ)
    (hpositive : ∀ v,degree v=0 → v≠0 → 0<energy v)
    (v : V) (hdegree : degree v=0) (hisotropic : energy v=0) : v=0 := by
  by_contra hne
  have h := hpositive v hdegree hne
  rw [hisotropic] at h
  exact (lt_irrefl 0) h

/-- In geometry energy(v)=-integral(v² h^(d-2)); Hodge index supplies positivity. -/
theorem connected_anti_isotropic_zero (degree : V →ₗ[ℚ] ℚ)
    (deck : Module.End ℚ V) (hdegree : ∀ v,degree (deck v)=degree v)
    (energy : V → ℚ)
    (hpositive : ∀ v,degree v=0 → v≠0 → 0<energy v)
    (v : V) (hanti : deck v = -v) (hisotropic : energy v=0) : v=0 := by
  exact primitive_isotropic_zero degree energy hpositive v
    (anti_invariant_has_degree_zero degree deck hdegree v hanti) hisotropic

/-- Tensor readout also vanishes once one genuine Betti factor is zero. -/
theorem mixed_readout_zero {W : Type*} [AddCommGroup W] [Module ℚ W]
    (degree : V →ₗ[ℚ] ℚ) (deck : Module.End ℚ V)
    (hdegree : ∀ v,degree (deck v)=degree v) (energy : V → ℚ)
    (hpositive : ∀ v,degree v=0 → v≠0 → 0<energy v)
    (v : V) (hanti : deck v = -v) (hisotropic : energy v=0)
    (multiplyByOtherFactors : V →ₗ[ℚ] W) : multiplyByOtherFactors v=0 := by
  rw [connected_anti_isotropic_zero degree deck hdegree energy hpositive v hanti hisotropic,
    map_zero]

#print axioms connected_anti_isotropic_zero
#print axioms mixed_readout_zero
end GSTConnectedSpectralHodgeRigidity
