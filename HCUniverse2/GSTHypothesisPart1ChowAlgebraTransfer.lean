import Mathlib

/-!
# GST Hypothesis Part 1: typed native/Betti algebraic-fold transfer

This formally checks the cycle-class *algebra* used in the user's
"HYPOTHESIS PROOF, PART 1.pdf":
  Z := Z0 + N Z0,
  cl (N Z) = T (cl Z),
  cl (N^n Z0) = T^n (cl Z0),
  commutator of two genuine geometric actions transports to its Betti side.

The paper independently constructs the actual ORIGINAL-X Chow correspondence
Gamma = diagonal + exterior ample-source projector and proves its canonical
intersection-theoretic naturality. This Lean module proves the linear-algebra
transfer step assuming that genuine geometric naturality. It does NOT assume
or prove all rational Hodge classes algebraic, a cyclic Hodge basis, the
existence of the original GST U+J+M geometric realization, or a new axiom.
-/

set_option maxHeartbeats 2000000
noncomputable section

namespace GSTHypothesisPart1ChowAlgebraTransfer

variable {A B : Type*}
variable [AddCommGroup A] [Module ℚ A]
variable [AddCommGroup B] [Module ℚ B]

/-- The rank-one algebraic source operator: on original X this is the
genuine Chow action of pr1*(h^(d-p)) pr2*(h^p)/int_X h^d. -/
def nativeRankOne (readout : A →ₗ[ℚ] ℚ) (seed : A) :
    Module.End ℚ A where
  toFun z := readout z • seed
  map_add' := by
    intro x y
    simp [map_add, add_smul]
  map_smul' := by
    intro q z
    simp [map_smul, smul_smul]

/-- The source fold: diagonal identity plus a genuine rank-one
native algebraic source projector in its original-X instantiation. -/
def nativeFold (readout : A →ₗ[ℚ] ℚ) (seed : A) :
    Module.End ℚ A :=
  LinearMap.id + nativeRankOne readout seed

/-- Source normalization makes the rank-one action an idempotent. -/
theorem rankOne_idempotent
    (readout : A →ₗ[ℚ] ℚ) (seed z : A)
    (hnorm : readout seed = 1) :
    nativeRankOne readout seed (nativeRankOne readout seed z) =
      nativeRankOne readout seed z := by
  change (readout (readout z • seed)) • seed = readout z • seed
  rw [map_smul, hnorm]
  simp

/-- The non-circular typed commuting square is supplied by the true
canonical geometric equality between native intersection-degree readout
and the rational Betti cup/integration readout. -/
theorem rankOne_class_natural
    (cl : A →ₗ[ℚ] B)
    (readoutA : A →ₗ[ℚ] ℚ)
    (readoutB : B →ₗ[ℚ] ℚ)
    (seed : A)
    (hreadout : ∀ z, readoutA z = readoutB (cl z))
    (z : A) :
    cl (nativeRankOne readoutA seed z) =
      nativeRankOne readoutB (cl seed) (cl z) := by
  change cl (readoutA z • seed) =
    readoutB (cl z) • cl seed
  rw [map_smul, hreadout]

/-- Exact native-Betti commuting square for the ORIGINAL-X geometric
Chow projector plus the diagonal, without assumed Hodge surjectivity. -/
theorem fold_class_natural
    (cl : A →ₗ[ℚ] B)
    (readoutA : A →ₗ[ℚ] ℚ)
    (readoutB : B →ₗ[ℚ] ℚ)
    (seed : A)
    (hreadout : ∀ z, readoutA z = readoutB (cl z))
    (z : A) :
    cl (nativeFold readoutA seed z) =
      nativeFold readoutB (cl seed) (cl z) := by
  change cl (z + readoutA z • seed) =
    cl z + readoutB (cl z) • cl seed
  rw [map_add, map_smul, hreadout]

/-- Abstract iteration of a genuine native operator, with n=0 the
original algebraic seed, not zero. -/
def sourceOrbit (N : Module.End ℚ A) (z : A) : ℕ → A
  | 0 => z
  | n + 1 => N (sourceOrbit N z n)

/-- The user's universal natural-number transport after the basic
geometric cycle-class square has been independently proved. -/
theorem orbit_class_natural
    (cl : A →ₗ[ℚ] B)
    (N : Module.End ℚ A)
    (T : Module.End ℚ B)
    (hcompat : ∀ z : A, cl (N z) = T (cl z))
    (z : A) :
    ∀ n : ℕ,
      cl (sourceOrbit N z n) = sourceOrbit T (cl z) n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      change cl (N (sourceOrbit N z n)) =
        T (sourceOrbit T (cl z) n)
      rw [hcompat, ih]

/-- Exact corrected interpretation of the user's proposed
Z = Z0 + N(Z0), without using that recursion circularly to
derive the geometric commuting square itself. -/
theorem proposed_double_source_class
    (cl : A →ₗ[ℚ] B)
    (N : Module.End ℚ A)
    (T : Module.End ℚ B)
    (hcompat : ∀ z : A, cl (N z) = T (cl z))
    (z0 : A) :
    cl (N (z0 + N z0)) =
      T (cl z0) + T (T (cl z0)) := by
  calc
    cl (N (z0 + N z0)) = T (cl (z0 + N z0)) := hcompat _
    _ = T (cl z0 + cl (N z0)) := by rw [map_add]
    _ = T (cl z0 + T (cl z0)) := by rw [hcompat]
    _ = T (cl z0) + T (T (cl z0)) := by rw [map_add]

/-- Genuine algebraic curvature commutators preserve the canonical
native-to-Betti square when each constituent action does. -/
theorem commutator_class_natural
    (cl : A →ₗ[ℚ] B)
    (N₁ N₂ : Module.End ℚ A)
    (T₁ T₂ : Module.End ℚ B)
    (h₁ : ∀ z : A, cl (N₁ z) = T₁ (cl z))
    (h₂ : ∀ z : A, cl (N₂ z) = T₂ (cl z))
    (z : A) :
    cl ((N₁.comp N₂ - N₂.comp N₁) z) =
      (T₁.comp T₂ - T₂.comp T₁) (cl z) := by
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, map_sub]
  rw [h₁ (N₂ z), h₂ z, h₂ (N₁ z), h₁ z]

#check rankOne_idempotent
#check rankOne_class_natural
#check fold_class_natural
#check orbit_class_natural
#check proposed_double_source_class
#check commutator_class_natural

#print axioms rankOne_idempotent
#print axioms fold_class_natural
#print axioms orbit_class_natural
#print axioms proposed_double_source_class
#print axioms commutator_class_natural

end GSTHypothesisPart1ChowAlgebraTransfer
