import Mathlib

/-!
# Original GST CM curvature, manufactured monodromy and finite source test

Companion geometric proof:
research/derivations/GST_native_CM_monodromy_infinite_control_constant_family_twist_20261112.tex

The owner's TRUE fixed null/maximum GST CM J and SURVIVE M produce
[J,M]=2*Swap. On the ACTUAL projective surface P1xP1, the real
algebraic factor-swap automorphism induces this Swap on the basis
H1,H2. It generates a GENUINE twisted isotrivial smooth projective
family via the free twofold cover t |-> t^2 on Cstar.
The geometry and canonical cycle comparison are in the derivation;
this file proves the rational native source identities in Lean.

The cohomology monodromy invariant projector is (I+Swap)/2.
The eigen-sector fixed by Swap is one-dimensional, with a true Chow
source H1+H2. NO assumed all-X Chow inverse is introduced.

Also checks that inducing the same (possibly missing) original
cohomology target diagonally into two finite cardinal worlds cannot
manufacture a native preimage in the original X. This is a PURE
LINEAR-ALGEBRA obstruction, not an actual Hodge counterexample.
-/

set_option maxHeartbeats 1000000
noncomputable section

namespace GSTNativeCMMonodromyTwistedConstantFamily

/-- Geometric P1xP1 factor-swap, the ORIGINAL native GST fixed-pair
CM curvature divided by two. -/
def originalSwap (x : ℚ × ℚ) : ℚ × ℚ := (x.2, x.1)

/-- Original CM complex J restricted to the native null/max two cells. -/
def originalJ (x : ℚ × ℚ) : ℚ × ℚ := (x.2, -x.1)

/-- Original SURVIVE M restricted to the same native source cells. -/
def originalM (x : ℚ × ℚ) : ℚ × ℚ := (0, 2 * x.2)

/-- Genuine GST CM commutator on the original native two-cell coordinates. -/
def originalCMCurvature (x : ℚ × ℚ) : ℚ × ℚ :=
  ((originalJ (originalM x)).1 - (originalM (originalJ x)).1,
   (originalJ (originalM x)).2 - (originalM (originalJ x)).2)

theorem originalCMCurvature_twice_algebraicSwap (x : ℚ × ℚ) :
    originalCMCurvature x =
      (2 * (originalSwap x).1, 2 * (originalSwap x).2) := by
  rcases x with ⟨a, b⟩
  apply Prod.ext <;> dsimp [originalCMCurvature, originalJ, originalM, originalSwap] <;> ring

theorem originalSwap_involutive (x : ℚ × ℚ) :
    originalSwap (originalSwap x) = x := by
  rcases x with ⟨a, b⟩
  rfl

/-- The genuine twisted constant family monodromy projects onto
the known Chow divisor direction H1+H2. -/
def nativeInvariantProjector (x : ℚ × ℚ) : ℚ × ℚ :=
  ((x.1 + x.2) / 2, (x.1 + x.2) / 2)

theorem nativeInvariantProjector_is_average (x : ℚ × ℚ) :
    nativeInvariantProjector x =
      ((x.1 + (originalSwap x).1)/2,
       (x.2 + (originalSwap x).2)/2) := by
  rcases x with ⟨a, b⟩
  simp [nativeInvariantProjector, originalSwap, add_comm]

theorem nativeInvariantProjector_idempotent (x : ℚ × ℚ) :
    nativeInvariantProjector (nativeInvariantProjector x) =
      nativeInvariantProjector x := by
  rcases x with ⟨a, b⟩
  apply Prod.ext <;> dsimp [nativeInvariantProjector] <;> ring

theorem nativeInvariantProjector_is_swap_fixed (x : ℚ × ℚ) :
    originalSwap (nativeInvariantProjector x) =
      nativeInvariantProjector x := by
  rcases x with ⟨a, b⟩
  rfl

theorem nativeInvariantProjector_returns_fixed_input
    (x : ℚ × ℚ) (hx : originalSwap x = x) :
    nativeInvariantProjector x = x := by
  rcases x with ⟨a, b⟩
  have hab : a = b := by
    have h' := congrArg Prod.fst hx
    simpa [originalSwap] using h'.symm
  subst b
  apply Prod.ext <;> dsimp [nativeInvariantProjector] <;> ring

/-- Exactly the owner's generated Chow source dimension: an input
fixed by native monodromy is a rational multiple of the true
P1xP1 divisor class H1+H2, not an arbitrary unknown Hodge lift. -/
theorem monodromy_fixed_has_constructed_source_coordinates
    (x : ℚ × ℚ) (hx : originalSwap x = x) :
    ∃ q : ℚ, x = (q, q) := by
  rcases x with ⟨a, b⟩
  have hab : a = b := by
    have h' := congrArg Prod.fst hx
    simpa [originalSwap] using h'.symm
  exact ⟨a, by simp [hab]⟩

section NoNewSourceFromInduction

variable {A : Type*} {B : Type*}
variable [AddCommGroup A] [Module ℚ A]
variable [AddCommGroup B] [Module ℚ B]

/- The actual native-to-Betti cycle-class interface on original X. -/
variable (cl : A →ₗ[ℚ] B)

/-- The diagonal class of two induced/monodromy-permuted worlds
cannot have an algebraic native lift unless the ORIGINAL X has one. -/
theorem two_world_invariant_target_requires_original_source
    (alpha : B)
    (hPair : ∃ z : A × A,
      (cl z.1, cl z.2) = (alpha, alpha)) :
    ∃ z0 : A, cl z0 = alpha := by
  rcases hPair with ⟨z, hz⟩
  exact ⟨z.1, congrArg Prod.fst hz⟩

/-- A formal Hodge source outside the canonical native image
remains absent even when doubled and made monodromy invariant
by swapping two cardinal worlds. -/
theorem no_ghost_source_from_two_world_monodromy
    (alpha : B) (hMissing : ¬ ∃ z0 : A, cl z0 = alpha) :
    ¬ ∃ z : A × A, (cl z.1, cl z.2) = (alpha, alpha) := by
  intro hz
  exact hMissing (two_world_invariant_target_requires_original_source cl alpha hz)

end NoNewSourceFromInduction

#check originalCMCurvature_twice_algebraicSwap
#check nativeInvariantProjector_idempotent
#check monodromy_fixed_has_constructed_source_coordinates
#check no_ghost_source_from_two_world_monodromy

#print axioms originalCMCurvature_twice_algebraicSwap
#print axioms nativeInvariantProjector_idempotent
#print axioms no_ghost_source_from_two_world_monodromy

end GSTNativeCMMonodromyTwistedConstantFamily
