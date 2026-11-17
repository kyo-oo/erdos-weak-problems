import Mathlib

/-!
# GST full-N wave: a cyclic original seed destroys the commutant

The separate full-N GST derivation proves a nonzero exact Krylov
determinant for the ORIGINAL Wave-I U+J+SURVIVE operator in any
positive number of independent Wave-II holes.

This file proves the geometry-independent, arbitrary-rational-module
algebra theorem needed to turn that cyclic signal and its original
rank-one source coupling into a *scalar commutant*.

A SOURCE VECTOR is supplied; no basis of algebraic Hodge classes,
Hodge-to-Chow inverse, canonical X-realization, or source surjectivity
hypothesis is introduced. The theorem is only about the commutant
of an actually cyclic vector and the source-rank-one operator.
The separate original-X Chow source projector is proven in the
LaTeX derivation. No claim of unconditional Hodge algebraicity.
-/

set_option maxHeartbeats 1500000

noncomputable section

namespace GSTFullWaveCyclicSourceCommutant

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

def sourceOrbit (T : Module.End ℚ V) (seed : V) : ℕ → V
  | 0 => seed
  | n + 1 => T (sourceOrbit T seed n)

/-- The complete rational GST source-orbit hypothesis on an abstract
rational module; for the full N-wave information carrier it follows
from the explicit original twelve-cell CRT determinant. -/
def IsSourceCyclic (T : Module.End ℚ V) (seed : V) : Prop :=
  Submodule.span ℚ (Set.range (sourceOrbit T seed)) = ⊤

/-- An ORIGINAL source-rank-one operator with a chosen native rational
readout. For the full-N information realization it is the uniform
source vector times its transpose. -/
def sourceRankOne (readout : V →ₗ[ℚ] ℚ) (seed : V) :
    Module.End ℚ V where
  toFun x := (readout x) • seed
  map_add' := by
    intro x y
    simp [map_add, add_smul]
  map_smul' := by
    intro q x
    simp [map_smul, smul_smul]

@[simp]
theorem sourceRankOne_apply
    (readout : V →ₗ[ℚ] ℚ) (seed x : V) :
    sourceRankOne readout seed x = (readout x) • seed := rfl

/-- GST source-commutant theorem: no non-scalar rational operation can
commute with BOTH a cyclic GST fold and a nondegenerate rank-one
operator built from its original source. This is stronger than
the previously failed scalar-common-commutant shortcut because
the needed cyclic orbit is proved independently on the full
native information carrier by the CRT theorem. -/
theorem scalar_commutant_of_source_cyclic
    (T S : Module.End ℚ V)
    (seed : V) (readout : V →ₗ[ℚ] ℚ)
    (hseed : readout seed ≠ 0)
    (hcyclic : IsSourceCyclic T seed)
    (hTS : ∀ x : V, S (T x) = T (S x))
    (hSP : ∀ x : V,
      S (sourceRankOne readout seed x) =
        sourceRankOne readout seed (S x)) :
    ∃ c : ℚ, ∀ x : V, S x = c • x := by
  let c : ℚ := (readout (S seed)) / (readout seed)
  have hscaled :
      (readout seed) • S seed =
        (readout (S seed)) • seed := by
    simpa [sourceRankOne, map_smul] using hSP seed
  have hseedS : S seed = c • seed := by
    have h := congrArg (fun z : V => (readout seed)⁻¹ • z) hscaled
    simpa [c, smul_smul, inv_mul_cancel₀ hseed,
      div_eq_mul_inv, mul_comm] using h
  have horbit :
      ∀ n : ℕ, S (sourceOrbit T seed n) =
        c • sourceOrbit T seed n := by
    intro n
    induction n with
    | zero =>
        simpa [sourceOrbit] using hseedS
    | succ n ih =>
        change
          S (T (sourceOrbit T seed n)) =
            c • T (sourceOrbit T seed n)
        rw [hTS, ih, map_smul]
  let R : Module.End ℚ V := S - c • LinearMap.id
  have hset :
      Set.range (sourceOrbit T seed) ⊆ LinearMap.ker R := by
    rintro x ⟨n, rfl⟩
    change R (sourceOrbit T seed n) = 0
    simp [R, horbit n]
  have hspan :
      Submodule.span ℚ (Set.range (sourceOrbit T seed)) ≤
        LinearMap.ker R :=
    Submodule.span_le.mpr hset
  refine ⟨c, ?_⟩
  intro x
  have hx : x ∈ LinearMap.ker R := by
    apply hspan
    rw [hcyclic]
    trivial
  change R x = 0 at hx
  have hdiff : S x - c • x = 0 := by
    simpa [R] using hx
  exact sub_eq_zero.mp hdiff

#check sourceOrbit
#check IsSourceCyclic
#check sourceRankOne_apply
#check scalar_commutant_of_source_cyclic
#print axioms scalar_commutant_of_source_cyclic

end GSTFullWaveCyclicSourceCommutant
