import GSTFourPowerAffineChannelAutomaton
import Mathlib

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
# GST 406: precise no-go for generic cubic BAD branch descent

The historical unmerged module GSTFourPowerUniversalInduction.lean
defines the triple BranchBadDescent over the actual
`affineOrbit q` and `renormOrbit q`, and gives a correct
CONDITIONAL induction. These generic-X statements are STRONGER:
they replace the actual orbit source X=(4^q-1)/3 with any X
and the actual renormalized source with the same polynomial
P(X)=X+3X^2+3X^3.

ALL THREE generic implications are false, with exact countermodels:
 X=52: P=429988;  BadChannel 0 P;       NOT BadChannel 1 X
 X=53: P=455111;  BadChannel 1 (4*P);   NOT BadChannel 1 X
 X=44: P=261404;  BadChannel 3 (16*P+1); NOT BadChannel 1 X.

Every BAD assertion quantifies over ALL ternary positions.
Finite exact Fin16 verification covers p<16; p>=16 has
source digit zero since each source is below 3^16.
This does NOT refute source-specific BranchBadDescent(q),
nor the original Erdős 406 theorem.
-/

namespace GSTProblem406CubicBranchCountermodels

open GSTFourPowerDirectResidue
open GSTFourPowerAffineBadState
open GSTFourPowerAffineChannelAutomaton

def cubicPeel (X : Nat) : Nat := X + 3*X^2 + 3*X^3

/-- Complete proof from a finite prefix and an exact source bound,
without any extrapolation from a truncated check. -/
private theorem bad_channel_of_finite_source
    (c x L : Nat) (hx : x < 3^L)
    (hfinite : ∀ p : Fin L,
      ¬ (digit3 x p.val=2 ∧ digit3 (4*x+c) p.val=2)) :
    BadChannel c x := by
  intro hgood
  rcases hgood with ⟨p,hsrc,htgt⟩
  by_cases hp : p < L
  · exact hfinite ⟨p,hp⟩ ⟨hsrc,htgt⟩
  · have hpow : 3^L ≤ 3^p :=
      Nat.pow_le_pow_of_le (by decide : 1 < (3:Nat)) (by omega)
    have hsmall : x < 3^p := lt_of_lt_of_le hx hpow
    have hz : digit3 x p=0 := by
      unfold digit3
      rw [Nat.div_eq_of_lt hsmall]
    omega

private theorem generic_zero_source_bad :
    BadChannel 0 (cubicPeel 52) := by
  apply bad_channel_of_finite_source 0 (cubicPeel 52) 16
  · decide
  · decide

private theorem generic_one_source_bad :
    BadChannel 1 (4*cubicPeel 53) := by
  apply bad_channel_of_finite_source 1 (4*cubicPeel 53) 16
  · decide
  · decide

private theorem generic_three_source_bad :
    BadChannel 3 (16*cubicPeel 44+1) := by
  apply bad_channel_of_finite_source 3 (16*cubicPeel 44+1) 16
  · decide
  · decide

/-- The parent true physical affine channel is GOOD at the
respective exact finite countermodel X's. -/
theorem three_good_affine_parent_channels :
    ¬ BadChannel 1 52 ∧
    ¬ BadChannel 1 53 ∧
    ¬ BadChannel 1 44 := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    apply h
    refine ⟨2, ?_, ?_⟩ <;> norm_num [digit3]
  · intro h
    apply h
    refine ⟨1, ?_, ?_⟩ <;> norm_num [digit3]
  · intro h
    apply h
    refine ⟨1, ?_, ?_⟩ <;> norm_num [digit3]

/-- ALL three unrestricted cubic BAD-to-parent branch implications
are FALSE. The exact source-origin restriction cannot be removed. -/
theorem no_generic_cubic_branch_bad_descent :
    (¬ (∀ X : Nat,
      BadChannel 0 (cubicPeel X) → BadChannel 1 X)) ∧
    (¬ (∀ X : Nat,
      BadChannel 1 (4*cubicPeel X) → BadChannel 1 X)) ∧
    (¬ (∀ X : Nat,
      BadChannel 3 (16*cubicPeel X+1) → BadChannel 1 X)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    exact three_good_affine_parent_channels.1
      (h 52 generic_zero_source_bad)
  · intro h
    exact three_good_affine_parent_channels.2.1
      (h 53 generic_one_source_bad)
  · intro h
    exact three_good_affine_parent_channels.2.2
      (h 44 generic_three_source_bad)

/-- The exact integer source values and the global-size cut used to
ensure that our counterexamples really cover every ternary row. -/
theorem cubic_branch_countermodel_fingerprints :
    cubicPeel 52 = 429988 ∧
    cubicPeel 53 = 455111 ∧
    cubicPeel 44 = 261404 ∧
    16*cubicPeel 44+1 < 3^16 := by
  decide

#print axioms three_good_affine_parent_channels
#print axioms no_generic_cubic_branch_bad_descent
#print axioms cubic_branch_countermodel_fingerprints

end GSTProblem406CubicBranchCountermodels
