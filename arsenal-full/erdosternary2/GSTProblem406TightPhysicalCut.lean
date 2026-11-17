import GSTProblem406BinaryOriginExponentScale
import GSTFourPowerDirectResidue
import GSTFourPowerDirectExistence
import Mathlib

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
# GST direct physical-origin tighter 24/19 scale

19-step origin growth uses literal integer inequality
4^19=274877906944 < 282429536481=3^24.
For every physical source K>=13, the complete ternary
word lies below ceil(24*K/19), uniformly tighter than
the previous floor((4*K-1)/3) for many K.

This changes the quantitative dual-radix exclusion
target, but it does NOT assume or prove CommonTwo.
-/

namespace GSTProblem406TightPhysicalCut

open GSTProblem406BinaryOriginExponentScale
open GSTFourPowerDirectResidue

/-- Pure rational upper envelope ceil(24K/19). -/
def tighterPhysicalCut (K : Nat) : Nat := (24*K+18)/19

private theorem nineteen_origin_step :
    (4:Nat)^19 < 3^24 := by decide

/-- Strict physical Archimedean bound at every exponent K>=13. -/
theorem physical_source_lt_tighter_cut (K : Nat) (hK : 13 ≤ K) :
    (4:Nat)^K < 3^(tighterPhysicalCut K) := by
  induction K using Nat.strongRecOn with
  | ind K ih =>
    by_cases hsmall : K < 32
    · interval_cases K <;> norm_num [tighterPhysicalCut] at *
    · have hprev : 13 ≤ K-19 := by omega
      have ih' := ih (K-19) (by omega) hprev
      have hcut : tighterPhysicalCut K =
          tighterPhysicalCut (K-19)+24 := by
        unfold tighterPhysicalCut
        omega
      have hpow : (4:Nat)^K = 4^(K-19)*4^19 := by
        conv_lhs => rw [show K = (K-19)+19 by omega]
        rw [pow_add]
      calc
        4^K = 4^(K-19)*4^19 := hpow
        _ < 3^(tighterPhysicalCut (K-19))*4^19 :=
          Nat.mul_lt_mul_of_pos_right ih' (by decide)
        _ < 3^(tighterPhysicalCut (K-19))*3^24 :=
          Nat.mul_lt_mul_of_pos_left nineteen_origin_step (by positivity)
        _ = 3^(tighterPhysicalCut K) := by rw [hcut, pow_add]

/-- The new cut is never above the old physical four-thirds cut. -/
theorem tighter_cut_le_old_cut (K : Nat) (hK : 13 ≤ K) :
    tighterPhysicalCut K ≤ physicalShortCut K := by
  by_cases hBig : 28 ≤ K
  · unfold tighterPhysicalCut physicalShortCut
    omega
  · have hKsmall : K ≤ 27 := by omega
    interval_cases K <;> norm_num [tighterPhysicalCut,physicalShortCut] at *

/-- The improved cutoff retains the exact high 2-adic order of 4^K. -/
theorem tighter_cut_high_binary_order (K : Nat) (hK : 13 ≤ K) :
    (2:Nat)^((3*tighterPhysicalCut K)/2+1) ∣ 4^K := by
  have hle : (3*tighterPhysicalCut K)/2+1 ≤ 2*K := by
    by_cases hBig : 28 ≤ K
    · unfold tighterPhysicalCut
      omega
    · have hKsmall : K ≤ 27 := by omega
      interval_cases K <;> norm_num [tighterPhysicalCut] at *
  have hdiv : (2:Nat)^((3*tighterPhysicalCut K)/2+1) ∣
      (2:Nat)^(2*K) := pow_dvd_pow 2 hle
  simpa only [show (4:Nat)=2^2 by decide, pow_mul] using hdiv

/-- Every source digit at or beyond the new terminal cut is zero. -/
theorem digit_zero_above_tighter_cut (K p : Nat)
    (hK : 13 ≤ K) (hp : tighterPhysicalCut K ≤ p) :
    digit3 (4^K) p=0 := by
  have hpow : (3:Nat)^(tighterPhysicalCut K) ≤ 3^p :=
    Nat.pow_le_pow_of_le (by decide : 1 < (3:Nat)) hp
  have hlt : (4:Nat)^K < 3^p :=
    lt_of_lt_of_le (physical_source_lt_tighter_cut K hK) hpow
  unfold digit3
  rw [Nat.div_eq_of_lt hlt]

/-- The original quantified CommonTwo is exactly a witness below
the tighter cutoff. This is an iff, not existence of a witness. -/
theorem original_commonTwo_iff_tighter_cut (K : Nat)
    (hK : 13 ≤ K) :
    GSTFourPowerDirectExistence.CommonTwo K ↔
      ∃ p : Nat, 1 ≤ p ∧ p < tighterPhysicalCut K ∧
        digit3 (4^K) p=2 ∧ digit3 (4^(K+1)) p=2 := by
  constructor
  · rintro ⟨p,hp,hs,hn⟩
    have hcut : p < tighterPhysicalCut K := by
      by_contra hncut
      have hz := digit_zero_above_tighter_cut K p hK (by omega)
      omega
    exact ⟨p,hp,hcut,hs,hn⟩
  · rintro ⟨p,hp,_,hs,hn⟩
    exact ⟨p,hp,hs,hn⟩

#print axioms physical_source_lt_tighter_cut
#print axioms tighter_cut_le_old_cut
#print axioms tighter_cut_high_binary_order
#print axioms digit_zero_above_tighter_cut
#print axioms original_commonTwo_iff_tighter_cut

/-- Stronger than the old binary threshold by a margin that grows
linearly with K: exact 24/19 physical scale certifies 19*t <=36*K+46,
where t=floor(3*L/2)+1. -/
theorem tighter_binary_threshold_linear (K : Nat) :
    19*((3*tighterPhysicalCut K)/2+1) ≤ 36*K+46 := by
  unfold tighterPhysicalCut
  omega

/-- Every true physical source K>=13 has a 2-adic valuation margin
delta=2K-(floor(3L/2)+1) that grows at least proportionally to K:
2K <= 19*delta+46. The source value remains EXACTLY 4^K; this
does not assert a universal BAD-exclusion theorem. -/
theorem physical_origin_binary_gap_linear (K : Nat) (hK : 13 ≤ K) :
    2*K ≤ 19*(2*K-((3*tighterPhysicalCut K)/2+1))+46 := by
  have hbound := tighter_binary_threshold_linear K
  have hle : (3*tighterPhysicalCut K)/2+1 ≤ 2*K := by
    by_cases hBig : 28 ≤ K
    · unfold tighterPhysicalCut
      omega
    · have hKsmall : K ≤ 27 := by omega
      interval_cases K <;> norm_num [tighterPhysicalCut] at *
  omega

#print axioms tighter_binary_threshold_linear
#print axioms physical_origin_binary_gap_linear

end GSTProblem406TightPhysicalCut
