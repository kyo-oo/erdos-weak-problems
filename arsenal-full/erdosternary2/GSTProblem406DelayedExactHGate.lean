import GSTProblem406HGateCoreClass
import GSTOmegaThreeTritMultiplierLaw
import GSTFourPowerThirdWave

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
# Exact arbitrarily delayed FIRST simultaneous GST source-neighbor gate

Existing GST Worldtrace work proved an arbitrarily late FIRST SOURCE
two for normalized multiplier u=2 mod3. A genuine source-neighbor
statement requires proving that 4^(K+1) also carries two at THAT
SAME row; here it is derived directly from the exact one-trit physical
Worldtrace block law. This proves first CommonTwo time = L+1.

Thus there can be no universal constant prefix-scan bound for the
unconditional hGate goal: every finite horizon is missed by some
true original physical perfect-power pair, even though the pair
eventually has its exact first common two. This is a genuine,
noncircular infinite-range geometric constraint on proof search.
-/

namespace GSTProblem406DelayedExactHGate

open GSTFourPowerDirectResidue
open GSTFourPowerDirectExistence

/-- Full physical neighbor wave at precisely the source's first
postcut row, uniformly in every L>=6 and 3-free multiplier u=2 mod3. -/
theorem neighbor_fires_first_cut
    (L u : Nat) (hL : 6 ≤ L) (hu : u%3=2) :
    digit3 (4^(5+u*3^L)) (L+1)=2 := by
  have h :=
    (GSTProblem406HGateCoreClass.two_wave_any_width_block_exact
      L u 1 hL (by decide) (by omega)).2
  have hmod : (u*GSTCanonicalTailLTE.lteCoeff L*1024)%3=2 := by
    have h1 :
        (u*GSTCanonicalTailLTE.lteCoeff L*1024)%3 =
        (((u*GSTCanonicalTailLTE.lteCoeff L)%3)*(1024%3))%3 :=
      Nat.mul_mod _ _ _
    have h2 :
        (u*GSTCanonicalTailLTE.lteCoeff L)%3 =
        ((u%3)*(GSTCanonicalTailLTE.lteCoeff L%3))%3 :=
      Nat.mul_mod _ _ _
    calc
      (u*GSTCanonicalTailLTE.lteCoeff L*1024)%3 =
        (((u*GSTCanonicalTailLTE.lteCoeff L)%3)*(1024%3))%3 := h1
      _ = (((u%3)*(GSTCanonicalTailLTE.lteCoeff L%3))%3*(1024%3))%3 := by
        rw [h2]
      _ = 2 := by
        rw [hu, GSTCanonicalTailLTE.lteCoeff_mod3_one]
  change (4^(5+u*3^L)/3^(L+1))%3=2
  simpa only [show (3:Nat)^1=3 by decide] using h.trans hmod

/-- The first SAME-ROW two for the exact consecutive powers occurs
at row L+1. Earlier rows have no source two at all, while both
physical powers have two at row L+1. -/
theorem first_same_row_two_at_delayed_cut
    (L u : Nat) (hL : 6 ≤ L) (hu : u%3=2) :
    digit3 (4^(4+u*3^L)) (L+1)=2 ∧
    digit3 (4^((4+u*3^L)+1)) (L+1)=2 ∧
    ∀ p : Nat, p < L+1 →
      ¬ (digit3 (4^(4+u*3^L)) p=2 ∧
         digit3 (4^((4+u*3^L)+1)) p=2) := by
  obtain ⟨hs,hfirst⟩ :=
    GSTOmegaThreeTritMultiplierLaw.first_two_for_two_mod_three_multiplier
      L u (by omega) hu
  refine ⟨hs, ?_, ?_⟩
  · have he : (4+u*3^L)+1=5+u*3^L := by omega
    rw [he]
    exact neighbor_fires_first_cut L u hL hu
  · intro p hp hpair
    exact hfirst p hp hpair.1

/-- Every prescribed prefix horizon B is defeated by a *true*
physical pair whose first common-two gate occurs strictly beyond B.
The source and neighbor agree at that first delayed gate. -/
theorem arbitrarily_delayed_first_original_hGate
    (B : Nat) :
    ∃ K p : Nat, 5 ≤ K ∧ B < p ∧
      digit3 (4^K) p=2 ∧ digit3 (4^(K+1)) p=2 ∧
      (∀ j : Nat, j < p →
         ¬ (digit3 (4^K) j=2 ∧ digit3 (4^(K+1)) j=2)) := by
  let L := B+6
  let K := 4+2*3^L
  have hL : 6 ≤ L := by dsimp [L]; omega
  have hfire :=
    first_same_row_two_at_delayed_cut L 2 hL (by decide)
  refine ⟨K,L+1, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [K]
    have hp : 1 ≤ 3^L := by
      have hpos : 0 < 3^L := pow_pos (by decide : 0 < (3:Nat)) _
      omega
    omega
  · dsimp [L]; omega
  · simpa [K] using hfire.1
  · simpa [K] using hfire.2.1
  · intro j hj hbad
    exact hfire.2.2 j hj (by simpa [K] using hbad)

#print axioms neighbor_fires_first_cut
#print axioms first_same_row_two_at_delayed_cut
#print axioms arbitrarily_delayed_first_original_hGate

end GSTProblem406DelayedExactHGate
