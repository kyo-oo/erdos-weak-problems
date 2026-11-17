import GSTFourPowerDirectExistence
import GSTFourPowerExponentTritObstruction

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
# The Third Wave: band reformulation of the four-power direct existence law

This file is the Lean core of the third-wave analysis produced by the
six-agent strike on the legacy production boundary
`gst_four_power_direct_existence_inline`.

## The reformulation

For every row `p`, write `b := 4^K % 3^p` for the prefix of `4^K` below
row `p`.  Multiplication by four acts on row `p` by the carry law

    digit3 (4 * R) p = (4 * digit3 R p + c) % 3,   c := 4 * (R % 3^p) / 3^p ≤ 3,

so a row-`p` digit two of `4^K` survives the passage to `4^(K+1)` exactly
when the prefix `b` lies in the outer quarter bands

    prefixBand K p :=  4 * b < 3^p   ∨   3 * 3^p ≤ 4 * b.

Consequently the direct existence law is *equivalent* to the statement that
every exponent `K ≥ 5`, `K ≠ 7`, has some row `p ≥ 1` whose row digit is
two while its prefix lies in the outer quarter band — the gate predicate of
the third wave.  This file proves that equivalence unconditionally, with
no unproven assertion of any kind.

## Research record of the strike (not discharged here)

The six-agent strike established, outside this file:

* the exponent trie `K mod 3^p ↦ 4^K mod 3^(p+1)` is a bijection onto the
  principal units (the residue files carry the exact period law
  `pow4_digit_period` and the LTE identity `pow4_three_power_lte_exact`);
* at each trie level the new row digit can be steered freely by the
  exponent trit (`pow4_exponent_trit_lift_digit`), so the gate structure is
  a self-similar walk on the prefix value;
* the set of exponent classes dodging every gate grows geometrically at
  rate ≈ 2.48 per level against 3 per level of the trie, and the measured
  exception set is exactly `{0, 1, 2, 3, 4, 7}`.

Closing the final step — that no natural exponent `K ≥ 8` follows a
gate-dodging walk forever — is the open boundary that the legacy
declaration was holding.  It is deliberately NOT asserted here.
-/

namespace GSTFourPowerThirdWave

open GSTFourPowerDirectResidue
open GSTFourPowerDirectExistence
open GSTFourPowerExponentTritObstruction

/-- Outer quarter-band condition on the row-`p` prefix of `4^K`:
the value of `4^K` below row `p` lies in the lowest quarter or the
highest quarter of the block `[0, 3^p)`.  This is the gate band of the
third wave. -/
def prefixBand (K p : Nat) : Prop :=
  4 * (4^K % 3^p) < 3^p ∨ 3 * 3^p ≤ 4 * (4^K % 3^p)

/-- The row-`p` gate of the third wave: row digit two with a band prefix. -/
def thirdWaveRow (K p : Nat) : Prop :=
  digit3 (4^K) p = 2 ∧ prefixBand K p

/-- The third wave of `K`: some row gate fires. -/
def thirdWave (K : Nat) : Prop :=
  ∃ p : Nat, 1 ≤ p ∧ thirdWaveRow K p

/-! ## The multiplication-by-four row law -/

/-- Row law, low band: prefix in the lowest quarter (carry `c = 0`).
The row-`p` digit of `4 * R` is then just the quadrupled row digit of `R`. -/
theorem digit3_four_mul_of_lt (R p : Nat)
    (hband : 4 * (R % 3^p) < 3^p) :
    digit3 (4 * R) p = (4 * (R / 3^p)) % 3 := by
  have hpow : 0 < 3^p := Nat.pow_pos (by decide)
  have hR : R % 3^p + 3^p * (R / 3^p) = R := Nat.mod_add_div R (3^p)
  have h4R : 4 * R = 4 * (R % 3^p) + 3^p * (4 * (R / 3^p)) := by
    calc
      4 * R = 4 * (R % 3^p + 3^p * (R / 3^p)) := by rw [hR]
      _ = 4 * (R % 3^p) + 3^p * (4 * (R / 3^p)) := by ring
  unfold digit3
  rw [h4R, Nat.add_mul_div_left _ _ hpow, Nat.div_eq_of_lt hband]
  omega

/-- Row law, high band: prefix in the top quarter (carry `c = 3`). -/
theorem digit3_four_mul_of_ge (R p : Nat)
    (hband : 3 * 3^p ≤ 4 * (R % 3^p)) :
    digit3 (4 * R) p = (4 * (R / 3^p) + 3) % 3 := by
  have hpow : 0 < 3^p := Nat.pow_pos (by decide)
  have hs : 4 * (R % 3^p) =
      (4 * (R % 3^p) - 3 * 3^p) + 3^p * 3 := by omega
  have hslt : 4 * (R % 3^p) - 3 * 3^p < 3^p := by omega
  have hdiv : 4 * (R % 3^p) / 3^p = 3 := by
    rw [hs, Nat.add_mul_div_left _ _ hpow, Nat.div_eq_of_lt hslt]
  have hR : R % 3^p + 3^p * (R / 3^p) = R := Nat.mod_add_div R (3^p)
  have h4R : 4 * R = 4 * (R % 3^p) + 3^p * (4 * (R / 3^p)) := by
    calc
      4 * R = 4 * (R % 3^p + 3^p * (R / 3^p)) := by rw [hR]
      _ = 4 * (R % 3^p) + 3^p * (4 * (R / 3^p)) := by ring
  unfold digit3
  rw [h4R, Nat.add_mul_div_left _ _ hpow, hdiv]
  omega

/-- Row law, low-middle band: prefix in the second quarter (carry `c = 1`). -/
theorem digit3_four_mul_of_mid1 (R p : Nat)
    (hlo : 3^p ≤ 4 * (R % 3^p)) (hhi : 4 * (R % 3^p) < 2 * 3^p) :
    digit3 (4 * R) p = (4 * (R / 3^p) + 1) % 3 := by
  have hpow : 0 < 3^p := Nat.pow_pos (by decide)
  have hs : 4 * (R % 3^p) =
      (4 * (R % 3^p) - 3^p) + 3^p * 1 := by omega
  have hslt : 4 * (R % 3^p) - 3^p < 3^p := by omega
  have hdiv : 4 * (R % 3^p) / 3^p = 1 := by
    rw [hs, Nat.add_mul_div_left _ _ hpow, Nat.div_eq_of_lt hslt]
  have hR : R % 3^p + 3^p * (R / 3^p) = R := Nat.mod_add_div R (3^p)
  have h4R : 4 * R = 4 * (R % 3^p) + 3^p * (4 * (R / 3^p)) := by
    calc
      4 * R = 4 * (R % 3^p + 3^p * (R / 3^p)) := by rw [hR]
      _ = 4 * (R % 3^p) + 3^p * (4 * (R / 3^p)) := by ring
  unfold digit3
  rw [h4R, Nat.add_mul_div_left _ _ hpow, hdiv]
  omega

/-- Row law, high-middle band: prefix in the third quarter (carry `c = 2`). -/
theorem digit3_four_mul_of_mid2 (R p : Nat)
    (hlo : 2 * 3^p ≤ 4 * (R % 3^p)) (hhi : 4 * (R % 3^p) < 3 * 3^p) :
    digit3 (4 * R) p = (4 * (R / 3^p) + 2) % 3 := by
  have hpow : 0 < 3^p := Nat.pow_pos (by decide)
  have hs : 4 * (R % 3^p) =
      (4 * (R % 3^p) - 2 * 3^p) + 3^p * 2 := by omega
  have hslt : 4 * (R % 3^p) - 2 * 3^p < 3^p := by omega
  have hdiv : 4 * (R % 3^p) / 3^p = 2 := by
    rw [hs, Nat.add_mul_div_left _ _ hpow, Nat.div_eq_of_lt hslt]
  have hR : R % 3^p + 3^p * (R / 3^p) = R := Nat.mod_add_div R (3^p)
  have h4R : 4 * R = 4 * (R % 3^p) + 3^p * (4 * (R / 3^p)) := by
    calc
      4 * R = 4 * (R % 3^p + 3^p * (R / 3^p)) := by rw [hR]
      _ = 4 * (R % 3^p) + 3^p * (4 * (R / 3^p)) := by ring
  unfold digit3
  rw [h4R, Nat.add_mul_div_left _ _ hpow, hdiv]
  omega

/-! ## The gate equivalence -/

/-- **Row gate equivalence — the interval law at every row.**
A row-`p` pair of digit twos (`4^K` and `4^(K+1)`) is the same thing as a
row-`p` digit two of `4^K` whose prefix lies in the outer quarter band.
This upgrades the per-class row overlap theorems of the residue tower into
one uniform law. -/
theorem row_pair_iff_band (K p : Nat) :
    (digit3 (4^K) p = 2 ∧ digit3 (4^(K+1)) p = 2) ↔
      thirdWaveRow K p := by
  have hpow4 : 4^(K+1) = 4 * 4^K := by
    rw [Nat.pow_succ]
    ring
  unfold thirdWaveRow prefixBand
  constructor
  · rintro ⟨hd, hd2⟩
    refine ⟨hd, ?_⟩
    rw [hpow4] at hd2
    by_cases h1 : 4 * (4^K % 3^p) < 3^p
    · exact Or.inl h1
    · by_cases h3 : 3 * 3^p ≤ 4 * (4^K % 3^p)
      · exact Or.inr h3
      · by_cases h2 : 4 * (4^K % 3^p) < 2 * 3^p
        · rw [digit3_four_mul_of_mid1 (4^K) p (by omega) h2] at hd2
          exfalso
          unfold digit3 at hd
          omega
        · rw [digit3_four_mul_of_mid2 (4^K) p (by omega) (by omega)] at hd2
          exfalso
          unfold digit3 at hd
          omega
  · rintro ⟨hd, hband⟩
    refine ⟨hd, ?_⟩
    rw [hpow4]
    rcases hband with hlow | hhigh
    · rw [digit3_four_mul_of_lt (4^K) p hlow]
      unfold digit3 at hd
      omega
    · rw [digit3_four_mul_of_ge (4^K) p hhigh]
      unfold digit3 at hd
      omega

/-- **The third wave is the direct existence law, exponent by exponent.** -/
theorem thirdWave_iff_commonTwo (K : Nat) :
    thirdWave K ↔ CommonTwo K := by
  constructor
  · rintro ⟨p, hp1, hd, hband⟩
    exact ⟨p, hp1, (row_pair_iff_band K p).mpr ⟨hd, hband⟩⟩
  · rintro ⟨p, hp1, hd, hd2⟩
    exact ⟨p, hp1, (row_pair_iff_band K p).mp ⟨hd, hd2⟩⟩

/-- **The full law restated in wave language.** -/
theorem fourPowerDirectExistence_iff_thirdWave :
    FourPowerDirectExistence ↔ ∀ K : Nat, 5 ≤ K → K ≠ 7 → thirdWave K := by
  constructor
  · intro h K hK5 hK7
    exact (thirdWave_iff_commonTwo K).mpr (h K hK5 hK7)
  · intro h K hK5 hK7
    exact (thirdWave_iff_commonTwo K).mp (h K hK5 hK7)

/-- Every established row overlap class fires the third wave. -/
theorem thirdWave_of_mod9_five_or_six (K : Nat)
    (hres : K % 9 = 5 ∨ K % 9 = 6) : thirdWave K := by
  obtain ⟨p, hp1, hd, hd2⟩ := commonTwo_of_mod9_five_or_six K hres
  exact ⟨p, hp1, (row_pair_iff_band K p).mp ⟨hd, hd2⟩⟩

/-- Every established row-three overlap class fires the third wave. -/
theorem thirdWave_of_mod27_row_three (K : Nat)
    (hres : K % 27 = 14 ∨ K % 27 = 18 ∨ K % 27 = 19 ∨ K % 27 = 25) :
    thirdWave K := by
  obtain ⟨p, hp1, hd, hd2⟩ := commonTwo_of_mod27_row_three K hres
  exact ⟨p, hp1, (row_pair_iff_band K p).mp ⟨hd, hd2⟩⟩


/-! ## Third wave as exponent-prefix phase geometry -/

/-- **THIRD-WAVE / KILLING-TRIT EQUIVALENCE.**  The geometric third wave
fires exactly when some exponent-prefix scale hits its unique killing trit.
This identifies the wave picture with the recursive exponent geometry. -/
theorem thirdWave_iff_exists_killingTrit_hit (K : Nat) :
    thirdWave K ↔
      ∃ p : Nat,
        digit3 (4^(exponentPrefix K p)) (p+1) =
          digit3 (4^((exponentPrefix K p)+1)) (p+1) ∧
        exponentTrit K p = killingTrit K p := by
  rw [thirdWave_iff_commonTwo]
  exact commonTwo_iff_exists_killingTrit_hit K


#print axioms row_pair_iff_band
#print axioms thirdWave_iff_commonTwo
#print axioms fourPowerDirectExistence_iff_thirdWave
#print axioms thirdWave_iff_exists_killingTrit_hit

end GSTFourPowerThirdWave
