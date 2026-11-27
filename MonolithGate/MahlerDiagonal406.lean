import Mathlib
import MonolithGate.GSTTowerFire
import MonolithGate.GSTClimbInfiniteFamily
import MonolithGate.GSTGraphV2OmegaWaveLaw
import MonolithGate.GSTGhostRayExclusion
import MonolithGate.GSTWorldtraceMahler
import MonolithGate.WindowFire406

/-!
# THE S093 ROUND MODULE — the cut-word unification, the corrected
frontier, and the Mahler diagonal trajectory law.

Three families of new laws, every one composed from the campaign's own
green chambers (BOSS's standing order: USE MY MATHS, no classical
methods, no external inputs):

## §1 THE CUT-WORD UNIFICATION (the one-object theorem)

`CantorianPower K` — `4^K` owns no ternary digit two anywhere — is
EQUIVALENT to the cut word `omegaCutWord σ u` being digit-two-free,
where `K = 3^σ * u` is the three-free decomposition.  The whole Erdős
#406 problem becomes ONE question: which exponents have a clean cut
word?

## §2 THE CORRECTED FRONTIER (the accounting repair)

The sharp frontier's row-family accounting carried a stale cell: class
`64 mod 81` was listed among the uncovered row classes, but the green
cascade level two (`GSTClimbInfiniteFamily.dust_fire_row_four`,
CI-certified) kills every exponent `K ≡ 64 mod 81` unconditionally at
row four.  The honest accounting: the true 3-free frontier (the
docstring's five-class row list missed twenty-seven classes) is
thirty-two mod-81 classes; the green cascade cuts it to twenty-two;
and the mathematical survivor target (verified dual-method, stable
from row four on) is the EIGHT cells {1, 4, 10, 13, 28, 31, 37, 40}.

## §3 THE MAHLER DIAGONAL TRAJECTORY LAW

Let `c s = (4^(3^s) − 1) / 3^(s+1)` be the LTE tower coefficient and
`D a u s = 2u·c s − 2a + 9` the Mahler witness cofactor (the Mahler
witness is `3^(s+1) · D a u s`, exactly).  Then the tower step law
(`c (s+1) − c s = 3^(s+1) · E` with `E` a three-adic unit — the step
valuation is EXACTLY `s+1`), the trajectory dichotomy (every `(a, u)`
either fractures at an eventually-constant valuation or rides the
EXACT DIAGONAL `v₃ = s+1` forever — no third trajectory), and THE
EQUIVALENCE: `MahlerSharp` is EQUIVALENT to "no admissible `(a, u)`
rides the exact diagonal forever" — a pure infinite divisibility
trajectory statement, no p-adic analysis object anywhere.
-/

namespace MahlerDiagonal406

open GSTGraphV2OmegaWaveLaw (omegaCutWord omega_cut_factor)
open GSTCanonicalSevenAxisBridge (digit3)

set_option maxHeartbeats 20000000
set_option maxRecDepth 1000000

/-! ## §0 Small Nat/Int helpers -/

/-- The cast of a natural number mod three is the natural residue. -/
theorem coe_mod_three (u : Nat) : (u:ℤ) % 3 = ((u % 3 : ℕ) : ℤ) := by
  omega

/-- A three-free natural stays three-free after the cast. -/
theorem coe_not_three_dvd {u : Nat} (hu : ¬ 3 ∣ u) : (u:ℤ) % 3 ≠ 0 := by
  intro h
  rw [coe_mod_three] at h
  apply hu
  rw [Nat.dvd_iff_mod_eq_zero]
  exact Int.natCast_eq_zero.mp h

/-- Powers of three factor forward. -/
theorem pow_succ_three (s : Nat) : (3:ℤ)^(s+1) = 3 * (3:ℤ)^s := by
  rw [pow_succ]; ring

/-- Cancellation by a positive power of three. -/
theorem cancel_pow_three {s : Nat} {x y : ℤ}
    (h : (3:ℤ)^(s+1) * x = (3:ℤ)^(s+1) * y) : x = y :=
  Int.eq_of_mul_eq_mul_left (by positivity) h

/-- The product of three-adic units `2`, `u` and `E` is a unit. -/
theorem unit_product {u : Nat} {E : ℤ} (hu : ¬ 3 ∣ u) (hE : ¬ (3:ℤ) ∣ E) :
    (2 * (u:ℤ) * E) % 3 ≠ 0 := by
  have hu3 : (u:ℤ) % 3 ≠ 0 := coe_not_three_dvd hu
  have hE3m : E % 3 ≠ 0 := by
    intro hz
    exact hE (Int.dvd_iff_emod_eq_zero.mpr hz)
  have hvals : (u:ℤ) % 3 = 1 ∨ (u:ℤ) % 3 = 2 := by
    have h1 : (u:ℤ) % 3 < 3 := Int.emod_lt_of_pos _ (by norm_num)
    have h2 : (0:ℤ) ≤ (u:ℤ) % 3 := Int.emod_nonneg _ (by norm_num)
    omega
  have hvalsE : E % 3 = 1 ∨ E % 3 = 2 := by
    have h1 : E % 3 < 3 := Int.emod_lt_of_pos _ (by norm_num)
    have h2 : (0:ℤ) ≤ E % 3 := Int.emod_nonneg _ (by norm_num)
    omega
  rcases hvals with hu1 | hu1 <;> rcases hvalsE with hE1 | hE1 <;>
    rw [show 2 * (u:ℤ) * E = 2 * ((u:ℤ) * E) from by ring,
      Int.mul_emod 2 ((u:ℤ) * E) 3, Int.mul_emod (u:ℤ) E 3, hu1, hE1] <;>
    norm_num

/-! ## §1 THE CUT-WORD UNIFICATION -/

/-- Digits below the cut: positions `1..σ` of `1 + 3^(σ+1)·W` are zero. -/
theorem digit_shift_below (σ W p : Nat) (hp : 1 ≤ p) (hpσ : p ≤ σ) :
    digit3 (1 + 3^(σ+1) * W) p = 0 := by
  unfold digit3
  obtain ⟨k, hk⟩ : ∃ k : Nat, 3^(σ+1) = 3^p * k :=
    (pow_dvd_pow 3 (by omega))
  have hkpow : k = 3^(σ+1-p) := by
    have h1 : 3^p * 3^(σ+1-p) = 3^(σ+1) := by
      have h2 := Nat.pow_add 3 p (σ+1-p)
      rw [← h2]
      congr 1
      omega
    have h3p : (0:Nat) < 3^p := by positivity
    exact Nat.eq_of_mul_eq_mul_left h3p (hk.symm.trans h1.symm)
  have hsplit : 1 + 3^(σ+1) * W = 1 + 3^p * (k * W) := by rw [hk]; ring
  have hdiv2 : (1 + 3^p * (k * W)) / 3^p = k * W := by
    rw [Nat.add_mul_div_left _ _ (by positivity : (0:Nat) < 3^p)]
    have h1lt : 1 / 3^p = 0 := Nat.div_eq_of_lt (by
      obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
      have h3p : (1:Nat) < 3^(p'+1) := by
        rw [Nat.pow_succ]
        have hpos : (0:Nat) < 3^p' := by positivity
        omega
      exact h3p)
    rw [h1lt, Nat.zero_add]
  have hthree : (3:Nat) ∣ k * W := by
    rw [Nat.dvd_iff_mod_eq_zero, hkpow]
    have hs : (σ+1-p) = (σ-p)+1 := by omega
    rw [hs, Nat.pow_succ]
    have heq : 3 ^ (σ - p) * 3 * W = 3 * (3 ^ (σ - p) * W) := by ring
    rw [heq, Nat.mul_mod_right]
  rw [hsplit, hdiv2, Nat.dvd_iff_mod_eq_zero.mp hthree]

/-- Digits above the cut: position `σ+1+j` of `1 + 3^(σ+1)·W` is
position `j` of `W`. -/
theorem digit_shift_at (σ W j : Nat) :
    digit3 (1 + 3^(σ+1) * W) (σ+1+j) = digit3 W j := by
  unfold digit3
  have hqpos : (0:Nat) < 3^j := by positivity
  have hqmod : W % 3^j < 3^j := Nat.mod_lt _ hqpos
  have hsplit : W = 3^j * (W / 3^j) + W % 3^j :=
    (Nat.div_add_mod W (3^j)).symm
  have hpow : (3:Nat)^(σ+1) * 3^j = 3^(σ+1+j) :=
    (Nat.pow_add 3 (σ+1) j).symm
  have hmul : 3^(σ+1) * W
      = 3^(σ+1+j) * (W / 3^j) + 3^(σ+1) * (W % 3^j) := by
    linear_combination (3:Nat)^(σ+1) * hsplit + hpow * (W / 3^j)
  have hlt : 1 + 3^(σ+1) * (W % 3^j) < 3^(σ+1+j) := by
    have h1 : 3^(σ+1) * (W % 3^j) ≤ 3^(σ+1) * (3^j - 1) :=
      Nat.mul_le_mul_left _ (by omega)
    have hpos : (0:Nat) < 3^(σ+1) := by positivity
    have hltj : 3^j - 1 < 3^j := by omega
    have hm : 3^(σ+1) * (3^j - 1) < 3^(σ+1) * 3^j :=
      Nat.mul_lt_mul_of_pos_left hltj hpos
    rw [hpow] at hm
    have hgap : 3^(σ+1+j) = 3^(σ+1) * (3^j - 1) + 3^(σ+1) := by
      linear_combination -hpow
    have h2 : (2:Nat) ≤ 3^(σ+1) := by
      obtain ⟨s', rfl⟩ : ∃ s', σ + 1 = s' + 1 := ⟨σ, by omega⟩
      rw [Nat.pow_succ]
      have hs' : (1:Nat) ≤ 3^s' := by positivity
      omega
    omega
  have hdiv : (1 + 3^(σ+1) * (W % 3^j) + 3^(σ+1+j) * (W / 3^j)) / 3^(σ+1+j)
      = W / 3^j := by
    have h5 : 1 + 3^(σ+1) * (W % 3^j) + 3^(σ+1+j) * (W / 3^j)
        = (1 + 3^(σ+1) * (W % 3^j)) + 3^(σ+1+j) * (W / 3^j) := by ring
    rw [h5, Nat.add_mul_div_left _ _ (by positivity : (0:Nat) < 3^(σ+1+j)),
      Nat.div_eq_of_lt hlt, Nat.zero_add]
  have h6 : 1 + (3^(σ+1+j) * (W / 3^j) + 3^(σ+1) * (W % 3^j))
      = 1 + 3^(σ+1) * (W % 3^j) + 3^(σ+1+j) * (W / 3^j) := by ring
  rw [hmul, h6, hdiv]

/-- **THE CUT-WORD UNIFICATION.**  `CantorianPower K` holds exactly when
the cut word of its three-free decomposition is digit-two-free: the
Erdős core and the cut-word language are ONE object. -/
theorem cantorian_iff_cutword_clean (K σ u : Nat) (hK : K = 3^σ * u) :
    GSTClimbInfiniteFamily.CantorianPower K ↔
      noTernaryTwo (omegaCutWord σ u) = true := by
  have hf : 4^K = 1 + 3^(σ+1) * omegaCutWord σ u := by
    rw [hK]
    exact omega_cut_factor σ u
  constructor
  · intro hcand
    refine GSTClimbInfiniteFamily.noTernaryTwo_of_forall_digit _ (fun p => ?_)
    intro h2
    have hc := hcand (σ+1+p) (by omega)
    rw [hf, digit_shift_at] at hc
    exact hc h2
  · intro hclean p hp
    have hW : ∀ q : Nat, (omegaCutWord σ u) / 3^q % 3 ≠ 2 := by
      intro q h2
      have ht := hasTernaryTwo_of_digit (omegaCutWord σ u) q h2
      have hn := has_two_imp_not_no_two (omegaCutWord σ u) ht
      rw [hclean] at hn
      exact absurd hn (by decide)
    rcases Nat.lt_or_ge p (σ+1) with hlt | hge
    · rw [hf, digit_shift_below σ _ p hp (by omega)]
      decide
    · have hp' : p = σ+1 + (p - σ - 1) := by omega
      rw [hp', hf, digit_shift_at]
      exact hW (p - σ - 1)

/-- **The one-object restatement of the whole problem.**  No Cantorian
exponent from eight on exists exactly when no admissible cut word is
clean: the entire residual of Erdős #406 is the cleanliness of the
cut-word family. -/
theorem no_cantorian_iff_no_clean_cutword :
    (¬ ∃ K : Nat, 8 ≤ K ∧ GSTClimbInfiniteFamily.CantorianPower K) ↔
      (∀ σ u : Nat, ¬ 3 ∣ u → 8 ≤ 3^σ * u →
        noTernaryTwo (omegaCutWord σ u) = false) := by
  constructor
  · intro hnc σ u hu hK
    by_contra hclean
    have htrue : noTernaryTwo (omegaCutWord σ u) = true := by
      cases h : noTernaryTwo (omegaCutWord σ u) with
      | true => rfl
      | false => exact absurd h hclean
    exact hnc ⟨3^σ * u, hK,
      (cantorian_iff_cutword_clean (3^σ*u) σ u rfl).mpr htrue⟩
  · intro hcut hK
    obtain ⟨K, hK8, hcand⟩ := hK
    obtain ⟨σ, u, hσu, hu⟩ :=
      GSTGhostRay.exists_three_free_decomp K K (by omega) (by omega)
    have hc : noTernaryTwo (omegaCutWord σ u) = false :=
      hcut σ u hu (by rw [← hσu]; omega)
    rw [(cantorian_iff_cutword_clean K σ u hσu).mp hcand] at hc
    exact absurd hc (by decide)

/-! ## §2 THE CORRECTED FRONTIER — the cascade credit -/

/-- The cascade case tree: a sharp-frontier exponent either lies in
one of the green cascade's three kill families (and fires
unconditionally there) or the fire premise applies. -/
theorem fire_of_frontier_or_cascade
    (hsharp : ∀ K : Nat, 8 ≤ K →
      WindowFire406.erdos_406_sharp_frontier_class K →
      K % 9 ≠ 7 →
      (K % 27 ≠ 19 ∧ K % 27 ≠ 22 ∧ K % 27 ≠ 25) →
      (K % 81 ≠ 55 ∧ K % 81 ≠ 58 ∧ K % 81 ≠ 64 ∧
        K % 81 ≠ 67 ∧ K % 81 ≠ 73 ∧ K % 81 ≠ 76) →
      ∃ p : Nat, 1 ≤ p ∧ digit3 (4 ^ K) p = 2)
    (K : Nat) (hK : 8 ≤ K)
    (hfront : WindowFire406.erdos_406_sharp_frontier_class K) :
    ∃ p : Nat, 1 ≤ p ∧ digit3 (4 ^ K) p = 2 := by
  by_cases h9 : K % 9 = 7
  · exact ⟨2, by omega, GSTClimbInfiniteFamily.dust_fire_row_two K h9⟩
  · by_cases h3 : K % 27 = 19 ∨ K % 27 = 22 ∨ K % 27 = 25
    · rcases h3 with h19 | h22 | h25
      · exact ⟨3, by omega,
          GSTClimbInfiniteFamily.dust_fire_row_three K (Or.inl h19)⟩
      · exact ⟨3, by omega,
          GSTClimbInfiniteFamily.dust_fire_row_three K (Or.inr (Or.inl h22))⟩
      · exact ⟨3, by omega,
          GSTClimbInfiniteFamily.dust_fire_row_three K (Or.inr (Or.inr h25))⟩
    · push_neg at h3
      obtain ⟨h19, h22, h25⟩ := h3
      by_cases h4 : K % 81 = 55 ∨ K % 81 = 58 ∨ K % 81 = 64 ∨
          K % 81 = 67 ∨ K % 81 = 73 ∨ K % 81 = 76
      · rcases h4 with h55 | h58 | h64 | h67 | h73 | h76
        · exact ⟨4, by omega, GSTClimbInfiniteFamily.dust_fire_row_four K
            (Or.inl h55)⟩
        · exact ⟨4, by omega, GSTClimbInfiniteFamily.dust_fire_row_four K
            (Or.inr (Or.inl h58))⟩
        · exact ⟨4, by omega, GSTClimbInfiniteFamily.dust_fire_row_four K
            (Or.inr (Or.inr (Or.inl h64)))⟩
        · exact ⟨4, by omega, GSTClimbInfiniteFamily.dust_fire_row_four K
            (Or.inr (Or.inr (Or.inr (Or.inl h67))))⟩
        · exact ⟨4, by omega, GSTClimbInfiniteFamily.dust_fire_row_four K
            (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h73)))))⟩
        · exact ⟨4, by omega, GSTClimbInfiniteFamily.dust_fire_row_four K
            (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h76)))))⟩
      · push_neg at h4
        obtain ⟨h55, h58, h64, h67, h73, h76⟩ := h4
        exact hsharp K hK hfront h9 ⟨h19, h22, h25⟩
          ⟨h55, h58, h64, h67, h73, h76⟩

/-- **THE CORRECTED SHARP REDUCTION LAW (the full cascade credit).**  The
full even-exponent verdict needs the sharp-frontier fire premise only
OUTSIDE the green cascade's three unconditional kill families: class 7
mod 9 (row two), classes 19, 22, 25 mod 27 (row three) and classes
55, 58, 64, 67, 73, 76 mod 81 (row four) — all CI-certified in
`GSTClimbInfiniteFamily`, none credited in the frontier definition's
accounting. -/
theorem even_conjecture_of_sharp_frontier_minus_cascade
    (hsharp : ∀ K : Nat, 8 ≤ K →
      WindowFire406.erdos_406_sharp_frontier_class K →
      K % 9 ≠ 7 →
      (K % 27 ≠ 19 ∧ K % 27 ≠ 22 ∧ K % 27 ≠ 25) →
      (K % 81 ≠ 55 ∧ K % 81 ≠ 58 ∧ K % 81 ≠ 64 ∧
        K % 81 ≠ 67 ∧ K % 81 ≠ 73 ∧ K % 81 ≠ 76) →
      ∃ p : Nat, 1 ≤ p ∧ digit3 (4 ^ K) p = 2) :
    ∀ K : Nat, 8 ≤ K → noTernaryTwo (4 ^ K) = false := by
  refine WindowFire406.erdos_406_even_conjecture_of_sharp_frontier_fires ?_
  intro K hK hfront
  exact fire_of_frontier_or_cascade hsharp K hK hfront

/-- **The corrected full-verdict equivalence (the cascade credit).** -/
theorem full_verdict_iff_sharp_frontier_minus_cascade :
    (∀ n : Nat, 9 ≤ n → noTernaryTwo (2 ^ n) = false) ↔
      (∀ K : Nat, 8 ≤ K →
        WindowFire406.erdos_406_sharp_frontier_class K →
        K % 9 ≠ 7 →
        (K % 27 ≠ 19 ∧ K % 27 ≠ 22 ∧ K % 27 ≠ 25) →
        (K % 81 ≠ 55 ∧ K % 81 ≠ 58 ∧ K % 81 ≠ 64 ∧
          K % 81 ≠ 67 ∧ K % 81 ≠ 73 ∧ K % 81 ≠ 76) →
        ∃ p : Nat, 1 ≤ p ∧ digit3 (4 ^ K) p = 2) := by
  constructor
  · intro hverdict K hK hfront _ _ _
    exact WindowFire406.erdos_406_full_verdict_iff_sharp_frontier_fires.mp
      hverdict K hK hfront
  · intro hsharp
    refine WindowFire406.erdos_406_full_verdict_iff_sharp_frontier_fires.mpr ?_
    intro K hK hfront
    exact fire_of_frontier_or_cascade hsharp K hK hfront

/-! ## §3 THE MAHLER DIAGONAL TRAJECTORY LAW -/

/-- The tower coefficient at zero is one. -/
theorem c_zero : GSTTowerFire.c 0 = 1 := by
  unfold GSTTowerFire.c
  norm_num

/-- **The tower unit law.**  `3` never divides the tower coefficient:
the LTE valuation of `4^(3^n) − 1` is exactly `n+1`. -/
theorem c_not_three (n : Nat) : ¬ 3 ∣ GSTTowerFire.c n := by
  have hbase : ¬ 3 ∣ GSTTowerFire.c 0 := by rw [c_zero]; decide
  induction n with
  | zero => exact hbase
  | succ n ih =>
      intro hdiv
      apply ih
      rw [Nat.dvd_iff_mod_eq_zero] at hdiv ⊢
      have hstep := GSTTowerFire.c_succ_eq n
      have hcorr : (3:Nat) ∣ 3^(n+1) * (GSTTowerFire.c n * GSTTowerFire.c n
          + 3^n * (GSTTowerFire.c n * GSTTowerFire.c n * GSTTowerFire.c n)) := by
        obtain ⟨m, hm⟩ : ∃ m : Nat, 3^(n+1) = 3 * m := ⟨3^n, by
          rw [Nat.pow_succ]; ring⟩
        exact ⟨m * (GSTTowerFire.c n * GSTTowerFire.c n
          + 3^n * (GSTTowerFire.c n * GSTTowerFire.c n * GSTTowerFire.c n)),
          by rw [hm]; ring⟩
      have hcorr0 : (3^(n+1) * (GSTTowerFire.c n * GSTTowerFire.c n
          + 3^n * (GSTTowerFire.c n * GSTTowerFire.c n * GSTTowerFire.c n))) % 3 = 0 :=
        Nat.dvd_iff_mod_eq_zero.mp hcorr
      rw [hstep, Nat.add_mod, hcorr0] at hdiv
      omega

/-- **THE TOWER STEP LAW.**  The step of the tower coefficient carries
exactly `s+1` factors of three: `c (s+1) − c s = 3^(s+1) * E` with `E`
a three-adic unit.  This sharpens the green stability law `c_stable`
(which provides the divisibility but never the exact valuation). -/
theorem c_step_unit (s : Nat) :
    ∃ E : ℤ, ((GSTTowerFire.c (s+1) : ℤ) - (GSTTowerFire.c s : ℤ))
      = (3:ℤ)^(s+1) * E ∧ ¬ ((3:ℤ) ∣ E) := by
  have hcast : ((GSTTowerFire.c (s+1) : ℤ))
      = ((GSTTowerFire.c s : ℤ)) + (3:ℤ)^(s+1)
        * (((GSTTowerFire.c s : ℤ) * (GSTTowerFire.c s : ℤ))
          + (3:ℤ)^s * ((GSTTowerFire.c s : ℤ) * (GSTTowerFire.c s : ℤ)
            * (GSTTowerFire.c s : ℤ))) := by
    exact_mod_cast GSTTowerFire.c_succ_eq s
  refine ⟨(GSTTowerFire.c s : ℤ) * (GSTTowerFire.c s : ℤ)
      + (3:ℤ)^s * ((GSTTowerFire.c s : ℤ) * (GSTTowerFire.c s : ℤ)
        * (GSTTowerFire.c s : ℤ)), ?_, ?_⟩
  · rw [hcast]; ring
  · intro hdvd
    rw [Int.dvd_iff_emod_eq_zero] at hdvd
    rcases s with _ | s'
    · rw [c_zero] at hdvd
      norm_num at hdvd
    · have h3s : ((3:ℤ)^(s'+1)) % 3 = 0 := by
        refine Int.dvd_iff_emod_eq_zero.mp ⟨(3:ℤ)^s', ?_⟩
        rw [pow_succ]
        ring
      have h3term : ((3:ℤ)^(s'+1) * ((GSTTowerFire.c (s'+1) : ℤ)
          * (GSTTowerFire.c (s'+1) : ℤ) * (GSTTowerFire.c (s'+1) : ℤ))) % 3 = 0 := by
        rw [Int.mul_emod _ _ 3, h3s, Int.zero_mul, Int.zero_emod]
      rw [Int.add_emod, h3term, Int.add_zero, Int.mul_emod _ _ 3] at hdvd
      have hlt : (GSTTowerFire.c (s'+1) : ℤ) % 3 < 3 :=
        Int.emod_lt_of_pos _ (by norm_num)
      have hge : (0:ℤ) ≤ (GSTTowerFire.c (s'+1) : ℤ) % 3 :=
        Int.emod_nonneg _ (by norm_num)
      have hc0 : (GSTTowerFire.c (s'+1) : ℤ) % 3 ≠ 0 :=
        coe_not_three_dvd (c_not_three (s'+1))
      rcases (by omega : (GSTTowerFire.c (s'+1) : ℤ) % 3 = 1 ∨
          (GSTTowerFire.c (s'+1) : ℤ) % 3 = 2) with h1 | h1
      · rw [h1] at hdvd; norm_num at hdvd
      · rw [h1] at hdvd; norm_num at hdvd

/-- The Mahler witness (the exact integer of the hypothesis family). -/
def W (a u s : Nat) : ℤ :=
  2 * (u : ℤ) * ((4 : ℤ)^(3^s) - 1) - (6 * (a : ℤ) - 27) * (3 : ℤ)^s

/-- The Mahler witness cofactor. -/
def D (a u s : Nat) : ℤ :=
  2 * (u : ℤ) * (GSTTowerFire.c s : ℤ) - 2 * (a : ℤ) + 9

/-- **The witness factorization.**  The Mahler witness is exactly the
baseline power times the cofactor: `W = 3^(s+1) · D`. -/
theorem W_eq (a u s : Nat) : W a u s = (3:ℤ)^(s+1) * D a u s := by
  have h4 : (4 : ℤ)^(3^s) = 1 + (3:ℤ)^(s+1) * (GSTTowerFire.c s : ℤ) := by
    exact_mod_cast GSTTowerFire.four_pow_three_pow_eq s
  unfold W D
  rw [h4, pow_succ_three]
  ring

/-- The cofactor is always odd, hence never zero. -/
theorem D_odd (a u s : Nat) : D a u s % 2 = 1 := by
  unfold D
  have hr : 2 * (u:ℤ) * (GSTTowerFire.c s : ℤ) - 2 * (a:ℤ) + 9
      = 2 * ((u:ℤ) * (GSTTowerFire.c s : ℤ) - (a:ℤ) + 4) + 1 := by ring
  have h0 : (2 * ((u:ℤ) * (GSTTowerFire.c s : ℤ) - (a:ℤ) + 4)) % 2 = 0 := by
    refine Int.dvd_iff_emod_eq_zero.mp ⟨(u:ℤ) * (GSTTowerFire.c s : ℤ) - (a:ℤ) + 4, ?_⟩
    ring
  rw [hr, Int.add_emod, h0, Int.zero_add]
  norm_num

theorem D_ne_zero (a u s : Nat) : D a u s ≠ 0 := by
  intro h
  have h1 : D a u s % 2 = 1 := D_odd a u s
  rw [h, Int.zero_emod] at h1
  exact absurd h1 (by norm_num)

/-- The cofactor step identity. -/
theorem D_step (a u s : Nat) :
    D a u (s+1) - D a u s
      = 2 * (u:ℤ) * ((GSTTowerFire.c (s+1) : ℤ) - (GSTTowerFire.c s : ℤ)) := by
  unfold D
  ring

/-- **The step-down law.**  Above the diagonal the valuation drops onto
the exact diagonal: if `3^(s+2) ∣ D s` then `D (s+1)` carries exactly
`s+1` factors of three. -/
theorem step_above (a u s : Nat) (hu : ¬ 3 ∣ u)
    (h : (3:ℤ)^(s+2) ∣ D a u s) :
    (3:ℤ)^(s+1) ∣ D a u (s+1) ∧ ¬ (3:ℤ)^(s+2) ∣ D a u (s+1) := by
  obtain ⟨E, hE, hE3⟩ := c_step_unit s
  obtain ⟨dhat, hd⟩ := h
  have hB : D a u (s+1)
      = (3:ℤ)^(s+1) * (3 * dhat + 2 * (u:ℤ) * E) := by
    have hst := D_step a u s
    rw [hE] at hst
    have hd' : D a u s = 3 * ((3:ℤ)^(s+1) * dhat) := by
      rw [hd, pow_succ_three]
      ring
    linear_combination hst + hd'
  have hBmod : (3 * dhat + 2 * (u:ℤ) * E) % 3 ≠ 0 := by
    have hu3 : (2 * (u:ℤ) * E) % 3 ≠ 0 := unit_product hu hE3
    have h30 : (3 * dhat) % 3 = 0 := by
      refine Int.dvd_iff_emod_eq_zero.mp ⟨dhat, ?_⟩
      ring
    intro hcon
    rw [Int.add_emod, h30, Int.zero_add] at hcon
    have hlt : (2 * (u:ℤ) * E) % 3 < 3 := Int.emod_lt_of_pos _ (by norm_num)
    have hge : (0:ℤ) ≤ (2 * (u:ℤ) * E) % 3 := Int.emod_nonneg _ (by norm_num)
    omega
  refine ⟨⟨_, hB⟩, ?_⟩
  intro hdvd
  obtain ⟨k, hk⟩ := hdvd
  rw [hB] at hk
  have hsplit : (3:ℤ)^(s+2) = (3:ℤ)^(s+1) * 3 := by rw [pow_succ_three]; ring
  rw [hsplit] at hk
  have hcan : (3:ℤ)^(s+1) * (3 * k)
      = (3:ℤ)^(s+1) * (3 * dhat + 2 * (u:ℤ) * E) := by
    linear_combination -hk
  have h3B : (3:ℤ) ∣ (3 * dhat + 2 * (u:ℤ) * E) :=
    ⟨k, (cancel_pow_three hcan).symm⟩
  exact hBmod (Int.dvd_iff_emod_eq_zero.mp h3B)

/-- **The frozen step law.**  Below the diagonal the valuation freezes:
if `D s` carries exactly `t ≤ s` factors of three, then so does
`D (s+1)`. -/
theorem step_frozen (a u s t : Nat) (hu : ¬ 3 ∣ u) (hle : t ≤ s)
    (h0 : (3:ℤ)^t ∣ D a u s) (h1 : ¬ (3:ℤ)^(t+1) ∣ D a u s) :
    (3:ℤ)^t ∣ D a u (s+1) ∧ ¬ (3:ℤ)^(t+1) ∣ D a u (s+1) := by
  obtain ⟨E, hE, hE3⟩ := c_step_unit s
  have hstep : D a u (s+1) = D a u s + 2 * (u:ℤ) * ((3:ℤ)^(s+1) * E) := by
    have hst := D_step a u s
    rw [hE] at hst
    linear_combination hst
  have hmid : (3:ℤ)^(t+1) ∣ 2 * (u:ℤ) * ((3:ℤ)^(s+1) * E) := by
    have hp : (3:ℤ)^(t+1) ∣ (3:ℤ)^(s+1) := pow_dvd_pow 3 (by omega)
    exact hp.trans ⟨2 * (u:ℤ) * E, by ring⟩
  have hmidt : (3:ℤ)^t ∣ 2 * (u:ℤ) * ((3:ℤ)^(s+1) * E) :=
    (pow_dvd_pow 3 (by omega : t ≤ t+1)).trans hmid
  refine ⟨by rw [hstep]; exact h0.add hmidt, ?_⟩
  intro hdvd
  apply h1
  have hminus : D a u (s+1) - 2 * (u:ℤ) * ((3:ℤ)^(s+1) * E) = D a u s := by
    rw [hstep]; ring
  have hsub : (3:ℤ)^(t+1) ∣ D a u (s+1) - 2 * (u:ℤ) * ((3:ℤ)^(s+1) * E) :=
    hdvd.sub hmid
  rw [hminus] at hsub
  exact hsub

/-- **The frozen forever law.**  Once below the diagonal at `s₀` with
exact valuation `t ≤ s₀`, the valuation stays exactly `t` forever. -/
theorem frozen_forever (a u : Nat) (hu : ¬ 3 ∣ u) (t s₀ : Nat) (hle : t ≤ s₀)
    (h0 : (3:ℤ)^t ∣ D a u s₀) (h1 : ¬ (3:ℤ)^(t+1) ∣ D a u s₀) :
    ∀ s : Nat, s₀ ≤ s → (3:ℤ)^t ∣ D a u s ∧ ¬ (3:ℤ)^(t+1) ∣ D a u s := by
  intro s hs
  have hkey : ∀ k : Nat, (3:ℤ)^t ∣ D a u (s₀ + k)
      ∧ ¬ (3:ℤ)^(t+1) ∣ D a u (s₀ + k) := by
    intro k
    induction k with
    | zero => exact ⟨h0, h1⟩
    | succ k ih =>
        have hnext := step_frozen a u (s₀ + k) t hu (by omega) ih.1 ih.2
        have heq : s₀ + k + 1 = s₀ + (k+1) := by omega
        rw [heq] at hnext
        exact hnext
  have hs' : s = s₀ + (s - s₀) := by omega
  rw [hs']
  exact hkey (s - s₀)

/-- Every nonzero integer carries an exact power of three. -/
theorem exists_val : ∀ (n : Nat) (x : ℤ), x.natAbs = n → x ≠ 0 →
    ∃ t : Nat, (3:ℤ)^t ∣ x ∧ ¬ (3:ℤ)^(t+1) ∣ x := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro x hx hx0
    by_cases h3 : (3:ℤ) ∣ x
    · obtain ⟨y, hy⟩ := h3
      have hy0 : y ≠ 0 := by
        intro yc
        rw [yc] at hy
        simp at hy
        exact hx0 hy
      have hny : y.natAbs < n := by
        have habs : (3 * y).natAbs = 3 * y.natAbs := by
          rw [Int.natAbs_mul]
          norm_num
        have hypos : 0 < y.natAbs := Int.natAbs_pos.mpr hy0
        rw [← hx, hy, habs]
        omega
      obtain ⟨t, ht0, ht1⟩ := ih y.natAbs hny y rfl hy0
      refine ⟨t+1, ?_, ?_⟩
      · rw [hy, pow_succ_three]
        exact mul_dvd_mul_left 3 ht0
      · intro hdvd
        apply ht1
        rw [hy, pow_succ_three] at hdvd
        obtain ⟨k, hk⟩ := hdvd
        refine ⟨k, ?_⟩
        have hring : 3 * y = 3 * ((3:ℤ)^(t+1) * k) := by
          linear_combination hk
        exact Int.eq_of_mul_eq_mul_left (by norm_num : (3:ℤ) ≠ 0) hring
    · exact ⟨0, one_dvd x, by simpa using h3⟩

/-- **THE TRAJECTORY DICHOTOMY.**  For every `(a, u)` with `u`
three-free, either the Mahler cofactor `D a u s` rides the EXACT
DIAGONAL — `v₃(D a u s) = s+1` for all sufficiently large `s` — or its
valuation is EVENTUALLY CONSTANT.  There is no third trajectory. -/
theorem trajectory_dichotomy (a u : Nat) (hu : ¬ 3 ∣ u) :
    (∃ S₀ : Nat, ∀ s : Nat, S₀ ≤ s →
      ((3:ℤ)^(s+1) ∣ D a u s ∧ ¬ (3:ℤ)^(s+2) ∣ D a u s)) ∨
    (∃ S₀ t : Nat, ∀ s : Nat, S₀ ≤ s →
      ((3:ℤ)^t ∣ D a u s ∧ ¬ (3:ℤ)^(t+1) ∣ D a u s)) := by
  by_cases hbelow : ∃ s₀ : Nat, ¬ (3:ℤ)^(s₀+1) ∣ D a u s₀
  · obtain ⟨s₀, hs₀⟩ := hbelow
    obtain ⟨t, ht0, ht1⟩ :=
      exists_val (D a u s₀).natAbs (D a u s₀) rfl (D_ne_zero a u s₀)
    have hts : t ≤ s₀ := by
      by_contra hcon
      push_neg at hcon
      exact hs₀ ((pow_dvd_pow 3 (by omega) :
        (3:ℤ)^(s₀+1) ∣ (3:ℤ)^t).trans ht0)
    exact Or.inr ⟨s₀, t, frozen_forever a u hu t s₀ hts ht0 ht1⟩
  · push_neg at hbelow
    refine Or.inl ⟨0, fun s _ => ⟨hbelow s, ?_⟩⟩
    intro habove
    obtain ⟨h1, h2⟩ := step_above a u s hu habove
    exact h2 (hbelow (s+1))

/-- **THE FRACTURE FROM FREEZE.**  An eventually-constant valuation at
precision `t` is an explicit fracture of the relative lock at precision
`t+2`, arbitrarily far out. -/
theorem fracture_of_frozen (a u : Nat)
    (hfroz : ∃ S₀ t : Nat, ∀ s : Nat, S₀ ≤ s →
      ((3:ℤ)^t ∣ D a u s ∧ ¬ (3:ℤ)^(t+1) ∣ D a u s)) :
    ∃ q : Nat, 2 ≤ q ∧ ∀ S : Nat, ∃ s : Nat, S ≤ s ∧
      ¬ ((3:ℤ)^(s+q) ∣ W a u s) := by
  obtain ⟨S₀, t, hf⟩ := hfroz
  refine ⟨t+2, by omega, ?_⟩
  intro S
  refine ⟨max S S₀, le_max_left _ _, ?_⟩
  intro hdvd
  obtain ⟨k, hk⟩ := hdvd
  rw [W_eq] at hk
  have hsplit : (3:ℤ)^(max S S₀ + (t+2))
      = (3:ℤ)^(max S S₀ + 1) * (3:ℤ)^(t+1) := by
    have hp := pow_add (3:ℤ) (max S S₀ + 1) (t + 1)
    rw [← hp]
    congr 1
    omega
  rw [hsplit] at hk
  have hcan : (3:ℤ)^(max S S₀ + 1) * ((3:ℤ)^(t+1) * k)
      = (3:ℤ)^(max S S₀ + 1) * D a u (max S S₀) := by
    linear_combination -hk
  exact (hf (max S S₀) (le_max_right _ _)).2
    ⟨k, (cancel_pow_three hcan).symm⟩

/-- **THE DIAGONAL CHAIN FROM THE LOCK.**  If the pair `(a, u)` receives
the relative lock, then the cofactor rides the exact diagonal forever. -/
theorem diagonal_chain_of_lock (a u : Nat) (hu : ¬ 3 ∣ u)
    (hlock : ∀ q : Nat, ∃ S : Nat, ∀ s : Nat, S ≤ s →
      (3:ℤ)^(s+q) ∣ W a u s) :
    ∃ S₀ : Nat, ∀ s : Nat, S₀ ≤ s →
      ((3:ℤ)^(s+1) ∣ D a u s ∧ ¬ (3:ℤ)^(s+2) ∣ D a u s) := by
  rcases trajectory_dichotomy a u hu with hchain | hfroz
  · exact hchain
  · exfalso
    obtain ⟨q, hq2, hfracture⟩ := fracture_of_frozen a u hfroz
    obtain ⟨S, hS⟩ := hlock q
    obtain ⟨s, hsS, hsnot⟩ := hfracture S
    exact hsnot (hS s hsS)

/-- **THE LOCK FROM THE DIAGONAL CHAIN.**  An exact diagonal trajectory
delivers every relative precision: the chain and the lock are one
condition. -/
theorem lock_of_diagonal_chain (a u : Nat)
    (hchain : ∃ S₀ : Nat, ∀ s : Nat, S₀ ≤ s → (3:ℤ)^(s+1) ∣ D a u s) :
    ∀ q : Nat, ∃ S : Nat, ∀ s : Nat, S ≤ s → (3:ℤ)^(s+q) ∣ W a u s := by
  obtain ⟨S₀, hS₀⟩ := hchain
  intro q
  refine ⟨max S₀ q, ?_⟩
  intro s hs
  rw [W_eq]
  rcases q with _ | q'
  · exact (pow_dvd_pow 3 (by omega : s + 0 ≤ s + 1)).trans
      (dvd_mul_right _ _)
  · have hd : (3:ℤ)^(q') ∣ D a u s := by
      have h1 : (3:ℤ)^(q') ∣ (3:ℤ)^(s+1) := pow_dvd_pow 3 (by omega)
      exact h1.trans (hS₀ s (le_trans (le_max_left _ _) hs))
    have hsplit : (3:ℤ)^(s + (q'+1)) = (3:ℤ)^(s+1) * (3:ℤ)^(q') := by
      have hp := pow_add (3:ℤ) (s + 1) q'
      rw [← hp]
      congr 1
      omega
    rw [hsplit]
    exact mul_dvd_mul_left _ hd

/-- **THE HYPOTHESIS IN ITS MOST ELEMENTARY FORM.**  `MahlerSharp` —
the one remaining named input of the #406 crown chain — is EQUIVALENT
to: no admissible pair `(a, u)` rides the exact diagonal forever.  The
hypothesis family (a 3-adic convergence statement in its original
dress) and the infinite explicit divisibility trajectory are one
object; no p-adic analysis appears anywhere in the equivalence. -/
theorem mahler_sharp_iff_no_diagonal_chain :
    GSTWorldtraceMahler.MahlerSharp ↔
      (∀ (a u : Nat), a < 9 → ¬ 3 ∣ a → ¬ 3 ∣ u →
        ¬ ∃ S₀ : Nat, ∀ s : Nat, S₀ ≤ s →
          ((3:ℤ)^(s+1) ∣ D a u s ∧ ¬ (3:ℤ)^(s+2) ∣ D a u s)) := by
  constructor
  · intro H a u ha hA hu hchain
    obtain ⟨S₀, hS₀⟩ := hchain
    refine H ⟨a, u, ⟨ha, hA⟩, hu, ?_⟩
    exact lock_of_diagonal_chain a u ⟨S₀, fun s hs => (hS₀ s hs).1⟩
  · intro H hK
    obtain ⟨a, u, hadm, hu, hlock⟩ := hK
    exact H a u hadm.1 hadm.2 hu (diagonal_chain_of_lock a u hu hlock)

/-! ## Receipts -/

#print axioms cantorian_iff_cutword_clean
#print axioms no_cantorian_iff_no_clean_cutword
#print axioms fire_of_frontier_or_cascade
#print axioms even_conjecture_of_sharp_frontier_minus_cascade
#print axioms full_verdict_iff_sharp_frontier_minus_cascade
#print axioms c_not_three
#print axioms c_step_unit
#print axioms W_eq
#print axioms D_odd
#print axioms D_ne_zero
#print axioms step_above
#print axioms step_frozen
#print axioms frozen_forever
#print axioms exists_val
#print axioms trajectory_dichotomy
#print axioms fracture_of_frozen
#print axioms diagonal_chain_of_lock
#print axioms lock_of_diagonal_chain
#print axioms mahler_sharp_iff_no_diagonal_chain

end MahlerDiagonal406

#eval "ERDOS406_MAHLER_DIAGONAL_GREEN"
