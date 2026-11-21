import Arsenal.ErdosTernary2.Basic
import Arsenal.CardinalWorlds
import Arsenal.CardinalWorldsV2

-- Family pattern (green kernels): explicit depth headroom.
set_option maxRecDepth 262144
set_option maxHeartbeats 4000000

/-!
# ERDŐS #406 — THE 2-ADIC BUDGET-TOWER KERNEL (S077, the LX-successor round)

## THE ORIGIN (the war council of S077 — BOSS order: crack the hypothesis)

The S076 session named the LX conjecture (`v₂(cantor n) ≤ 2·popcount₃(n)`)
as the next target. The S077 war council (Attacker + Strategist dispositions)
REFUTED LX outright — the minimal counterexample sits ONE position past the
S076 census boundary:

  **n₁ = 3⁰ + 3⁷ + 3⁸ + 3¹³ = 1,603,072 = 2⁹·3131**
  (digit set {0, 7, 8, 13}: popcount 4, v₂ = 9 > 8 = 2·4),

and the falsity is total: at popcount 4 (and every even popcount ≥ 4) the
2-adic valuation is UNBOUNDED (the far-cap family `13 + 3^d`, dual-verified:
d = 69 gives v₂ = 11; the construction is the 2-adic dlog of −13 in ⟨3⟩).
The assault produced something better than the dead conjecture: **the
mechanism that killed it** — the 2-adic twin of the DustLaw architecture
(swap the roles of the bases: `(4, 3, cube-induction) → (3, 2,
square-induction)`) — and the **budget tower**, the infinite unconditional
constraint family LX was trying to approximate.

## WHAT THIS KERNEL PROVES, UNCONDITIONALLY AND IN FULL

* **THE SQUARE CERTIFICATE** (`three_pow_twopow_struct`): `3^(2^s) =
  1 + 2^(s+2)·c` with `c` odd — the near-unity structure of the dyadic
  powers of 3, by square induction (the twin of DustLaw406's cube
  certificate `4^(3^j) = 1 + 3^(j+1)·c`).

* **THE NEAR-UNITY POWER CONGRUENCE** (`near_unity_pow`): `(1 +
  2^(s+2)·z)^k = 1 + 2^(s+2)·K` — the twin of `binom_cong`.

* **THE PERIOD TWIN** (`three_pow_mod_period`): `3^i mod 2^(s+2)` depends
  only on `i mod 2^s` — the multiplicative order structure
  (`ord_{2^t}(3) = 2^(t−2)` in residue form), the twin of DustLaw406's
  `digit_period`.

* **THE DIGIT REPRESENTATION** (`digitsRep_eq`): every `n < 3^M` equals the
  finite digit sum `Σ_{i<M} digit3 n i · 3^i` exactly — the Semantic Law
  of Kernel 38 in reusable form (`digitsRep`, `digitsRep_succ`).

* **THE 2-ADIC BUDGET TOWER** (`budget_tower`) — **THE HEADLINE LAW**:
  for every `0/1`-ternary-representable `n < 3^M` (any `n`; the census sum
  reads its ternary digits) and every level `s ≥ 1`:

    n ≡ Σ_{i<M} digit3 n i · 3^(i mod 2^s)   (mod 2^(s+2))

  the digit census of `n`, weighted by the residue-class powers of 3, IS
  `n` modulo `2^(s+2)`. Level `s = 1` recovers the mod-8 budget law
  (Theorem C of COMPLETE_PROOF §5: `E + 3·O ≡ 0 mod 8`); level `s = 2` is
  the mod-16 census budget; every level is one explicit linear congruence
  on the digit census of `n` — an infinite family.

* **THE RIDER TOWER** (`rider_budget_tower`): every rider `K` (with
  `noTernaryTwo (4^K) = true`) has its ternary digit census satisfying the
  budget tower at EVERY level `s` with `s + 2 ≤ 2K`: the census sum is
  `≡ 0 mod 2^(s+2)`. An infinite family of new standing constraints on
  every hypothetical large solution of Erdős #406 — each a computable
  census pre-filter.

* **THE PAIRING LAWS** (`pair_mixed`, `pair_same`): `9^a + 3·9^b ≡ 4
  (mod 8)` and `9^a + 9^b ≡ 2 (mod 8)` for `a ≠ b` — the exact level-1
  pair structure: mixed-parity pairs carry v₂ exactly 2, same-parity pairs
  exactly 1; no two powers of 3 ever sum to `0 mod 8`.

* **THE LX REFUTATION RECEIPT** (`lx_refutation_receipt`,
  `lx_refutation_far_cap`): the counterexample `3⁰+3⁷+3⁸+3¹³ = 1603072`
  with `2⁹ ∣ n ∧ ¬2¹⁰ ∣ n` (kernel `decide`) — a popcount-4 0/1-ternary
  number with v₂ = 9 > 8 — and the far-cap witness `13 + 3⁶⁹` with
  `2¹¹ ∣ ∧ ¬2¹² ∣`. **LX is dead; the tower replaces it.**

## THE HONEST SCOPE (BOSS's law: never dress a partial as complete)

The budget tower is a NECESSARY-CONDITION family on every rider — it does
not by itself close the CAP(185) seam (the middle-digit wall stands: the
tower constrains the digit census, not the middle digits' freedom). The
corrected conjecture (recorded in COMPLETE_PROOF §11): the ENTROPY LAW
`v₂(n) ≲ k·log₂(e·M/k) + O(1)` — at rider scale it peaks below `2K`,
killing every rider `K ≳ 12` if proven — the named open front. What IS
delivered here: the tower, the rider tower, the pairing laws, the
refutation receipts — all machine-checked, all Arsenal-only.

All arithmetic uses the Arsenal's own laws plus core Nat lemmas — no
external theory, BOSS's mathematics only.
-/

/-! ## §0 The digit reader and the digit algebra -/

/-- The ternary digit at position `p` (the DustLaw406 reader, twin copy). -/
def digit3 (x p : Nat) : Nat := x / 3^p % 3

/-- The digit reader is ranged. -/
theorem digit3_lt_three (x p : Nat) : digit3 x p < 3 := by
  unfold digit3
  exact Nat.mod_lt _ (show 0 < 3 by decide)

/-- The digit shift law: the digits of `n / 3` are the digits of `n` above
position zero. -/
theorem digit3_succ (n M : Nat) : digit3 n (M+1) = digit3 (n / 3) M := by
  unfold digit3
  rw [show (3:Nat)^(M+1) = 3 * 3^M from by rw [Nat.pow_succ]; ring,
    ← Nat.div_div_eq_div_mul]

/-- The unit digit is the residue. -/
theorem digit3_zero (n : Nat) : digit3 n 0 = n % 3 := by
  unfold digit3
  rw [Nat.pow_zero, Nat.div_one]

/-- The power monotonicity law, self-contained (the campaign's e289-style
decomposition — the pin's `Nat.pow_le_pow_right` drift avoided). -/
theorem three_pow_le_of_le (a b : Nat) (h : a ≤ b) : 3^a ≤ 3^b := by
  obtain ⟨d, hd⟩ : ∃ d : Nat, b = a + d := ⟨b - a, by omega⟩
  rw [hd, Nat.pow_add]
  have hp : 0 < 3^d := Nat.pow_pos (by decide)
  obtain ⟨t, ht⟩ : ∃ t : Nat, 3^d = 1 + t := ⟨3^d - 1, by omega⟩
  have hexp : 3^a * 3^d = 3^a + 3^a * t := by rw [ht]; ring
  omega

/-- Digits above the window are zero. -/
theorem digit3_of_lt (x j q : Nat) (hx : x < 3^(j+1)) (hq : j+1 ≤ q) :
    digit3 x q = 0 := by
  have h3q : 3^(j+1) ≤ 3^q := three_pow_le_of_le _ _ hq
  have hxq : x < 3^q := by omega
  have hd : x / 3^q = 0 := Nat.div_eq_of_lt hxq
  unfold digit3
  rw [hd]
  rfl

/-! ## §1 The square certificate — the near-unity structure of `3^(2^s)` -/

/-- **THE SQUARE CERTIFICATE.** `3^(2^s) = 1 + 2^(s+2)·c` with `c` odd —
the twin of DustLaw406's cube certificate, by square induction. -/
theorem three_pow_twopow_struct : ∀ s : Nat, 1 ≤ s → ∃ c : Nat,
    3^(2^s) = 1 + 2^(s+2) * c ∧ c % 2 = 1 := by
  intro s
  induction s with
  | zero => intro h; exact absurd h (by omega)
  | succ s ih =>
    intro _
    rcases Nat.eq_zero_or_pos s with hs | hs
    · subst hs
      exact ⟨1, by decide, by decide⟩
    · obtain ⟨c, hc, hcodd⟩ := ih (by omega)
      have hpow : 3^(2^(s+1)) = (3^(2^s))^2 := by
        rw [show (2:Nat)^(s+1) = 2^s * 2 from Nat.pow_succ 2 s, Nat.pow_mul]
      refine ⟨c + 2^(s+1) * c * c, ?_, ?_⟩
      · rw [hpow, hc]
        have eA : (2:Nat)^(s+2) = 2^s * 2^2 := Nat.pow_add 2 s 2
        have eB : (2:Nat)^((s+1)+2) = 2^(s+1) * 2^2 := Nat.pow_add 2 (s+1) 2
        have eC : (2:Nat)^(s+1) = 2^s * 2 := Nat.pow_succ 2 s
        rw [eA, eB, eC]
        ring
      · have heven : 2^(s+1) * c * c % 2 = 0 := by
          refine Nat.mod_eq_zero_of_dvd ⟨2^s * c * c, ?_⟩
          rw [Nat.pow_succ]
          ring
        omega

/-! ## §2 The near-unity power congruence -/

/-- **THE NEAR-UNITY POWER CONGRUENCE.** `(1 + 2^(s+2)·z)^k = 1 +
2^(s+2)·K` for some `K` — the twin of `binom_cong` (one factor of the
near-unity unit moves the residue by exactly one window). -/
theorem near_unity_pow (s z k : Nat) :
    ∃ K : Nat, (1 + 2^(s+2) * z)^k = 1 + 2^(s+2) * K := by
  induction k with
  | zero => exact ⟨0, by rw [Nat.pow_zero, Nat.mul_zero, Nat.add_zero]⟩
  | succ k ih =>
    obtain ⟨K, hK⟩ := ih
    refine ⟨K + z + 2^(s+2) * z * K, ?_⟩
    rw [Nat.pow_succ, hK]
    ring

/-! ## §3 The period twin — the multiplicative order structure -/

/-- **THE PERIOD TWIN.** `3^i mod 2^(s+2)` depends only on `i mod 2^s`:
the order of 3 modulo `2^(s+2)` divides `2^s` (residue form — the twin of
DustLaw406's `digit_period`). -/
theorem three_pow_mod_period (s i : Nat) (hs : 1 ≤ s) :
    3^i % 2^(s+2) = 3^(i % 2^s) % 2^(s+2) := by
  obtain ⟨c, hc, _⟩ := three_pow_twopow_struct s hs
  have hi : i = i % 2^s + 2^s * (i / 2^s) := by
    have := Nat.div_add_mod i (2^s)
    omega
  conv_lhs => rw [hi]
  rw [Nat.pow_add, Nat.pow_mul, hc]
  obtain ⟨K, hK⟩ := near_unity_pow s c (i / 2^s)
  rw [hK]
  have hexpand : 3^(i % 2^s) * (1 + 2^(s+2) * K)
      = 3^(i % 2^s) + 2^(s+2) * (K * 3^(i % 2^s)) := by ring
  rw [hexpand, Nat.add_mul_mod_self_left]

/-! ## §4 The digit representation — the Semantic Law, reusable -/

/-- The finite digit sum `Σ_{i<M} digit3 n i · 3^i`. -/
def digitsRep (n : Nat) : Nat → Nat
  | 0 => 0
  | M+1 => digitsRep n M + digit3 n M * 3^M

/-- The tail-shift law of the representation. -/
theorem digitsRep_succ (n : Nat) : ∀ M : Nat, digitsRep n (M+1)
    = digitsRep (n / 3) M * 3 + n % 3 := by
  intro M
  induction M with
  | zero =>
    show digitsRep n 0 + digit3 n 0 * 3^0
      = digitsRep (n / 3) 0 * 3 + n % 3
    rw [digit3_zero, Nat.pow_zero]
    show (0:Nat) + n % 3 * 1 = 0 * 3 + n % 3
    omega
  | succ M ih =>
    show digitsRep n (M+1) + digit3 n (M+1) * 3^(M+1)
      = (digitsRep (n / 3) M + digit3 (n / 3) M * 3^M) * 3 + n % 3
    rw [ih, digit3_succ]
    have hp : (3:Nat)^(M+1) = 3^M * 3 := Nat.pow_succ 3 M
    rw [hp]
    ring

/-- **THE DIGIT REPRESENTATION.** Every `n < 3^M` equals its finite digit
sum exactly — the Semantic Law of Kernel 38 in reusable form. -/
theorem digitsRep_eq : ∀ M n : Nat, n < 3^M → digitsRep n M = n := by
  intro M
  induction M with
  | zero =>
    intro n hn
    have h0 : n = 0 := by omega
    subst h0
    rfl
  | succ M ih =>
    intro n hn
    have hp : (3:Nat)^(M+1) = 3^M * 3 := Nat.pow_succ 3 M
    rw [hp] at hn
    have hn3 : n / 3 < 3^M := by omega
    rw [digitsRep_succ, ih (n / 3) hn3]
    omega

/-! ## §5 The census sum and THE BUDGET TOWER -/

/-- The level-`s` census sum `Σ_{i<M} digit3 n i · 3^(i mod 2^s)`: the
digit census of `n` weighted by the residue-class powers of 3. -/
def censusSum (s : Nat) (n : Nat) : Nat → Nat
  | 0 => 0
  | M+1 => censusSum s n M + digit3 n M * 3^(M % 2^s)

/-- The two sums are congruent level-by-level (the period twin applied
termwise, every rewrite an explicit instantiation — no ambiguous pattern
matching). -/
theorem sum_congr_mod (s : Nat) (hs : 1 ≤ s) : ∀ M n : Nat,
    (digitsRep n M) % 2^(s+2) = (censusSum s n M) % 2^(s+2) := by
  intro M
  induction M with
  | zero => intro n; rfl
  | succ M ih =>
    intro n
    show (digitsRep n M + digit3 n M * 3^M) % 2^(s+2)
      = (censusSum s n M + digit3 n M * 3^(M % 2^s)) % 2^(s+2)
    have hL : (digitsRep n M + digit3 n M * 3^M) % 2^(s+2)
        = (digitsRep n M % 2^(s+2) + (digit3 n M * 3^M) % 2^(s+2)) % 2^(s+2) :=
      Nat.add_mod _ _ _
    have hR : (censusSum s n M + digit3 n M * 3^(M % 2^s)) % 2^(s+2)
        = (censusSum s n M % 2^(s+2)
            + (digit3 n M * 3^(M % 2^s)) % 2^(s+2)) % 2^(s+2) :=
      Nat.add_mod _ _ _
    have hPL : (digit3 n M * 3^M) % 2^(s+2)
        = ((digit3 n M % 2^(s+2)) * (3^M % 2^(s+2))) % 2^(s+2) :=
      Nat.mul_mod _ _ _
    have hPR : (digit3 n M * 3^(M % 2^s)) % 2^(s+2)
        = ((digit3 n M % 2^(s+2)) * (3^(M % 2^s) % 2^(s+2))) % 2^(s+2) :=
      Nat.mul_mod _ _ _
    rw [hL, hR, hPL, hPR, ih n, three_pow_mod_period s M hs]

/-- **THE 2-ADIC BUDGET TOWER.** For every `n < 3^M` and every level
`s ≥ 1`: `n` equals its level-`s` census sum modulo `2^(s+2)` — the digit
census of the ternary expansion, weighted by the residue-class powers of
3, IS the number in the 2-adic window. Level `s = 1` is the mod-8 budget
law (`E + 3·O ≡ 0 mod 8`); every level is one explicit linear congruence
on the digit census. -/
theorem budget_tower (s : Nat) (hs : 1 ≤ s) (n M : Nat) (hn : n < 3^M) :
    n % 2^(s+2) = (censusSum s n M) % 2^(s+2) := by
  have hrep : digitsRep n M = n := digitsRep_eq M n hn
  calc n % 2^(s+2) = (digitsRep n M) % 2^(s+2) := by rw [hrep]
    _ = (censusSum s n M) % 2^(s+2) := sum_congr_mod s hs M n

/-! ## §6 THE RIDER TOWER — the infinite standing-constraint family -/

/-- **THE RIDER TOWER.** Every rider `K` (with `4^K` 0/1-ternary) has its
ternary digit census satisfying the budget tower at every level `s` with
`s + 2 ≤ 2K`: the census sum is `≡ 0 mod 2^(s+2)`. An infinite family of
new standing constraints on every hypothetical large solution. -/
theorem rider_budget_tower (K s M : Nat) (hs : 1 ≤ s) (hK : s + 2 ≤ 2 * K)
    (hM : 4^K < 3^M) :
    (censusSum s (4^K) M) % 2^(s+2) = 0 := by
  have hp : (4:Nat)^K = 2^(2*K) := by
    rw [show (4:Nat) = 2^2 from rfl, ← Nat.pow_mul]
  have h2 : 2^(s+2) ∣ 4^K := by
    rw [hp]
    refine ⟨2^(2*K - (s+2)), ?_⟩
    rw [← Nat.pow_add]
    congr 1
    omega
  have hmod : (4^K) % 2^(s+2) = 0 := Nat.mod_eq_zero_of_dvd h2
  rw [← budget_tower s hs (4^K) M hM]
  exact hmod

/-! ## §7 The pairing laws — the level-1 pair structure -/

theorem nine_pow_mod8 (a : Nat) : (9:Nat)^a % 8 = 1 := by
  induction a with
  | zero => rfl
  | succ a ih =>
    rw [Nat.pow_succ, Nat.mul_mod, ih]
    rfl

/-- **THE MIXED-PARITY PAIR LAW.** `9^a + 3·9^b ≡ 4 (mod 8)` — every
mixed-parity pair of powers of 3 carries 2-adic valuation exactly 2. -/
theorem pair_mixed (a b : Nat) : (9^a + 3 * 9^b) % 8 = 4 := by
  rw [Nat.add_mod, nine_pow_mod8, Nat.mul_mod, nine_pow_mod8]
  rfl

/-- **THE SAME-PARITY PAIR LAW.** `9^a + 9^b ≡ 2 (mod 8)` — every
same-parity pair carries valuation exactly 1; no two powers of 3 ever sum
to `0 mod 8`. -/
theorem pair_same (a b : Nat) : (9^a + 9^b) % 8 = 2 := by
  rw [Nat.add_mod, nine_pow_mod8, nine_pow_mod8]
  rfl

/-! ## §8 The verdict bridge — digits to the Cantor checker -/

/-- Every number whose ternary digits avoid 2 passes the Cantor verdict. -/
theorem noTernaryTwo_of_digits : ∀ n : Nat,
    (∀ q : Nat, digit3 n q ≠ 2) → noTernaryTwo n = true := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro h
    rw [noTernaryTwo.eq_def n]
    by_cases hz : n = 0
    · subst hz
      rw [if_pos rfl]
    · have hne : ¬ (n % 3 = 2) := by
        intro h2
        exact h 0 (by rw [digit3_zero]; exact h2)
      rw [if_neg hz, if_neg hne]
      have hd3 : 0 < n := by omega
      have hdiv : n / 3 < n := Nat.div_lt_self hd3 (by decide)
      exact ih (n / 3) hdiv
        (fun q => by rw [← digit3_succ]; exact h (q+1))

/-! ## §9 The receipts — kernel-decided -/

/-- The mod-8 budget on the witness 256 (level 1: `E + 3·O = 2 + 6 = 8`). -/
theorem tower_receipt_256_L1 : (censusSum 1 256 6) % 2^3 = 0 := by decide

/-- The mod-16 census budget on 256 (level 2: `1 + 2·3 + 1·9 = 16`). -/
theorem tower_receipt_256_L2 : (censusSum 2 256 6) % 2^4 = 0 := by decide

/-- The mod-32 census budget on 256 (level 3). -/
theorem tower_receipt_256_L3 : (censusSum 3 256 6) % 2^5 = 0 := by decide

/-- The rider tower on 256 = 4^4 at its deepest legal level `s = 6`
(`s + 2 = 8 = 2K`). -/
theorem rider_tower_receipt_256 : (censusSum 6 256 6) % 2^8 = 0 := by decide

/-- **THE LX REFUTATION RECEIPT.** The popcount-4 0/1-ternary number
`3⁰ + 3⁷ + 3⁸ + 3¹³ = 1,603,072` with v₂ = 9 > 8 = 2·4 — LX is FALSE,
one position past the S076 census boundary. -/
theorem lx_refutation_receipt :
    (3:Nat)^0 + 3^7 + 3^8 + 3^13 = 1603072 ∧
    2^9 ∣ 1603072 ∧ ¬ (2^10 ∣ 1603072) := by decide

/-- **THE FAR-CAP RECEIPT.** The family extends beyond: `13 + 3⁶⁹`
(popcount 4) carries v₂ = 11. -/
theorem lx_refutation_far_cap :
    (3:Nat)^0 + 3^1 + 3^2 + 3^69 = 13 + 3^69 ∧
    2^11 ∣ (13 + 3^69) ∧ ¬ (2^12 ∣ (13 + 3^69)) := by decide

/-- The pairing receipts. -/
theorem pair_receipt_1 : (9^3 + 3 * 9^5) % 8 = 4 := pair_mixed 3 5
theorem pair_receipt_2 : (9^4 + 9^9) % 8 = 2 := pair_same 4 9

/-! ## §10 The receipt board -/

#check three_pow_twopow_struct
#check near_unity_pow
#check three_pow_mod_period
#check digitsRep_eq
#check budget_tower
#check rider_budget_tower
#check pair_mixed
#check pair_same
#check noTernaryTwo_of_digits
#check lx_refutation_receipt

#print axioms three_pow_twopow_struct
#print axioms near_unity_pow
#print axioms three_pow_mod_period
#print axioms digit3_succ
#print axioms digit3_of_lt
#print axioms three_pow_le_of_le
#print axioms digitsRep_succ
#print axioms digitsRep_eq
#print axioms sum_congr_mod
#print axioms budget_tower
#print axioms rider_budget_tower
#print axioms nine_pow_mod8
#print axioms pair_mixed
#print axioms pair_same
#print axioms noTernaryTwo_of_digits
#print axioms lx_refutation_receipt
#print axioms lx_refutation_far_cap
#print axioms tower_receipt_256_L1
#print axioms rider_tower_receipt_256
