import Arsenal.ErdosTernary2.Basic
import Arsenal.CardinalWorlds
import Arsenal.CardinalWorldsV2

-- Family pattern (green kernels K38/K68/DustLaw): explicit depth headroom.
set_option maxRecDepth 262144
set_option maxHeartbeats 4000000

/-!
# ERDŐS #406 — THE RIDER-CONSTRAINT-LAW KERNEL (S076, Kernel 69)

## THE SOURCE (BOSS's order: "crack the HFTAIL hypothesis completely")

The `hTailF` hypothesis (= `the_act` = CAP(185)-class = the remaining open seam
of the #406 assembly) is the middle-digit wall: every named surface of the
hypothesis reduces to the fresh digits of `4^K` in the position band
`[log₃ K, 1.26K]`.  This kernel banks the S076 war council's extraction:
five new unconditional necessary-condition laws on every hypothetical rider —
each machine-checked here, each sharpening every future census, each
constraining the CAP(185) target from a different side.

## WHAT THIS KERNEL PROVES, UNCONDITIONALLY AND IN FULL

* **§1 THE LEVEL LAW** (`noTernaryTwo_lvl`): every level-`j` ternary digit of
  a `0/1`-ternary number is not `2` — the digit-by-digit unfold of the
  checker, stated at every depth `j`.

* **§2 THE HALF-LINE LAW (L1 — the fractional law)** (`cantor_half_line`,
  `rider_half_line`, `erdos406_half_line_kill`): every positive `0/1`-ternary
  `n` satisfies `2·n < 3^(ternaryLog3 n + 1)` — the Cantor number sits
  strictly in the lower half of its leading range.  For a rider `K` this
  forces `{K·log₃ 4} < 1 − log₃ 2 ≈ 0.36907`; the kill form eliminates every
  exponent `K` with `3^(ternaryLog3 (4^K) + 1) ≤ 2·4^K` — an infinite family
  (battery-certified density `63.09%` on `[200001, 10^6]`).

* **§3 THE TAIL LAW (L2)** (`noTernaryTwo_div_pow3`, `rider_tail_law`): the
  high-digit truncation `n / 3^c` of a `0/1`-ternary number is `0/1`-ternary.
  Rider form: `⌊4^K / 3^(K+1)⌋ = ⌊(4/3)^K / 3⌋` is a Cantor number — a NEW
  necessary condition on the top `0.26K` digits (the carry-only zone above
  position `K`).

* **§4 THE MOD-9 CYCLE AND THE CONSECUTIVE-RIDER LAWS (L4/L5)**
  (`pow4_mod9`, `rider_mod3_ne_two`, `no_three_consecutive_riders`,
  `consecutive_riders_mod3_gap`): `4^r mod 9` is `1, 4, 7` as `r ≡ 0, 1, 2
  (mod 3)`; every rider has `r ≢ 2 (mod 3)`; NO THREE CONSECUTIVE riders
  exist; consecutive riders `r, r+1` force `r ≡ 0 (mod 3)`.

* **§5 THE CANTOR T²-LAW** (`cantor_T2_mod3`): for every `0/1`-ternary `u`,
  not both `4u+1` and `16u+5` are `0/1`-ternary — pure mod-3 arithmetic
  (`4u+1 ≡ u+1`, `16u+5 ≡ u+2 (mod 3)`).

* **§6 THE ADJACENT-ONES KILL LAW (L3 — the repunit no-carry engine)**
  (`adjacent_ones_kill`): if `u`'s ternary digits at positions `j−1, j` are
  both `1` (`u ≡ 3^(j−1) + 3^j (mod 3^(j+1))`, `j ≥ 1`), then `4u+1` owns
  the digit `2` at position `j` — DEAD.  This is the digit-exact form of the
  repunit no-carry law: for `0/1`-ternary `u` the ternary digits of `4u+1`
  are `e_0 = d_0 + 1` and `e_i = d_i + d_{i−1}` (no carries, since every
  `e_i ≤ 2 < 3`), so every adjacent `1`-pair produces the dead digit.

## THE HONEST SCOPE (BOSS's law: no dressing)

These are necessary-condition laws — they sharpen the standing constraint
set on every hypothetical rider (the census extension to `10^6` rides the
§2 pre-filter; the §4/§6 laws thin the rider-set structure), but the
middle-digit wall itself (CAP(185) / the anti-concentration core) remains
the named open seam.  Nothing here should be read as closing it.

All arithmetic is the Arsenal's own readers (`noTernaryTwo`, `ternaryLog3`)
plus core Nat lemmas — BOSS's mathematics only, no external theory.
-/

/-! ## §1 THE LEVEL LAW — the digit-by-digit engine -/

/-- **THE LEVEL LAW.**  Every level-`j` ternary digit of a `0/1`-ternary
number is not `2` — the checker's verdict, extracted at every depth. -/
theorem noTernaryTwo_lvl (n : Nat) :
    noTernaryTwo n = true → ∀ j : Nat, (n / 3^j) % 3 ≠ 2 := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro h j
    by_cases hn : n = 0
    · subst hn
      have hz : (0:Nat) / 3^j = 0 := Nat.zero_div _
      rw [hz]
      omega
    · have hn0 : n ≠ 0 := hn
      rw [noTernaryTwo.eq_def n, if_neg hn0] at h
      by_cases h2 : n % 3 = 2
      · rw [if_pos h2] at h
        simp at h
      · rw [if_neg h2] at h
        match j with
        | 0 =>
            have e : n / 3^0 = n := by rw [Nat.pow_zero, Nat.div_one]
            rw [e]
            omega
        | j + 1 =>
            have hrec := ih (n / 3) (Nat.div_lt_self (by omega)
              (by decide : 1 < 3)) h j
            have e : n / 3^(j+1) = (n / 3) / 3^j := by
              rw [Nat.div_div_eq_div_mul, Nat.pow_succ 3 j,
                Nat.mul_comm 3 (3^j)]
            rw [e]
            exact hrec

/-! ## §2 THE HALF-LINE LAW (L1) — the fractional cut -/

/-- **THE HALF-LINE LAW.**  Every positive `0/1`-ternary number `n` satisfies
`2·n < 3^(ternaryLog3 n + 1)`: the Cantor number sits strictly in the lower
half of its leading range.  (For a rider `K` this is
`2·4^K < 3^(⌊log₃ 4^K⌋ + 1)`, i.e. `{K·log₃ 4} < 1 − log₃ 2 ≈ 0.36907` —
the law kills every exponent whose leading fractional lands in the upper
band, forever.) -/
theorem cantor_half_line (n : Nat) :
    0 < n → noTernaryTwo n = true → 2 * n < 3^(ternaryLog3 n + 1) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro hn h
    by_cases h3 : n < 3
    · rw [ternaryLog3.eq_def n, if_pos h3]
      have e3 : (3:Nat)^(0 + 1) = 3 := by decide
      rw [noTernaryTwo.eq_def n] at h
      by_cases hn0 : n = 0
      · omega
      · rw [if_neg hn0] at h
        by_cases h2 : n % 3 = 2
        · rw [if_pos h2] at h; simp at h
        · rw [if_neg h2] at h
          omega
    · have hn0 : n ≠ 0 := by omega
      rw [noTernaryTwo.eq_def n, if_neg hn0] at h
      by_cases h2 : n % 3 = 2
      · rw [if_pos h2] at h; simp at h
      · rw [if_neg h2] at h
        have hdiv : 0 < n / 3 := by omega
        have hrec := ih (n / 3) (Nat.div_lt_self (by omega)
          (by decide : 1 < 3)) hdiv h
        have hlog : ternaryLog3 n = 1 + ternaryLog3 (n / 3) := by
          rw [ternaryLog3.eq_def n, if_neg h3]
        have hdm : n = 3 * (n / 3) + n % 3 := (Nat.div_add_mod n 3).symm
        have hm : n % 3 ≤ 1 := by omega
        have hA : (3:Nat)^(1 + ternaryLog3 (n/3) + 1)
            = 9 * 3^(ternaryLog3 (n/3)) := by
          have er : 1 + ternaryLog3 (n/3) + 1 = ternaryLog3 (n/3) + 2 := by omega
          have e2 : (3:Nat)^2 = 9 := by decide
          rw [er, Nat.pow_add, e2]
          ring
        have hB : (3:Nat)^(ternaryLog3 (n/3) + 1)
            = 3 * 3^(ternaryLog3 (n/3)) := by
          have e3 : (3:Nat)^1 = 3 := Nat.pow_one 3
          rw [Nat.pow_add, e3]
          ring
        rw [hlog]
        rw [hA]
        rw [hB] at hrec
        omega

/-- **THE RIDER HALF-LINE LAW (L1).**  Every rider `K` (`4^K` a `0/1`-ternary
number) satisfies `2·4^K < 3^(ternaryLog3 (4^K) + 1)` — the leading
fractional `{K·log₃ 4}` is confined to `[0, 1 − log₃ 2)`. -/
theorem rider_half_line (K : Nat)
    (hRider : noTernaryTwo (4^K) = true) :
    2 * 4^K < 3^(ternaryLog3 (4^K) + 1) :=
  cantor_half_line (4^K) (Nat.pow_pos (by decide)) hRider

/-- **THE KILL FORM.**  Every exponent `K` whose double `2·4^K` reaches the
next ternary power is dead: `noTernaryTwo (4^K) = false`.  This is the
contrapositive of the half-line law — an infinite-family kill lane with
per-exponent integer certificates. -/
theorem erdos406_half_line_kill (K : Nat)
    (hGe : 3^(ternaryLog3 (4^K) + 1) ≤ 2 * 4^K) :
    noTernaryTwo (4^K) = false := by
  by_contra hRider
  have hTrue : noTernaryTwo (4^K) = true := by
    cases hh : noTernaryTwo (4^K) with
    | false => exact absurd hh hRider
    | true => rfl
  have hlt := rider_half_line K hTrue
  omega

/-! ## §3 THE TAIL LAW (L2) — the high-digit truncation -/

/-- **THE TAIL LAW.**  The high-digit truncation `n / 3^c` of a `0/1`-ternary
number is `0/1`-ternary (the digit recursion is prefix-closed under
right-shift). -/
theorem noTernaryTwo_div_pow3 : ∀ (n : Nat), noTernaryTwo n = true →
    ∀ c : Nat, noTernaryTwo (n / 3^c) = true := by
  intro n h c
  induction c generalizing n with
  | zero =>
      rw [Nat.pow_zero, Nat.div_one]
      exact h
  | succ c ih =>
      have e : n / 3^(c+1) = (n / 3) / 3^c := by
        rw [Nat.div_div_eq_div_mul, Nat.pow_succ 3 c,
          Nat.mul_comm 3 (3^c)]
      rw [e]
      rw [noTernaryTwo.eq_def n] at h
      by_cases hn : n = 0
      · subst hn
        have h1 : (0:Nat) / 3 = 0 := Nat.zero_div 3
        have hz : (0:Nat) / 3 / 3^c = 0 := by
          rw [h1]
          exact Nat.zero_div _
        rw [hz]
        rw [noTernaryTwo.eq_def 0, if_pos rfl]
      · rw [if_neg hn] at h
        by_cases h2 : n % 3 = 2
        · rw [if_pos h2] at h; simp at h
        · rw [if_neg h2] at h
          exact ih (n / 3) h

/-- **THE RIDER TAIL LAW (L2).**  For every rider `K`, the top-zone number
`⌊4^K / 3^(K+1)⌋ = ⌊(4/3)^K / 3⌋` is `0/1`-ternary — a NEW necessary
condition on the carry-only top `0.26K` digits of the rider's expansion. -/
theorem rider_tail_law (K : Nat) (hRider : noTernaryTwo (4^K) = true) :
    noTernaryTwo (4^K / 3^(K+1)) = true :=
  noTernaryTwo_div_pow3 (4^K) hRider (K + 1)

/-! ## §4 THE MOD-9 CYCLE AND THE CONSECUTIVE-RIDER LAWS (L4/L5) -/

/-- **THE MOD-9 CYCLE.**  `4^r mod 9` is `1, 4, 7` according as
`r ≡ 0, 1, 2 (mod 3)`. -/
theorem pow4_mod9 (r : Nat) :
    (r % 3 = 0 ∧ 4^r % 9 = 1) ∨
    (r % 3 = 1 ∧ 4^r % 9 = 4) ∨
    (r % 3 = 2 ∧ 4^r % 9 = 7) := by
  have hcycle : ∀ r : Nat, 4^(r+3) % 9 = 4^r % 9 := by
    intro r
    have e : 4^(r+3) = 4^r * 4^3 := by
      rw [← Nat.pow_add]
    have h64 : (4:Nat)^3 % 9 = 1 := by decide
    rw [e, Nat.mul_mod, Nat.mul_mod, h64, Nat.mul_one]
    omega
  induction r using Nat.strongRecOn with
  | ind r ih =>
    rcases Nat.lt_or_ge r 3 with hlt | hge
    · rcases ErdosTernary2.lt_three_cases r hlt with h | h | h
      · subst h
        exact Or.inl ⟨by omega, by decide⟩
      · subst h
        exact Or.inr (Or.inl ⟨by omega, by decide⟩)
      · subst h
        exact Or.inr (Or.inr ⟨by omega, by decide⟩)
    · have hrm : r = (r - 3) + 3 := by omega
      rw [hrm, hcycle (r - 3)]
      rcases ih (r - 3) (by omega) with ⟨h0, hm⟩ | ⟨h1, hm⟩ | ⟨h2, hm⟩
      · exact Or.inl ⟨by omega, hm⟩
      · exact Or.inr (Or.inl ⟨by omega, hm⟩)
      · exact Or.inr (Or.inr ⟨by omega, hm⟩)

/-- **THE RIDER MOD-3 LAW.**  Every rider `r` satisfies `r % 3 ≠ 2`: the
second-level digit of `4^r` reads the mod-9 residue `7` as the dead digit
`2` at position `1`. -/
theorem rider_mod3_ne_two (r : Nat)
    (hRider : noTernaryTwo (4^r) = true) : r % 3 ≠ 2 := by
  intro h2
  rcases pow4_mod9 r with ⟨h0, hm⟩ | ⟨h1, hm⟩ | ⟨h2r, hm⟩
  · omega
  · omega
  · have hdm := Nat.div_add_mod (4^r) 9
    have hrec := noTernaryTwo_lvl (4^r) hRider 1
    rw [Nat.pow_one] at hrec
    omega

/-- **NO THREE CONSECUTIVE RIDERS.**  Riders at `K`, `K+1`, `K+2` cannot
coexist: every rider avoids the residue `2 (mod 3)`, and any three
consecutive integers cover all three residues. -/
theorem no_three_consecutive_riders (K : Nat)
    (hK : noTernaryTwo (4^K) = true)
    (hK1 : noTernaryTwo (4^(K+1)) = true)
    (hK2 : noTernaryTwo (4^(K+2)) = true) : False := by
  have e0 := rider_mod3_ne_two K hK
  have e1 := rider_mod3_ne_two (K+1) hK1
  have e2 := rider_mod3_ne_two (K+2) hK2
  have hdm : K = 3 * (K / 3) + K % 3 := (Nat.div_add_mod K 3).symm
  have hK3 : K % 3 < 3 := by omega
  rcases ErdosTernary2.lt_three_cases (K % 3) hK3 with h | h | h
  · omega
  · omega
  · omega

/-- **THE MOD-3 GAP LAW.**  Consecutive riders `K, K+1` force
`K ≡ 0 (mod 3)`. -/
theorem consecutive_riders_mod3_gap (K : Nat)
    (hK : noTernaryTwo (4^K) = true)
    (hK1 : noTernaryTwo (4^(K+1)) = true) : K % 3 = 0 := by
  have e0 := rider_mod3_ne_two K hK
  have e1 := rider_mod3_ne_two (K+1) hK1
  have hdm : K = 3 * (K / 3) + K % 3 := (Nat.div_add_mod K 3).symm
  have hK3 : K % 3 < 3 := by omega
  rcases ErdosTernary2.lt_three_cases (K % 3) hK3 with h | h | h
  · omega
  · omega
  · omega

/-! ## §5 THE CANTOR T²-LAW — pure mod-3 arithmetic -/

/-- The units digit of a `0/1`-ternary number is not `2` (the level-0 law,
with the `n = 0` edge). -/
theorem cantor_mod3_ne_two (u : Nat) (h : noTernaryTwo u = true) :
    u % 3 ≠ 2 := by
  rw [noTernaryTwo.eq_def u] at h
  by_cases hu : u = 0
  · subst hu; omega
  · rw [if_neg hu] at h
    by_cases h2 : u % 3 = 2
    · rw [if_pos h2] at h; simp at h
    · omega

/-- **THE CANTOR T²-LAW.**  For every `0/1`-ternary `u`, not both `4u+1`
and `16u+5` are `0/1`-ternary.  (The digit-0 arithmetic:
`4u+1 ≡ u+1`, `16u+5 ≡ u+2 (mod 3)` — the two conditions force
`u ≢ 1` and `u ≢ 0 (mod 3)`, contradicting the Cantor units digit.) -/
theorem cantor_T2_mod3 (u : Nat) (h : noTernaryTwo u = true) :
    ¬ (noTernaryTwo (4*u+1) = true ∧ noTernaryTwo (16*u+5) = true) := by
  intro hp
  obtain ⟨h1, h5⟩ := hp
  have hu := cantor_mod3_ne_two u h
  have hu1 := cantor_mod3_ne_two (4*u+1) h1
  have hu5 := cantor_mod3_ne_two (16*u+5) h5
  have e1 : (4*u+1) % 3 = (u+1) % 3 := by omega
  have e5 : (16*u+5) % 3 = (u+2) % 3 := by omega
  have hu3 : u % 3 < 3 := by omega
  rcases ErdosTernary2.lt_three_cases (u % 3) hu3 with h | h | h
  · omega
  · omega
  · omega

/-! ## §6 THE ADJACENT-ONES KILL LAW (L3) — the no-carry engine -/

/-- **THE ADJACENT-ONES KILL LAW.**  If `u`'s ternary digits at positions
`j−1` and `j` are both `1` (i.e. `u ≡ 3^(j−1) + 3^j (mod 3^(j+1))`, `j ≥ 1`),
then `4u+1` owns the digit `2` at position `j` — it is NOT `0/1`-ternary.
This is the digit-exact form of the repunit no-carry law: for `0/1`-ternary
`u` the ternary digits of `4u+1` are `e_0 = d_0 + 1` and `e_i = d_i + d_{i−1}`
with no carries (every `e_i ≤ 2 < 3`), so every adjacent `1`-pair produces
the dead digit. -/
theorem adjacent_ones_kill (u j : Nat) (hj : 1 ≤ j)
    (hu : u % 3^(j+1) = 3^(j-1) + 3^j) :
    noTernaryTwo (4*u+1) = false := by
  by_contra hRider
  have hTrue : noTernaryTwo (4*u+1) = true := by
    cases hh : noTernaryTwo (4*u+1) with
    | false => exact absurd hh hRider
    | true => rfl
  obtain ⟨d, hd⟩ : ∃ d, j = d + 1 := ⟨j - 1, by omega⟩
  subst hd
  have hu' : u % 3^(d+2) = 3^d + 3^(d+1) := by
    have e1 : (d:Nat) + 1 + 1 = d + 2 := by omega
    have e2 : (d:Nat) + 1 - 1 = d := by omega
    rw [e1, e2] at hu
    exact hu
  -- the division decomposition, with the quotient opaque
  have hq : 3^(d+2) * (u / 3^(d+2)) + u % 3^(d+2) = u :=
    Nat.div_add_mod u (3^(d+2))
  rw [hu'] at hq
  -- the key identity: 4u+1 = 3^(d+1) * (12w + 5) + (3^d + 1)
  have hkey : 4 * u + 1
      = 3^(d+1) * (12 * (u / 3^(d+2)) + 5) + (3^d + 1) := by
    have h31 : 3^(d+1) = 3 * 3^d := by
      rw [Nat.pow_succ 3 d]
      ring
    have h32 : 3^(d+2) = 9 * 3^d := by
      rw [Nat.pow_add 3 d 2]
      have e2 : (3:Nat)^2 = 9 := by decide
      rw [e2]
      ring
    rw [h31] at hq ⊢
    rw [h32] at hq ⊢
    linear_combination (-4) * hq
  -- the digit at position d+1 is exactly 2
  have hdig : (4*u+1) / 3^(d+1) % 3 = 2 := by
    have hp : 0 < 3^(d+1) := Nat.pow_pos (by decide)
    rw [hkey]
    rw [mul_add_div_lemma (12 * (u / 3^(d+2)) + 5) (3^d + 1)
      (3^(d+1)) hp]
    have hlt : 3^d + 1 < 3^(d+1) := by
      rw [Nat.pow_succ 3 d]
      have hs : 0 < 3^d := Nat.pow_pos (by decide)
      omega
    rw [Nat.div_eq_of_lt hlt]
    omega
  have hrec := noTernaryTwo_lvl (4*u+1) hTrue (d+1)
  omega

/-! ## §7 THE RECEIPTS -/

#check noTernaryTwo_lvl
#check cantor_half_line
#check rider_half_line
#check erdos406_half_line_kill
#check noTernaryTwo_div_pow3
#check rider_tail_law
#check pow4_mod9
#check rider_mod3_ne_two
#check no_three_consecutive_riders
#check consecutive_riders_mod3_gap
#check cantor_mod3_ne_two
#check cantor_T2_mod3
#check adjacent_ones_kill

#print axioms noTernaryTwo_lvl
#print axioms cantor_half_line
#print axioms rider_half_line
#print axioms erdos406_half_line_kill
#print axioms noTernaryTwo_div_pow3
#print axioms rider_tail_law
#print axioms pow4_mod9
#print axioms rider_mod3_ne_two
#print axioms no_three_consecutive_riders
#print axioms consecutive_riders_mod3_gap
#print axioms cantor_mod3_ne_two
#print axioms cantor_T2_mod3
#print axioms adjacent_ones_kill

-- Kill receipts: exponents dead by fact (struct-eval, kernel-decided —
-- the half-line family members 6, 7, 10, 11, 12 are all dead).
theorem half_line_kill_6 : noTernaryTwo (4^6) = false := by
  rw [noTernaryTwo_eq_struct (4^6) 4097 (by decide)]
  decide
theorem half_line_kill_7 : noTernaryTwo (4^7) = false := by
  rw [noTernaryTwo_eq_struct (4^7) 16385 (by decide)]
  decide
theorem half_line_kill_10 : noTernaryTwo (4^10) = false := by
  rw [noTernaryTwo_eq_struct (4^10) 1048577 (by decide)]
  decide
theorem half_line_kill_11 : noTernaryTwo (4^11) = false := by
  rw [noTernaryTwo_eq_struct (4^11) 4194305 (by decide)]
  decide
theorem half_line_kill_12 : noTernaryTwo (4^12) = false := by
  rw [noTernaryTwo_eq_struct (4^12) 16777217 (by decide)]
  decide

-- Rider receipts: the three known riders satisfy every law of this kernel.
theorem rider_receipt_0 : noTernaryTwo (4^0) = true := by
  rw [noTernaryTwo_eq_struct (4^0) 2 (by decide)]
  decide
theorem rider_receipt_1 : noTernaryTwo (4^1) = true := by
  rw [noTernaryTwo_eq_struct (4^1) 5 (by decide)]
  decide
theorem rider_receipt_4 : noTernaryTwo (4^4) = true := by
  rw [noTernaryTwo_eq_struct (4^4) 257 (by decide)]
  decide
theorem rider_half_line_receipt_0 :
    2 * 4^0 < 3^(ternaryLog3 (4^0) + 1) :=
  rider_half_line 0 rider_receipt_0
theorem rider_half_line_receipt_1 :
    2 * 4^1 < 3^(ternaryLog3 (4^1) + 1) :=
  rider_half_line 1 rider_receipt_1
theorem rider_half_line_receipt_4 :
    2 * 4^4 < 3^(ternaryLog3 (4^4) + 1) :=
  rider_half_line 4 rider_receipt_4
theorem rider_tail_receipt_1 : noTernaryTwo (4^1 / 3^2) = true :=
  rider_tail_law 1 rider_receipt_1
theorem rider_tail_receipt_4 : noTernaryTwo (4^4 / 3^5) = true :=
  rider_tail_law 4 rider_receipt_4

#print axioms half_line_kill_6
#print axioms half_line_kill_7
#print axioms half_line_kill_10
#print axioms half_line_kill_11
#print axioms half_line_kill_12
#print axioms rider_receipt_0
#print axioms rider_receipt_1
#print axioms rider_receipt_4
#print axioms rider_half_line_receipt_0
#print axioms rider_half_line_receipt_1
#print axioms rider_half_line_receipt_4
#print axioms rider_tail_receipt_1
#print axioms rider_tail_receipt_4
