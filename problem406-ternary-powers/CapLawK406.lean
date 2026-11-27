import Arsenal.ErdosTernary2.Basic
import Arsenal.CardinalWorlds
import Arsenal.CardinalWorldsV2

-- Family pattern (green kernels): explicit depth headroom.
set_option maxRecDepth 262144
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 1000

/-!
# ERDŐS #406 — THE SMALL-DIGIT CAP LAWS (S094, the council's ATTACKER round)

## THE ORDER

BOSS order (S094): crack the hTailF hypothesis completely — the HFTAIL
family, `erdos_406_the_last_hypothesis := ¬ ∃ K ≥ 8, CantorianPower K`.
The kill chain (Kernel 68, `CapLaw406.lean`): **any provable explicit cap
constant C ≤ 185 closes Erdős #406 outright** through the composition with
the green Kernel-38 census.  This kernel opens the CAP frontier's FIRST
UNCONDITIONAL BLOCK: the exact small-digit laws, all levels, all scales,
zero hypotheses.

## WHAT THIS KERNEL PROVES (new mathematics, S094, BOSS's laws only)

The cap question lives on the $0/1$-ternary numbers $n = \sum_{i \in S} 3^i$
(the Arsenal's own reading: `noTernaryTwo` ⟺ distinct-powers-of-3 value).
The $v_2$ of such a sum depends only on the PARITY STRUCTURE of the digit
positions — and at small digit count $k = |S|$ the dependence is total:

* **§1 THE ODD-POPCOUNT LAW** (`v2r_pow3_sum_odd_length`): every $0/1$-ternary
  number with an ODD number of ternary digits set is ODD — $v_2 = 0$,
  exactly.  (Every $3^i \equiv 1 \pmod 2$; a sum of $k$ of them is
  $k \bmod 2$.)  HALF THE SUBSET LATTICE IS VALUATION-DEAD: every cap
  constant $C \ge 0$ already holds on the entire odd-$k$ family.

* **§2 THE PAIR LAW — EXACT** (`v2r_pair`): for $b < a$,
  $v_2(3^a + 3^b) = 2$ if $a - b$ is odd, $= 1$ if $a - b$ is even —
  the complete classification of the 2-digit family.  The mechanism: the
  8-period of the powers of three (`three_pow_mod_eight`) read through
  the Arsenal's own LTE factoring `v2r_mul_three_pow`.  CAP form
  (`cap_pair`): the 2-digit family obeys the cap with constant $C = 2$
  at every scale.

* **§3 THE PRODUCT-QUADRUPLE LAW** (`v2r_product_four`): the 4-digit
  product family $n = (1 + 3^x)(1 + 3^y) = 1 + 3^x + 3^y + 3^{x+y}$
  obeys $v_2 \le 4$ — the multiplicativity of `v2r` (§0, self-contained:
  the $2^t$-decomposition engine) composed with the one-plus-power law.
  CAP form (`cap_product_four`): constant $C = 4$ on the whole family.

* **§0 THE ENGINE** — self-contained $v_2$ theory in the Arsenal's own
  terms: the odd characterization, the mod-8 valuation levels, the full
  multiplicativity law `v2r_mul` ($v_2(ab) = v_2(a) + v_2(b)$ via the
  $2^t$-decomposition), the 8-period of the powers of three.

## THE HONEST SCOPE (the frontier map)

The odd law kills half the lattice outright; the pair law classifies
$k = 2$ completely (max $v_2 = 2$, witnessed by $1 + 3 = 4 = 2^2$); the
product law caps the factorable 4-digit family at 4.  The open CAP core
begins at the NON-PRODUCT 4-digit shapes (the far-cap dlog family,
$v_2 \sim \log_2 M$ empirically) and the $k \ge 6$ block constructions
(the MITM extremals).  Every law here is UNCONDITIONAL — all digit
positions, all scales, zero hypotheses — the assault base for the
remaining even-$k \ge 4$ core.

All arithmetic is the Arsenal's own readers (`v2r`, `ternaryLog3`) plus
core Nat lemmas — BOSS's mathematics only, no external theory, no
classical methods.
-/

namespace CapLawK406

-- (the r4 receipt: Arsenal/CardinalWorlds.lean declares everything at ROOT —
-- no namespace to open; `v2r`, `ternaryLog3` resolve directly)

/-! ## §0 The engine — self-contained `v2r` theory -/

/-- **The odd characterization.**  An odd number has `v2r = 0`. -/
theorem v2r_eq_zero_of_odd {n : Nat} (h : n % 2 = 1) : v2r n = 0 := by
  rw [v2r.eq_def n, if_neg (by omega : ¬ n = 0),
    if_neg (by omega : ¬ n % 2 = 0)]

/-- **The mod-8 level one.**  `n % 8 = 2` forces `v2r n = 1`. -/
theorem v2r_eq_one_of_mod_eight {n : Nat} (h : n % 8 = 2) : v2r n = 1 := by
  have h0 : ¬ n = 0 := by omega
  have h1 : n % 2 = 0 := by omega
  have hd1 : ¬ n / 2 = 0 := by omega
  have hd2 : ¬ (n / 2) % 2 = 0 := by omega
  rw [v2r.eq_def n, if_neg h0, if_pos h1, v2r.eq_def (n / 2),
    if_neg hd1, if_neg hd2]

/-- **The mod-8 level two.**  `n % 8 = 4` forces `v2r n = 2`. -/
theorem v2r_eq_two_of_mod_eight {n : Nat} (h : n % 8 = 4) : v2r n = 2 := by
  have h0 : ¬ n = 0 := by omega
  have h1 : n % 2 = 0 := by omega
  have hd1 : ¬ n / 2 = 0 := by omega
  have hd2 : (n / 2) % 2 = 0 := by omega
  have hd3 : ¬ n / 2 / 2 = 0 := by omega
  have hd4 : ¬ (n / 2 / 2) % 2 = 0 := by omega
  rw [v2r.eq_def n, if_neg h0, if_pos h1, v2r.eq_def (n / 2),
    if_neg hd1, if_pos hd2, v2r.eq_def (n / 2 / 2),
    if_neg hd3, if_neg hd4]

/-- **The 8-period of nine.**  `9^a ≡ 1 (mod 8)` — the engine period
(the green TwoAdic idiom, self-contained). -/
theorem nine_pow_mod_eight (a : Nat) : (9 : Nat)^a % 8 = 1 := by
  induction a with
  | zero => rfl
  | succ a ih => rw [Nat.pow_succ, Nat.mul_mod, ih]

/-- **THE 8-PERIOD OF THE POWERS OF THREE.**  `3^d ≡ 3 (mod 8)` when `d`
is odd, `3^d ≡ 1 (mod 8)` when `d` is even. -/
theorem three_pow_mod_eight (d : Nat) :
    3^d % 8 = if d % 2 = 1 then 3 else 1 := by
  have h9 : (3 : Nat)^2 = 9 := by decide
  rcases Nat.mod_two_eq_zero_or_one d with hd | hd
  · rw [if_neg (by omega : ¬ d % 2 = 1)]
    obtain ⟨e, he⟩ : ∃ e, d = 2 * e := ⟨d / 2, by omega⟩
    have hpow : 3^d = 9^e := by
      rw [he, Nat.pow_mul, h9]
    rw [hpow, nine_pow_mod_eight]
  · rw [if_pos (by omega : d % 2 = 1)]
    obtain ⟨e, he⟩ : ∃ e, d = 2 * e + 1 := ⟨d / 2, by omega⟩
    have hpow : 3^d = 3 * 9^e := by
      rw [he, Nat.pow_succ 3 (2 * e), Nat.pow_mul, h9]
      ring
    rw [hpow, Nat.mul_mod, nine_pow_mod_eight]
    -- (the r4 receipt: the rw chain closes the goal; no `decide` needed)

/-- Every power of three is odd. -/
theorem three_pow_odd (i : Nat) : 3^i % 2 = 1 := by
  have h8 := three_pow_mod_eight i
  rcases Nat.mod_two_eq_zero_or_one i with h | h
  · rw [if_neg (by omega : ¬ i % 2 = 1)] at h8; omega
  · rw [if_pos (by omega : i % 2 = 1)] at h8; omega

/-- **THE 2-POWER SCALING LAW.**  A power of two times an odd number has
`v2r` exactly the exponent. -/
theorem v2r_two_pow_mul_odd (t : Nat) (m : Nat) (hm : m % 2 = 1) :
    v2r (2^t * m) = t := by
  induction t with
  | zero =>
    rw [Nat.pow_zero, Nat.one_mul]
    exact v2r_eq_zero_of_odd hm
  | succ t ih =>
    have hp : 2^(t + 1) = 2^t * 2 := pow_succ 2 t
    have hmul : 2^(t + 1) * m = 2 * (2^t * m) := by rw [hp]; ring
    have hne : ¬ 2^(t + 1) * m = 0 := by
      have hm1 : 1 ≤ m := by omega
      have h2 : 2 ≤ 2^(t + 1) := by
        rw [hp]
        have h1t : (0:Nat) < 2^t := by positivity
        omega
      omega
    have heven : (2^(t + 1) * m) % 2 = 0 := by
      rw [hmul, Nat.mul_mod]
      norm_num
    have hdiv : (2^(t + 1) * m) / 2 = 2^t * m := by
      rw [hmul, Nat.two_mul_div_two]
    rw [v2r.eq_def (2^(t + 1) * m), if_neg hne, if_pos heven, hdiv, ih]
    omega

/-- **THE DECOMPOSITION.**  Every positive number is a power of two times
an odd number. -/
theorem exists_two_pow_decomp (n : Nat) (hn : 0 < n) :
    ∃ t m : Nat, n = 2^t * m ∧ m % 2 = 1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases Nat.mod_two_eq_zero_or_one n with h | h
    · have hn2 : 2 ≤ n := by omega
      have hlt : n / 2 < n := Nat.div_lt_self (by omega) (by omega)
      obtain ⟨t, m, heq, hm⟩ := ih (n / 2) hlt (by omega)
      refine ⟨t + 1, m, ?_, hm⟩
      calc n = 2 * (n / 2) := by omega
        _ = 2 * (2^t * m) := by rw [heq]
        _ = (2 * 2^t) * m := by ring
        _ = 2^(t + 1) * m := by rw [pow_succ 2 t]; ring
    · exact ⟨0, n, by rw [Nat.pow_zero, Nat.one_mul], h⟩

/-- **THE MULTIPLICATIVITY LAW.**  `v2r (a * b) = v2r a + v2r b` for
positive `a b` — the full valuation law, self-contained. -/
theorem v2r_mul (a b : Nat) (ha : 0 < a) (hb : 0 < b) :
    v2r (a * b) = v2r a + v2r b := by
  obtain ⟨ta, ma, haeq, hma⟩ := exists_two_pow_decomp a ha
  obtain ⟨tb, mb, hbeq, hmb⟩ := exists_two_pow_decomp b hb
  have hodd : ma * mb % 2 = 1 := by
    rw [Nat.mul_mod, hma, hmb]
  have hprod : a * b = 2^(ta + tb) * (ma * mb) := by
    have hpt : 2^ta * 2^tb = 2^(ta + tb) := (Nat.pow_add 2 ta tb).symm
    rw [haeq, hbeq]
    rw [show (2^ta * ma) * (2^tb * mb) = 2^ta * 2^tb * (ma * mb) from by ring]
    rw [hpt]
  rw [hprod, v2r_two_pow_mul_odd _ _ hodd, haeq,
    v2r_two_pow_mul_odd _ _ hma, hbeq, v2r_two_pow_mul_odd _ _ hmb]

/-! ## §1 The odd-popcount law -/

/-- **THE SUM-PARITY LAW.**  A sum of powers of three, one per list entry,
has parity exactly the parity of the entry count. -/
theorem pow3_sum_mod_two (l : List Nat) :
    (l.map (fun i => 3^i)).sum % 2 = l.length % 2 := by
  induction l with
  | nil => rfl
  | cons x s ih =>
    have h1 : (3 : Nat)^x % 2 = 1 := three_pow_odd x
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    rw [Nat.add_mod, h1, ih]
    omega

/-- **THE ODD-POPCOUNT LAW.**  Every $0/1$-ternary number with an odd
number of set digits is odd — $v_2 = 0$ exactly.  Half the subset lattice
is valuation-dead. -/
theorem v2r_pow3_sum_odd_length (l : List Nat) (hl : l.length % 2 = 1) :
    v2r ((l.map (fun i => 3^i)).sum) = 0 := by
  have hmod := pow3_sum_mod_two l
  rw [hl] at hmod
  exact v2r_eq_zero_of_odd hmod

/-! ## §2 The pair law — the exact 2-digit classification -/

/-- **THE ONE-PLUS-POWER LAW.**  $v_2(1 + 3^d)$ is $2$ when $d$ is odd,
$1$ when $d$ is even. -/
theorem v2r_one_add_three_pow (d : Nat) :
    v2r (1 + 3^d) = if d % 2 = 1 then 2 else 1 := by
  have h8 := three_pow_mod_eight d
  rcases Nat.mod_two_eq_zero_or_one d with hd | hd
  · rw [if_neg (by omega : ¬ d % 2 = 1)]
    rw [if_neg (by omega : ¬ d % 2 = 1)] at h8
    exact v2r_eq_one_of_mod_eight (by omega)
  · rw [if_pos (by omega : d % 2 = 1)]
    rw [if_pos (by omega : d % 2 = 1)] at h8
    exact v2r_eq_two_of_mod_eight (by omega)

/-- **THE PAIR LAW, EXACT.**  For $b < a$: $v_2(3^a + 3^b) = 2$ when
$a - b$ is odd, $1$ when $a - b$ is even — the complete classification of
the 2-digit $0/1$-ternary family. -/
theorem v2r_pair (a b : Nat) (h : b < a) :
    v2r (3^a + 3^b) = if (a - b) % 2 = 1 then 2 else 1 := by
  have hsplit : 3^a + 3^b = 3^b * (3^(a - b) + 1) := by
    have hpa : 3^a = 3^(b + (a - b)) := by
      congr 1
      omega
    rw [hpa, Nat.pow_add]
    ring
  rw [hsplit, v2r_mul_three_pow]
  have hlaw := v2r_one_add_three_pow (a - b)
  rw [Nat.add_comm] at hlaw
  rw [hlaw]

/-- **THE PAIR CAP.**  The 2-digit family obeys the cap law with constant
`C = 2` at every scale. -/
theorem cap_pair (a b : Nat) (h : b < a) :
    v2r (3^a + 3^b) ≤ ternaryLog3 (3^a + 3^b) + 2 := by
  have hval := v2r_pair a b h
  rcases Nat.mod_two_eq_zero_or_one (a - b) with hd | hd
  · rw [if_neg (by omega : ¬ (a - b) % 2 = 1)] at hval
    omega
  · rw [if_pos (by omega : (a - b) % 2 = 1)] at hval
    omega

/-! ## §3 The product-quadruple law -/

/-- **THE PRODUCT-QUADRUPLE LAW.**  The 4-digit product family
$(1 + 3^x)(1 + 3^y)$ has $v_2 \le 4$. -/
theorem v2r_product_four (x y : Nat) :
    v2r ((1 + 3^x) * (1 + 3^y)) ≤ 4 := by
  have hx : 0 < 1 + 3^x := by
    have h3 : (0:Nat) < 3^x := by positivity
    omega
  have hy : 0 < 1 + 3^y := by
    have h3 : (0:Nat) < 3^y := by positivity
    omega
  rw [v2r_mul _ _ hx hy]
  have vx := v2r_one_add_three_pow x
  have vy := v2r_one_add_three_pow y
  rcases Nat.mod_two_eq_zero_or_one x with hx1 | hx1
  · rw [if_neg (by omega : ¬ x % 2 = 1)] at vx
    rcases Nat.mod_two_eq_zero_or_one y with hy1 | hy1
    · rw [if_neg (by omega : ¬ y % 2 = 1)] at vy
      omega
    · rw [if_pos (by omega : y % 2 = 1)] at vy
      omega
  · rw [if_pos (by omega : x % 2 = 1)] at vx
    rcases Nat.mod_two_eq_zero_or_one y with hy1 | hy1
    · rw [if_neg (by omega : ¬ y % 2 = 1)] at vy
      omega
    · rw [if_pos (by omega : y % 2 = 1)] at vy
      omega

/-- **THE PRODUCT-QUADRUPLE CAP.**  The product family obeys the cap law
with constant `C = 4`. -/
theorem cap_product_four (x y : Nat) :
    v2r ((1 + 3^x) * (1 + 3^y))
      ≤ ternaryLog3 ((1 + 3^x) * (1 + 3^y)) + 4 := by
  have h := v2r_product_four x y
  omega

/-! ## §4 The receipts -/

#print axioms v2r_eq_zero_of_odd
#print axioms v2r_eq_one_of_mod_eight
#print axioms v2r_eq_two_of_mod_eight
#print axioms three_pow_mod_eight
#print axioms v2r_mul
#print axioms v2r_pow3_sum_odd_length
#print axioms v2r_one_add_three_pow
#print axioms v2r_pair
#print axioms cap_pair
#print axioms v2r_product_four
#print axioms cap_product_four

end CapLawK406
