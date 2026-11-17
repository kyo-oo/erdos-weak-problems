import Mathlib
import GSTCanonicalTailLTE
import GSTCanonicalTailStateIso
import GSTTheAct

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
# THE DIAGONAL READ — every exponent's entire low band, one law

One separate file, zero monolith bytes.  The 4D object, constructed:

* **§0 THE ENGINE.**  `binom_two_term` (the two-term binomial expansion,
  by induction) and `digit3_mod_congr` (digits are stable under
  congruence mod `3^(p+1)`).

* **§1 THE WINDOW LAW.**  `diagonal_window_law`: for EVERY valuation cut
  `v` and EVERY reduced exponent `u`, the digit stream of `4^(3^v·u)` at
  rows `v+1 .. 2v+1` IS the ternary digit stream of `u · lteCoeff v`,
  trit by trit: `digit3 (4^(3^v·u)) (v+1+j) = digit3 (u · lteCoeff v) j`
  for every `j ≤ v`.  One law, every scale, every core, every row of
  the band — the digit stream READS the frozen diagonal.  At `v = 0`
  it subsumes the front law itself.

* **§2 THE FROZEN DIAGONAL.**  `lteCoeff_succ_mod` + `lteCoeff_stable`:
  the coefficient's trits freeze level by level (`lteCoeff (v+1) ≡
  lteCoeff v mod 3^(v+1)`), so the readable diagonal is the same object
  at every depth.  Residues: `7 mod 9`, `16 mod 27`, `16 mod 81`.

* **§3 THE FIRE FAMILIES.**  Unconditional digit-two laws, uniform in
  `v` and `u` — the ladder's first three levels:
  `u ≡ 1 mod 9` fires at row `v+2`; `u ≡ 13, 25 mod 27` fire at row
  `v+3`; `u ≡ 4, 34, 49, 70 mod 81` fire at row `v+4`.
  Witness receipts: `4^9` fires at row 4, `4^108` fires at row 7 —
  both delivered by the uniform law alone, no bounded decide.

* **§4 THE TRIAGE, THE DUST, THE SOCKET.**  Every `K ≥ 8` either owns
  its digit two (front fire or window fire) or is `WindowCleanDust` —
  the exact residual, named.  `no22_of_not_dust`: the read kills the
  dust's entire complement.  `hTailF_of_dust_empty`: dust empty ⇒
  the act ⇒ `hTailF`, through the standing green bridges.

* **§5 THE RECEIPT.**  Everything assembled in one theorem, with axiom
  printouts: the classical three only.
-/

namespace GSTDiagonalRead

open GSTCanonicalSevenAxisBridge (digit3)

/-! ## §0 THE ENGINE -/

/-- The two-term binomial expansion: `(1+x)^u = 1 + u·x + x²·s` for some
natural `s`.  By induction on `u` — pure algebra, no hypothesis. -/
theorem binom_two_term (x u : Nat) :
    ∃ s : Nat, (1 + x)^u = 1 + u * x + x * x * s := by
  induction u with
  | zero => exact ⟨0, by rw [Nat.pow_zero]; ring⟩
  | succ u ih =>
      obtain ⟨s, hs⟩ := ih
      refine ⟨u + s + x * s, ?_⟩
      calc (1 + x)^(u+1) = (1 + x)^u * (1 + x) := by rw [Nat.pow_succ]
        _ = (1 + u * x + x * x * s) * (1 + x) := by rw [hs]
        _ = 1 + (u + 1) * x + x * x * (u + s + x * s) := by ring

/-- Mod-zero folding: if `m ∣ b` then `(a + b) % m = a % m`.  The core
congruence step for the window law. -/
theorem add_mod_of_dvd (a b m : Nat) (hdvd : m ∣ b) :
    (a + b) % m = a % m := by
  obtain ⟨q, rfl⟩ := hdvd
  first
    | rw [Nat.add_mul_mod_self_left]
    | rw [Nat.add_mul_mod_self_right]

/-- Digit division below a modulus factor: dividing `3^p·3·q + r` by
`3^p` reads off the quotient `3·q` plus the sub-quotient. -/
theorem div_pow_add (q r p : Nat) :
    (3^p * 3 * q + r) / 3^p = 3 * q + r / 3^p := by
  have hp : 0 < 3^p := Nat.pow_pos (by decide)
  rw [show 3^p * 3 * q + r = r + 3^p * (3 * q) from by ring]
  rw [Nat.add_mul_div_left _ _ hp]
  omega

/-- Digits are stable under congruence mod `3^(p+1)`: if two numbers
agree modulo `3^(p+1)`, their row-`p` ternary digits agree. -/
theorem digit3_mod_congr (R R' p : Nat)
    (h : R % 3^(p+1) = R' % 3^(p+1)) :
    digit3 R p = digit3 R' p := by
  unfold digit3
  have hp1 : 3^(p+1) = 3^p * 3 := by rw [Nat.pow_succ]
  rw [hp1] at h
  have hR := Nat.div_add_mod R (3^p * 3)
  have hR' := Nat.div_add_mod R' (3^p * 3)
  rw [← hR, ← hR', div_pow_add, div_pow_add, h]
  omega

/-! ## §1 THE WINDOW LAW — the digit stream reads the diagonal -/

/-- The correction-term divisibility: with `j ≤ v`, the binomial tail
`(3^(v+1)·c)²·s` is divisible by `3^(v+2+j)` — the window's boundary. -/
theorem pow_cut_dvd (v j c s : Nat) (hj : j ≤ v) :
    3^(v+2+j) ∣ (3^(v+1) * c) * (3^(v+1) * c) * s := by
  refine ⟨3^(v-j) * (c * c * s), ?_⟩
  have hp2 : 3^(v+1) * 3^(v+1) = 3^(v+2+j) * 3^(v-j) := by
    rw [← Nat.pow_add, ← Nat.pow_add]
    congr 1; omega
  calc (3^(v+1) * c) * (3^(v+1) * c) * s
      = (3^(v+1) * 3^(v+1)) * (c * c * s) := by ring
    _ = (3^(v+2+j) * 3^(v-j)) * (c * c * s) := by rw [hp2]
    _ = 3^(v+2+j) * (3^(v-j) * (c * c * s)) := by ring

/-- **THE WINDOW LAW.**  For every valuation cut `v` and every reduced
exponent `u`, the digit stream of `4^(3^v·u)` at row `v+1+j` IS the
`j`-th ternary digit of `u · lteCoeff v`, for every `j ≤ v`.  The
tower's entire readable band, one law, all scales at once — including
`v = 0`, where it subsumes the front law. -/
theorem diagonal_window_law (v u j : Nat) (hj : j ≤ v) :
    digit3 (4^(3^v * u)) (v + 1 + j) =
      digit3 (u * GSTCanonicalTailLTE.lteCoeff v) j := by
  have hLTE : 4^(3^v) = 1 + 3^(v+1) * GSTCanonicalTailLTE.lteCoeff v :=
    GSTCanonicalTailLTE.pow4_three_power_lte_exact v
  have hK : 4^(3^v * u) = (4^(3^v))^u := by rw [Nat.pow_mul]
  obtain ⟨s, hs⟩ :=
    binom_two_term (3^(v+1) * GSTCanonicalTailLTE.lteCoeff v) u
  have hu : u * (3^(v+1) * GSTCanonicalTailLTE.lteCoeff v) =
      3^(v+1) * (u * GSTCanonicalTailLTE.lteCoeff v) := by ring
  have hcorr : 3^(v+2+j) ∣ (3^(v+1) * GSTCanonicalTailLTE.lteCoeff v) *
      (3^(v+1) * GSTCanonicalTailLTE.lteCoeff v) * s :=
    pow_cut_dvd v j (GSTCanonicalTailLTE.lteCoeff v) s hj
  have hcongr : 4^(3^v * u) % 3^((v+1+j)+1) =
      (1 + 3^(v+1) * (u * GSTCanonicalTailLTE.lteCoeff v)) % 3^((v+1+j)+1) := by
    rw [show 3^((v+1+j)+1) = 3^(v+2+j) from by congr 1; omega]
    rw [hK, hLTE, hs, hu]
    exact add_mod_of_dvd _ _ _ hcorr
  have hdig := digit3_mod_congr (4^(3^v * u))
    (1 + 3^(v+1) * (u * GSTCanonicalTailLTE.lteCoeff v)) (v+1+j) hcongr
  rw [hdig]
  have h1lt : 1 < 3^(v+1) := by
    cases v with
    | zero => norm_num
    | succ v =>
        have h0 : 0 < 3^(v+1) := Nat.pow_pos (by decide)
        rw [Nat.pow_succ]
        omega
  simpa only [GSTCanonicalTailStateIso.digit3, digit3] using
    GSTCanonicalTailStateIso.prefix_slice_digit_exact (v+1) 1
      (u * GSTCanonicalTailLTE.lteCoeff v) j h1lt

/-- At the zero cut the window law IS the front law: row one of `4^u`
reads `u % 3` directly. -/
theorem window_subsumes_front (u : Nat) :
    digit3 (4^(3^0 * u)) (0 + 1 + 0) = u % 3 := by
  simpa [digit3, GSTCanonicalTailLTE.lteCoeff] using
    diagonal_window_law 0 u 0 (by omega)

/-! ## §2 THE FROZEN DIAGONAL — the coefficient's trits stabilize -/

/-- The coefficient's trits freeze: each recursion step preserves the
previous coefficient modulo `3^(v+1)`. -/
theorem lteCoeff_succ_mod (v : Nat) :
    GSTCanonicalTailLTE.lteCoeff (v+1) % 3^(v+1) =
      GSTCanonicalTailLTE.lteCoeff v % 3^(v+1) := by
  have hsplit : 3^(2*v+1) = 3^(v+1) * 3^v := by
    rw [← Nat.pow_add]
    congr 1; omega
  have hd1 : 3^(v+1) ∣ 3^(v+1) * (GSTCanonicalTailLTE.lteCoeff v)^2 :=
    ⟨_, rfl⟩
  have hd2 : 3^(v+1) ∣ 3^(2*v+1) * (GSTCanonicalTailLTE.lteCoeff v)^3 :=
    ⟨3^v * (GSTCanonicalTailLTE.lteCoeff v)^3, by rw [hsplit]; ring⟩
  simp only [GSTCanonicalTailLTE.lteCoeff]
  rw [add_mod_of_dvd _ _ _ hd2, add_mod_of_dvd _ _ _ hd1]

theorem mod_dvd_modeq (a b m n : Nat) (hmn : m ∣ n) (h : a % n = b % n) :
    a % m = b % m := by
  rw [← Nat.mod_mod_of_dvd a hmn, h, Nat.mod_mod_of_dvd b hmn]

/-- **THE FROZEN DIAGONAL.**  From index `v` upward, the coefficient is
constant modulo `3^(v+1)`: the readable diagonal is the same object at
every depth. -/
theorem lteCoeff_stable (v w : Nat) (hw : v ≤ w) :
    GSTCanonicalTailLTE.lteCoeff w % 3^(v+1) =
      GSTCanonicalTailLTE.lteCoeff v % 3^(v+1) := by
  induction w with
  | zero =>
      have hv0 : v = 0 := by omega
      subst hv0
      rfl
  | succ w ih =>
      by_cases hwv : v ≤ w
      · have h := lteCoeff_succ_mod w
        have hdvd : 3^(v+1) ∣ 3^(w+1) := by
          refine ⟨3^(w-v), ?_⟩
          rw [← Nat.pow_add]
          congr 1; omega
        have h2 := mod_dvd_modeq (GSTCanonicalTailLTE.lteCoeff (w+1))
          (GSTCanonicalTailLTE.lteCoeff w) (3^(v+1)) (3^(w+1)) hdvd h
        rw [h2]
        exact ih hwv
      · have hvw : v = w + 1 := by omega
        subst hvw
        rfl

/-- The frozen diagonal's residue modulo 9 from index one: `7`. -/
theorem lteCoeff_mod9 (v : Nat) (hv : 1 ≤ v) :
    GSTCanonicalTailLTE.lteCoeff v % 9 = 7 := by
  have h := lteCoeff_stable 1 v hv
  have hbase : GSTCanonicalTailLTE.lteCoeff 1 % 3^(1+1) = 7 := by decide
  calc GSTCanonicalTailLTE.lteCoeff v % 9
      = GSTCanonicalTailLTE.lteCoeff v % 3^(1+1) := by norm_num
    _ = GSTCanonicalTailLTE.lteCoeff 1 % 3^(1+1) := h
    _ = 7 := hbase

/-- The frozen diagonal's residue modulo 27 from index two: `16`. -/
theorem lteCoeff_mod27 (v : Nat) (hv : 2 ≤ v) :
    GSTCanonicalTailLTE.lteCoeff v % 27 = 16 := by
  have h := lteCoeff_stable 2 v hv
  have hbase : GSTCanonicalTailLTE.lteCoeff 2 % 3^(2+1) = 16 := by decide
  calc GSTCanonicalTailLTE.lteCoeff v % 27
      = GSTCanonicalTailLTE.lteCoeff v % 3^(2+1) := by norm_num
    _ = GSTCanonicalTailLTE.lteCoeff 2 % 3^(2+1) := h
    _ = 16 := hbase

/-- The frozen diagonal's residue modulo 81 from index three: `16`. -/
theorem lteCoeff_mod81 (v : Nat) (hv : 3 ≤ v) :
    GSTCanonicalTailLTE.lteCoeff v % 81 = 16 := by
  have h := lteCoeff_stable 3 v hv
  have hbase : GSTCanonicalTailLTE.lteCoeff 3 % 3^(3+1) = 16 := by decide
  calc GSTCanonicalTailLTE.lteCoeff v % 81
      = GSTCanonicalTailLTE.lteCoeff v % 3^(3+1) := by norm_num
    _ = GSTCanonicalTailLTE.lteCoeff 3 % 3^(3+1) := h
    _ = 16 := hbase

/-! ## §3 THE FIRE FAMILIES — the ladder's first three levels -/

/-- **LEVEL ONE.**  Every core `u ≡ 1 mod 9` at every cut `v ≥ 1` fires
its digit two at row `v+2`: the diagonal's second trit is `2` because
`u·c ≡ 7 mod 9`. -/
theorem window_fire_level1 (v : Nat) (hv : 1 ≤ v) (u : Nat) (hu : u % 9 = 1) :
    digit3 (4^(3^v * u)) (v + 2) = 2 := by
  have hw := diagonal_window_law v u 1 (by omega)
  have hc := lteCoeff_mod9 v hv
  have humod : (u * GSTCanonicalTailLTE.lteCoeff v) % 9 = 7 := by
    rw [Nat.mul_mod, hu, hc]
  have hd : digit3 (u * GSTCanonicalTailLTE.lteCoeff v) 1 = 2 := by
    unfold digit3
    omega
  rw [show v + 2 = v + 1 + 1 from rfl, hw]
  exact hd

/-- **LEVEL TWO.**  Every core `u ≡ 13 or 25 mod 27` at every cut `v ≥ 2`
fires its digit two at row `v+3`. -/
theorem window_fire_level2 (v : Nat) (hv : 2 ≤ v) (u : Nat)
    (hu : u % 27 = 13 ∨ u % 27 = 25) :
    digit3 (4^(3^v * u)) (v + 3) = 2 := by
  have hw := diagonal_window_law v u 2 (by omega)
  have hc := lteCoeff_mod27 v hv
  have hd : digit3 (u * GSTCanonicalTailLTE.lteCoeff v) 2 = 2 := by
    unfold digit3
    rcases hu with h13 | h25
    · have humod : (u * GSTCanonicalTailLTE.lteCoeff v) % 27 = 19 := by
        rw [Nat.mul_mod, h13, hc]
      omega
    · have humod : (u * GSTCanonicalTailLTE.lteCoeff v) % 27 = 22 := by
        rw [Nat.mul_mod, h25, hc]
      omega
  rw [show v + 3 = v + 1 + 2 from rfl, hw]
  exact hd

/-- **LEVEL THREE.**  Every core `u ≡ 4, 34, 49, or 70 mod 81` at every
cut `v ≥ 3` fires its digit two at row `v+4`. -/
theorem window_fire_level3 (v : Nat) (hv : 3 ≤ v) (u : Nat)
    (hu : u % 81 = 4 ∨ u % 81 = 34 ∨ u % 81 = 49 ∨ u % 81 = 70) :
    digit3 (4^(3^v * u)) (v + 4) = 2 := by
  have hw := diagonal_window_law v u 3 (by omega)
  have hc := lteCoeff_mod81 v hv
  have hd : digit3 (u * GSTCanonicalTailLTE.lteCoeff v) 3 = 2 := by
    unfold digit3
    rcases hu with h4 | h34 | h49 | h70
    · have humod : (u * GSTCanonicalTailLTE.lteCoeff v) % 81 = 64 := by
        rw [Nat.mul_mod, h4, hc]
      omega
    · have humod : (u * GSTCanonicalTailLTE.lteCoeff v) % 81 = 58 := by
        rw [Nat.mul_mod, h34, hc]
      omega
    · have humod : (u * GSTCanonicalTailLTE.lteCoeff v) % 81 = 55 := by
        rw [Nat.mul_mod, h49, hc]
      omega
    · have humod : (u * GSTCanonicalTailLTE.lteCoeff v) % 81 = 67 := by
        rw [Nat.mul_mod, h70, hc]
      omega
  rw [show v + 4 = v + 1 + 3 from rfl, hw]
  exact hd

/-- Witness receipt: `4^9` fires its digit two at row 4, delivered by
the uniform level-one family (`9 = 3^2·1`, `u = 1 ≡ 1 mod 9`), not by a
bounded decide. -/
theorem fire_nine_row_four : digit3 (4^9) 4 = 2 := by
  have h := window_fire_level1 2 (by omega) 1 (by decide)
  norm_num at h ⊢
  exact h

/-- Witness receipt: `4^108` fires its digit two at row 7, delivered by
the uniform level-three family (`108 = 3^3·4`, `u = 4 ≡ 4 mod 81`) — a
fire beyond every prior uniform witness, no bounded decide. -/
theorem fire_108_row_seven : digit3 (4^108) 7 = 2 := by
  have h := window_fire_level3 3 (by omega) 4 (Or.inl (by decide))
  norm_num at h ⊢
  exact h

/-- The full kill-chain instance: `4^108` fails `noTernaryTwo`, by the
uniform law alone. -/
theorem no22_four_pow_108 : noTernaryTwo (4^108) = false :=
  has_two_imp_not_no_two (4^108)
    (hasTernaryTwo_of_digit (4^108) 7 (by simpa [digit3] using fire_108_row_seven))

/-! ## §4 THE TRIAGE, THE DUST, THE SOCKET -/

/-- Every positive exponent decomposes uniquely as `3^v · u` with
`u` not divisible by three — the valuation cut. -/
theorem valuation_decomp (K : Nat) :
    0 < K → ∃ v u : Nat, K = 3^v * u ∧ u % 3 ≠ 0 := by
  induction K using Nat.strongRecOn with
  | ind K ih =>
      intro hK
      by_cases h3 : K % 3 = 0
      · have hKd : 0 < K / 3 := by
          by_contra h0
          have hd0 : K / 3 = 0 := by omega
          have hdm := Nat.div_add_mod K 3
          omega
        obtain ⟨v, u, hKu, hu⟩ :=
          ih (K / 3) (Nat.div_lt_self hK (by decide : 1 < 3)) hKd
        refine ⟨v + 1, u, ?_, hu⟩
        have hdm : 3 * (K / 3) + K % 3 = K := Nat.div_add_mod K 3
        rw [h3, Nat.add_zero] at hdm
        rw [← hdm, hKu, Nat.pow_succ]
        ring
      · exact ⟨0, K, by ring, h3⟩

/-- **THE WINDOW-CLEAN DUST.**  The read's exact residual: exponents
whose reduced core is `1 mod 3` and whose readable diagonal never fires
— the Cantor slice, named once. -/
def WindowCleanDust (K : Nat) : Prop :=
  ∃ v u : Nat, K = 3^v * u ∧ u % 3 = 1 ∧
    ∀ j ≤ v, digit3 (u * GSTCanonicalTailLTE.lteCoeff v) j ≠ 2

/-- **THE TRIAGE.**  Every exponent `K ≥ 8` either owns its digit two —
by the front fire or by a window fire, both uniform laws — or is
window-clean dust.  No third case: the whole plane of exponents, one
dichotomy, one construction. -/
theorem every_exponent_fires (K : Nat) (hK : 8 ≤ K) :
    (∃ p : Nat, digit3 (4^K) p = 2) ∨ WindowCleanDust K := by
  obtain ⟨v, u, hKu, hu3⟩ := valuation_decomp K (by omega)
  have hu3' : u % 3 = 1 ∨ u % 3 = 2 := by omega
  rcases hu3' with hu1 | hu2
  · by_cases hfire :
      ∃ j : Nat, j ≤ v ∧
        digit3 (u * GSTCanonicalTailLTE.lteCoeff v) j = 2
    · left
      obtain ⟨j, hjv, hj⟩ := hfire
      have hw := diagonal_window_law v u j hjv
      refine ⟨v + 1 + j, ?_⟩
      rw [hKu, hw]
      exact hj
    · right
      refine ⟨v, u, hKu, hu1, ?_⟩
      intro j hjv h2
      exact hfire ⟨j, hjv, h2⟩
  · left
    have hf := GSTTheAct.front_law v u
    refine ⟨v + 1, ?_⟩
    rw [hKu, hf]
    exact hu2

/-- Canonical least firing row for every exponent outside the
window-clean dust. -/
noncomputable def firstFireRow
    (K : Nat) (hK : 8 ≤ K)
    (hNotDust : ¬ WindowCleanDust K) : Nat :=
  Nat.find ((every_exponent_fires K hK).resolve_right hNotDust)

/-- The canonical row really fires. -/
theorem firstFireRow_fires
    (K : Nat) (hK : 8 ≤ K)
    (hNotDust : ¬ WindowCleanDust K) :
    digit3 (4^K) (firstFireRow K hK hNotDust) = 2 := by
  exact Nat.find_spec
    ((every_exponent_fires K hK).resolve_right hNotDust)

/-- **LEAST-FIRE RIGIDITY.**
No smaller ternary row than firstFireRow can carry digit two. -/
theorem firstFireRow_minimal
    (K : Nat) (hK : 8 ≤ K)
    (hNotDust : ¬ WindowCleanDust K)
    (p : Nat)
    (hp : digit3 (4^K) p = 2) :
    firstFireRow K hK hNotDust ≤ p := by
  exact Nat.find_min'
    ((every_exponent_fires K hK).resolve_right hNotDust) hp

/-- Every row strictly before the canonical fire is digit-two free. -/
theorem before_firstFireRow_not_two
    (K : Nat) (hK : 8 ≤ K)
    (hNotDust : ¬ WindowCleanDust K)
    (p : Nat)
    (hp : p < firstFireRow K hK hNotDust) :
    digit3 (4^K) p ≠ 2 := by
  intro htwo
  have hle := firstFireRow_minimal K hK hNotDust p htwo
  omega

/-- **THE READ KILLS THE COMPLEMENT.**  Every `K ≥ 8` outside the
window-clean dust owns its digit two: `noTernaryTwo (4^K) = false`,
through the repo's own kill chain. -/
theorem no22_of_not_dust (K : Nat) (hK : 8 ≤ K) (h : ¬ WindowCleanDust K) :
    noTernaryTwo (4^K) = false := by
  rcases every_exponent_fires K hK with ⟨p, hp⟩ | hdust
  · exact has_two_imp_not_no_two (4^K)
      (hasTernaryTwo_of_digit (4^K) p (by simpa [digit3] using hp))
  · exact absurd hdust h

/-- **THE SOCKET, FIRST STAGE.**  Dust empty ⇒ the act: every `4^K`
from eight onward fails `noTernaryTwo`. -/
theorem the_act_of_dust_empty
    (h : ∀ K : Nat, 8 ≤ K → ¬ WindowCleanDust K) :
    GSTTheAct.the_act :=
  fun K hK => no22_of_not_dust K hK (h K hK)

/-- **THE SOCKET, COMPLETE.**  Dust empty ⇒ the act ⇒ `hTailF`, through
the standing green bridges.  The one remaining mathematical object is
named: kill the window-clean dust and the campaign closes. -/
theorem hTailF_of_dust_empty
    (hB : erdos_even_conjecture_iff_tailF)
    (h : ∀ K : Nat, 8 ≤ K → ¬ WindowCleanDust K) :
    GSTGraphV2OmegaWaveLaw.four_power_omega_shadow_wave_tailF :=
  (GSTTheAct.the_act_iff_hTailF hB).mp (the_act_of_dust_empty h)

/-! ## §5 THE RECEIPT — everything in one theorem -/

/-- **THE DIAGONAL READ, ASSEMBLED.**  (1) The window law: every
exponent's entire readable band, one law, all scales.  (2) The frozen
diagonal: the readable object is depth-invariant.  (3) The fire
families: three ladder levels, uniform.  (4) The triage: every `K ≥ 8`
fires or is dust.  (5) The socket: dust empty ⇒ `hTailF`.  (6) Witness
receipts beyond every prior uniform witness. -/
theorem the_diagonal_read_receipt
    (hB : erdos_even_conjecture_iff_tailF) :
    (∀ v u j : Nat, j ≤ v →
      digit3 (4^(3^v * u)) (v + 1 + j) =
        digit3 (u * GSTCanonicalTailLTE.lteCoeff v) j) ∧
    (∀ v w : Nat, v ≤ w →
      GSTCanonicalTailLTE.lteCoeff w % 3^(v+1) =
        GSTCanonicalTailLTE.lteCoeff v % 3^(v+1)) ∧
    (∀ v : Nat, 1 ≤ v → ∀ u : Nat, u % 9 = 1 →
      digit3 (4^(3^v * u)) (v + 2) = 2) ∧
    (∀ v : Nat, 2 ≤ v → ∀ u : Nat, u % 27 = 13 ∨ u % 27 = 25 →
      digit3 (4^(3^v * u)) (v + 3) = 2) ∧
    (∀ v : Nat, 3 ≤ v → ∀ u : Nat,
      u % 81 = 4 ∨ u % 81 = 34 ∨ u % 81 = 49 ∨ u % 81 = 70 →
      digit3 (4^(3^v * u)) (v + 4) = 2) ∧
    (∀ K : Nat, 8 ≤ K →
      (∃ p : Nat, digit3 (4^K) p = 2) ∨ WindowCleanDust K) ∧
    (∀ h : ∀ K : Nat, 8 ≤ K → ¬ WindowCleanDust K,
        GSTGraphV2OmegaWaveLaw.four_power_omega_shadow_wave_tailF) ∧
    (digit3 (4^9) 4 = 2) ∧
    (digit3 (4^108) 7 = 2) ∧
    (noTernaryTwo (4^108) = false) :=
  ⟨diagonal_window_law, lteCoeff_stable,
    window_fire_level1, window_fire_level2, window_fire_level3,
    every_exponent_fires, hTailF_of_dust_empty hB,
    fire_nine_row_four, fire_108_row_seven, no22_four_pow_108⟩

#print axioms binom_two_term
#print axioms div_pow_add
#print axioms digit3_mod_congr
#print axioms diagonal_window_law
#print axioms window_subsumes_front
#print axioms lteCoeff_succ_mod
#print axioms mod_dvd_modeq
#print axioms lteCoeff_stable
#print axioms lteCoeff_mod9
#print axioms lteCoeff_mod27
#print axioms lteCoeff_mod81
#print axioms window_fire_level1
#print axioms window_fire_level2
#print axioms window_fire_level3
#print axioms fire_nine_row_four
#print axioms fire_108_row_seven
#print axioms no22_four_pow_108
#print axioms valuation_decomp
#print axioms every_exponent_fires
#print axioms firstFireRow_fires
#print axioms firstFireRow_minimal
#print axioms before_firstFireRow_not_two
#print axioms no22_of_not_dust
#print axioms the_act_of_dust_empty
#print axioms hTailF_of_dust_empty
#print axioms the_diagonal_read_receipt

end GSTDiagonalRead
