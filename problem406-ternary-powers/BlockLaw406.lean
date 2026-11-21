import Arsenal.ErdosTernary2.Basic
import Arsenal.CardinalWorlds
import Arsenal.CardinalWorldsV2

-- Family pattern (green kernels): explicit depth headroom.
set_option maxRecDepth 262144
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 1000

/-!
# ERDŐS #406 — THE BLOCK-LAW KERNEL (S079): the second digit, the window,
the killing trit, and the fire ladder to level five

## THE OBJECT (BOSS order: crack the hTailF hypothesis — the rider
## structure laws, full proof, BOSS's laws only)

A rider is an exponent `K` with `noTernaryTwo (4^K) = true` (the power
`4^K = 2^(2K)` has only ternary digits `0/1`).  The hTailF/`the_act`
hypothesis is `∀ K ≥ 8, noTernaryTwo (4^K) = false`.  This kernel banks
THE BLOCK DECOMPOSITION of the rider payload — unconditional structure
laws every rider must obey, all levels, all scales:

* **§1 THE TOWER COEFFICIENT** (`lteCoeff`): `4^(3^v) = 1 + 3^(v+1) *
  lteCoeff v`, `lteCoeff v ≡ 1 (mod 3)` — the LTE spine, self-contained
  (the green TailLTE engine, ported verbatim; division-free).
* **§2 THE CUT RESIDUE — THE SECOND-DIGIT LAW**
  (`pow4_cut_residue_exact`): for every `v u`,
  `4^(3^v·u) % 3^(v+2) = 1 + (u % 3)·3^(v+1)`, EXACTLY.  A rider with
  valuation cut `K = 3^v·u` (so `u ≡ 1 mod 3`) therefore owns digits
  `1..v` equal to zero and digit `v+1` equal to one
  (`rider_second_digit_residue`): the second-lowest set digit of every
  rider IS `v₃(K)+1` — the LTE valuation law read as a digit law.
* **§3 THE WINDOW LAW** (`diagonal_window_law`, the Diagonal Read
  port): for every `v u j` with `j ≤ v`,
  `digit3 (4^(3^v·u)) (v+1+j) = digit3 (u * lteCoeff v) j` — the digit
  stream of the power in the band `v+1..2v+1` IS the trit stream of
  `u·lteCoeff v`, trit by trit, every scale at once.
* **§4 THE FIRE LADDER, LEVELS ONE THROUGH FIVE** — infinite uniform
  families: every `u` in a level-`L` fire class fires its digit two at
  row `v+1+L`, for ALL `v ≥ L` at once.  Levels 1–3 are the green
  Diagonal Read families; levels 4–5 are NEW (S079):
  `u ≡ 16, 31, 61, 76, 124, 139, 169, 184 (mod 243)` and
  `u ≡ 58, 103, 193, 205, 238, 250, 340, 385, 463, 508, 529, 574, 598,
  643, 664, 709 (mod 729)`.  New uniform witness receipts:
  `K = 1296 = 3^4·16` fires at row 9; `K = 14094 = 3^5·58` fires at
  row 11; `K = 42282 = 3^6·58` fires at row 12 — no bounded decide.
* **§5 THE EXPONENT-TRIT KILLING LAW** (`pow4_killing_trit`): for
  every `r t j`,
  `digit3 (4^(r + t·3^j)) (j+1) = (digit3 (4^r) (j+1) + t) % 3` — the
  exponent trit at position `j` ADDS to the payload digit at position
  `j+1`.  THE MASTER DYNAMICS: exactly one of the three dust lifts
  fires (`wheel_fire_exists`) — the dust tree is a full binary tree.

## THE HONEST SCOPE

These are unconditional rider-structure laws — the block decomposition
of the payload.  They do not close the CAP(185) seam (the wall stands);
they arm the block-by-block assault: every rider must be clean in every
block, and the blocks are read by explicit coefficient streams.

All arithmetic is the Arsenal's own laws plus core Nat lemmas — BOSS's
mathematics only, no external theory, no classical methods.
-/

namespace BlockLaw406

/-! ## §0 The engine (self-contained; the green Diagonal Read engine) -/

/-- The ternary digit at position `p`. -/
def digit3 (x p : Nat) : Nat := x / 3^p % 3

theorem digit3_lt_three (x p : Nat) : digit3 x p < 3 := by
  unfold digit3
  exact Nat.mod_lt _ (show 0 < 3 by decide)

/-- The two-term binomial expansion: `(1+x)^u = 1 + u·x + x²·s`. -/
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

/-- Mod-zero folding: if `m ∣ b` then `(a + b) % m = a % m`. -/
theorem add_mod_of_dvd (a b m : Nat) (hdvd : m ∣ b) :
    (a + b) % m = a % m := by
  obtain ⟨q, rfl⟩ := hdvd
  first
    | rw [Nat.add_mul_mod_self_left]
    | rw [Nat.add_mul_mod_self_right]

/-- Digit division below a modulus factor. -/
theorem div_pow_add (q r p : Nat) :
    (3^p * 3 * q + r) / 3^p = 3 * q + r / 3^p := by
  have hp : 0 < 3^p := Nat.pow_pos (by decide)
  rw [show 3^p * 3 * q + r = r + 3^p * (3 * q) from by ring]
  rw [Nat.add_mul_div_left _ _ hp]
  omega

/-- Digits are stable under congruence mod `3^(p+1)`. -/
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

/-- Digit addition at a power position: adding `3^m·B` shifts `B` into
digit `m` modulo three. -/
theorem digit3_add_pow (A B m : Nat) :
    digit3 (A + 3^m * B) m = (digit3 A m + B) % 3 := by
  unfold digit3
  have hp : 0 < 3^m := Nat.pow_pos (by decide)
  rw [Nat.add_mul_div_left _ _ hp, Nat.add_mod]
  omega

/-- `3^(p+1) = 3 * 3^p` (the succ shape, usable left-to-right on
`3^(p+1)`). -/
theorem pow_succ_mul (p : Nat) : 3^(p+1) = 3 * 3^p := by
  rw [Nat.pow_succ]
  ring

/-- `3^(v+2) = 3 * 3^(v+1)` (the double-succ shape). -/
theorem pow_succ_two (v : Nat) : 3^(v+2) = 3 * 3^(v+1) := by
  rw [show (v:Nat) + 2 = (v+1) + 1 from by omega, Nat.pow_succ]
  ring

/-- The digit of one is zero at every positive position. -/
theorem digit3_one_pos (p : Nat) (hp : 1 ≤ p) : digit3 1 p = 0 := by
  unfold digit3
  have h1 : 1 < 3^p := by
    have h0 : 3^1 ≤ 3^p :=
      Nat.pow_le_pow_of_le (by decide : 1 < 3) (by omega)
    omega
  rw [Nat.div_eq_of_lt h1]

/-- The residue-to-digit bridge: if `R ≡ 1 + 2·3^p (mod 3^(p+1))` with
`p ≥ 1`, then digit `p` of `R` is `2`. -/
theorem digit3_of_residue_two (R p : Nat) (hp1 : 1 ≤ p)
    (hr : R % 3^(p+1) = 1 + 2 * 3^p) :
    digit3 R p = 2 := by
  have hlt : 1 + 2 * 3^p < 3^(p+1) := by
    have h1 : 1 < 3^p := by
      have h0 : 3^1 ≤ 3^p :=
        Nat.pow_le_pow_of_le (by decide : 1 < 3) (by omega)
      omega
    rw [pow_succ_mul]
    omega
  have hmod : (1 + 2 * 3^p) % 3^(p+1) = 1 + 2 * 3^p :=
    Nat.mod_eq_of_lt hlt
  have hcongr := digit3_mod_congr R (1 + 2 * 3^p) p (by rw [hr, hmod])
  rw [hcongr, show 1 + 2 * 3^p = 1 + 3^p * 2 from by ring,
      digit3_add_pow 1 2 p, digit3_one_pos p hp1]

/-- The residue-to-digit bridge, one case: `R ≡ 1 + 3^p` with `p ≥ 1`
gives digit `p` equal to one. -/
theorem digit3_of_residue_one (R p : Nat) (hp1 : 1 ≤ p)
    (hr : R % 3^(p+1) = 1 + 3^p) :
    digit3 R p = 1 := by
  have hlt : 1 + 3^p < 3^(p+1) := by
    have h1 : 1 < 3^p := by
      have h0 : 3^1 ≤ 3^p :=
        Nat.pow_le_pow_of_le (by decide : 1 < 3) (by omega)
      omega
    rw [pow_succ_mul]
    omega
  have hmod : (1 + 3^p) % 3^(p+1) = 1 + 3^p :=
    Nat.mod_eq_of_lt hlt
  have hcongr := digit3_mod_congr R (1 + 3^p) p (by rw [hr, hmod])
  rw [hcongr, show 1 + 3^p = 1 + 3^p * 1 from by ring,
      digit3_add_pow 1 1 p, digit3_one_pos p hp1]

/-- **The verdict bridge.**  A digit two at any position kills the
Cantor verdict. -/
theorem noTernaryTwo_of_digit_two :
    ∀ (p x : Nat), digit3 x p = 2 → noTernaryTwo x = false
  | 0, x => by
      intro h
      unfold digit3 at h
      rw [Nat.pow_zero, Nat.div_one] at h
      have hx0 : ¬ (x = 0) := by
        intro he
        rw [he] at h
        exact absurd h (by decide)
      rw [noTernaryTwo.eq_def x, if_neg hx0, if_pos h]
  | p+1, x => by
      intro h
      have hx0 : ¬ (x = 0) := by
        intro he
        rw [he] at h
        have h0 : digit3 0 (p+1) = 0 := by
          unfold digit3
          rw [Nat.zero_div, Nat.zero_mod]
        rw [h0] at h
        exact absurd h (by decide)
      rw [noTernaryTwo.eq_def x, if_neg hx0]
      by_cases hm : x % 3 = 2
      · rw [if_pos hm]
      · rw [if_neg hm]
        exact noTernaryTwo_of_digit_two p (x / 3) (by
          unfold digit3 at h ⊢
          rw [Nat.div_div_eq_div_mul, Nat.mul_comm 3 (3^p), ← Nat.pow_succ]
          exact h)

/-! ## §1 The LTE tower coefficient — the spine (green engine) -/

/-- The tower coefficient: `4^(3^v) = 1 + 3^(v+1) * lteCoeff v`. -/
def lteCoeff : Nat → Nat
  | 0 => 1
  | r+1 =>
      let c := lteCoeff r
      c + 3^(r+1) * c^2 + 3^(2*r+1) * c^3

/-- **THE TOWER IDENTITY.**  `4^(3^v) = 1 + 3^(v+1) * lteCoeff v`. -/
theorem pow4_three_power_lte_exact : ∀ r : Nat,
    4^(3^r) = 1 + 3^(r+1) * lteCoeff r
  | 0 => by norm_num [lteCoeff]
  | r+1 => by
      have ih := pow4_three_power_lte_exact r
      calc
        4^(3^(r+1)) = (4^(3^r))^3 := by
          rw [Nat.pow_succ, Nat.pow_mul]
        _ = (1 + 3^(r+1) * lteCoeff r)^3 := by rw [ih]
        _ = 1 + 3^((r+1)+1) * lteCoeff (r+1) := by
          simp only [lteCoeff]
          rw [show (r+1)+1 = r+2 by omega]
          have h1 : 3^(r+1) = 3^r * 3 := by rw [Nat.pow_succ]
          have h2 : 3^(2*r+1) = (3^r)^2 * 3 := by
            calc
              3^(2*r+1) = 3^((r+r)+1) := by congr 1 <;> omega
              _ = 3^(r+r) * 3 := by rw [Nat.pow_succ]
              _ = (3^r * 3^r) * 3 := by rw [Nat.pow_add]
              _ = (3^r)^2 * 3 := by ring
          have h3 : 3^(r+2) = 3^r * 9 := by
            calc
              3^(r+2) = 3^((r+1)+1) := by congr 1 <;> omega
              _ = 3^(r+1) * 3 := by rw [Nat.pow_succ]
              _ = 3^r * 9 := by rw [h1]; ring
          rw [h3, h1, h2]
          ring

/-- The exact LTE quotient is always one modulo three. -/
theorem lteCoeff_mod3_one : ∀ r : Nat, lteCoeff r % 3 = 1
  | 0 => by decide
  | r+1 => by
      have ih := lteCoeff_mod3_one r
      simp only [lteCoeff]
      have hpow1 : 3^(r+1) % 3 = 0 := by
        rw [Nat.pow_succ]
        simp
      have hpow2 : 3^(2*r+1) % 3 = 0 := by
        rw [Nat.pow_succ]
        simp
      simp [Nat.add_mod, Nat.mul_mod, hpow1, hpow2, ih]

/-- Every power of four is one modulo three. -/
theorem pow4_mod3 (r : Nat) : 4^r % 3 = 1 := by
  induction r with
  | zero => decide
  | succ r ih =>
      rw [Nat.pow_succ, Nat.mul_mod, ih]

/-- Any multiple of the scale exponent is one modulo the next ternary
cut. -/
theorem pow4_scaled_mod_next (r u : Nat) :
    4^(3^r * u) % 3^(r+1) = 1 := by
  have hA := pow4_three_power_lte_exact r
  rw [Nat.pow_mul, hA, Nat.pow_mod]
  have hMgt1 : 1 < 3^(r+1) := by
    have h3 : 3^1 ≤ 3^(r+1) :=
      Nat.pow_le_pow_of_le (by decide : 1 < 3) (by omega)
    norm_num at h3 ⊢
  have hbase : (1 + 3^(r+1) * lteCoeff r) % 3^(r+1) = 1 := by
    simp [Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt hMgt1]
  simpa [hbase, Nat.mod_eq_of_lt hMgt1]

/-! ## §2 THE CUT RESIDUE — THE SECOND-DIGIT LAW -/

/-- The bounded-residue helper: `1 + r·3^(v+1) < 3^(v+2)` for `r < 3`. -/
theorem lt_cut_residue (v r : Nat) (hr : r < 3) :
    1 + r * 3^(v+1) < 3^(v+2) := by
  have h1 : 1 ≤ 3^(v+1) := by
    have hp : 0 < 3^(v+1) := Nat.pow_pos (by decide : 0 < 3)
    omega
  rcases ErdosTernary2.lt_three_cases r hr with h0 | h0 | h0
  · rw [h0, pow_succ_two]
    omega
  · rw [h0, pow_succ_two]
    omega
  · rw [h0, pow_succ_two]
    omega

/-- **THE CUT RESIDUE, EXACT.**  For every valuation cut `v` and every
multiplier `u`: `4^(3^v·u) % 3^(v+2) = 1 + (u % 3)·3^(v+1)` — the first
two nonzero ternary digits of the power are `1` and `u % 3`, and every
digit between them is zero. -/
theorem pow4_cut_residue_exact (v u : Nat) :
    4^(3^v * u) % 3^(v+2) = 1 + (u % 3) * 3^(v+1) := by
  have hK : 4^(3^v * u) = (1 + 3^(v+1) * lteCoeff v)^u := by
    rw [Nat.pow_mul, pow4_three_power_lte_exact]
  obtain ⟨s, hs⟩ := binom_two_term (3^(v+1) * lteCoeff v) u
  have huc : u * lteCoeff v % 3 = u % 3 := by
    rw [Nat.mul_mod, lteCoeff_mod3_one]
    omega
  -- the three-part split: the power = target + multiple of 3^(v+2)
  have hsplit : 4^(3^v * u) = (1 + (u % 3) * 3^(v+1)) +
      3^(v+2) * ((u * lteCoeff v) / 3 +
        3^v * (lteCoeff v * lteCoeff v * s)) := by
    rw [hK, hs]
    have hk := Nat.div_add_mod (u * lteCoeff v) 3
    rw [huc] at hk
    -- hk : 3 * ((u * lteCoeff v) / 3) + u % 3 = u * lteCoeff v
    have hmul : u * (3^(v+1) * lteCoeff v) =
        3^(v+2) * ((u * lteCoeff v) / 3) + (u % 3) * 3^(v+1) := by
      calc u * (3^(v+1) * lteCoeff v)
          = 3^(v+1) * (u * lteCoeff v) := by ring
        _ = 3^(v+1) * (3 * ((u * lteCoeff v) / 3) + u % 3) := by rw [hk]
        _ = 3^(v+2) * ((u * lteCoeff v) / 3) + (u % 3) * 3^(v+1) := by
            rw [pow_succ_two]
            ring
    have hcorr : (3^(v+1) * lteCoeff v) * (3^(v+1) * lteCoeff v) * s =
        3^(v+2) * (3^v * (lteCoeff v * lteCoeff v * s)) := by
      have hp2 : 3^(v+1) * 3^(v+1) = 3^(v+2) * 3^v := by
        rw [← Nat.pow_add, ← Nat.pow_add]
        congr 1; omega
      calc (3^(v+1) * lteCoeff v) * (3^(v+1) * lteCoeff v) * s
          = (3^(v+1) * 3^(v+1)) * (lteCoeff v * lteCoeff v * s) := by
              ring
        _ = (3^(v+2) * 3^v) * (lteCoeff v * lteCoeff v * s) := by rw [hp2]
        _ = 3^(v+2) * (3^v * (lteCoeff v * lteCoeff v * s)) := by ring
    rw [hmul, hcorr]
    ring
  rw [hsplit, add_mod_of_dvd _ _ _ (by
    refine ⟨(u * lteCoeff v) / 3 + 3^v * (lteCoeff v * lteCoeff v * s),
      ?_⟩
    ring),
    Nat.mod_eq_of_lt (lt_cut_residue v (u % 3) (Nat.mod_lt _ (by decide)))]

/-- Every positive exponent decomposes as `3^v·u` with `u` not
divisible by three — the valuation cut. -/
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

/-- **THE SECOND-DIGIT LAW (rider form).**  A rider `K` with valuation
cut `K = 3^v·u` (so `u ≡ 1 mod 3`) owns: digit `0` equal to one, digits
`1..v` equal to zero, and digit `v+1` equal to one.  The second-lowest
set digit of every rider IS `v₃(K)+1`. -/
theorem rider_second_digit_residue (K : Nat)
    (hK : 0 < K) (hrider : noTernaryTwo (4^K) = true) :
    ∃ v u : Nat, K = 3^v * u ∧ u % 3 = 1 ∧
      digit3 (4^K) 0 = 1 ∧
      (∀ j : Nat, 0 < j → j ≤ v → digit3 (4^K) j = 0) ∧
      digit3 (4^K) (v + 1) = 1 := by
  obtain ⟨v, u, hKu, hu3⟩ := valuation_decomp K hK
  have hu1 : u % 3 = 1 := by
    rcases ErdosTernary2.lt_three_cases (u % 3)
      (Nat.mod_lt _ (show 0 < 3 by decide)) with h | h | h
    · omega
    · exact h
    · exfalso
      have hres := pow4_cut_residue_exact v u
      rw [h] at hres
      have hv1 : 1 ≤ v + 1 := by omega
      have hfire : digit3 (4^K) (v+1) = 2 := by
        have hmod : 4^K % 3^((v+1)+1) =
            (1 + 2 * 3^(v+1)) % 3^((v+1)+1) := by
          rw [show ((v:Nat)+1)+1 = v+2 from by omega, hKu, hres,
              Nat.mod_eq_of_lt (lt_cut_residue v 2 (by decide))]
        have hcon := digit3_mod_congr (4^K) (1 + 2 * 3^(v+1)) (v+1) hmod
        have hres2 : (1 + 2 * 3^(v+1)) % 3^((v+1)+1)
            = 1 + 2 * 3^(v+1) := by
          rw [show ((v:Nat)+1)+1 = v+2 from by omega]
          exact Nat.mod_eq_of_lt (lt_cut_residue v 2 (by decide))
        rw [hcon]
        exact digit3_of_residue_two (1 + 2 * 3^(v+1)) (v+1) hv1 hres2
      rw [noTernaryTwo_of_digit_two (v+1) (4^K) hfire] at hrider
      exact absurd hrider (by decide)
  refine ⟨v, u, hKu, hu1, ?_, ?_, ?_⟩
  · -- digit 0 = 1
    unfold digit3
    rw [Nat.pow_zero, Nat.div_one]
    exact (pow4_mod3 K).symm
  · -- digits 1..v are zero: 4^K ≡ 1 mod 3^(v+1), and the congruence
    -- descends to every 3^(j+1) with j ≤ v
    intro j hjpos hjv
    have hnext : 4^(3^v * u) % 3^(v+1) = 1 := pow4_scaled_mod_next v u
    have hdvd : 3^(j+1) ∣ 3^(v+1) := by
      refine ⟨3^(v-j), ?_⟩
      rw [← Nat.pow_add]
      congr 1; omega
    have hmodj : 4^K % 3^(j+1) = 1 % 3^(j+1) := by
      rw [hKu, ← Nat.mod_mod_of_dvd (4^(3^v * u)) hdvd, hnext]
      rfl
    have hcon := digit3_mod_congr (4^K) 1 j hmodj
    rw [hcon]
    exact digit3_one_pos j hjpos
  · -- digit v+1 = 1 (u % 3 = 1)
    have hres := pow4_cut_residue_exact v u
    have hmod : 4^K % 3^((v+1)+1) =
        (1 + 1 * 3^(v+1)) % 3^((v+1)+1) := by
      rw [show ((v:Nat)+1)+1 = v+2 from by omega, hKu, hres, hu1,
          Nat.mod_eq_of_lt (lt_cut_residue v 1 (by decide))]
    have hres2 : (1 + 1 * 3^(v+1)) % 3^((v+1)+1)
        = 1 + 1 * 3^(v+1) := by
      rw [show ((v:Nat)+1)+1 = v+2 from by omega]
      exact Nat.mod_eq_of_lt (lt_cut_residue v 1 (by decide))
    have hcon := digit3_mod_congr (4^K) (1 + 1 * 3^(v+1)) (v+1) hmod
    rw [hcon]
    exact digit3_of_residue_one (1 + 1 * 3^(v+1)) (v+1) (by omega) hres2

/-! ## §3 THE WINDOW LAW — the digit stream reads the diagonal -/

/-- The correction-term divisibility: with `j ≤ v`, the binomial tail
`(3^(v+1)·c)²·s` is divisible by `3^(v+2+j)`. -/
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

/-- Exact quotient projection through a low prefix. -/
theorem prefix_slice_quotient_exact
    (b P tail q : Nat) (hP : P < 3^b) :
    (P + 3^b * tail) / 3^(b+q) = tail / 3^q := by
  have hp : 0 < 3^b := Nat.pow_pos (by decide)
  rw [Nat.pow_add, ← Nat.div_div_eq_div_mul]
  rw [Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt hP, Nat.zero_add]

/-- Exact ternary digit projection through a low prefix. -/
theorem prefix_slice_digit_exact
    (b P tail q : Nat) (hP : P < 3^b) :
    digit3 (P + 3^b * tail) (b+q) = digit3 tail q := by
  unfold digit3
  rw [prefix_slice_quotient_exact b P tail q hP]

/-- **THE WINDOW LAW.**  For every valuation cut `v` and every reduced
exponent `u`, the digit stream of `4^(3^v·u)` at row `v+1+j` IS the
`j`-th ternary digit of `u · lteCoeff v`, for every `j ≤ v`. -/
theorem diagonal_window_law (v u j : Nat) (hj : j ≤ v) :
    digit3 (4^(3^v * u)) (v + 1 + j) =
      digit3 (u * lteCoeff v) j := by
  have hLTE : 4^(3^v) = 1 + 3^(v+1) * lteCoeff v :=
    pow4_three_power_lte_exact v
  have hK : 4^(3^v * u) = (4^(3^v))^u := by rw [Nat.pow_mul]
  obtain ⟨s, hs⟩ := binom_two_term (3^(v+1) * lteCoeff v) u
  have hu : u * (3^(v+1) * lteCoeff v) =
      3^(v+1) * (u * lteCoeff v) := by ring
  have hcorr : 3^(v+2+j) ∣ (3^(v+1) * lteCoeff v) *
      (3^(v+1) * lteCoeff v) * s :=
    pow_cut_dvd v j (lteCoeff v) s hj
  have hcongr : 4^(3^v * u) % 3^((v+1+j)+1) =
      (1 + 3^(v+1) * (u * lteCoeff v)) % 3^((v+1+j)+1) := by
    rw [show 3^((v+1+j)+1) = 3^(v+2+j) from by congr 1; omega]
    rw [hK, hLTE, hs, hu]
    exact add_mod_of_dvd _ _ _ hcorr
  have hdig := digit3_mod_congr (4^(3^v * u))
    (1 + 3^(v+1) * (u * lteCoeff v)) (v+1+j) hcongr
  rw [hdig]
  have h1lt : 1 < 3^(v+1) := by
    cases v with
    | zero => norm_num
    | succ v =>
        have h0 : 0 < 3^(v+1) := Nat.pow_pos (by decide)
        rw [pow_succ_mul]
        omega
  rw [prefix_slice_digit_exact (v+1) 1 (u * lteCoeff v) j h1lt]

/-! ## §4 THE FIRE LADDER — levels one through five -/

/-- The coefficient's trits freeze: each recursion step preserves the
previous coefficient modulo `3^(v+1)`. -/
theorem lteCoeff_succ_mod (v : Nat) :
    lteCoeff (v+1) % 3^(v+1) = lteCoeff v % 3^(v+1) := by
  have hsplit : 3^(2*v+1) = 3^(v+1) * 3^v := by
    rw [← Nat.pow_add]
    congr 1; omega
  have hd1 : 3^(v+1) ∣ 3^(v+1) * (lteCoeff v)^2 := ⟨_, rfl⟩
  have hd2 : 3^(v+1) ∣ 3^(2*v+1) * (lteCoeff v)^3 :=
    ⟨3^v * (lteCoeff v)^3, by rw [hsplit]; ring⟩
  simp only [lteCoeff]
  rw [add_mod_of_dvd _ _ _ hd2, add_mod_of_dvd _ _ _ hd1]

theorem mod_dvd_modeq (a b m n : Nat) (hmn : m ∣ n) (h : a % n = b % n) :
    a % m = b % m := by
  rw [← Nat.mod_mod_of_dvd a hmn, h, Nat.mod_mod_of_dvd b hmn]

/-- **THE FROZEN DIAGONAL.**  From index `v` upward, the coefficient is
constant modulo `3^(v+1)`. -/
theorem lteCoeff_stable (v w : Nat) (hw : v ≤ w) :
    lteCoeff w % 3^(v+1) = lteCoeff v % 3^(v+1) := by
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
        have h2 := mod_dvd_modeq (lteCoeff (w+1))
          (lteCoeff w) (3^(v+1)) (3^(w+1)) hdvd h
        rw [h2]
        exact ih hwv
      · have hvw : v = w + 1 := by omega
        subst hvw
        rfl

/-- The frozen diagonal's residue modulo 9 from index one: `7`. -/
theorem lteCoeff_mod9 (v : Nat) (hv : 1 ≤ v) : lteCoeff v % 9 = 7 := by
  have h := lteCoeff_stable 1 v hv
  have hbase : lteCoeff 1 % 3^(1+1) = 7 := by decide
  calc lteCoeff v % 9
      = lteCoeff v % 3^(1+1) := by norm_num
    _ = lteCoeff 1 % 3^(1+1) := h
    _ = 7 := hbase

/-- The frozen diagonal's residue modulo 27 from index two: `16`. -/
theorem lteCoeff_mod27 (v : Nat) (hv : 2 ≤ v) : lteCoeff v % 27 = 16 := by
  have h := lteCoeff_stable 2 v hv
  have hbase : lteCoeff 2 % 3^(2+1) = 16 := by decide
  calc lteCoeff v % 27
      = lteCoeff v % 3^(2+1) := by norm_num
    _ = lteCoeff 2 % 3^(2+1) := h
    _ = 16 := hbase

/-- The frozen diagonal's residue modulo 81 from index three: `16`. -/
theorem lteCoeff_mod81 (v : Nat) (hv : 3 ≤ v) : lteCoeff v % 81 = 16 := by
  have h := lteCoeff_stable 3 v hv
  have hbase : lteCoeff 3 % 3^(3+1) = 16 := by decide
  calc lteCoeff v % 81
      = lteCoeff v % 3^(3+1) := by norm_num
    _ = lteCoeff 3 % 3^(3+1) := h
    _ = 16 := hbase

/-- **NEW (S079).**  The frozen diagonal's residue modulo 243 from
index four: `178`. -/
theorem lteCoeff_mod243 (v : Nat) (hv : 4 ≤ v) :
    lteCoeff v % 243 = 178 := by
  have h := lteCoeff_stable 4 v hv
  have hbase : lteCoeff 4 % 3^(4+1) = 178 := by
    unfold lteCoeff
    decide
  calc lteCoeff v % 243
      = lteCoeff v % 3^(4+1) := by norm_num
    _ = lteCoeff 4 % 3^(4+1) := h
    _ = 178 := hbase

/-- **NEW (S079).**  The frozen diagonal's residue modulo 729 from
index five: `664`. -/
theorem lteCoeff_mod729 (v : Nat) (hv : 5 ≤ v) :
    lteCoeff v % 729 = 664 := by
  have h := lteCoeff_stable 5 v hv
  have hbase : lteCoeff 5 % 3^(5+1) = 664 := by
    unfold lteCoeff
    decide
  calc lteCoeff v % 729
      = lteCoeff v % 3^(5+1) := by norm_num
    _ = lteCoeff 5 % 3^(5+1) := h
    _ = 664 := hbase

/-- **LEVEL ONE.**  Every core `u ≡ 1 mod 9` at every cut `v ≥ 1` fires
its digit two at row `v+2`. -/
theorem window_fire_level1 (v : Nat) (hv : 1 ≤ v) (u : Nat)
    (hu : u % 9 = 1) :
    digit3 (4^(3^v * u)) (v + 2) = 2 := by
  have hw := diagonal_window_law v u 1 (by omega)
  have hc := lteCoeff_mod9 v hv
  have humod : (u * lteCoeff v) % 9 = 7 := by
    rw [Nat.mul_mod, hu, hc]
  have hd : digit3 (u * lteCoeff v) 1 = 2 := by
    unfold digit3
    omega
  rw [show v + 2 = v + 1 + 1 from rfl, hw]
  exact hd

/-- **LEVEL TWO.**  Every core `u ≡ 13 or 25 mod 27` at every cut
`v ≥ 2` fires its digit two at row `v+3`. -/
theorem window_fire_level2 (v : Nat) (hv : 2 ≤ v) (u : Nat)
    (hu : u % 27 = 13 ∨ u % 27 = 25) :
    digit3 (4^(3^v * u)) (v + 3) = 2 := by
  have hw := diagonal_window_law v u 2 (by omega)
  have hc := lteCoeff_mod27 v hv
  have hd : digit3 (u * lteCoeff v) 2 = 2 := by
    unfold digit3
    rcases hu with h13 | h25
    · have humod : (u * lteCoeff v) % 27 = 19 := by
        rw [Nat.mul_mod, h13, hc]
      omega
    · have humod : (u * lteCoeff v) % 27 = 22 := by
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
  have hd : digit3 (u * lteCoeff v) 3 = 2 := by
    unfold digit3
    rcases hu with h4 | h34 | h49 | h70
    · have humod : (u * lteCoeff v) % 81 = 64 := by
        rw [Nat.mul_mod, h4, hc]
      omega
    · have humod : (u * lteCoeff v) % 81 = 58 := by
        rw [Nat.mul_mod, h34, hc]
      omega
    · have humod : (u * lteCoeff v) % 81 = 55 := by
        rw [Nat.mul_mod, h49, hc]
      omega
    · have humod : (u * lteCoeff v) % 81 = 67 := by
        rw [Nat.mul_mod, h70, hc]
      omega
  rw [show v + 4 = v + 1 + 3 from rfl, hw]
  exact hd

/-- **LEVEL FOUR (NEW, S079).**  Every core `u` in the level-4 fire set
`{16, 31, 61, 76, 124, 139, 169, 184} mod 243` at every cut `v ≥ 4`
fires its digit two at row `v+5`. -/
theorem window_fire_level4 (v : Nat) (hv : 4 ≤ v) (u : Nat)
    (hu : u % 243 = 16 ∨ u % 243 = 31 ∨ u % 243 = 61 ∨ u % 243 = 76 ∨
           u % 243 = 124 ∨ u % 243 = 139 ∨ u % 243 = 169 ∨
           u % 243 = 184) :
    digit3 (4^(3^v * u)) (v + 5) = 2 := by
  have hw := diagonal_window_law v u 4 (by omega)
  have hc := lteCoeff_mod243 v hv
  have hd : digit3 (u * lteCoeff v) 4 = 2 := by
    unfold digit3
    rcases hu with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
    · have humod : (u * lteCoeff v) % 243 = 175 := by
        rw [Nat.mul_mod, h1, hc]
      omega
    · have humod : (u * lteCoeff v) % 243 = 172 := by
        rw [Nat.mul_mod, h2, hc]
      omega
    · have humod : (u * lteCoeff v) % 243 = 166 := by
        rw [Nat.mul_mod, h3, hc]
      omega
    · have humod : (u * lteCoeff v) % 243 = 163 := by
        rw [Nat.mul_mod, h4, hc]
      omega
    · have humod : (u * lteCoeff v) % 243 = 202 := by
        rw [Nat.mul_mod, h5, hc]
      omega
    · have humod : (u * lteCoeff v) % 243 = 199 := by
        rw [Nat.mul_mod, h6, hc]
      omega
    · have humod : (u * lteCoeff v) % 243 = 193 := by
        rw [Nat.mul_mod, h7, hc]
      omega
    · have humod : (u * lteCoeff v) % 243 = 190 := by
        rw [Nat.mul_mod, h8, hc]
      omega
  rw [show v + 5 = v + 1 + 4 from rfl, hw]
  exact hd

/-- **LEVEL FIVE (NEW, S079).**  Every core `u` in the level-5 fire set
`{58, 103, 193, 205, 238, 250, 340, 385, 463, 508, 529, 574, 598, 643,
664, 709} mod 729` at every cut `v ≥ 5` fires its digit two at row
`v+6`. -/
theorem window_fire_level5 (v : Nat) (hv : 5 ≤ v) (u : Nat)
    (hu : u % 729 = 58 ∨ u % 729 = 103 ∨ u % 729 = 193 ∨
           u % 729 = 205 ∨ u % 729 = 238 ∨ u % 729 = 250 ∨
           u % 729 = 340 ∨ u % 729 = 385 ∨ u % 729 = 463 ∨
           u % 729 = 508 ∨ u % 729 = 529 ∨ u % 729 = 574 ∨
           u % 729 = 598 ∨ u % 729 = 643 ∨ u % 729 = 664 ∨
           u % 729 = 709) :
    digit3 (4^(3^v * u)) (v + 6) = 2 := by
  have hw := diagonal_window_law v u 5 (by omega)
  have hc := lteCoeff_mod729 v hv
  have hd : digit3 (u * lteCoeff v) 5 = 2 := by
    unfold digit3
    rcases hu with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 |
      h11 | h12 | h13 | h14 | h15 | h16
    · have humod : (u * lteCoeff v) % 729 = 604 := by
        rw [Nat.mul_mod, h1, hc]
      omega
    · have humod : (u * lteCoeff v) % 729 = 595 := by
        rw [Nat.mul_mod, h2, hc]
      omega
    · have humod : (u * lteCoeff v) % 729 = 577 := by
        rw [Nat.mul_mod, h3, hc]
      omega
    · have humod : (u * lteCoeff v) % 729 = 526 := by
        rw [Nat.mul_mod, h4, hc]
      omega
    · have humod : (u * lteCoeff v) % 729 = 568 := by
        rw [Nat.mul_mod, h5, hc]
      omega
    · have humod : (u * lteCoeff v) % 729 = 517 := by
        rw [Nat.mul_mod, h6, hc]
      omega
    · have humod : (u * lteCoeff v) % 729 = 499 := by
        rw [Nat.mul_mod, h7, hc]
      omega
    · have humod : (u * lteCoeff v) % 729 = 490 := by
        rw [Nat.mul_mod, h8, hc]
      omega
    · have humod : (u * lteCoeff v) % 729 = 523 := by
        rw [Nat.mul_mod, h9, hc]
      omega
    · have humod : (u * lteCoeff v) % 729 = 514 := by
        rw [Nat.mul_mod, h10, hc]
      omega
    · have humod : (u * lteCoeff v) % 729 = 607 := by
        rw [Nat.mul_mod, h11, hc]
      omega
    · have humod : (u * lteCoeff v) % 729 = 598 := by
        rw [Nat.mul_mod, h12, hc]
      omega
    · have humod : (u * lteCoeff v) % 729 = 496 := by
        rw [Nat.mul_mod, h13, hc]
      omega
    · have humod : (u * lteCoeff v) % 729 = 487 := by
        rw [Nat.mul_mod, h14, hc]
      omega
    · have humod : (u * lteCoeff v) % 729 = 580 := by
        rw [Nat.mul_mod, h15, hc]
      omega
    · have humod : (u * lteCoeff v) % 729 = 571 := by
        rw [Nat.mul_mod, h16, hc]
      omega
  rw [show v + 6 = v + 1 + 5 from rfl, hw]
  exact hd

/-! ### The witness receipts — uniform laws, no bounded decides -/

/-- Witness receipt: `4^9` fires its digit two at row 4, delivered by
the uniform level-one family (`9 = 3^2·1`, `u = 1 ≡ 1 mod 9`). -/
theorem fire_nine_row_four : digit3 (4^9) 4 = 2 := by
  have h := window_fire_level1 2 (by omega) 1 (by decide)
  have hK : (3:Nat)^2 * 1 = 9 := by decide
  rw [hK] at h
  exact h

/-- Witness receipt: `4^108` fires its digit two at row 7, delivered by
the uniform level-three family (`108 = 3^3·4`, `u = 4 ≡ 4 mod 81`). -/
theorem fire_108_row_seven : digit3 (4^108) 7 = 2 := by
  have h := window_fire_level3 3 (by omega) 4 (Or.inl (by decide))
  have hK : (3:Nat)^3 * 4 = 108 := by decide
  rw [hK] at h
  exact h

/-- **NEW WITNESS (S079).**  `K = 1296 = 3^4·16` fires its digit two at
row 9, delivered by the uniform level-four family — no bounded decide. -/
theorem fire_1296_row_nine : digit3 (4^1296) 9 = 2 := by
  have h := window_fire_level4 4 (by omega) 16 (Or.inl (by decide))
  have hK : (3:Nat)^4 * 16 = 1296 := by decide
  rw [hK] at h
  exact h

/-- **NEW WITNESS (S079).**  `K = 14094 = 3^5·58` fires its digit two
at row 11, delivered by the uniform level-five family. -/
theorem fire_14094_row_eleven : digit3 (4^14094) 11 = 2 := by
  have h := window_fire_level5 5 (by omega) 58 (Or.inl (by decide))
  have hK : (3:Nat)^5 * 58 = 14094 := by decide
  rw [hK] at h
  exact h

/-- **NEW WITNESS (S079).**  `K = 42282 = 3^6·58` fires its digit two
at row 12, delivered by the uniform level-five family at cut six. -/
theorem fire_42282_row_twelve : digit3 (4^42282) 12 = 2 := by
  have h := window_fire_level5 6 (by omega) 58 (Or.inl (by decide))
  have hK : (3:Nat)^6 * 58 = 42282 := by decide
  rw [hK] at h
  exact h

/-- The full kill-chain instance: `4^1296` fails `noTernaryTwo`, by the
uniform level-four law alone. -/
theorem no22_four_pow_1296 : noTernaryTwo (4^1296) = false :=
  noTernaryTwo_of_digit_two 9 (4^1296) fire_1296_row_nine

/-- `4^14094` fails `noTernaryTwo`, by the uniform level-five law. -/
theorem no22_four_pow_14094 : noTernaryTwo (4^14094) = false :=
  noTernaryTwo_of_digit_two 11 (4^14094) fire_14094_row_eleven

/-- `4^42282` fails `noTernaryTwo`, by the uniform level-five law at
cut six. -/
theorem no22_four_pow_42282 : noTernaryTwo (4^42282) = false :=
  noTernaryTwo_of_digit_two 12 (4^42282) fire_42282_row_twelve

/-! ## §5 THE EXPONENT-TRIT KILLING LAW — the master dynamics -/

/-- **THE KILLING LAW (maximally general — no hypotheses).**  For every
base exponent `r`, every trit lift `t`, and every position `j`: the
payload digit at position `j+1` of the lifted exponent `r + t·3^j` IS
the parent's digit plus `t`, modulo three.  The exponent trit ADDS to
the payload digit — the master dynamics of the dust tree. -/
theorem pow4_killing_trit (r t j : Nat) :
    digit3 (4^(r + t * 3^j)) (j+1) =
      (digit3 (4^r) (j+1) + t) % 3 := by
  have hK : 4^(r + t * 3^j) = 4^r * (1 + 3^(j+1) * lteCoeff j)^t := by
    rw [Nat.pow_add, Nat.mul_comm t (3^j), Nat.pow_mul,
        pow4_three_power_lte_exact]
  obtain ⟨s, hs⟩ := binom_two_term (3^(j+1) * lteCoeff j) t
  have hcorrdvd : 3^((j+1)+1) ∣ 4^r * ((3^(j+1) * lteCoeff j) *
      (3^(j+1) * lteCoeff j) * s) := by
    refine ⟨4^r * (3^j * (lteCoeff j * lteCoeff j * s)), ?_⟩
    have hp2 : 3^(j+1) * 3^(j+1) = 3^((j+1)+1) * 3^j := by
      rw [← Nat.pow_add, ← Nat.pow_add]
      congr 1; omega
    calc 4^r * ((3^(j+1) * lteCoeff j) * (3^(j+1) * lteCoeff j) * s)
        = 4^r * ((3^(j+1) * 3^(j+1)) * (lteCoeff j * lteCoeff j * s)) := by
            ring
      _ = 4^r * ((3^((j+1)+1) * 3^j) * (lteCoeff j * lteCoeff j * s)) := by
            rw [hp2]
      _ = 3^((j+1)+1) * (4^r * (3^j * (lteCoeff j * lteCoeff j * s))) := by
            ring
  have hmod : (4^r * (1 + 3^(j+1) * lteCoeff j)^t) % 3^((j+1)+1) =
      (4^r + 3^(j+1) * (t * lteCoeff j * 4^r)) % 3^((j+1)+1) := by
    rw [hs]
    have hsplit : 4^r * (1 + t * (3^(j+1) * lteCoeff j) +
        (3^(j+1) * lteCoeff j) * (3^(j+1) * lteCoeff j) * s) =
        (4^r + 3^(j+1) * (t * lteCoeff j * 4^r)) +
          4^r * ((3^(j+1) * lteCoeff j) * (3^(j+1) * lteCoeff j) * s) := by
      ring
    rw [hsplit, add_mod_of_dvd _ _ _ hcorrdvd]
  have hcongr := digit3_mod_congr (4^r * (1 + 3^(j+1) * lteCoeff j)^t)
    (4^r + 3^(j+1) * (t * lteCoeff j * 4^r)) (j+1) hmod
  rw [hK, hcongr, digit3_add_pow]
  have hc1 : lteCoeff j % 3 = 1 := lteCoeff_mod3_one j
  have hc2 : 4^r % 3 = 1 := pow4_mod3 r
  have hmod3 : (t * lteCoeff j * 4^r) % 3 = t % 3 := by
    have e1 : (t * lteCoeff j) % 3 = t % 3 := by
      rw [Nat.mul_mod, hc1]
      omega
    have e2 : (t % 3 * (4^r % 3)) % 3 = t % 3 := by
      rw [hc2]
      omega
    calc t * lteCoeff j * 4^r % 3
        = (t * lteCoeff j) % 3 * (4^r % 3) % 3 := Nat.mul_mod _ _ _
      _ = t % 3 * (4^r % 3) % 3 := by rw [e1]
      _ = t % 3 := e2
  omega

/-- **THE WHEEL: EXACTLY ONE LIFT FIRES.**  Of the three trit lifts of
any dust node, exactly one owns the payload digit two at the lifted
position.  The dust tree is a full binary tree: every node has exactly
one dead child and two live children. -/
theorem wheel_fire_exists (r j : Nat) :
    ∃ t : Nat, t < 3 ∧ digit3 (4^(r + t * 3^j)) (j+1) = 2 := by
  have hd := digit3_lt_three (4^r) (j+1)
  rcases ErdosTernary2.lt_three_cases (digit3 (4^r) (j+1)) hd
    with h | h | h
  · refine ⟨2, by omega, ?_⟩
    rw [pow4_killing_trit r 2 j, h]
  · refine ⟨1, by omega, ?_⟩
    rw [pow4_killing_trit r 1 j, h]
  · refine ⟨0, by omega, ?_⟩
    rw [pow4_killing_trit r 0 j, h]

/-- **THE WHEEL: NO SECOND FIRES.**  Two distinct trit lifts cannot both
fire — the firing lift is unique. -/
theorem wheel_fire_unique (r j : Nat) (t1 t2 : Nat)
    (ht1 : t1 < 3) (ht2 : t2 < 3)
    (h1 : digit3 (4^(r + t1 * 3^j)) (j+1) = 2)
    (h2 : digit3 (4^(r + t2 * 3^j)) (j+1) = 2) : t1 = t2 := by
  have hk1 := pow4_killing_trit r t1 j
  have hk2 := pow4_killing_trit r t2 j
  rw [h1] at hk1
  rw [h2] at hk2
  omega

end BlockLaw406

/-! ## THE RECEIPTS BOARD -/

#check BlockLaw406.pow4_cut_residue_exact
#check BlockLaw406.rider_second_digit_residue
#check BlockLaw406.diagonal_window_law
#check BlockLaw406.window_fire_level4
#check BlockLaw406.window_fire_level5
#check BlockLaw406.pow4_killing_trit
#check BlockLaw406.wheel_fire_exists
#check BlockLaw406.wheel_fire_unique
#check BlockLaw406.fire_1296_row_nine

#print axioms BlockLaw406.pow4_cut_residue_exact
#print axioms BlockLaw406.rider_second_digit_residue
#print axioms BlockLaw406.diagonal_window_law
#print axioms BlockLaw406.window_fire_level1
#print axioms BlockLaw406.window_fire_level2
#print axioms BlockLaw406.window_fire_level3
#print axioms BlockLaw406.window_fire_level4
#print axioms BlockLaw406.window_fire_level5
#print axioms BlockLaw406.fire_1296_row_nine
#print axioms BlockLaw406.fire_14094_row_eleven
#print axioms BlockLaw406.fire_42282_row_twelve
#print axioms BlockLaw406.pow4_killing_trit
#print axioms BlockLaw406.wheel_fire_exists
#print axioms BlockLaw406.wheel_fire_unique

#eval "ERDOS406_BLOCKLAW_KERNEL_GREEN"
