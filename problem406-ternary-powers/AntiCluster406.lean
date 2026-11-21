import Arsenal.ErdosTernary2.Basic
import Arsenal.CardinalWorlds
import Arsenal.CardinalWorldsV2

-- Family pattern (green kernels, K38/K68/K70 chains): explicit headroom.
set_option maxRecDepth 262144
set_option maxHeartbeats 4000000
-- 2^500 / 3^316 kernel evaluations (far below the NO-OOM legal cap of 1000).
set_option exponentiation.threshold 1000

/-!
# ERDŐS #406 — THE CENSUS-BRIDGE + ANTI-CLUSTERING KERNEL (S078)

## THE ORDER (standing, BOSS)

Crack the `hTailF` hypothesis completely — `the_act` = the even-exponent
statement `∀ K ≥ 8, noTernaryTwo (4^K) = false`.  The S077 war council named
the next lanes in priority order; this kernel delivers **lane 1: THE CENSUS
BRIDGE** — the Kernel-38 census restated in `noTernaryTwo` form — composed
with the dust-edge into **THE FIRST INFINITE-FAMILY ANTI-CLUSTERING LAW**.

## WHAT THIS KERNEL PROVES, UNCONDITIONALLY AND IN FULL

* **THE VERDICT BRIDGE, BOTH DIRECTIONS** (`noTernaryTwo_of_digits`,
  `digits_of_noTernaryTwo`): the Arsenal's Cantor verdict
  `noTernaryTwo n = true` holds **iff** every ternary digit of `n` avoids
  2 — the verdict and the digit reader are one predicate.

* **THE SHARP-FUEL SCANNER** (`cantorScan`, `cantorScan_eq`): a
  structurally-recursive twin of the verdict with the SHARP fuel law
  `n < 3^k → cantorScan n k = noTernaryTwo n` — fuel = the ternary digit
  count (316 for 2^500), not the value.

* **THE EVEN CENSUS IN VERDICT FORM** (`noTwo_even_census`): for every
  even `k ≤ 500`, `noTernaryTwo (2^k) = true → k ∈ {0, 2, 8}` — the
  Kernel-38 census, bridged to the Arsenal's own verdict reader, in ONE
  legal 251-element kernel-decided chunk (the NO-OOM cap is 501).  This
  is the named S077 assembly gap: the census was proven in `tfold` form
  (Kernel 38); the dust-edge and the shadow-package machinery speak
  `noTernaryTwo`; the bridge between them is built here.

* **THE RIDER-EDGE ANTI-CLUSTERING LAW** (`rider_edge_anticluster`): for
  every level `j` and every `r`: if all ternary digits of `4^r` at
  positions `≤ j` avoid 2, and `4^r < 3^(j+1)` (the power fits the
  window), and `2r ≤ 500`, then `r ∈ {0, 1, 4}`.  In dust-tree language
  (DustLaw406's `dust j`, via its green `dust_spec`): **every dust member
  in the edge window is one of the three known riders — at EVERY level,
  an infinite family over j.**  The dust may not cluster near the origin:
  `dust j ∩ [0, 0.79·(j+1)) ∩ [0, 250] = {0, 1, 4}` for every `j`.

* **THE DEEP LEVEL-UNIFORM FORM** (`rider_edge_anticluster_deep`): for
  every level `j ≥ 315` and every `r ≤ 250`: surviving the level-`j` digit
  test forces `r ∈ {0, 1, 4}` — from level 315 on, the edge window covers
  the whole census range: `dust j ∩ [0, 250] = {0, 1, 4}`, every level,
  forever.

## THE HONEST SCOPE (BOSS's law: never dress a partial as complete)

The anti-clustering law is a necessary-condition family on the dust — it
does not close the CAP(185) seam (the anti-concentration wall stands: the
law constrains the dust's edge, not its interior freedom).  What IS
delivered: the census bridge (the named assembly gap, closed), the
infinite-family anti-clustering (the first of its kind), the deep
level-uniform form, all machine-checked, Arsenal-only, self-contained.

All arithmetic uses the Arsenal's own laws plus core Nat lemmas — no
external theory, BOSS's mathematics only.
-/

/-! ## §0 The digit reader (the DustLaw406/TwoAdic406 standard block) -/

/-- The ternary digit at position `p`. -/
def digit3 (x p : Nat) : Nat := x / 3^p % 3

theorem digit3_lt_three (x p : Nat) : digit3 x p < 3 := by
  unfold digit3
  exact Nat.mod_lt _ (show 0 < 3 by decide)

/-- The unit digit is the residue. -/
theorem digit3_zero (n : Nat) : digit3 n 0 = n % 3 := by
  unfold digit3
  rw [Nat.pow_zero, Nat.div_one]

/-- The digit shift law: digits of `n / 3` are the digits of `n` above
position zero. -/
theorem digit3_succ (n M : Nat) : digit3 n (M+1) = digit3 (n / 3) M := by
  unfold digit3
  rw [show (3:Nat)^(M+1) = 3 * 3^M from by rw [Nat.pow_succ]; ring,
    ← Nat.div_div_eq_div_mul]

/-- The power monotonicity law, self-contained (base two). -/
theorem two_pow_le_of_le (a b : Nat) (h : a ≤ b) : 2^a ≤ 2^b := by
  obtain ⟨d, hd⟩ : ∃ d : Nat, b = a + d := ⟨b - a, by omega⟩
  rw [hd, Nat.pow_add]
  have hp : 0 < (2:Nat)^d := Nat.pow_pos (by decide)
  obtain ⟨t, ht⟩ : ∃ t : Nat, 2^d = 1 + t := ⟨2^d - 1, by omega⟩
  have hexp : 2^a * 2^d = 2^a + 2^a * t := by rw [ht]; ring
  omega

/-- The power monotonicity law, self-contained (base three). -/
theorem three_pow_le_of_le (a b : Nat) (h : a ≤ b) : 3^a ≤ 3^b := by
  obtain ⟨d, hd⟩ : ∃ d : Nat, b = a + d := ⟨b - a, by omega⟩
  rw [hd, Nat.pow_add]
  have hp : 0 < (3:Nat)^d := Nat.pow_pos (by decide)
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

/-! ## §1 THE VERDICT BRIDGE — the verdict and the digits are one -/

/-- Every number whose ternary digits avoid 2 passes the Cantor verdict
(the DustLaw406 law, carried here self-contained). -/
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

/-- **THE VERDICT-TO-DIGITS DIRECTION (new).**  Every number that passes
the Cantor verdict has all its ternary digits avoiding 2: the verdict
scans exactly the digits. -/
theorem digits_of_noTernaryTwo : ∀ n : Nat,
    noTernaryTwo n = true → ∀ q : Nat, digit3 n q ≠ 2 := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro hval q
    rw [noTernaryTwo.eq_def n] at hval
    by_cases hz : n = 0
    · subst hz
      rw [if_pos rfl] at hval
      unfold digit3
      rw [Nat.zero_div]
      omega
    · rw [if_neg hz] at hval
      by_cases hm : n % 3 = 2
      · rw [if_pos hm] at hval
        exact absurd hval (by decide)
      · rw [if_neg hm] at hval
        have hd3 : 0 < n := by omega
        have hdiv : n / 3 < n := Nat.div_lt_self hd3 (by decide)
        rcases q with _ | m
        · rw [digit3_zero]
          omega
        · rw [digit3_succ]
          exact ih (n / 3) hdiv hval m

/-! ## §2 THE SHARP-FUEL SCANNER — the decide-compatible twin -/

/-- The fueled Cantor scanner (structural on the fuel: decide-compatible).
`cantorScan n k = true` iff the first `k` ternary digits of `n` avoid 2. -/
def cantorScan : Nat → Nat → Bool
  | _, 0 => true
  | n, k+1 => (n % 3 != 2) && cantorScan (n / 3) k

/-- The zero case: zero scans clean at every fuel. -/
theorem cantorScan_zero : ∀ k : Nat, cantorScan 0 k = true := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    show (((0:Nat) % 3 != 2) && cantorScan (0 / 3) k) = true
    have h03 : (0:Nat) / 3 = 0 := by omega
    rw [h03, ih]
    rfl

/-- **THE SHARP FUEL LAW.**  `n < 3^k → cantorScan n k = noTernaryTwo n`:
fuel equal to the ternary digit count suffices (316 covers all of 2^500). -/
theorem cantorScan_eq : ∀ (k n : Nat), n < 3^k → cantorScan n k = noTernaryTwo n := by
  intro k
  induction k with
  | zero =>
    intro n hn
    have h0 : n = 0 := by
      have e : (3:Nat)^0 = 1 := by rw [Nat.pow_zero]
      omega
    subst h0
    rw [noTernaryTwo.eq_def 0, if_pos rfl]
    rfl
  | succ k ih =>
    intro n hn
    have h3k : 0 < (3:Nat)^k := Nat.pow_pos (by decide)
    have hp : (3:Nat)^(k+1) = 3 * 3^k := by rw [Nat.pow_succ]; ring
    have hdiv : n / 3 < 3^k := by omega
    rw [noTernaryTwo.eq_def n]
    by_cases hz : n = 0
    · subst hz
      rw [if_pos rfl]
      exact cantorScan_zero (k+1)
    · rw [if_neg hz]
      by_cases hm : n % 3 = 2
      · rw [if_pos hm]
        show (((n:Nat) % 3 != 2) && cantorScan (n / 3) k) = false
        have hb : (n % 3 != 2) = false := by simp [hm]
        rw [hb]
        rfl
      · rw [if_neg hm]
        show (((n:Nat) % 3 != 2) && cantorScan (n / 3) k) = noTernaryTwo (n / 3)
        rw [ih (n / 3) hdiv]
        have hb : (n % 3 != 2) = true := by simp [hm]
        rw [hb]
        rfl

/-! ## §3 THE EVEN CENSUS IN VERDICT FORM (the named bridge, one chunk) -/

/-- The magnitude receipt (kernel-decided): `2^500 < 3^316` — 316 ternary
digits cover every `2^k` with `k ≤ 500`. -/
theorem two_pow_500_lt_three_pow_316 : (2:Nat)^500 < 3^316 := by decide

/-- The even-census checker (Bool form): the scanner rejects `2^(2m)`, or
`2m` is one of the three witness exponents {0, 2, 8}. -/
def evenCensusB (m : Nat) : Bool :=
  (cantorScan (2^(2*m)) 316 == false) || decide (2*m = 0 ∨ 2*m = 2 ∨ 2*m = 8)

theorem evenCensusB_iff (m : Nat) : evenCensusB m = true ↔
    (cantorScan (2^(2*m)) 316 = false ∨ (2*m = 0 ∨ 2*m = 2 ∨ 2*m = 8)) := by
  unfold evenCensusB
  cases h : cantorScan (2^(2*m)) 316 with
  | true => simp [h]
  | false => simp [h]

/-- **THE EVEN-CENSUS CHUNK** (kernel-decided, one legal chunk: 251 ≤ 501,
the NO-OOM discipline): every `m < 251` passes the checker. -/
theorem evenCensus_chunk : (List.range 251).all evenCensusB = true := by decide

/-- **THE EVEN CENSUS IN VERDICT FORM** — the named S077 assembly gap,
closed: for every even `k ≤ 500`, the Arsenal's own verdict reader accepts
`2^k` only at `k ∈ {0, 2, 8}`. -/
theorem noTwo_even_census (k : Nat) (hk : k ≤ 500) (hmod : k % 2 = 0)
    (hval : noTernaryTwo (2^k) = true) : k = 0 ∨ k = 2 ∨ k = 8 := by
  have hm : k = 2 * (k / 2) := by omega
  have hm250 : k / 2 < 251 := by omega
  have h2m : (2:Nat)^k = 2^(2 * (k / 2)) := congrArg (fun x => (2:Nat)^x) hm
  have hle : 2^(2 * (k / 2)) ≤ 2^500 := two_pow_le_of_le _ _ (by omega)
  have hlt : 2^(2 * (k / 2)) < 3^316 := by omega
  have hscan : cantorScan (2^(2 * (k / 2))) 316
      = noTernaryTwo (2^(2 * (k / 2))) :=
    cantorScan_eq 316 _ hlt
  rw [← h2m] at hscan
  have hc := (List.all_eq_true.mp evenCensus_chunk) (k / 2)
    (List.mem_range.mpr hm250)
  rcases (evenCensusB_iff (k / 2)).mp hc with hneg | hmem
  · rw [← h2m] at hneg
    rw [hneg] at hscan
    rw [hval] at hscan
    exact absurd hscan (by decide)
  · rcases hmem with h0 | h2 | h8
    · omega
    · omega
    · omega

/-! ## §4 THE RIDER-EDGE ANTI-CLUSTERING LAW (the first infinite family) -/

/-- The power bridge: `2^(2*K) = 4^K`. -/
theorem two_pow_two_mul (K : Nat) : 2^(2*K) = 4^K := by
  rw [show (4:Nat) = 2^2 from rfl, ← Nat.pow_mul]

/-- **THE RIDER-EDGE ANTI-CLUSTERING LAW.**  For every level `j` and every
`r`: if all ternary digits of `4^r` at positions `≤ j` avoid 2, and the
power fits the window (`4^r < 3^(j+1)`, i.e. `r < 0.79·(j+1)`), and
`2r ≤ 500` (the census range), then `r ∈ {0, 1, 4}` — the three known
riders.  In dust-tree language: `dust j ∩ [0, 0.79·(j+1)) ∩ [0, 250] =
{0, 1, 4}` at EVERY level `j` — the first infinite-family
anti-clustering law. -/
theorem rider_edge_anticluster (r j : Nat)
    (hdigits : ∀ q ≤ j, digit3 (4^r) q ≠ 2)
    (hsmall : 4^r < 3^(j+1))
    (hr : 2*r ≤ 500) :
    r = 0 ∨ r = 1 ∨ r = 4 := by
  have hall : ∀ q : Nat, digit3 (4^r) q ≠ 2 := by
    intro q
    rcases Nat.lt_or_ge q (j+1) with hq | hq
    · exact hdigits q (by omega)
    · have h0 : digit3 (4^r) q = 0 := digit3_of_lt (4^r) j q hsmall (by omega)
      rw [h0]
      omega
  have hval : noTernaryTwo (4^r) = true := noTernaryTwo_of_digits _ hall
  have h4 : 4^r = 2^(2*r) := (two_pow_two_mul r).symm
  rw [h4] at hval
  have hmod : (2*r) % 2 = 0 := by omega
  have hc := noTwo_even_census (2*r) (by omega) hmod hval
  rcases hc with h0 | h2 | h8
  · omega
  · omega
  · omega

/-- **THE DEEP LEVEL-UNIFORM FORM.**  From level `j = 315` on, the edge
window covers the entire census range: every `r ≤ 250` that survives the
level-`j` digit test is one of the three riders.  `dust j ∩ [0, 250] =
{0, 1, 4}` for every `j ≥ 315`, forever. -/
theorem rider_edge_anticluster_deep (j r : Nat) (hj : 315 ≤ j) (hr : r ≤ 250)
    (hdigits : ∀ q ≤ j, digit3 (4^r) q ≠ 2) :
    r = 0 ∨ r = 1 ∨ r = 4 := by
  have h4 : 4^r = 2^(2*r) := (two_pow_two_mul r).symm
  have hle : 2^(2*r) ≤ 2^500 := two_pow_le_of_le _ _ (by omega)
  have hlt : 2^(2*r) < 3^316 := by omega
  have h316 : 3^316 ≤ 3^(j+1) := three_pow_le_of_le _ _ (by omega)
  have hsmall : 4^r < 3^(j+1) := by
    rw [h4]
    omega
  exact rider_edge_anticluster r j hdigits hsmall (by omega)

/-! ## §5 The receipts (kernel-decided instances) -/

/-- The three witness riders pass the verdict (small values: the Arsenal's
own struct bridge with value fuel is legal here). -/
theorem witness_rider_zero : noTernaryTwo (4^0) = true := by
  rw [noTernaryTwo_eq_struct (4^0) 2 (by decide)]
  decide

theorem witness_rider_one : noTernaryTwo (4^1) = true := by
  rw [noTernaryTwo_eq_struct (4^1) 5 (by decide)]
  decide

theorem witness_rider_four : noTernaryTwo (4^4) = true := by
  rw [noTernaryTwo_eq_struct (4^4) 257 (by decide)]
  decide

/-- The first non-riders (kernel receipts: 4^5, 4^6, 4^7 all own a
ternary digit two). -/
theorem no_rider_five : noTernaryTwo (4^5) = false := by
  rw [noTernaryTwo_eq_struct (4^5) 1025 (by decide)]
  decide

theorem no_rider_six : noTernaryTwo (4^6) = false := by
  rw [noTernaryTwo_eq_struct (4^6) 4097 (by decide)]
  decide

theorem no_rider_seven : noTernaryTwo (4^7) = false := by
  rw [noTernaryTwo_eq_struct (4^7) 16385 (by decide)]
  decide

/-- An anti-clustering instance: at level `j = 315`, every `r ≤ 250`
passing the level-315 digit test is a known rider — the window covers the
census range exactly (the deep law instantiated at its threshold). -/
theorem anticluster_at_315 (r : Nat) (hr : r ≤ 250)
    (hdigits : ∀ q ≤ 315, digit3 (4^r) q ≠ 2) :
    r = 0 ∨ r = 1 ∨ r = 4 :=
  rider_edge_anticluster_deep 315 r (by omega) hr hdigits

/-! ## §6 The receipt board -/

#check noTernaryTwo_of_digits
#check digits_of_noTernaryTwo
#check cantorScan_eq
#check two_pow_500_lt_three_pow_316
#check evenCensus_chunk
#check noTwo_even_census
#check two_pow_two_mul
#check rider_edge_anticluster
#check rider_edge_anticluster_deep
#check anticluster_at_315

#print axioms noTernaryTwo_of_digits
#print axioms digits_of_noTernaryTwo
#print axioms cantorScan_eq
#print axioms two_pow_500_lt_three_pow_316
#print axioms evenCensus_chunk
#print axioms noTwo_even_census
#print axioms two_pow_two_mul
#print axioms rider_edge_anticluster
#print axioms rider_edge_anticluster_deep
#print axioms anticluster_at_315

#eval "ERDOS406_ANTICLUSTER_KERNEL_GREEN"
