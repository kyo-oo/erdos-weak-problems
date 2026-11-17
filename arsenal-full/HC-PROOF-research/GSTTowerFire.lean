import Mathlib
import GSTBladeWave

open GSTCanonicalSevenAxisBridge (digit3)
open GSTBladeWave (digit3_mod_pow)

namespace GSTTowerFire

/-!
# THE TOWER FIRES — Lane D's deep-hider laws, landed in Lean

Lane D (worldtrace) of the four-lane derivation volley, Lean-ified.
One new file, zero monolith bytes.  Machine receipts BEFORE landing
(fresh this session, exact big-int, modular tower arithmetic):

* `T1 30/30`  (n ∈ [1, 30]):  digit3 (4^(3^n)) (n+2) = 2
* `T2 28/28`  (n ∈ [3, 30]):  digit3 (4^(3^n + 1)) (n+4) = 2
* `T3 31/31`  (n ∈ [0, 30]):  digit3 (4^(2 * 3^n)) (n+1) = 2
* `T4 720/720`  (j ∈ [1, 8), n ∈ [1, 13), k ≤ n):
    digit3 (4^(j * 3^n)) (n+1+k) = digit3 (j * c n) k
* tower stabilization `c_(t+1) ≡ c_t mod 3^(t+1)`: 26/26 (t ∈ [0, 26))
* `c_t ≡ 7 mod 9` (t ∈ [1, 27)), `c_t ≡ 16 mod 81` (t ∈ [3, 27)), `c_0 = 1`

* **§1 THE c-TOWER.**  `c n = (4^(3^n) − 1) / 3^(n+1)` — integral by
  the green LTE cut `GSTBladeWave.four_pow_three_pow_dvd`.  The exact
  decomposition `four_pow_three_pow_eq : 4^(3^n) = 1 + 3^(n+1) * c n`,
  the cube recursion `c_succ_eq`, and the three congruence laws
  `c_mod3` (c ≡ 1 mod 3), `c_mod9` (c ≡ 7 mod 9 for n ≥ 1),
  `c_mod81` (c ≡ 16 mod 81 for n ≥ 3).

* **§2 THE READ GLUE.**  `div_add_lt` (divide-and-mod gluing) and
  `prefaced_digit`: if `s < 3^(n+1)` then row `n+1+k` of the prefaced
  object `3^(n+1) * A + s` is row `k` of `A`.

* **§3 THE TOWER READS.**  `tower_digit_read` (Lane D's L10 deep-hider
  master lemma): rows `n+1 .. 2n+1` of `4^(j * 3^n)` are the digits
  `0 .. n` of `j * c n` — ONE tower constant governs every scaled
  family at every depth.  The three fire laws fall out:
  `three_pow_fires` (3^n fires at row n+2 — L7), `two_mul_three_pow_fires`
  (2 * 3^n at row n+1 — L8), `three_pow_plus_one_fires` (3^n + 1 at
  row n+4 for n ≥ 3 — L9).
-/

set_option maxHeartbeats 400000

/-! ## §1 The c-tower -/

/-- The tower coefficients `c n = (4^(3^n) − 1) / 3^(n+1)`,
integral by the green LTE cut. -/
def c (n : Nat) : Nat := (4^(3^n) - 1) / 3^(n+1)

theorem c_zero : c 0 = 1 := by decide

/-- **The exact tower decomposition** — LTE made an equation. -/
theorem four_pow_three_pow_eq (n : Nat) : 4^(3^n) = 1 + 3^(n+1) * c n := by
  have h1 : (0:Nat) < 4^(3^n) := by positivity
  have h := GSTBladeWave.four_pow_three_pow_dvd 0 n
  rw [Nat.zero_add] at h
  obtain ⟨w, hw⟩ := h
  have hcw : c n = w := by
    unfold c
    rw [hw]
    exact Nat.mul_div_cancel_left _ (by positivity : (0:Nat) < 3^(n+1))
  rw [hcw]
  omega

/-- **The cube recursion of the tower.**  Cubing the decomposition of
`4^(3^n)` and matching orders gives `c (n+1)` from `c n` with exactly
the two binomial corrections. -/
theorem c_succ_eq (n : Nat) :
    c (n+1) = c n + 3^(n+1) * (c n * c n + 3^n * (c n * c n * c n)) := by
  have hpow : 4^(3^(n+1)) = (4^(3^n))^3 := by
    rw [Nat.pow_succ 3 n, Nat.pow_mul]
  have key : 1 + 3^((n+1)+1) * c (n+1)
      = 1 + 3^((n+1)+1) * (c n + 3^(n+1) * (c n * c n + 3^n * (c n * c n * c n))) := by
    calc 1 + 3^((n+1)+1) * c (n+1)
        = (4^(3^n))^3 := by rw [← four_pow_three_pow_eq (n+1), hpow]
      _ = (1 + 3^(n+1) * c n)^3 := by rw [four_pow_three_pow_eq]
      _ = 1 + 3^((n+1)+1) * (c n + 3^(n+1) * (c n * c n + 3^n * (c n * c n * c n))) := by
          have p1 : 3^((n+1)+1) = 3^n * 9 := by
            rw [Nat.pow_succ, Nat.pow_succ]; ring
          have p2 : 3^(n+1) = 3^n * 3 := Nat.pow_succ 3 n
          rw [p1, p2]
          ring
  have hcancel : 3^((n+1)+1) * c (n+1)
      = 3^((n+1)+1) * (c n + 3^(n+1) * (c n * c n + 3^n * (c n * c n * c n))) := by
    omega
  exact Nat.mul_left_cancel (by positivity : (0:Nat) < 3^((n+1)+1)) hcancel

/-- **The tower's first congruence: `c n ≡ 1 mod 3` at every level. -/
theorem c_mod3 (n : Nat) : c n % 3 = 1 := by
  induction n with
  | zero => decide
  | succ n ih =>
    have h := c_succ_eq n
    have hf : 3^(n+1) * (c n * c n + 3^n * (c n * c n * c n))
        = 3 * (3^n * (c n * c n + 3^n * (c n * c n * c n))) := by
      rw [Nat.pow_succ]; ring
    rw [hf] at h
    omega

/-- **The tower's second congruence: `c n ≡ 7 mod 9` from level one on. -/
theorem c_mod9_all (n : Nat) : 1 ≤ n → c n % 9 = 7 := by
  induction n with
  | zero => intro h; omega
  | succ n ih =>
    intro _
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · rw [h0]
      decide
    · have h := c_succ_eq n
      have hm : 3^(n+1) * (c n * c n + 3^n * (c n * c n * c n))
          = 9 * (3^(n-1) * (c n * c n + 3^n * (c n * c n * c n))) := by
        have hexp : n+1 = 2 + (n-1) := by omega
        have e : 3^(n+1) = 3^2 * 3^(n-1) := by rw [hexp, ← Nat.pow_add]
        rw [e]; ring
      rw [hm] at h
      have iih := ih hpos
      omega

theorem c_mod9 (n : Nat) (hn : 1 ≤ n) : c n % 9 = 7 := c_mod9_all n hn

/-- **The tower's third congruence: `c n ≡ 16 mod 81` from level three on. -/
theorem c_mod81_all (n : Nat) : 3 ≤ n → c n % 81 = 16 := by
  induction n with
  | zero => intro h; omega
  | succ n ih =>
    intro hn1
    rcases Nat.lt_or_ge n 3 with hlt | hge
    · have e2 : n = 2 := by omega
      subst e2
      decide
    · have h := c_succ_eq n
      have hm : 3^(n+1) * (c n * c n + 3^n * (c n * c n * c n))
          = 81 * (3^(n-3) * (c n * c n + 3^n * (c n * c n * c n))) := by
        have hexp : n+1 = 4 + (n-3) := by omega
        have e : 3^(n+1) = 3^4 * 3^(n-3) := by rw [hexp, ← Nat.pow_add]
        rw [e]; ring
      rw [hm] at h
      have iih := ih hge
      omega

theorem c_mod81 (n : Nat) (hn : 3 ≤ n) : c n % 81 = 16 := c_mod81_all n hn

/-! ## §2 The read glue -/

/-- **Divide-and-mod gluing:** `3^k * q + s` divided by `3^k` is `q`
when `s < 3^k`. -/
theorem div_add_lt (k q s : Nat) (hs : s < 3^k) : (3^k * q + s) / 3^k = q := by
  have hmod : (3^k * q + s) % 3^k = s := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hs]
  have h := Nat.div_add_mod (3^k * q + s) (3^k)
  rw [hmod] at h
  have h2 : 3^k * ((3^k * q + s) / 3^k) = 3^k * q := by omega
  exact Nat.mul_left_cancel (by positivity : (0:Nat) < 3^k) h2

/-- **The prefaced read.**  If `s < 3^(n+1)` then row `n+1+k` of the
prefaced object `3^(n+1) * A + s` is row `k` of `A`. -/
theorem prefaced_digit (A s n k : Nat) (hs : s < 3^(n+1)) :
    digit3 (3^(n+1) * A + s) (n+1+k) = digit3 A k := by
  unfold digit3
  have hdd : (3^(n+1) * A + s) / 3^(n+1+k)
      = ((3^(n+1) * A + s) / 3^(n+1)) / 3^k := by
    rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]
  rw [hdd, div_add_lt (n+1) A s hs]

/-- **The two-term binomial.**  `(1 + x)^j = 1 + j*x + x*x*R` for some `R`. -/
theorem one_add_pow_two_term (x j : Nat) : ∃ R, (1+x)^j = 1 + j*x + x*x*R := by
  induction j with
  | zero => exact ⟨0, by ring⟩
  | succ j ih =>
    obtain ⟨R, hR⟩ := ih
    refine ⟨R + j + x*R, ?_⟩
    rw [Nat.pow_succ, hR]
    ring

/-! ## §3 The tower reads -/

/-- **THE DEEP-HIDER MASTER LEMMA (Lane D's L10).**  Rows `n+1 .. 2n+1`
of `4^(j * 3^n)` are the digits `0 .. n` of `j * c n`: one tower
constant governs every scaled family at every depth. -/
theorem tower_digit_read (j n k : Nat) (hk : k ≤ n) :
    digit3 (4^(j * 3^n)) (n+1+k) = digit3 (j * c n) k := by
  obtain ⟨R, hR⟩ := one_add_pow_two_term (3^(n+1) * c n) j
  have hexp : 4^(j * 3^n)
      = 3^(n+1) * (j * c n + 3^(n+1) * ((c n * c n) * R)) + 1 := by
    rw [Nat.mul_comm j (3^n), Nat.pow_mul, four_pow_three_pow_eq, hR]
    ring
  have h1lt : (1:Nat) < 3^(n+1) := by
    have hp : (0:Nat) < 3^n := by positivity
    rw [Nat.pow_succ]
    omega
  rw [hexp, prefaced_digit _ 1 n k h1lt]
  unfold digit3
  have hsplit : j * c n + 3^(n+1) * (c n * c n * R)
      = j * c n + (3^(n+1-k) * (c n * c n * R)) * 3^k := by
    have hexp : n+1 = k + (n+1-k) := by omega
    have e : 3^(n+1) = 3^k * 3^(n+1-k) := by
      conv_lhs => rw [hexp]
      rw [← Nat.pow_add]
    rw [e]; ring
  rw [hsplit, Nat.add_mul_div_right _ _ (by positivity : (0:Nat) < 3^k)]
  have hd3 : 3 ∣ 3^(n+1-k) * (c n * c n * R) := by
    have e : n+1-k = (n-k)+1 := by omega
    have h9 : 3^(n+1-k) = 3 * 3^(n-k) := by rw [e, Nat.pow_succ]; ring
    rw [h9]
    exact ⟨3^(n-k) * (c n * c n * R), by ring⟩
  omega

/-- The complete finite read profile exposed by one scaled tower. -/
def towerReadProfile (j n : Nat) :
    Fin (n+1) → Nat :=
  fun k => digit3 (4^(j * 3^n)) (n+1+k.1)

/-- The coefficient-side profile controlling the same tower window. -/
def towerCoefficientProfile (j n : Nat) :
    Fin (n+1) → Nat :=
  fun k => digit3 (j * c n) k.1

/-- **FINITE-PROFILE TOWER ISOMORPHISM.**
The deep-hider lemma upgrades from pointwise equality to equality of the
entire n+1-coordinate read profile. -/
theorem towerReadProfile_exact
    (j n : Nat) :
    towerReadProfile j n = towerCoefficientProfile j n := by
  funext k
  unfold towerReadProfile towerCoefficientProfile
  exact tower_digit_read j n k.1 (by omega)

/-- Every predicate on the finite read profile can therefore be transferred
between the perfect-power tower and the compact coefficient profile. -/
theorem towerReadProfile_predicate_iff
    (j n : Nat)
    (P : (Fin (n+1) → Nat) → Prop) :
    P (towerReadProfile j n) ↔
      P (towerCoefficientProfile j n) := by
  rw [towerReadProfile_exact]

/-- Every functional observable of the finite read profile is identical on
the tower and coefficient presentations. -/
theorem towerReadProfile_observable_exact
    {α : Type}
    (j n : Nat)
    (F : (Fin (n+1) → Nat) → α) :
    F (towerReadProfile j n) =
      F (towerCoefficientProfile j n) :=
  congrArg F (towerReadProfile_exact j n)

/-- **THE n+2 LAW (Lane D's L7).**  `3^n` fires at row `n+2` for every
`n ≥ 1`: the first rows are zero (the valuation), row `n+1` is one,
row `n+2` is TWO — the tower constant's second trit. -/
theorem three_pow_fires (n : Nat) (hn : 1 ≤ n) : digit3 (4^(3^n)) (n+2) = 2 := by
  have h := tower_digit_read 1 n 1 hn
  rw [Nat.one_mul, Nat.one_mul] at h
  rw [show n+2 = n+1+1 from by omega, h]
  rw [digit3_mod_pow, show (3:Nat)^(1+1) = 9 from by norm_num, c_mod9 n hn]
  norm_num

/-- **THE n+1 LAW (Lane D's L8).**  `2 * 3^n` fires at row `n+1` for
every `n ≥ 0` — the doubled tower constant reads its leading TWO. -/
theorem two_mul_three_pow_fires (n : Nat) : digit3 (4^(2 * 3^n)) (n+1) = 2 := by
  have h := tower_digit_read 2 n 0 (by omega)
  rw [show n+1 = n+1+0 from by omega, h]
  unfold digit3
  norm_num
  rw [Nat.mul_mod, c_mod3 n]

/-- **THE n+4 LAW (Lane D's L9).**  `3^n + 1` fires at row `n+4` for
every `n ≥ 3`: the prefaced tower constant `4 * c n ≡ 64 mod 81 = 2101₃`
plants the TWO at offset three. -/
theorem three_pow_plus_one_fires (n : Nat) (hn : 3 ≤ n) :
    digit3 (4^(3^n + 1)) (n+4) = 2 := by
  have hbig : (4:Nat) < 3^(n+1) := by
    have hexp : n+1 = 4 + (n-3) := by omega
    have e : 3^(n+1) = 3^4 * 3^(n-3) := by rw [hexp, ← Nat.pow_add]
    have hpos : (0:Nat) < 3^(n-3) := by positivity
    rw [e]
    omega
  have hdec : 4^(3^n + 1) = 3^(n+1) * (4 * c n) + 4 := by
    have h := four_pow_three_pow_eq n
    rw [Nat.pow_add, Nat.pow_one, h]
    ring
  rw [hdec, show n+4 = n+1+3 from by omega,
    prefaced_digit _ 4 n 3 hbig]
  rw [digit3_mod_pow, show (3:Nat)^(3+1) = 81 from by norm_num,
    Nat.mul_mod, c_mod81 n hn]
  norm_num

#print axioms three_pow_fires
#print axioms two_mul_three_pow_fires
#print axioms three_pow_plus_one_fires
#print axioms tower_digit_read
#print axioms towerReadProfile_exact
#print axioms towerReadProfile_predicate_iff
#print axioms towerReadProfile_observable_exact

end GSTTowerFire
