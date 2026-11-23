import Arsenal.ErdosTernary2.Basic
import Arsenal.CardinalWorlds
import Arsenal.CardinalWorldsV2

-- Family pattern (green kernels): explicit depth headroom.
set_option maxRecDepth 262144
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 1000

/-!
# ERDŐS #406 — THE TAILF DECOMPOSITION KERNEL (S084, Kernel 76)

## THE OBJECT (BOSS order, standing: prove the hypothesis — my laws only)

The source monolith's terminal identity names the hypothesis exactly:
`erdos_even_conjecture_iff_tailF` — the even-exponent Erdős statement and
the second-observer input `four_power_omega_shadow_wave_tailF` are ONE
object, certified in BOTH directions at the monolith (§7.15).  The
monolith's own tailF chamber (GSTTailFFourthDimension — the dimensional
laws) decomposes the input into TWO named 3-adic primitives — the ROW
primitive (the sheet-zero family) and the TOWER primitive (the deep tail
beyond the dodge band) — and proves the composition unconditionally.

THIS KERNEL ports the decomposition into the campaign's self-contained
language (the green Block-Law / Ghost-Extinction spine) and drives every
named weapon onto it:

* **§1 THE Ω-CUT WORD** — the monolith's `omegaGeoSum` / `omegaCutWord` /
  `omega_cut_factor` (`4^(3^s·core) = 1 + 3^(s+1)·(lteCoeff s · geoSum)`),
  ported division-free, plus the diagonal congruence (the cut word IS
  the diagonal-times-core inside the window: `W ≡ c_s·core [MOD 3^(s+1)]`)
  and the prefix-slice law (the digit transfer at EVERY depth).
* **§2 THE FULL OBSERVER** — the all-depth reading instrument:
  `digit3 (4^(3^s·core)) (s+1+q) = digit3 (omegaCutWord s core) q` —
  NO window bound (the monolith's tower observer was window-limited to
  `k ≤ s+1`; the cut-word reading has no limit), and the exact fire
  classifier `digit = 2 ↔ residue in the top third` at every depth.
* **§3 THE COMPRESSION LAW** — `CantorianPower (3^s·core) ↔ the cut
  word carries no ternary digit two at ANY position`: the (G2) grant in
  its exact monolith language.  The Cantorian hypothesis on the power
  IS the digit-2-freeness of ONE explicit integer.
* **§4 THE DECOMPOSITION** — the monolith's two named primitives
  (`tailF_row_primitive`, `tailF_tower_primitive`), stated in campaign
  language, and the machine-checked composition
  `tailF_of_row_and_tower`: the two primitives carry the full
  second-observer input.
* **§5 THE SIX-ADIC GHOST SKEW** — BOSS's six-adic machinery on the
  ghost pair: `six_adic_pair_saturation` (the 4^t dyadic burn + the
  triadic shadow = the six-adic resolution), the oddness of the frozen
  diagonal, and the ghost-pair collapse (uniqueness via triadic
  cancellation + unboundedness — an independent campaign proof).
* **§6 THE PARADOX WALL** — the u-jump sign laws (the monolith's
  handwritten-U jump table, all twelve cells): a Happy cell (digit two,
  carry 0 or 3) forces a STRICTLY NEGATIVE jump; every non-Happy cell
  is nonnegative.  Consequence: a Cantorian power (no digit two
  anywhere) rides an ETERNALLY NON-NEGATIVE flux, and beyond position
  `3K+3` the wave is FROZEN at the (0,0) cell with jump exactly TEN —
  the eternal-dodge fuel gauge for the extinction round.
* **§7 THE CROWN V3** — the full #406 statement from the weakened grant
  pair: (G1') ghost extinction on the rider sheet + (G2') the
  compression in cut-word form.  Everything else unconditional: the
  kernel-75 census base (both decide chunks), the odd wing, the
  digit-to-verdict bridge.

## THE HONEST SCOPE (unchanged law: no dressing)

The two grants stand, now in their exact monolith language: (G1') the π
non-naturality (the trit stream of `T/(2W)` never terminating); (G2')
the compression (a digit-2-free cut word forces the ghost ray).  The
decomposition banked here splits (G2') into the row primitive and the
tower primitive — the named next lanes, each one statement.  The engine
never stops; it never lies.
-/

namespace TailFDecomposition406

/-! ## §0 The engine (ported verbatim from the green kernels) -/

/-- The ternary digit at position `p`. -/
def digit3 (x p : Nat) : Nat := x / 3^p % 3

/-- The power monotonicity law, self-contained (base three). -/
theorem three_pow_le_of_le (a b : Nat) (h : a ≤ b) : 3^a ≤ 3^b := by
  obtain ⟨d, hd⟩ : ∃ d : Nat, b = a + d := ⟨b - a, by omega⟩
  rw [hd, Nat.pow_add]
  have hp : 0 < (3:Nat)^d := Nat.pow_pos (by decide)
  obtain ⟨t, ht⟩ : ∃ t : Nat, 3^d = 1 + t := ⟨3^d - 1, by omega⟩
  have hexp : 3^a * 3^d = 3^a + 3^a * t := by rw [ht]; ring
  omega

/-- Powers of three are unbounded. -/
theorem three_pow_unbounded : ∀ n : Nat, ∃ k : Nat, n < 3^k
  | 0 => ⟨1, by decide⟩
  | n+1 => by
      obtain ⟨k, hk⟩ := three_pow_unbounded n
      refine ⟨k + 1, ?_⟩
      have hp : 0 < 3^k := Nat.pow_pos (by decide)
      have h3 : 3^(k+1) = 3^k * 3 := by rw [Nat.pow_succ]
      omega

/-- The tower coefficient: `lteCoeff v = c_v` with
`4^(3^v) = 1 + 3^(v+1) * c_v` (division-free cube recursion). -/
def lteCoeff : Nat → Nat
  | 0 => 1
  | r+1 =>
      let c := lteCoeff r
      c + 3^(r+1) * c^2 + 3^(2*r+1) * c^3

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
              _ = (3^r * 3) * 3 := by rw [h1]
              _ = 3^r * 9 := by ring
          have hcube : (1 + 3^(r+1) * lteCoeff r)^3
              = 1 + 3^(r+2) * (lteCoeff r
                  + 3^(r+1) * (lteCoeff r)^2 + 3^(2*r+1) * (lteCoeff r)^3) := by
            rw [h1, h2, h3]
            ring
          rw [hcube]

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

/-- Powers of three are odd. -/
theorem three_pow_odd : ∀ r : Nat, 3^r % 2 = 1
  | 0 => by decide
  | r+1 => by
      rw [Nat.pow_succ, Nat.mul_mod, three_pow_odd r]

theorem odd_mul_odd (a b : Nat) (ha : a % 2 = 1) (hb : b % 2 = 1) :
    (a * b) % 2 = 1 := by
  rw [Nat.mul_mod, ha, hb, Nat.mul_one]

/-- Mod-zero folding: if `m ∣ b` then `(a + b) % m = a % m`. -/
theorem add_mod_of_dvd (a b m : Nat) (hdvd : m ∣ b) :
    (a + b) % m = a % m := by
  obtain ⟨q, rfl⟩ := hdvd
  first
    | rw [Nat.add_mul_mod_self_left]
    | rw [Nat.add_mul_mod_self_right]

/-- **THE ODD DIAGONAL (NEW).**  Every tower coefficient is odd — the
frozen diagonal is a dyadic unit (the six-adic skew's odd half). -/
theorem lteCoeff_odd : ∀ r : Nat, lteCoeff r % 2 = 1
  | 0 => by decide
  | r+1 => by
      have ih := lteCoeff_odd r
      have h1 : (3:Nat)^(r+1) % 2 = 1 := three_pow_odd (r+1)
      have h2 : (3:Nat)^(2*r+1) % 2 = 1 := three_pow_odd (2*r+1)
      have hs : ((lteCoeff r) * (lteCoeff r)) % 2 = 1 := odd_mul_odd _ _ ih ih
      have hc : ((lteCoeff r) * (lteCoeff r) * (lteCoeff r)) % 2 = 1 :=
        odd_mul_odd _ _ hs ih
      have hA : 3^(r+1) * (lteCoeff r)^2 % 2 = 1 := by
        rw [show (lteCoeff r)^2 = (lteCoeff r) * (lteCoeff r) from by ring]
        exact odd_mul_odd _ _ h1 hs
      have hB : 3^(2*r+1) * (lteCoeff r)^3 % 2 = 1 := by
        rw [show (lteCoeff r)^3 = (lteCoeff r) * (lteCoeff r) * (lteCoeff r) from by ring]
        exact odd_mul_odd _ _ h2 hc
      have hdvd : (2:Nat) ∣ 3^(r+1) * (lteCoeff r)^2 + 3^(2*r+1) * (lteCoeff r)^3 := by
        rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, hA, hB]
      simp only [lteCoeff]
      rw [Nat.add_assoc, add_mod_of_dvd _ _ _ hdvd]
      exact ih

theorem lteCoeff_succ_mod (w : Nat) :
    lteCoeff (w+1) % 3^(w+1) = lteCoeff w % 3^(w+1) := by
  have hsplit : 3^(2*w+1) = 3^(w+1) * 3^w := by
    rw [← Nat.pow_add]
    congr 1; omega
  have hd1 : 3^(w+1) ∣ 3^(w+1) * (lteCoeff w)^2 := ⟨_, rfl⟩
  have hd2 : 3^(w+1) ∣ 3^(2*w+1) * (lteCoeff w)^3 :=
    ⟨3^w * (lteCoeff w)^3, by rw [hsplit]; ring⟩
  simp only [lteCoeff]
  rw [add_mod_of_dvd _ _ _ hd2, add_mod_of_dvd _ _ _ hd1]

theorem mod_dvd_modeq (a b m n : Nat) (hmn : m ∣ n) (h : a % n = b % n) :
    a % m = b % m := by
  rw [← Nat.mod_mod_of_dvd a hmn, ← Nat.mod_mod_of_dvd b hmn, h]

/-- **THE FROZEN DIAGONAL** (stabilization). -/
theorem lteCoeff_stable (v w : Nat) (hw : v ≤ w) :
    lteCoeff w % 3^(v+1) = lteCoeff v % 3^(v+1) := by
  induction w with
  | zero =>
      have hv0 : v = 0 := by omega
      subst hv0
      rfl
  | succ w ih =>
      by_cases hwv : v ≤ w
      · have hdvd : 3^(v+1) ∣ 3^(w+1) := by
          refine ⟨3^(w-v), ?_⟩
          rw [← Nat.pow_add]
          congr 1; omega
        exact (mod_dvd_modeq _ _ _ _ hdvd (lteCoeff_succ_mod w)).trans (ih hwv)
      · have hvw : v = w + 1 := by omega
        subst hvw
        rfl

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

theorem pow_succ_mul (p : Nat) : 3^(p+1) = 3 * 3^p := by
  rw [Nat.pow_succ]
  ring

theorem pow_succ_two (v : Nat) : 3^(v+2) = 3 * 3^(v+1) := by
  rw [show (v:Nat) + 2 = (v+1) + 1 from by omega, Nat.pow_succ]
  ring

theorem div_pow_add (q r p : Nat) :
    (3^p * 3 * q + r) / 3^p = 3 * q + r / 3^p := by
  have hp : 0 < 3^p := Nat.pow_pos (by decide)
  rw [show 3^p * 3 * q + r = r + 3^p * (3 * q) from by ring]
  rw [Nat.add_mul_div_left _ _ hp]
  omega

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

theorem digit3_one_pos (p : Nat) (hp : 1 ≤ p) : digit3 1 p = 0 := by
  unfold digit3
  have h1 : 1 < 3^p := by
    have h0 : 3^1 ≤ 3^p :=
      Nat.pow_le_pow_of_le (by decide : 1 < 3) (by omega)
    omega
  rw [Nat.div_eq_of_lt (by omega : (1:Nat) < 3^p)]

theorem lt_cut_residue (v r : Nat) (hr : r < 3) :
    1 + r * 3^(v+1) < 3^(v+2) := by
  have h1 : 1 ≤ 3^(v+1) := by
    have hp : 0 < 3^(v+1) := Nat.pow_pos (by decide)
    omega
  rcases ErdosTernary2.lt_three_cases r hr with h0 | h0 | h0
  · rw [h0, pow_succ_two]
    omega
  · rw [h0, pow_succ_two]
    omega
  · rw [h0, pow_succ_two]
    omega

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

theorem pow4_cut_residue_exact (v u : Nat) :
    4^(3^v * u) % 3^(v+2) = 1 + (u % 3) * 3^(v+1) := by
  have hK : 4^(3^v * u) = (1 + 3^(v+1) * lteCoeff v)^u := by
    rw [Nat.pow_mul, pow4_three_power_lte_exact]
  obtain ⟨s, hs⟩ := binom_two_term (3^(v+1) * lteCoeff v) u
  have huc : u * lteCoeff v % 3 = u % 3 := by
    rw [Nat.mul_mod, lteCoeff_mod3_one]
    omega
  have hsplit : 4^(3^v * u) = (1 + (u % 3) * 3^(v+1)) +
      3^(v+2) * ((u * lteCoeff v) / 3 +
        3^v * (lteCoeff v * lteCoeff v * s)) := by
    rw [hK, hs]
    have hk := Nat.div_add_mod (u * lteCoeff v) 3
    rw [huc] at hk
    have hmul : u * (3^(v+1) * lteCoeff v) =
        3^(v+2) * ((u * lteCoeff v) / 3) + (u % 3) * 3^(v+1) := by
      calc u * (3^(v+1) * lteCoeff v)
          = 3^(v+1) * (u * lteCoeff v) := by ring
        _ = 3^(v+1) * (3 * ((u * lteCoeff v) / 3) + u % 3) := by rw [hk]
        _ = 3^(v+2) * ((u * lteCoeff v) / 3) + (u % 3) * 3^(v+1) := by
            rw [pow_succ_two]
            ring
    rw [hmul]
    have hpow : 3^(v+2) = 3^(v+1) * 3 := by rw [Nat.pow_succ]
    rw [hpow]
    ring
  rw [hsplit, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt (lt_cut_residue v (u % 3) (Nat.mod_lt _ (by decide)))]

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
  have hzero : digit3 (1 + 2 * 3^p) p = 2 := by
    unfold digit3
    have hp : 0 < (3:Nat)^p := Nat.pow_pos (by decide)
    rw [show (1:Nat) + 2 * 3^p = 1 + 3^p * 2 from by ring]
    rw [Nat.add_mul_div_left _ _ hp,
        Nat.div_eq_of_lt (by omega : (1:Nat) < 3^p), Nat.add_zero]
  rw [hcongr, hzero]

theorem pow4_mod3 (r : Nat) : 4^r % 3 = 1 := by
  induction r with
  | zero => decide
  | succ r ih =>
      rw [Nat.pow_succ, Nat.mul_mod, ih]

theorem digit3_pow4_zero (K : Nat) : digit3 (4^K) 0 = 1 := by
  unfold digit3
  rw [Nat.pow_zero, Nat.div_one, pow4_mod3]

theorem two_pow_two_mul (K : Nat) : 2^(2*K) = 4^K := by
  rw [show (4:Nat) = 2^2 from rfl, ← Nat.pow_mul]

/-- The Cantorian power predicate: no ternary digit two from position
one on (position zero is always one). -/
def CantorianPower (K : Nat) : Prop :=
  ∀ p : Nat, 1 ≤ p → digit3 (4^K) p ≠ 2

/-- **THE GHOST RAY** (the stabilized middle-third condition). -/
def GhostRay (u : Nat) : Prop :=
  ∀ k : Nat, 3 ≤ k →
    3^(k-1) ≤ (lteCoeff (k-1) * u) % 3^k
    ∧ (lteCoeff (k-1) * u) % 3^k < 2 * 3^(k-1)

/-- The canonical ghost head. -/
def ghostHead (u : Nat) : Nat := (lteCoeff 1 * u) % 9

/-- **THE RIDER'S CORE LAW** (ported verbatim): every Cantorian power
`K = 3^σ·u` with three-free `u` satisfies `u ≡ 1 (mod 3)`. -/
theorem rider_core_one (K : Nat) (hK : 0 < K)
    (hCant : CantorianPower K) :
    ∃ σ u : Nat, K = 3^σ * u ∧ ¬ (3:Nat) ∣ u ∧ u % 3 = 1 := by
  obtain ⟨v, u, hKu, hu3⟩ := valuation_decomp K hK
  have hlt : u % 3 < 3 := Nat.mod_lt _ (by decide)
  rcases ErdosTernary2.lt_three_cases (u % 3) hlt with h | h | h
  · exact absurd h hu3
  · refine ⟨v, u, hKu, ?_, h⟩
    intro hd
    exact hu3 (Nat.dvd_iff_mod_eq_zero.mp hd)
  · exfalso
    have hres := pow4_cut_residue_exact v u
    rw [h] at hres
    have hv1 : 1 ≤ v + 1 := by omega
    have hfire : digit3 (4^K) (v+1) = 2 := by
      have hmod : 4^K % 3^((v+1)+1) = 1 + 2 * 3^(v+1) := by
        rw [show ((v:Nat)+1)+1 = v+2 from by omega, hKu, hres]
      exact digit3_of_residue_two (4^K) (v+1) hv1 hmod
    exact hCant (v+1) hv1 hfire

/-! ## §1 The Ω-cut word (the monolith's machinery, campaign-ported) -/

/-- The geometric block of the Ω-decomposition: `geoSum s core` is the
sum of the first `core` powers of `4^(3^s)`. -/
def geoSum : Nat → Nat → Nat
  | _, 0 => 0
  | s, core+1 => geoSum s core + 4^(3^s * core)

theorem geoSum_zero (s : Nat) : geoSum s 0 = 0 := rfl

theorem geoSum_succ (s core : Nat) :
    geoSum s (core+1) = geoSum s core + 4^(3^s * core) := rfl

/-- **THE Ω-CUT WORD** — the LTE mean times the geometric mean. -/
def omegaCutWord (s core : Nat) : Nat :=
  lteCoeff s * geoSum s core

theorem cutword_zero (s : Nat) : omegaCutWord s 0 = 0 := by
  unfold omegaCutWord
  rw [geoSum_zero]
  exact Nat.mul_zero _

/-- **THE Ω-CUT FACTORIZATION** (the monolith's `omega_cut_factor`,
ported division-free): for every sheet level and every core mass,
`4^(3^s·core) = 1 + 3^(s+1) · omegaCutWord s core`. -/
theorem omega_cut_factor (s core : Nat) :
    4^(3^s * core) = 1 + 3^(s+1) * omegaCutWord s core := by
  induction core with
  | zero =>
      have h0 : (3:Nat)^s * 0 = 0 := Nat.mul_zero _
      rw [h0, Nat.pow_zero, cutword_zero, Nat.mul_zero, Nat.add_zero]
  | succ core ih =>
      have hbase := pow4_three_power_lte_exact s
      have hstep : 4^(3^s * (core+1)) = 4^(3^s * core) * 4^(3^s) :=
        Nat.pow_add 4 (3^s * core) (3^s)
      have hcut : omegaCutWord s (core+1)
          = omegaCutWord s core + lteCoeff s * 4^(3^s * core) := by
        unfold omegaCutWord
        rw [geoSum_succ]
        ring
      have hident : (1 + 3^(s+1) * omegaCutWord s core)
            * (1 + 3^(s+1) * lteCoeff s)
          = 1 + 3^(s+1) * (omegaCutWord s core
              + lteCoeff s * 4^(3^s * core)) := by
        rw [ih]
        ring
      rw [hstep, ih, hbase, hcut]
      exact hident

/-- Each geometric block term is one modulo the scale. -/
theorem geo_term_mod (s j : Nat) :
    4^(3^s * j) % 3^(s+1) = 1 := pow4_scaled_mod_next s j

/-- **THE DIAGONAL CONGRUENCE** — inside the window, the cut word IS the
diagonal-times-core: `omegaCutWord s core ≡ lteCoeff s · core
[MOD 3^(s+1)]`.  This is why the monolith's window observer reads the
tower digits off the diagonal products. -/
theorem cutword_diag_congr (s core : Nat) :
    (omegaCutWord s core) % 3^(s+1)
      = (lteCoeff s * core) % 3^(s+1) := by
  induction core with
  | zero =>
      rw [cutword_zero, Nat.mul_zero]
  | succ core ih =>
      have hcut : omegaCutWord s (core+1)
          = omegaCutWord s core + lteCoeff s * 4^(3^s * core) := by
        unfold omegaCutWord
        rw [geoSum_succ]
        ring
      have htermm : (lteCoeff s * 4^(3^s * core)) % 3^(s+1)
          = lteCoeff s % 3^(s+1) := by
        rw [Nat.mul_mod, geo_term_mod s core, Nat.mul_one,
            Nat.mod_mod_of_dvd _ (dvd_refl _)]
      have hrhs : (lteCoeff s * (core+1)) % 3^(s+1)
          = ((lteCoeff s * core) % 3^(s+1)
              + lteCoeff s % 3^(s+1)) % 3^(s+1) := by
        have hsplit : lteCoeff s * (core+1)
            = lteCoeff s * core + lteCoeff s := by ring
        rw [hsplit, Nat.add_mod]
      rw [hcut, hrhs, Nat.add_mod, ih, htermm]

/-- The unit cut word is the diagonal itself (`geoSum s 1 = 1`). -/
theorem cutword_one (s : Nat) : omegaCutWord s 1 = lteCoeff s := by
  have h1 : geoSum s 1 = 1 := by
    rw [geoSum_succ, geoSum_zero, Nat.mul_zero, Nat.pow_zero]
  unfold omegaCutWord
  rw [h1]
  ring

/-- **THE PREFIX-SLICE LAW** — the digit transfer at every depth: for
`m ≥ 1`, the digit of `1 + 3^m·W` at position `m+q` is the digit of `W`
at position `q`.  The `+1` never carries past position `m`. -/
theorem prefix_slice_digit (m W q : Nat) (hm : 1 ≤ m) :
    digit3 (1 + 3^m * W) (m + q) = digit3 W q := by
  have hp : 0 < 3^m := Nat.pow_pos (by decide)
  have h1 : (1:Nat) < 3^m := by
    have h0 : 3^1 ≤ 3^m :=
      Nat.pow_le_pow_of_le (by decide : 1 < 3) (by omega)
    omega
  have hmod : (1 + 3^m * W) % 3^m = 1 := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h1]
  have hdm := Nat.div_add_mod (1 + 3^m * W) (3^m)
  rw [hmod] at hdm
  -- hdm : 1 + 3^m * W = 3^m * ((1 + 3^m * W) / 3^m) + 1
  have hdiv : (1 + 3^m * W) / 3^m = W := by
    refine Nat.eq_of_mul_eq_mul_left hp ?_
    omega
  unfold digit3
  rw [show (3:Nat)^(m+q) = 3^m * 3^q from by rw [Nat.pow_add],
      ← Nat.div_div_eq_div_mul, hdiv]

/-! ## §2 The full observer (every depth at once) -/
#print axioms TailFDecomposition406.omega_cut_factor  -- CK76 SECTION BOUNDARY

/-- **THE FULL OBSERVER (tower digit = cut-word digit).**  For every
sheet level `s`, every core and EVERY depth `q` — no window bound — the
digit of the power `4^(3^s·core)` at position `s+1+q` is the digit of
the cut word at position `q`.  The monolith's observer was limited to
the window `k ≤ s+1`; the cut-word reading sees the ENTIRE deep tail. -/
theorem tower_digit_eq_cutword (s core q : Nat) :
    digit3 (4^(3^s * core)) (s+1+q) = digit3 (omegaCutWord s core) q := by
  rw [omega_cut_factor s core]
  refine prefix_slice_digit (s+1) (omegaCutWord s core) q ?_
  omega

/-- **THE RESIDUE-FIRE CLASSIFIER** — the digit at any position is two
exactly when the residue window lands in the top third. -/
theorem digit_residue_fire_iff (W q : Nat) :
    digit3 W q = 2 ↔ 2 * 3^q ≤ W % 3^(q+1) := by
  have hq1 : 3^(q+1) = 3 * 3^q := by
    rw [Nat.pow_succ]
    ring
  have hcongr : digit3 (W % 3^(q+1)) q = digit3 W q :=
    digit3_mod_congr (W % 3^(q+1)) W q
      (Nat.mod_mod_of_dvd W (dvd_refl (3^(q+1))))
  have hlt : W % 3^(q+1) < 3 * 3^q := by
    rw [← hq1]
    exact Nat.mod_lt _ (Nat.pow_pos (by decide))
  have hdm := Nat.div_add_mod (W % 3^(q+1)) (3^q)
  have hmodlt : (W % 3^(q+1)) % 3^q < 3^q :=
    Nat.mod_lt _ (Nat.pow_pos (by decide))
  constructor
  · intro hd
    have hdX : digit3 (W % 3^(q+1)) q = 2 := by
      rw [hcongr]
      exact hd
    have hdivlt : (W % 3^(q+1)) / 3^q < 3 := by
      by_contra hge
      have h3 : 3 ≤ (W % 3^(q+1)) / 3^q := by omega
      have hbig : 3^q * 3 ≤ 3^q * ((W % 3^(q+1)) / 3^q) :=
        Nat.mul_le_mul_left _ h3
      omega
    have hdiv2 : (W % 3^(q+1)) / 3^q = 2 := by
      unfold digit3 at hdX
      rw [← Nat.mod_eq_of_lt hdivlt]
      exact hdX
    calc 2 * 3^q ≤ 3^q * 2 := by ring
      _ = 3^q * ((W % 3^(q+1)) / 3^q) := by rw [hdiv2]
      _ ≤ 3^q * ((W % 3^(q+1)) / 3^q) + (W % 3^(q+1)) % 3^q :=
          Nat.le_add_right _ _
      _ = W % 3^(q+1) := hdm
  · intro hge
    have hlt2 : (W % 3^(q+1)) / 3^q < 3 := by
      by_contra hge3
      have h3 : 3 ≤ (W % 3^(q+1)) / 3^q := by omega
      have hbig : 3^q * 3 ≤ 3^q * ((W % 3^(q+1)) / 3^q) :=
        Nat.mul_le_mul_left _ h3
      omega
    have hdiv : (W % 3^(q+1)) / 3^q = 2 := by
      rcases Nat.lt_trichotomy ((W % 3^(q+1)) / 3^q) 2 with h | h | h
      · exfalso
        have hle : (W % 3^(q+1)) / 3^q ≤ 1 := by omega
        have hsmall : 3^q * ((W % 3^(q+1)) / 3^q) ≤ 3^q * 1 :=
          Nat.mul_le_mul_left _ hle
        omega
      · exact h
      · exfalso
        omega
    have hdX : digit3 (W % 3^(q+1)) q = 2 := by
      unfold digit3
      rw [hdiv]
    rw [← hcongr]
    exact hdX

/-- **THE FULL OBSERVER, FIRE FORM** — the digit of the power at every
deep position is two exactly when the cut word's residue window lands
in the top third at the matching depth.  Every depth at once: the
monolith's two observers (tower window + row law) are instances at
`s ≥ 1` and `s = 0`. -/
theorem tower_fire_iff_full (s core q : Nat) :
    digit3 (4^(3^s * core)) (s+1+q) = 2
      ↔ 2 * 3^q ≤ (omegaCutWord s core) % 3^(q+1) := by
  rw [tower_digit_eq_cutword s core q, digit_residue_fire_iff]

/-! ## §3 THE COMPRESSION LAW — the Cantorian hypothesis is ONE integer's
#print axioms TailFDecomposition406.tower_fire_iff_full  -- CK76 SECTION BOUNDARY
digit-freeness -/

/-- The power's low digits vanish: positions `1..s` of `4^(3^s·core)`
are zero (the power is exactly one at the cut scale). -/
theorem pow4_low_digits_zero (s core p : Nat) (hp1 : 1 ≤ p) (hps : p ≤ s) :
    digit3 (4^(3^s * core)) p = 0 := by
  have hmod : 4^(3^s * core) % 3^(s+1) = 1 := pow4_scaled_mod_next s core
  have hdvd : 3^(p+1) ∣ 3^(s+1) := by
    refine ⟨3^(s-p), ?_⟩
    rw [← Nat.pow_add]
    congr 1
    omega
  have h := digit3_mod_congr (4^(3^s * core)) 1 p
    (show 4^(3^s * core) % 3^(p+1) = 1 % 3^(p+1) from by
      rw [← Nat.mod_mod_of_dvd (4^(3^s * core)) hdvd,
          ← Nat.mod_mod_of_dvd 1 hdvd, hmod]
      exact (Nat.mod_mod_of_dvd (1:Nat) hdvd).symm)
  rw [h]
  exact digit3_one_pos p hp1

/-- **THE COMPRESSION LAW (NEW).**  For every sheet level and core:
`CantorianPower (3^s·core)` holds exactly when the cut word
`omegaCutWord s core` carries NO ternary digit two at ANY position.
The (G2) grant in its exact monolith language: the entire Cantorian
hypothesis on the power is the digit-2-freeness of ONE explicit
integer. -/
theorem cantorian_iff_cutword_clean (s core : Nat) :
    CantorianPower (3^s * core)
      ↔ (∀ q : Nat, digit3 (omegaCutWord s core) q ≠ 2) := by
  constructor
  · intro hCant q
    have h := hCant (s+1+q) (by omega)
    rwa [tower_digit_eq_cutword s core q] at h
  · intro hclean p hp1
    rcases Nat.lt_or_ge p (s+1) with hlt | hge
    · have hz := pow4_low_digits_zero s core p hp1 (by omega)
      intro htwo
      rw [htwo] at hz
      exact absurd hz (by decide)
    · rw [show p = s+1 + (p - (s+1)) from by omega,
          tower_digit_eq_cutword s core (p - (s+1))]
      exact hclean (p - (s+1))

/-! ## §4 The decomposition — the monolith's two named primitives -/
#print axioms TailFDecomposition406.cantorian_iff_cutword_clean  -- CK76 SECTION BOUNDARY

/-- **THE Ω-SHADOW TAIL (SECOND OBSERVER FORM)** — the monolith's exact
residual input, ported verbatim (with `omegaCutWord` in campaign
language): the head families, the head-window dodge, the sheet gates,
the sheet-zero all-depths row clause, and the full tower window. -/
def omegaShadowTailF (K : Nat) : Prop :=
  ∃ s core : Nat, K = 3^s * core ∧ ¬ 3 ∣ core ∧
    (core % 9 = 4 ∨ (s = 0 ∧ core % 9 = 1) ∨ (1 ≤ s ∧ core % 9 = 7)) ∧
    ((omegaCutWord s core) % 3^(s+2) < 2 * 3^(s+1)) ∧
    (1 ≤ s → (core % 9 = 4 →
      3^(s+2) ≤ (lteCoeff s * core) % 3^(s+3))) ∧
    (1 ≤ s → (core % 9 = 7 →
      ((lteCoeff s * core) % 3^(s+3) < 3^(s+2)
        ∨ 2 * 3^(s+2) ≤ (lteCoeff s * core) % 3^(s+3)))) ∧
    (s = 0 → ∀ j : Nat, 2 ≤ j →
      (omegaCutWord 0 core) % 3^(j+1) < 2 * 3^j) ∧
    (∀ k : Nat, 3 ≤ k → k ≤ s+1 →
      (omegaCutWord s 1 * core) % 3^k < 2 * 3^(k-1))

/-- **THE SECOND-OBSERVER INPUT** — the monolith's terminal identity
partner: every shadow carrier above the kernel base still owns its
ternary digit two. -/
def four_power_omega_shadow_wave_tailF : Prop :=
  ∀ K : Nat, 500 < K → omegaShadowTailF K → ∃ p : Nat, digit3 (4^K) p = 2

/-- **THE ROW PRIMITIVE** — the sheet-zero family's entire carried
content: the row word of every 3-free class-one core above the base
owns its top-third fire at some depth. -/
def tailF_row_primitive : Prop :=
  ∀ core : Nat, 500 < core → ¬ 3 ∣ core →
    (core % 9 = 1 ∨ core % 9 = 4) →
      ∃ j : Nat, 2 * 3^j ≤ (omegaCutWord 0 core) % 3^(j+1)

/-- **THE TOWER PRIMITIVE** — the tower family's entire carried content:
every diagonal-dodging tower's cut word fires its top third in the deep
tail, at depth at least `s+2` — beyond the package's own dodge band. -/
def tailF_tower_primitive : Prop :=
  ∀ s core : Nat, 1 ≤ s → ¬ 3 ∣ core →
    (core % 9 = 4 ∨ core % 9 = 7) →
    (∀ k : Nat, 3 ≤ k → k ≤ s+1 →
      (omegaCutWord s 1 * core) % 3^k < 2 * 3^(k-1)) →
      ∃ i : Nat, s+2 ≤ i ∧
        2 * 3^i ≤ (omegaCutWord s core) % 3^(i+1)

/-- **THE DECOMPOSITION OF THE INPUT (NEW, campaign-ported).**  The two
named primitives compose into the full second-observer input: the row
primitive carries the sheet-zero family through the full observer at
`s = 0`, the tower primitive carries the tower family through the full
observer at `s ≥ 1`. -/
theorem tailF_of_row_and_tower
    (hRow : tailF_row_primitive)
    (hTower : tailF_tower_primitive) :
    four_power_omega_shadow_wave_tailF := by
  intro K hK hshadow
  obtain ⟨s, core, hKsc, hfree, hres, hA, hB1, hB2, hC, hD⟩ := hshadow
  rcases Nat.eq_zero_or_pos s with rfl | hs1
  · -- Sheet-zero family: the row primitive fires the row word, the
    -- full observer converts the fire into the power's digit two.
    have hc14 : core % 9 = 1 ∨ core % 9 = 4 := by
      rcases hres with h4 | ⟨_, h1⟩ | ⟨h1s, h7⟩
      · exact Or.inr h4
      · exact Or.inl h1
      · exact absurd h1s (by omega)
    rw [Nat.pow_zero, Nat.one_mul] at hKsc
    have hKc : 500 < core := by
      rw [← hKsc]
      exact hK
    obtain ⟨j, hj⟩ := hRow core hKc hfree hc14
    refine ⟨1+j, ?_⟩
    rw [hKsc]
    have hobs := (tower_fire_iff_full 0 core j).2 hj
    rw [Nat.pow_zero, Nat.one_mul,
        show (0:Nat)+1+j = 1+j from by omega] at hobs
    exact hobs
  · -- Tower family: the tower primitive fires the deep tail of the cut
    -- word, the full observer converts the fire into the power's digit
    -- two at a position beyond the dodge band.
    have hc47 : core % 9 = 4 ∨ core % 9 = 7 := by
      rcases hres with h4 | ⟨hs0, h1⟩ | ⟨hs1', h7⟩
      · exact Or.inl h4
      · exact absurd hs0 (by omega)
      · exact Or.inr h7
    obtain ⟨i, his2, hfire⟩ := hTower s core hs1 hfree hc47 hD
    refine ⟨s+1+i, ?_⟩
    rw [hKsc]
    exact (tower_fire_iff_full s core i).2 hfire

/-! ## §5 The six-adic ghost skew (BOSS's six-adic machinery) -/
#print axioms TailFDecomposition406.tailF_of_row_and_tower  -- CK76 SECTION BOUNDARY

/-- **THE SIX-ADIC PAIR SATURATION (NEW).**  If the triadic shadow holds
at depth `k` and the x4 chart has supplied at least `k` dyadic factors
(`k ≤ 2t`), then the six-adic resolution holds: `6^k ∣ 4^t·d`.  The
dyadic half is automatic after saturation; the triadic half is the
ghost's own shadow. -/
theorem six_adic_pair_saturation (d k t : Nat)
    (h3 : 3^k ∣ d) (hkt : k ≤ 2 * t) :
    (6:Nat)^k ∣ 4^t * d := by
  obtain ⟨a, rfl⟩ := h3
  have h6 : (6:Nat)^k = 2^k * 3^k := by
    rw [show (6:Nat) = 2 * 3 from rfl, Nat.mul_pow]
  have h4 : (4:Nat)^t = 2^(2*t) := by
    rw [show (4:Nat) = 2^2 from rfl, ← Nat.pow_mul]
  rw [h6, h4]
  refine ⟨2^(2*t-k) * a, ?_⟩
  have hsub : 2^k * 2^(2*t-k) = 2^(2*t) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  calc 2^(2*t) * (3^k * a)
      = (2^k * 2^(2*t-k)) * (3^k * a) := by rw [hsub]
    _ = 2^k * 3^k * (2^(2*t-k) * a) := by ring

/-- The three-free cancellation (ported verbatim from kernel 75). -/
theorem dvd_mul_cancel_three (g d : Nat) (hg : ¬ (3:Nat) ∣ g)
    (h : (3:Nat) ∣ g * d) : (3:Nat) ∣ d := by
  have hg2 : g % 3 = 1 ∨ g % 3 = 2 := by
    have hlt : g % 3 < 3 := Nat.mod_lt _ (by decide)
    have hne : g % 3 ≠ 0 := fun h0 => hg (Nat.dvd_iff_mod_eq_zero.mpr h0)
    omega
  have hmod : (g * d) % 3 = 0 := Nat.dvd_iff_mod_eq_zero.mp h
  rw [Nat.mul_mod] at hmod
  rcases hg2 with h1 | h1
  · rw [h1] at hmod
    rcases Nat.eq_zero_or_pos (d % 3) with h0 | hp
    · exact Nat.dvd_iff_mod_eq_zero.mpr (by omega)
    · have hd2 : d % 3 = 1 ∨ d % 3 = 2 := by
        have hlt : d % 3 < 3 := Nat.mod_lt _ (by decide)
        omega
      rcases hd2 with h2 | h2
      · rw [h2] at hmod; norm_num at hmod
      · rw [h2] at hmod; norm_num at hmod
  · rw [h1] at hmod
    rcases Nat.eq_zero_or_pos (d % 3) with h0 | hp
    · exact Nat.dvd_iff_mod_eq_zero.mpr (by omega)
    · have hd2 : d % 3 = 1 ∨ d % 3 = 2 := by
        have hlt : d % 3 < 3 := Nat.mod_lt _ (by decide)
        omega
      rcases hd2 with h2 | h2
      · rw [h2] at hmod; norm_num at hmod
      · rw [h2] at hmod; norm_num at hmod

/-- Unit cancellation at every scale (ported verbatim from kernel 75). -/
theorem dvd_of_unit_mul_cancel : ∀ (k g d : Nat), ¬ (3:Nat) ∣ g →
    3^k ∣ g * d → 3^k ∣ d
  | 0, g, d, _, _ => by simp
  | k+1, g, d, hg, hdvd => by
      have hprev : 3^k ∣ g * d :=
        (pow_dvd_pow (3:Nat) (Nat.le_succ k)).trans hdvd
      have ih := dvd_of_unit_mul_cancel k g d hg hprev
      obtain ⟨d', hd'⟩ := ih
      obtain ⟨e, he⟩ := hdvd
      have hgd : g * d = 3^k * (g * d') := by rw [hd']; ring
      have hpow : 3^(k+1) = 3^k * 3 := Nat.pow_succ 3 k
      have he2 : 3^k * (3 * e) = 3^k * (g * d') := by
        calc 3^k * (3 * e) = (3^k * 3) * e := by ring
          _ = 3^(k+1) * e := by rw [← hpow]
          _ = g * d := he.symm
          _ = 3^k * (g * d') := hgd
      have hcancel : 3 * e = g * d' :=
        Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by decide)) he2
      have hgd3 : (3:Nat) ∣ g * d' := ⟨e, hcancel.symm⟩
      have hd3 : (3:Nat) ∣ d' := dvd_mul_cancel_three g d' hg hgd3
      obtain ⟨f, hf⟩ := hd3
      exact ⟨f, by rw [hd', hf, Nat.pow_succ]; try ring⟩

/-- **THE GHOST-PAIR COLLAPSE (NEW).**  Two ghosts whose diagonal
products are triadically congruent at every depth are EQUAL: cancel the
odd, three-free diagonal (a unit at every depth), then the
unboundedness of the powers of three annihilates the difference.  An
independent campaign proof of the uniqueness collapse, driven by the
six-adic skew's triadic half. -/
theorem ghost_pair_collapse_of_congr (u u' : Nat)
    (hle : u' ≤ u)
    (hcongr : ∀ k : Nat, 3 ≤ k →
      3^k ∣ lteCoeff (k-1) * (u - u')) :
    u = u' := by
  by_contra hne
  have hpos : 0 < u - u' := by omega
  obtain ⟨k0, hk0⟩ := three_pow_unbounded (u - u')
  have hk : 3 ≤ k0 + 3 := by omega
  have hdvd := hcongr (k0 + 3) hk
  have hk3 : (k0+3)-1 = k0+2 := by omega
  rw [hk3] at hdvd
  have hunit : ¬ (3:Nat) ∣ lteCoeff (k0+2) := by
    intro hd
    have h1 := lteCoeff_mod3_one (k0+2)
    rw [Nat.dvd_iff_mod_eq_zero.mp hd] at h1
    exact absurd h1 (by decide)
  have hdvd' := dvd_of_unit_mul_cancel (k0+3) (lteCoeff (k0+2)) (u - u')
    hunit hdvd
  obtain ⟨q, hq⟩ := hdvd'
  have hlt : u - u' < 3^(k0+3) := by
    have h1 : u - u' < 3^k0 := hk0
    have h2 : 3^k0 ≤ 3^(k0+3) := three_pow_le_of_le k0 (k0+3) (by omega)
    omega
  have hq0 : q = 0 := by
    by_contra hq0
    have hq1 : 1 ≤ q := by omega
    have hge : 3^(k0+3) ≤ 3^(k0+3) * q := by
      calc 3^(k0+3) = 3^(k0+3) * 1 := by ring
        _ ≤ 3^(k0+3) * q := Nat.mul_le_mul_left _ hq1
    omega
  rw [hq0, Nat.mul_zero] at hq
  omega

/-! ## §6 The paradox wall — the u-jump sign laws and the frozen tail -/
#print axioms TailFDecomposition406.ghost_pair_collapse_of_congr  -- CK76 SECTION BOUNDARY

/-- The handwritten-U charge (the monolith's exact table). -/
def gstUCharge (C : Nat) : Int :=
  if C = 0 then 5 else if C = 3 then 21 else 15

/-- The exact step carry of the x4/base3 wave. -/
def gstStepCarry (C d : Nat) : Nat := (C + 4*d) / 3

/-- The exact handwritten-U jump (the monolith's `jumpWith`). -/
def gstUJump (C d : Nat) : Int :=
  3 * (gstUCharge (gstStepCarry C d)) - gstUCharge C - 24 * (d : Int)

/-- **THE TWELVE-CELL JUMP TABLE** (the monolith's exact table,
kernel-decided). -/
theorem gst_u_jump_table :
    gstUJump 0 0 = 10 ∧
    gstUJump 0 1 = 16 ∧
    gstUJump 0 2 = -8 ∧
    gstUJump 1 0 = 0 ∧
    gstUJump 1 1 = 6 ∧
    gstUJump 1 2 = 0 ∧
    gstUJump 2 0 = 0 ∧
    gstUJump 2 1 = 6 ∧
    gstUJump 2 2 = 0 ∧
    gstUJump 3 0 = 24 ∧
    gstUJump 3 1 = 0 ∧
    gstUJump 3 2 = -6 := by
  decide

/-- The Happy cell: digit two with carry zero or three (the monolith's
`HappyCell`). -/
def HappyCell (C d : Nat) : Prop := d = 2 ∧ (C = 0 ∨ C = 3)

/-- **HAPPY CELLS JUMP NEGATIVE** (the monolith's sign law, ported). -/
theorem u_jump_happy_negative (C d : Nat) (h : HappyCell C d) :
    gstUJump C d < 0 := by
  obtain ⟨rfl, h0 | h3⟩ := h
  · subst C
    decide
  · subst C
    decide

/-- **NON-HAPPY CELLS JUMP NONNEGATIVE** (the monolith's sign law,
ported): every physical cell (carry < 4, digit < 3) that is not Happy
has a nonnegative exact jump. -/
theorem u_jump_not_happy_nonneg (C d : Nat)
    (hC : C < 4) (hd : d < 3) (hbad : ¬ HappyCell C d) :
    0 ≤ gstUJump C d := by
  have hCc : C = 0 ∨ C = 1 ∨ C = 2 ∨ C = 3 := by omega
  have hdc : d = 0 ∨ d = 1 ∨ d = 2 := by omega
  rcases hCc with rfl | rfl | rfl | rfl <;>
    rcases hdc with rfl | rfl | rfl <;>
    first
      | exact absurd (show HappyCell 0 2 from ⟨rfl, Or.inl rfl⟩) hbad
      | exact absurd (show HappyCell 3 2 from ⟨rfl, Or.inr rfl⟩) hbad
      | decide

/-- The x4 carry coordinate of `R` at position `p` (the monolith's
`carry4`). -/
def carry4 (R p : Nat) : Nat := (4 * (R % 3^p)) / 3^p

/-- The carry is physical: always below four. -/
theorem carry4_lt_four (R p : Nat) : carry4 R p < 4 := by
  have hp : 0 < 3^p := Nat.pow_pos (by decide)
  have hmod : R % 3^p < 3^p := Nat.mod_lt _ hp
  unfold carry4
  by_contra hge
  have h4 : 4 ≤ (4 * (R % 3^p)) / 3^p := by omega
  have hdm := Nat.div_add_mod (4 * (R % 3^p)) (3^p)
  have hrem : (4 * (R % 3^p)) % 3^p < 3^p := Nat.mod_lt _ hp
  have hle : 3^p * 4 ≤ 3^p * ((4 * (R % 3^p)) / 3^p) :=
    Nat.mul_le_mul_left _ h4
  have hcomb := Nat.le_trans hle
    (Nat.le_add_right (3^p * ((4 * (R % 3^p)) / 3^p))
      ((4 * (R % 3^p)) % 3^p))
  rw [← hdm] at hcomb
  have hlt : 4 * (R % 3^p) < 4 * 3^p := by omega
  have hmul : 4 * 3^p = 3^p * 4 := by ring
  omega

/-- The digit is physical: always below three. -/
theorem digit3_lt_three (x p : Nat) : digit3 x p < 3 := by
  unfold digit3
  exact Nat.mod_lt (x / 3^p) (by decide : 0 < 3)

/-- **CANTORIAN POWERS HAVE NO HAPPY CELL** — a Happy cell IS a digit
two. -/
theorem cell_not_happy_of_cantorian (K : Nat) (hCant : CantorianPower K)
    (p : Nat) (h : HappyCell (carry4 (4^K) p) (digit3 (4^K) p)) :
    False := by
  have hd : digit3 (4^K) p = 2 := h.1
  rcases Nat.eq_zero_or_pos p with rfl | hp1
  · rw [digit3_pow4_zero] at hd
    exact absurd hd (by decide)
  · exact hCant p hp1 hd

/-- **THE JUMP WALL (NEW).**  A Cantorian power rides an ETERNALLY
NON-NEGATIVE flux: every cell of the wave is non-Happy (no digit two
anywhere), so every exact u-jump is nonnegative, at every position. -/
theorem cantorian_jump_wall (K : Nat) (hCant : CantorianPower K) :
    ∀ p : Nat, 0 ≤ gstUJump (carry4 (4^K) p) (digit3 (4^K) p) := by
  intro p
  exact u_jump_not_happy_nonneg _ _
    (carry4_lt_four _ _) (digit3_lt_three _ _)
    (fun h => cell_not_happy_of_cantorian K hCant p h)

/-- Base monotonicity: `a ≤ b` gives `a^e ≤ b^e` (the CapLaw kernel's
own law, ported verbatim). -/
theorem pow_mono_base (a b e : Nat) (h : a ≤ b) : a^e ≤ b^e := by
  induction e with
  | zero => rfl
  | succ e ih =>
    rw [Nat.pow_succ, Nat.pow_succ]
    exact Nat.mul_le_mul ih h

/-- The size law for the tail bound: `4^K < 3^(3K+1)`. -/
theorem pow4_lt_three_pow (K : Nat) : 4^K < 3^(3*K+1) := by
  have hle : 4^K ≤ 27^K :=
    pow_mono_base 4 27 K (by decide : (4:Nat) ≤ 27)
  have h27 : 27^K = 3^(3*K) := by
    rw [show (27:Nat) = 3^3 from rfl, Nat.pow_mul]
  have h1 : 3^(3*K) < 3^(3*K+1) := by
    have hp : 0 < (3:Nat)^(3*K) := Nat.pow_pos (by decide)
    have hsplit : 3^(3*K+1) = 3 * 3^(3*K) := by
      rw [Nat.pow_succ]
      ring
    omega
  omega

/-- Strict base monotonicity: `a < b` and `e ≥ 1` give `a^e < b^e`
(the CapLaw kernel's own law, ported verbatim). -/
theorem pow_lt_mono_base (a b e : Nat) (h : a < b) (he : 1 ≤ e) :
    a^e < b^e := by
  obtain ⟨f, rfl⟩ : ∃ f : Nat, e = f + 1 := ⟨e - 1, by omega⟩
  clear he
  induction f with
  | zero =>
    rw [Nat.zero_add, Nat.pow_one, Nat.pow_one]
    exact h
  | succ f ih =>
    show a^(f+1+1) < b^(f+1+1)
    by_cases ha0 : a = 0
    · -- a = 0: 0^(f+2) = 0 < b^(f+2) since b ≥ 1
      subst ha0
      have hb : 0 < b := by omega
      have hbp : 0 < b^(f+2) := Nat.pow_pos hb
      rw [Nat.pow_succ (0:Nat) (f+1), Nat.mul_zero]
      exact hbp
    · -- 1 ≤ a: the strict monotonicity route (positivity available)
      have hapos : 0 < a := by omega
      have h1 : a^(f+1) * a < a^(f+1) * b := by
        obtain ⟨s, hs⟩ : ∃ s : Nat, b = a + s + 1 := ⟨b - a - 1, by omega⟩
        have hexp : a^(f+1) * (a + s + 1)
            = a^(f+1) * a + (s + 1) * a^(f+1) := by
          ring
        have hstep : 0 < (s + 1) * a^(f+1) := by
          have hpos : 0 < a^(f+1) := Nat.pow_pos hapos
          obtain ⟨k, hk⟩ : ∃ k : Nat, a^(f+1) = k + 1 :=
            ⟨a^(f+1) - 1, by omega⟩
          rw [hk]
          have hms : (s + 1) * (k + 1) = (s + 1) * k + (s + 1) :=
            Nat.mul_succ (s + 1) k
          rw [hms]
          omega
        rw [hs, hexp]
        omega
      have h2 : a^(f+1) * b ≤ b^(f+1) * b := by
        have hle : a^(f+1) ≤ b^(f+1) := Nat.le_of_lt ih
        obtain ⟨t, ht⟩ : ∃ t : Nat, b^(f+1) = a^(f+1) + t :=
          ⟨b^(f+1) - a^(f+1), by omega⟩
        have hexp : (a^(f+1) + t) * b = a^(f+1) * b + t * b := by ring
        rw [ht, hexp]
        omega
      calc a^(f+1+1) = a^(f+1) * a := Nat.pow_succ a (f+1)
        _ < a^(f+1) * b := h1
        _ ≤ b^(f+1) * b := h2
        _ = b^(f+1+1) := (Nat.pow_succ b (f+1)).symm

/-- The successor tail bound: `4^(K+1) < 3^(3K+3)` (the frozen-carry
engine). -/
theorem pow4_succ_lt (K : Nat) : 4^(K+1) < 3^(3*K+3) := by
  have h3eq : (3:Nat)^(3*K+3) = 27^(K+1) := by
    rw [show (27:Nat) = 3^3 from rfl, ← Nat.pow_mul]
    congr 1
    omega
  rw [h3eq]
  exact pow_lt_mono_base 4 27 (K+1) (by decide : (4:Nat) < 27) (by omega)

/-- **THE FROZEN TAIL (NEW).**  Beyond position `3K+3` the wave of
`4^K` is frozen: digit zero, carry zero, and the exact jump is TEN —
the strictly positive frozen flux, forever. -/
theorem frozen_tail_jump_ten (K p : Nat) (hp : 3*K+3 ≤ p) :
    digit3 (4^K) p = 0 ∧ carry4 (4^K) p = 0
      ∧ gstUJump (carry4 (4^K) p) (digit3 (4^K) p) = 10 := by
  have hp3 : 0 < (3:Nat)^p := Nat.pow_pos (by decide)
  have hmod : 4^K % 3^p < 3^p := Nat.mod_lt _ hp3
  have hKlt1 : 4^K < 3^(3*K+1) := pow4_lt_three_pow K
  have hle1 : 3^(3*K+1) ≤ 3^p := three_pow_le_of_le (3*K+1) p (by omega)
  have hKlt : 4^K < 3^p := by omega
  have hd : digit3 (4^K) p = 0 := by
    unfold digit3
    rw [Nat.div_eq_of_lt hKlt]
  have hcarrylt : 4 * (4^K % 3^p) < 3^p := by
    have h4K : 4 * 4^K = 4^(K+1) := by
      rw [Nat.pow_succ]
      ring
    have hlt2 : 4^(K+1) < 3^(3*K+3) := pow4_succ_lt K
    have hle2 : 3^(3*K+3) ≤ 3^p := three_pow_le_of_le (3*K+3) p hp
    have hleM : 4 * (4^K % 3^p) ≤ 4 * 4^K :=
      Nat.mul_le_mul_left _ (Nat.mod_le (4^K) (3^p))
    omega
  have hc : carry4 (4^K) p = 0 := by
    unfold carry4
    exact Nat.div_eq_of_lt hcarrylt
  exact ⟨hd, hc, by rw [hc, hd]; decide⟩

/-- **THE PARADOX WALL (NEW, the receipt).**  A Cantorian power's flux
is eternally nonnegative with a strictly positive frozen tail: beyond
`3K+3` every jump is exactly ten.  This is the eternal-dodge fuel
gauge for the extinction round — the monolith's cocycle (Equation III)
pins this nonnegative frozen flux against the vacuum baseline. -/
theorem cantorian_paradox_wall (K : Nat) (hCant : CantorianPower K) :
    (∀ p : Nat, 0 ≤ gstUJump (carry4 (4^K) p) (digit3 (4^K) p))
    ∧ (∀ p : Nat, 3*K+3 ≤ p →
        gstUJump (carry4 (4^K) p) (digit3 (4^K) p) = 10) :=
  ⟨cantorian_jump_wall K hCant,
    fun p hp => (frozen_tail_jump_ten K p hp).2.2⟩

/-! ## §7 The crown v3 — the assembly -/
#print axioms TailFDecomposition406.cantorian_paradox_wall  -- CK76 SECTION BOUNDARY

/-- The digit-two scan (the kernel-75 census engine, ported). -/
def hasTwoScan : Nat → Nat → Bool
  | _, 0 => false
  | n, B+1 => (n % 3 == 2) || hasTwoScan (n / 3) B

theorem hasTwoScan_iff : ∀ (B n : Nat),
    hasTwoScan n B = true ↔ ∃ p : Nat, p < B ∧ digit3 n p = 2 := by
  intro B
  induction B with
  | zero =>
      intro n
      constructor
      · intro h; exact absurd h (by simp [hasTwoScan])
      · intro ⟨p, hp, _⟩; exact absurd hp (by omega)
  | succ B ih =>
      intro n
      have h0 : digit3 n 0 = n % 3 := by
        unfold digit3
        rw [Nat.pow_zero, Nat.div_one]
      have hsh : ∀ p : Nat, digit3 n (p + 1) = digit3 (n / 3) p := by
        intro p
        unfold digit3
        rw [Nat.pow_succ, Nat.div_div_eq_div_mul, Nat.mul_comm (3^p) (3:Nat)]
      by_cases hb : n % 3 = 2
      · have hbeq : (n % 3 == 2) = true := by rw [hb]; rfl
        simp only [hasTwoScan, hbeq, Bool.true_or]
        constructor
        · intro _
          exact ⟨0, by omega, by rw [h0, hb]⟩
        · intro _
          simp [hasTwoScan, hbeq]
      · have hbeq : (n % 3 == 2) = false := by
          cases hbb : (n % 3 == 2) with
          | true =>
              have h22 : n % 3 = 2 := by simpa using hbb
              exact absurd h22 hb
          | false => rfl
        simp only [hasTwoScan, hbeq, Bool.false_or]
        constructor
        · intro h
          obtain ⟨p, hp, hd⟩ := (ih (n / 3)).mp h
          exact ⟨p + 1, by omega, by rw [hsh p]; exact hd⟩
        · intro ⟨p, hp, hd⟩
          cases p with
          | zero =>
              rw [h0] at hd
              exact absurd hd hb
          | succ q =>
              rw [hsh q] at hd
              exact (ih (n / 3)).mpr ⟨q, by omega, hd⟩

/-- The census case: the exact digit scan of `4^(8+i)` at fuel 632. -/
def baseCaseB (i : Nat) : Bool := hasTwoScan (4^(8+i)) 632

theorem base_chunk_one : (List.range 251).all
    (fun i => baseCaseB i) = true := by decide

theorem base_chunk_two : (List.range 242).all
    (fun i => baseCaseB (251 + i)) = true := by decide

/-- **THE FINITE BASE** (ported verbatim): every exponent `8 ≤ K ≤ 500`
owns a ternary digit two. -/
theorem cantorian_base (K : Nat) (hK8 : 8 ≤ K) (hK500 : K ≤ 500) :
    ∃ p : Nat, digit3 (4^K) p = 2 := by
  rcases Nat.lt_or_ge K (8 + 251) with hlt | hge
  · have hc := (List.all_eq_true.mp base_chunk_one) (K - 8)
      (List.mem_range.mpr (by omega))
    unfold baseCaseB at hc
    rw [show 8 + (K - 8) = K from by omega] at hc
    obtain ⟨p, _, hd⟩ := (hasTwoScan_iff 632 _).mp hc
    exact ⟨p, hd⟩
  · have hc := (List.all_eq_true.mp base_chunk_two) (K - 8 - 251)
      (List.mem_range.mpr (by omega))
    unfold baseCaseB at hc
    rw [show 8 + (251 + (K - 8 - 251)) = K from by omega] at hc
    obtain ⟨p, _, hd⟩ := (hasTwoScan_iff 632 _).mp hc
    exact ⟨p, hd⟩

/-- A ternary digit two at any position certifies the Arsenal's
has-reader. -/
theorem hasTwo_of_digit : ∀ (n p : Nat), digit3 n p = 2 →
    hasTernaryTwo n = true :=
  fun n p hp => hasTernaryTwo_of_digit n p hp

/-- **THE CROWN V3 (NEW).**  The FULL Erdős #406 statement —
`∀ n ≥ 9, noTernaryTwo (2^n) = false` — follows from the weakened
grant pair, with the compression in its exact monolith cut-word form:
* (G1') **ghost extinction on the rider sheet**: no `u ≡ 1 mod 3` is
  a ghost ray;
* (G2') **compression, cut-word form**: every three-free core whose
  Ω-cut word is digit-2-free IS a ghost ray.
Everything else is unconditional and machine-checked here: the census
base, the rider's core law, the compression law (§3), the odd wing,
the digit-to-verdict bridge. -/
theorem erdos406_crown_v3
    (hNoGhost : ∀ u : Nat, u % 3 = 1 → ¬ GhostRay u)
    (hCompCut : ∀ (s u : Nat), ¬ (3:Nat) ∣ u →
      (∀ q : Nat, digit3 (omegaCutWord s u) q ≠ 2) → GhostRay u) :
    ∀ n : Nat, 9 ≤ n → noTernaryTwo (2^n) = false := by
  -- Step 1: no Cantorian power above eight
  have hnoCant : ∀ K : Nat, 8 ≤ K → ¬ CantorianPower K := by
    intro K hK8 hCant
    rcases Nat.lt_or_ge K 501 with hle | hgt
    · obtain ⟨p, hp⟩ := cantorian_base K hK8 (by omega)
      rcases Nat.eq_zero_or_pos p with h0 | hp1
      · rw [h0, digit3_pow4_zero] at hp
        exact absurd hp (by decide)
      · exact hCant p hp1 hp
    · obtain ⟨σ, u, hKu, hufree, hu1⟩ :=
        rider_core_one K (by omega) hCant
      have hclean : ∀ q : Nat, digit3 (omegaCutWord σ u) q ≠ 2 :=
        (cantorian_iff_cutword_clean σ u).mp (by rw [← hKu]; exact hCant)
      exact hNoGhost u hu1 (hCompCut σ u hufree hclean)
  -- Step 2: every 4^m, m ≥ 5, owns a digit two
  have hfire : ∀ m : Nat, 5 ≤ m → ∃ p : Nat, digit3 (4^m) p = 2 := by
    intro m hm
    rcases Nat.lt_or_ge m 8 with hlt | hge
    · have hm567 : m = 5 ∨ m = 6 ∨ m = 7 := by omega
      rcases hm567 with rfl | rfl | rfl
      · exact ⟨2, by decide⟩
      · exact ⟨2, by decide⟩
      · exact ⟨8, by decide⟩
    · have hnc := hnoCant m hge
      by_contra hclean
      exact hnc (fun p hp hdirty => hclean ⟨p, hdirty⟩)
  -- Step 3: the final assembly, odd and even wings
  intro n hn
  rcases Nat.mod_two_eq_zero_or_one n with heven | hodd
  · have hm : n = 2 * (n / 2) := by omega
    have hm5 : 5 ≤ n / 2 := by omega
    obtain ⟨p, hp⟩ := hfire (n / 2) hm5
    have hhas : hasTernaryTwo (4^(n / 2)) = true :=
      hasTwo_of_digit (4^(n / 2)) p hp
    have h2n : 2^n = 4^(n / 2) := by
      rw [hm, two_pow_two_mul]
      congr 1
      omega
    rw [h2n]
    exact has_two_imp_not_no_two (4^(n / 2)) hhas
  · have hnodd : n = 2 * (n / 2) + 1 := by omega
    have hmod : (2^n) % 3 = 2 := by
      rw [hnodd, Nat.pow_succ]
      have h2m : (2:Nat)^(2 * (n / 2)) % 3 = 1 := by
        rw [two_pow_two_mul]
        exact pow4_mod3 _
      rw [Nat.mul_mod, h2m]
    have hdig : digit3 (2^n) 0 = 2 := by
      unfold digit3
      rw [Nat.pow_zero, Nat.div_one, hmod]
    have hhas : hasTernaryTwo (2^n) = true :=
      hasTwo_of_digit (2^n) 0 hdig
    exact has_two_imp_not_no_two (2^n) hhas

/-! ## §8 Receipts -/
#print axioms TailFDecomposition406.erdos406_crown_v3  -- CK76 SECTION BOUNDARY

#print axioms TailFDecomposition406.omega_cut_factor
#print axioms TailFDecomposition406.cutword_diag_congr
#print axioms TailFDecomposition406.cutword_one
#print axioms TailFDecomposition406.prefix_slice_digit
#print axioms TailFDecomposition406.tower_digit_eq_cutword
#print axioms TailFDecomposition406.digit_residue_fire_iff
#print axioms TailFDecomposition406.tower_fire_iff_full
#print axioms TailFDecomposition406.cantorian_iff_cutword_clean
#print axioms TailFDecomposition406.tailF_of_row_and_tower
#print axioms TailFDecomposition406.six_adic_pair_saturation
#print axioms TailFDecomposition406.lteCoeff_odd
#print axioms TailFDecomposition406.ghost_pair_collapse_of_congr
#print axioms TailFDecomposition406.gst_u_jump_table
#print axioms TailFDecomposition406.u_jump_happy_negative
#print axioms TailFDecomposition406.u_jump_not_happy_nonneg
#print axioms TailFDecomposition406.carry4_lt_four
#print axioms TailFDecomposition406.cell_not_happy_of_cantorian
#print axioms TailFDecomposition406.cantorian_jump_wall
#print axioms TailFDecomposition406.pow4_succ_lt
#print axioms TailFDecomposition406.frozen_tail_jump_ten
#print axioms TailFDecomposition406.cantorian_paradox_wall
#print axioms TailFDecomposition406.cantorian_base
#print axioms TailFDecomposition406.erdos406_crown_v3

#eval "ERDOS406_TAILFDECOMPOSITION_KERNEL_GREEN"

end TailFDecomposition406
