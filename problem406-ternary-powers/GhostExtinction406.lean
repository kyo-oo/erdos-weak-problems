import Arsenal.ErdosTernary2.Basic
import Arsenal.CardinalWorlds
import Arsenal.CardinalWorldsV2

-- Family pattern (green kernels): explicit depth headroom.
set_option maxRecDepth 262144
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 1000

/-!
# ERDŐS #406 — THE GHOST-EXTINCTION KERNEL (S083, Kernel 75): the rider's
# core law, the head split, the uniqueness collapse, the depth-100 pins,
# the size law, and the crown at one-and-a-half grants

## THE OBJECT (BOSS order: crack the hTailF hypothesis — BOSS's laws only,
## the GST ghost machinery driven to its exact remaining content)

The remaining content of Erdős #406 (the even half; the odd half green) is
the SEPARATION: no exponent `m ≥ 5` has `4^m` with all ternary digits in
`{0, 1}`.  The S080 two-grant crown reduced the war to (G1) ghost
extinction + (G2) residual ghost compression.  THIS KERNEL sharpens the
grants to their exact minimum:

* **§2 THE RIDER'S CORE LAW** (`rider_core_one`, NEW): every Cantorian
  power `K = 3^σ·u` (three-free `u`) forces `u ≡ 1 (mod 3)` — the rider
  form rides only on the `u ≡ 1` lattice sheet.  Consequence: the crown's
  extinction grant needs ONLY the `u ≡ 1 (mod 3)` ghosts — the `u ≡ 2`
  sheet becomes irrelevant to #406.

* **§4 THE HEAD SPLIT** (`ghost_head_split`, NEW): every ghost ray with
  `u ≡ 1 (mod 3)` has head in `{1, 4, 7}` — exactly the three exhibited
  π-families.  The extinction grant reduces to THREE 3-adic points.

* **§5 THE UNIQUENESS COLLAPSE** (`ghost_uniqueness`, NEW): two ghost
  rays with the same head are EQUAL — the total number of ghost rays on
  the rider sheet `u ≡ 1 (mod 3)` is AT MOST THREE.

* **§6 THE DEPTH-100 PINS** (NEW): the three π-points extended from 61
  to 100 trits (W100 dual-verified: the cMod recursion ∥ the direct
  modular division `4^(3^99) mod 3^200`; the π-points dual-verified:
  pow-inverse ∥ independent Hensel lift; all three 61-trit prefixes
  matching the S080 kernel constants byte-for-byte).

* **§7 THE SIZE LAW** (NEW): every ghost ray on the rider sheet exceeds
  `3^98` (families 4 and 7 exceed `3^99`); the deep 2-trit receipts now
  run through position 99 (fam4: 18 twos in 61..99; fam7: 13; fam1: 12).

* **§9 THE CROWN V2** (`erdos406_crown_v2`, NEW): the FULL Erdős #406
  statement follows from the WEAKENED grant pair —
  (G1') `∀ u ≡ 1 (mod 3), ¬ GhostRay u` (the u≡1 sheet only) +
  (G2) the residual ghost compression.
  Everything else unconditional, self-contained, machine-checked here.

* **§9b THE COMPOSED WALL** (`rider_wall_v2`, NEW): under the single
  grant (G2), every Cantorian power above 500 exceeds `3^98` — the
  remaining content of #406 is at most THREE astronomically large
  numbers, one per π-family.

## THE HONEST SCOPE (unchanged law: no dressing)

The grants stand: (G1') is the π non-naturality beyond depth 100 (the
3-adic irrationality seam — the campaign's named wall, now pinned to
three specific points with 2-trits certified through position 99);
(G2) is the depth-σ to depth-∞ compression.  What this kernel delivers:
the grants' exact minimum form, the uniqueness collapse, the depth-100
extension, and the size wall.  The engine never stops; it never lies.
-/

namespace GhostExtinction406

/-! ## §0 The engine (self-contained; the green Block-Law/Pi-Collapse toolkit) -/

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

/-- Powers of three are unbounded (the uniqueness engine's fuel). -/
theorem three_pow_unbounded : ∀ n : Nat, ∃ k : Nat, n < 3^k
  | 0 => ⟨1, by decide⟩
      | n+1 => by
      obtain ⟨k, hk⟩ := three_pow_unbounded n
      refine ⟨k + 1, ?_⟩
      have hp : 0 < 3^k := Nat.pow_pos (by decide)
      have h3 : 3^(k+1) = 3^k * 3 := by rw [Nat.pow_succ]
      omega

/-- The tower coefficient: `lteCoeff v = c_v` with
`4^(3^v) = 1 + 3^(v+1) * c_v`. -/
def lteCoeff : Nat → Nat
  | 0 => 1
  | r+1 =>
      let c := lteCoeff r
      c + 3^(r+1) * c^2 + 3^(2*r+1) * c^3

/-- **THE TOWER IDENTITY.**  `4^(3^v) = 1 + 3^(v+1) * lteCoeff v`,
by division-free cube induction (the green Block-Law engine). -/
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

/-- Mod-zero folding: if `m ∣ b` then `(a + b) % m = a % m`. -/
theorem add_mod_of_dvd (a b m : Nat) (hdvd : m ∣ b) :
    (a + b) % m = a % m := by
  obtain ⟨q, rfl⟩ := hdvd
  first
    | rw [Nat.add_mul_mod_self_left]
    | rw [Nat.add_mul_mod_self_right]

/-- One-step frozen-diagonal drop: the lift adds a multiple of the scale. -/
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

/-- Mod is unchanged when the modulus drops along a divisibility. -/
theorem mod_dvd_modeq (a b m n : Nat) (hmn : m ∣ n) (h : a % n = b % n) :
    a % m = b % m := by
  rw [← Nat.mod_mod_of_dvd a hmn, ← Nat.mod_mod_of_dvd b hmn, h]

/-- **THE FROZEN DIAGONAL** (stabilization): `c_w ≡ c_v [MOD 3^(v+1)]`
for `v ≤ w` — the tower word stabilizes. -/
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

/-! ## §0b The cut-residue toolkit (the green Block-Law helpers) -/

/-- The two-term binomial shape. -/
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

/-- The digit of one is zero at every positive position. -/
theorem digit3_one_pos (p : Nat) (hp : 1 ≤ p) : digit3 1 p = 0 := by
  unfold digit3
  have h1 : 1 < 3^p := by
    have h0 : 3^1 ≤ 3^p :=
      Nat.pow_le_pow_of_le (by decide : 1 < 3) (by omega)
    omega
  rw [Nat.div_eq_of_lt (by omega : (1:Nat) < 3^p)]

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

/-- The next-scale residue: the power is exactly one at the cut. -/
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

/-- The valuation decomposition: every positive `K` is `3^v·u` with
`u % 3 ≠ 0`. -/
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

/-- Digit addition at a power position: adding `3^m·B` shifts `B` into
digit `m` modulo three. -/
theorem digit3_add_pow (A B m : Nat) :
    digit3 (A + 3^m * B) m = (digit3 A m + B) % 3 := by
  unfold digit3
  have hp : 0 < 3^m := Nat.pow_pos (by decide)
  rw [Nat.add_mul_div_left _ _ hp, Nat.add_mod]
  omega

/-- The residue-to-digit bridge: `R ≡ 1 + 2·3^p [MOD 3^(p+1)]` with
`p ≥ 1` forces `digit3 R p = 2` (the fire reader). -/
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

/-! ## §1 The Cantorian predicate and the ghost ray -/

/-- The Cantorian power predicate: every ternary digit from position
one on avoids two (position zero is always one). -/
def CantorianPower (K : Nat) : Prop :=
  ∀ p : Nat, 1 ≤ p → digit3 (4^K) p ≠ 2

/-- **THE GHOST RAY** — the stabilized middle-third condition: a core
`u` whose scaled LTE diagonal `(c (k-1) * u) % 3^k` sits in the exact
middle third at every ternary depth `k ≥ 3`. -/
def GhostRay (u : Nat) : Prop :=
  ∀ k : Nat, 3 ≤ k →
    3^(k-1) ≤ (lteCoeff (k-1) * u) % 3^k
    ∧ (lteCoeff (k-1) * u) % 3^k < 2 * 3^(k-1)

/-- The canonical ghost head: the residue that anchors the all-ones
tail. -/
def ghostHead (u : Nat) : Nat := (lteCoeff 1 * u) % 9

/-! ## §2 THE RIDER'S CORE LAW — riders ride only the u ≡ 1 sheet -/
#print axioms GhostExtinction406.ghostHead  -- CK75 SECTION BOUNDARY

/-- **THE RIDER'S CORE LAW (NEW).**  Every Cantorian power `K` with
`K = 3^σ·u` and `u` three-free satisfies `u ≡ 1 (mod 3)`: the second
nonzero digit of the power is `u % 3`, a two there fires, and three-free
excludes zero.  The rider sheet is exactly `u ≡ 1 (mod 3)`. -/
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
    -- the fire: digit (v+1) of the power is exactly two
    have hres := pow4_cut_residue_exact v u
    rw [h] at hres
    have hv1 : 1 ≤ v + 1 := by omega
    have hfire : digit3 (4^K) (v+1) = 2 := by
      have hmod : 4^K % 3^((v+1)+1) = 1 + 2 * 3^(v+1) := by
        rw [show ((v:Nat)+1)+1 = v+2 from by omega, hKu, hres]
      exact digit3_of_residue_two (4^K) (v+1) hv1 hmod
    exact hCant (v+1) hv1 hfire

/-! ## §3 Lemma A and Lemma B (the green Pi-Collapse engine) -/
#print axioms GhostExtinction406.ghostHead  -- CK75 SECTION BOUNDARY

/-- **LEMMA A (the exact ghost shape).**  A ghost ray forces the residue
of `c (k-1) * u` modulo `3^k` to be the all-ones tail — stated free of
division as `2 * residue + 9 = 2 * head + 3^k`. -/
theorem ghost_residue_shape (u : Nat) (hg : GhostRay u) :
    ∀ k : Nat, 3 ≤ k →
      2 * ((lteCoeff (k-1) * u) % 3^k) + 9
        = 2 * ghostHead u + 3^k := by
  intro k
  induction k with
  | zero => intro h; exact absurd h (by omega)
  | succ j ih =>
      intro hk
      rcases Nat.lt_or_ge j 3 with hj | hj
      · have hj2 : j = 2 := by omega
        subst hj2
        obtain ⟨hlo, hhi⟩ := hg 3 (by omega)
        norm_num at hlo hhi
        have hc9 : (lteCoeff 2 * u) % 9 = (lteCoeff 1 * u) % 9 := by
          have hc : lteCoeff 2 % 9 = lteCoeff 1 % 9 := by
            have h := lteCoeff_stable 1 2 (by omega)
            rw [show 1 + 1 = 2 from rfl] at h
            exact h
          rw [Nat.mul_mod, hc, ← Nat.mul_mod]
        have hmod : ((lteCoeff 2 * u) % 27) % 9
            = (lteCoeff 1 * u) % 9 := by
          rw [Nat.mod_mod_of_dvd _ (by decide : (9:Nat) ∣ 27)]
          exact hc9
        have ha : (lteCoeff 1 * u) % 9 < 9 := Nat.mod_lt _ (by decide)
        have hd := Nat.div_add_mod ((lteCoeff 2 * u) % 27) 9
        have h27 : (lteCoeff 2 * u) % 27 < 27 := Nat.mod_lt _ (by decide)
        unfold ghostHead at *
        norm_num
        omega
      · have ihj := ih hj
        rw [show j + 1 - 1 = j from rfl]
        obtain ⟨hlo, hhi⟩ := hg (j+1) (by omega)
        rw [show j + 1 - 1 = j from rfl] at hlo hhi
        set r' : Nat := (lteCoeff j * u) % 3^(j+1) with hr'
        have hsub : r' - 3^j < 3^j := by omega
        have hkey : r' - 3^j = r' % 3^j := by
          have e1 : r' = (r' - 3^j) + 1 * 3^j := by omega
          rw [e1, Nat.add_mul_mod_self_right, one_mul, Nat.add_sub_cancel,
            Nat.mod_eq_of_lt hsub]
        have hmodk : (lteCoeff j * u) % 3^(j+1) % 3^j
            = (lteCoeff j * u) % 3^j :=
          Nat.mod_mod_of_dvd _ (pow_dvd_pow (3 : ℕ) (by omega))
        rw [← hr'] at hmodk
        have hcs : lteCoeff j % 3^j = lteCoeff (j-1) % 3^j := by
          have h := lteCoeff_stable (j-1) j (by omega)
          rw [show (j-1)+1 = j from by omega] at h
          exact h
        have hstab : (lteCoeff j * u) % 3^j
            = (lteCoeff (j-1) * u) % 3^j := by
          rw [Nat.mul_mod, hcs, ← Nat.mul_mod]
        rw [Nat.pow_succ]
        omega

/-- **LEMMA B (the fundamental finite ghost congruence).**  A ghost ray
satisfies `2 * (c (k-1) * u) + 9 = 2 * head + 3^k * m` for every depth
`k ≥ 3`. -/
theorem ghost_congruence (u : Nat) (hg : GhostRay u) (k : Nat) (hk : 3 ≤ k) :
    ∃ m : Nat, 2 * (lteCoeff (k-1) * u) + 9
      = 2 * ghostHead u + 3^k * m := by
  have hshape := ghost_residue_shape u hg k hk
  have hq := Nat.div_add_mod (lteCoeff (k-1) * u) (3^k)
  refine ⟨2 * (lteCoeff (k-1) * u / 3^k) + 1, ?_⟩
  have hring : 3^k * (2 * (lteCoeff (k-1) * u / 3^k) + 1)
      = 2 * (3^k * (lteCoeff (k-1) * u / 3^k)) + 3^k := by ring
  have hring2 : 2 * (3^k * (lteCoeff (k-1) * u / 3^k)
      + (lteCoeff (k-1) * u) % 3^k)
      = 2 * (3^k * (lteCoeff (k-1) * u / 3^k))
        + 2 * ((lteCoeff (k-1) * u) % 3^k) := by ring
  omega

/-! ## §4 THE HEAD SPLIT — the rider sheet carries exactly three heads -/
#print axioms GhostExtinction406.ghost_congruence  -- CK75 SECTION BOUNDARY

/-- **THE HEAD SPLIT (NEW).**  Every ghost ray on the rider sheet
(`u ≡ 1 mod 3`) has head in `{1, 4, 7}` — exactly the three exhibited
π-families.  The `u ≡ 2` heads (`2, 5, 8`) are irrelevant to #406. -/
theorem ghost_head_split (u : Nat) (hg : GhostRay u) (hu3 : u % 3 = 1) :
    ghostHead u = 1 ∨ ghostHead u = 4 ∨ ghostHead u = 7 := by
  have hc1 : lteCoeff 1 = 7 := by decide
  have hlt : u % 9 < 9 := Nat.mod_lt _ (by decide)
  have hm : (u % 9) % 3 = u % 3 := by
    rw [Nat.mod_mod_of_dvd u (by decide : (3:Nat) ∣ 9)]
  rw [hu3] at hm
  have hdm : u % 9 = 3 * (u % 9 / 3) + (u % 9) % 3 :=
    (Nat.div_add_mod (u % 9) 3).symm
  have hq : u % 9 / 3 < 3 := by omega
  rcases ErdosTernary2.lt_three_cases (u % 9 / 3) hq with h0 | h0 | h0
  · refine Or.inr (Or.inr ?_)
    unfold ghostHead
    rw [hc1, Nat.mul_mod]
    have hu9 : u % 9 = 1 := by omega
    rw [hu9]
  · refine Or.inl ?_
    unfold ghostHead
    rw [hc1, Nat.mul_mod]
    have hu9 : u % 9 = 4 := by omega
    rw [hu9]
  · refine Or.inr (Or.inl ?_)
    unfold ghostHead
    rw [hc1, Nat.mul_mod]
    have hu9 : u % 9 = 7 := by omega
    rw [hu9]

/-! ## §5 The cancellation engine, the collapse, and the uniqueness -/
#print axioms GhostExtinction406.ghost_head_split  -- CK75 SECTION BOUNDARY

/-- Cancel a factor of three: if `3 ∣ g * d` and `3 ∣ g` then `3 ∣ d`. -/
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

/-- **Unit cancellation at every scale:** a factor not divisible by
three can be removed from a divisibility by `3^k`. -/
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

/-- The difference engine: two congruences against the same head give
the scale-divisibility of the difference. -/
theorem cancel_engine (k u u' H : Nat)
    (hunit : ¬ (3:Nat) ∣ 2 * lteCoeff (k-1))
    (hm : ∃ M, 2 * (lteCoeff (k-1) * u) + 9 = 2 * H + 3^k * M)
    (hm' : ∃ M, 2 * (lteCoeff (k-1) * u') + 9 = 2 * H + 3^k * M)
    (hle : u' ≤ u) :
    ∃ T : Nat, u = u' + 3^k * T := by
  obtain ⟨m, hm⟩ := hm
  obtain ⟨m', hm'⟩ := hm'
  have hu : u = u' + (u - u') := by omega
  have hmul : lteCoeff (k-1) * u
      = lteCoeff (k-1) * u' + lteCoeff (k-1) * (u - u') := by
    have hsplit : u' + (u - u') = u := by omega
    calc lteCoeff (k-1) * u = lteCoeff (k-1) * (u' + (u - u')) := by rw [hsplit]
      _ = lteCoeff (k-1) * u' + lteCoeff (k-1) * (u - u') :=
          Nat.mul_add _ _ _
  rw [hmul] at hm
  have hdist : 2 * (lteCoeff (k-1) * u' + lteCoeff (k-1) * (u - u'))
      = 2 * (lteCoeff (k-1) * u') + 2 * (lteCoeff (k-1) * (u - u')) := by
    ring
  rw [hdist] at hm
  have hdvd : 3^k ∣ 2 * (lteCoeff (k-1) * (u - u')) := by
    refine ⟨m - m', ?_⟩
    rw [show 3^k * (m - m') = 3^k * m - 3^k * m' from
      Nat.mul_sub (3^k) m m']
    omega
  have hcancel := dvd_of_unit_mul_cancel k (2 * lteCoeff (k-1)) (u - u')
    hunit (by rw [Nat.mul_assoc]; exact hdvd)
  obtain ⟨t, ht⟩ := hcancel
  exact ⟨t, by omega⟩

/-- The depth-`k ≥ 3` congruence engine. -/
theorem ghost_congruent_ge_three (u u' : Nat)
    (hg : GhostRay u) (hg' : GhostRay u') (hhead : ghostHead u = ghostHead u')
    (k : Nat) (hk : 3 ≤ k) : u % 3^k = u' % 3^k := by
  obtain ⟨m, hm⟩ := ghost_congruence u hg k hk
  obtain ⟨m', hm'⟩ := ghost_congruence u' hg' k hk
  rw [← hhead] at hm'
  have hc1 : lteCoeff (k-1) % 3 = 1 := lteCoeff_mod3_one _
  have hunit : ¬ (3:Nat) ∣ 2 * lteCoeff (k-1) := by
    intro hd
    have h0 : (2 * lteCoeff (k-1)) % 3 = 0 :=
      Nat.dvd_iff_mod_eq_zero.mp hd
    rw [Nat.mul_mod, hc1] at h0
    norm_num at h0
  by_cases hle : u' ≤ u
  · obtain ⟨t, ht⟩ := cancel_engine k u u' (ghostHead u) hunit
      ⟨m, hm⟩ ⟨m', hm'⟩ hle
    rw [ht, Nat.add_mul_mod_self_left]
  · have hgt : u ≤ u' := by omega
    obtain ⟨t, ht⟩ := cancel_engine k u' u (ghostHead u) hunit
      ⟨m', hm'⟩ ⟨m, hm⟩ hgt
    have hmod : u % 3^k = u' % 3^k := by
      rw [ht, Nat.add_mul_mod_self_left]
    rw [hmod]

/-- **THE COLLAPSE — same-head ghosts are one point.** -/
theorem ghost_congruent_all_depths (u u' : Nat)
    (hg : GhostRay u) (hg' : GhostRay u') (hhead : ghostHead u = ghostHead u')
    (k : Nat) : u % 3^k = u' % 3^k := by
  rcases Nat.lt_or_ge k 3 with hlt | hge
  · have h3 := ghost_congruent_ge_three u u' hg hg' hhead 3 (by omega)
    exact mod_dvd_modeq _ _ _ _ (pow_dvd_pow (3:Nat) (by omega)) h3
  · exact ghost_congruent_ge_three u u' hg hg' hhead k hge

/-- **THE UNIQUENESS COLLAPSE (NEW).**  Two ghost rays with the same
head are EQUAL: the total number of ghost rays on the rider sheet
(`u ≡ 1 mod 3`) is at most three — one per head in `{1, 4, 7}`. -/
theorem ghost_uniqueness (u u' : Nat)
    (hg : GhostRay u) (hg' : GhostRay u')
    (hhead : ghostHead u = ghostHead u') : u = u' := by
  obtain ⟨k, hk⟩ := three_pow_unbounded (max u u')
  have h := ghost_congruent_all_depths u u' hg hg' hhead k
  have hu : u < 3^k := Nat.lt_of_le_of_lt (Nat.le_max_left u u') hk
  have hu' : u' < 3^k := Nat.lt_of_le_of_lt (Nat.le_max_right u u') hk
  rw [Nat.mod_eq_of_lt hu, Nat.mod_eq_of_lt hu'] at h
  exact h

/-! ## §6 The depth-100 pins — the three π-points, kernel-decided -/
#print axioms GhostExtinction406.ghost_uniqueness  -- CK75 SECTION BOUNDARY

/-- The certified mod-recursion: `cMod k s = lteCoeff s % 3^k`, computed
without ever forming the astronomically large tower coefficient. -/
def cMod : Nat → Nat → Nat
  | k, 0 => 1 % 3^k
  | k, s+1 =>
      let c := cMod k s
      (c + 3^(s+1) * c^2 + 3^(2*s+1) * c^3) % 3^k

/-- Congruence respects addition (hardened: explicit lemma applications —
the double-rw form re-matches the outer term under the W82 Mathlib). -/
theorem mod_add_congr (k a b c d : Nat) (h1 : a % k = b % k)
    (h2 : c % k = d % k) : (a + c) % k = (b + d) % k := by
  calc (a + c) % k = ((a % k) + (c % k)) % k := Nat.add_mod a c k
    _ = ((b % k) + (d % k)) % k := by rw [h1, h2]
    _ = (b + d) % k := (Nat.add_mod b d k).symm

/-- Congruence respects multiplication (hardened the same way). -/
theorem mod_mul_congr (k a b c d : Nat) (h1 : a % k = b % k)
    (h2 : c % k = d % k) : (a * c) % k = (b * d) % k := by
  calc (a * c) % k = ((a % k) * (c % k)) % k := Nat.mul_mod a c k
    _ = ((b % k) * (d % k)) % k := by rw [h1, h2]
    _ = (b * d) % k := (Nat.mul_mod b d k).symm

/-- Congruence respects powers (hardened: explicit pow_succ shapes). -/
theorem mod_pow_congr (k : Nat) : ∀ (n a b : Nat), a % k = b % k →
    (a^n) % k = (b^n) % k
  | 0, a, b, _ => by simp
  | n+1, a, b, h => by
      have ih := mod_pow_congr k n a b h
      have pa : a^(n+1) = a * a^n := Nat.pow_succ a n
      have pb : b^(n+1) = b * b^n := Nat.pow_succ b n
      rw [pa, pb]
      exact mod_mul_congr k (a * a^n) (b * b^n) a b ih h

theorem cMod_eq (k : Nat) : ∀ s : Nat, cMod k s = lteCoeff s % 3^k
  | 0 => by
      simp only [cMod, lteCoeff]
  | s+1 => by
      have ih := cMod_eq k s
      simp only [cMod, lteCoeff]
      have e2 : (3^(s+1) * (lteCoeff s)^2) % 3^k
          = (3^(s+1) * (cMod k s)^2) % 3^k :=
        mod_mul_congr k _ _ _ _ rfl (mod_pow_congr k 2 _ _ ih)
      have e3 : (3^(2*s+1) * (lteCoeff s)^3) % 3^k
          = (3^(2*s+1) * (cMod k s)^3) % 3^k :=
        mod_mul_congr k _ _ _ _ rfl (mod_pow_congr k 3 _ _ ih)
      have eL : ((lteCoeff s + 3^(s+1) * (lteCoeff s)^2)
          + 3^(2*s+1) * (lteCoeff s)^3) % 3^k
          = ((cMod k s + 3^(s+1) * (cMod k s)^2)
          + 3^(2*s+1) * (cMod k s)^3) % 3^k :=
        mod_add_congr k _ _ _ _
          (mod_add_congr k _ _ _ _ rfl e2) e3
      rw [eL, ← ih]

/-- **W100** — the unit word at depth 100 (dual-verified by the assault
engine: the cMod recursion ∥ the direct modular division
`4^(3^99) mod 3^200`; `% 9 = 7`, `% 3 = 1` — the three-adic unit). -/
def W100 : Nat := 79542728300108260269642213640611567864276448732

theorem W100_receipt : cMod 100 99 = W100 := by native_decide

theorem W100_mod_three : W100 % 3 = 1 := by decide

theorem W100_lt : W100 < 3^100 := by decide

theorem lteCoeff_99_mod : lteCoeff 99 % 3^100 = W100 := by
  rw [← W100_receipt]
  exact (cMod_eq 100 99).symm

/-- The coefficient split at depth 100 (the congrArg idiom). -/
theorem coeff_split100 (u : Nat) :
    lteCoeff 99 * u
      = 3^100 * ((lteCoeff 99 / 3^100) * u) + W100 * u := by
  have hc := Nat.div_add_mod (lteCoeff 99) (3^100)
  rw [lteCoeff_99_mod] at hc
  calc lteCoeff 99 * u
      = (3^100 * (lteCoeff 99 / 3^100) + W100) * u := by
        conv_lhs => rw [hc]
    _ = 3^100 * ((lteCoeff 99 / 3^100) * u) + W100 * u := by ring

/-- **THE THREE FIXED POINTS AT DEPTH 100** — the assault engine's π
family extended from 61 to 100 trits (dual-verified: pow-inverse ∥
independent Hensel lift; the 61-trit prefixes match the S080 kernel
constants byte-for-byte; all three solve the rider sheet `π % 3 = 1`,
heads 1/4/7 respectively). -/
def pi100_fam4 : Nat := 442963202118286149036278158734808096675605174274  -- head 1
def pi100_fam7 : Nat := 284156537759188591735094506861667416397418248611  -- head 4
def pi100_fam1 : Nat := 125349873400091034433910854988526736119231322948  -- head 7

theorem pi100_fam4_lt : pi100_fam4 < 3^100 := by decide
theorem pi100_fam7_lt : pi100_fam7 < 3^100 := by decide
theorem pi100_fam1_lt : pi100_fam1 < 3^100 := by decide

theorem pi100_fam4_receipt :
    (2 * W100 * pi100_fam4 + 7) % 3^100 = 0 := by decide

theorem pi100_fam7_receipt :
    (2 * W100 * pi100_fam7 + 1) % 3^100 = 0 := by decide

theorem pi100_fam1_receipt :
    (2 * W100 * pi100_fam1 + (3^100 - 5)) % 3^100 = 0 := by decide

/-- **THE DEEP 2-TRIT RECEIPTS** — the three points are not eventually
zero through depth 100: fam4 carries 18 twos in positions 61..99, fam7
13, fam1 12 (kernel-decided witnesses at the deepest positions). -/
theorem pi100_fam4_trit99 : digit3 pi100_fam4 99 = 2 := by decide
theorem pi100_fam4_trit97 : digit3 pi100_fam4 97 = 2 := by decide
theorem pi100_fam4_trit92 : digit3 pi100_fam4 92 = 2 := by decide
theorem pi100_fam7_trit97 : digit3 pi100_fam7 97 = 2 := by decide
theorem pi100_fam7_trit96 : digit3 pi100_fam7 96 = 2 := by decide
theorem pi100_fam7_trit94 : digit3 pi100_fam7 94 = 2 := by decide
theorem pi100_fam7_trit93 : digit3 pi100_fam7 93 = 2 := by decide
theorem pi100_fam1_trit98 : digit3 pi100_fam1 98 = 2 := by decide
theorem pi100_fam1_trit95 : digit3 pi100_fam1 95 = 2 := by decide
theorem pi100_fam1_trit91 : digit3 pi100_fam1 91 = 2 := by decide

/-- **THE PIN ENGINE AT DEPTH 100.**  If both a core `u` and a fixed
point `π < 3^100` solve the same W-form congruence, then
`u ≡ π [MOD 3^100]`. -/
theorem pin100_of_W_congruence (u π D : Nat)
    (hu : 3^100 ∣ 2 * W100 * u + D)
    (hπ : 3^100 ∣ 2 * W100 * π + D)
    (hπlt : π < 3^100) :
    u % 3^100 = π := by
  have hunit : ¬ (3:Nat) ∣ 2 * W100 := by
    intro hd
    have h0 : (2 * W100) % 3 = 0 := Nat.dvd_iff_mod_eq_zero.mp hd
    rw [Nat.mul_mod, W100_mod_three] at h0
    norm_num at h0
  by_cases hle : π ≤ u
  · have hE : (2 * W100 * u + D) - (2 * W100 * π + D)
        = 2 * W100 * (u - π) := by
      rw [Nat.mul_sub]
      omega
    have hsub : 3^100 ∣ 2 * W100 * (u - π) := by
      obtain ⟨b, hb⟩ := hu
      obtain ⟨a, ha⟩ := hπ
      refine ⟨b - a, ?_⟩
      rw [Nat.mul_sub, Nat.mul_sub]
      omega
    have hcancel := dvd_of_unit_mul_cancel 100 (2 * W100) (u - π) hunit hsub
    obtain ⟨t, ht⟩ := hcancel
    have huπ : u = π + 3^100 * t := by omega
    rw [huπ, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hπlt]
  · have hgt : u < π := by omega
    have hE : (2 * W100 * π + D) - (2 * W100 * u + D)
        = 2 * W100 * (π - u) := by
      rw [Nat.mul_sub]
      omega
    have hsub : 3^100 ∣ 2 * W100 * (π - u) := by
      obtain ⟨a, ha⟩ := hu
      obtain ⟨b, hb⟩ := hπ
      refine ⟨a - b, ?_⟩
      rw [Nat.mul_sub, Nat.mul_sub]
      omega
    have hcancel := dvd_of_unit_mul_cancel 100 (2 * W100) (π - u) hunit hsub
    obtain ⟨t, ht⟩ := hcancel
    have hπu : π = u + 3^100 * t := by omega
    have hmod : u % 3^100 = π % 3^100 := by
      rw [hπu, Nat.add_mul_mod_self_left]
    rw [hmod, Nat.mod_eq_of_lt hπlt]

/-- The ghost-to-W congruence at depth 100, family four (head one). -/
theorem ghost_W100_congruence_fam4 (u : Nat) (hg : GhostRay u)
    (hhead : ghostHead u = 1) :
    3^100 ∣ 2 * W100 * u + 7 := by
  obtain ⟨m, hm⟩ := ghost_congruence u hg 100 (by omega)
  rw [hhead] at hm
  rw [coeff_split100 u] at hm
  have hring : 3^100 * (2 * ((lteCoeff 99 / 3^100) * u))
      = 2 * (3^100 * ((lteCoeff 99 / 3^100) * u)) := by ring
  refine ⟨m - 2 * ((lteCoeff 99 / 3^100) * u), ?_⟩
  rw [Nat.mul_sub, hring]
  omega

/-- The ghost-to-W congruence at depth 100, family seven (head four). -/
theorem ghost_W100_congruence_fam7 (u : Nat) (hg : GhostRay u)
    (hhead : ghostHead u = 4) :
    3^100 ∣ 2 * W100 * u + 1 := by
  obtain ⟨m, hm⟩ := ghost_congruence u hg 100 (by omega)
  rw [hhead] at hm
  rw [coeff_split100 u] at hm
  have hring : 3^100 * (2 * ((lteCoeff 99 / 3^100) * u))
      = 2 * (3^100 * ((lteCoeff 99 / 3^100) * u)) := by ring
  refine ⟨m - 2 * ((lteCoeff 99 / 3^100) * u), ?_⟩
  rw [Nat.mul_sub, hring]
  omega

/-- The ghost-to-W congruence at depth 100, family one (head seven). -/
theorem ghost_W100_congruence_fam1 (u : Nat) (hg : GhostRay u)
    (hhead : ghostHead u = 7) :
    3^100 ∣ 2 * W100 * u + (3^100 - 5) := by
  obtain ⟨m, hm⟩ := ghost_congruence u hg 100 (by omega)
  rw [hhead] at hm
  rw [coeff_split100 u] at hm
  have hring : 3^100 * (2 * ((lteCoeff 99 / 3^100) * u))
      = 2 * (3^100 * ((lteCoeff 99 / 3^100) * u)) := by ring
  refine ⟨m + 1 - 2 * ((lteCoeff 99 / 3^100) * u), ?_⟩
  have hdistrib : 3^100 * (m + 1 - 2 * ((lteCoeff 99 / 3^100) * u))
      = 3^100 * m + 3^100 * 1 - 3^100 * (2 * ((lteCoeff 99 / 3^100) * u)) := by
    rw [Nat.mul_sub, Nat.mul_add, Nat.mul_one]
  rw [hdistrib, hring, Nat.mul_one]
  omega

/-- **THE PIN AT DEPTH 100, FAMILY FOUR.** -/
theorem every_ghost_is_its_pi100_point_fam4 (u : Nat) (hg : GhostRay u)
    (hhead : ghostHead u = 1) : u % 3^100 = pi100_fam4 :=
  pin100_of_W_congruence u pi100_fam4 7
    (ghost_W100_congruence_fam4 u hg hhead)
    (Nat.dvd_of_mod_eq_zero pi100_fam4_receipt) pi100_fam4_lt

/-- **THE PIN AT DEPTH 100, FAMILY SEVEN.** -/
theorem every_ghost_is_its_pi100_point_fam7 (u : Nat) (hg : GhostRay u)
    (hhead : ghostHead u = 4) : u % 3^100 = pi100_fam7 :=
  pin100_of_W_congruence u pi100_fam7 1
    (ghost_W100_congruence_fam7 u hg hhead)
    (Nat.dvd_of_mod_eq_zero pi100_fam7_receipt) pi100_fam7_lt

/-- **THE PIN AT DEPTH 100, FAMILY ONE.** -/
theorem every_ghost_is_its_pi100_point_fam1 (u : Nat) (hg : GhostRay u)
    (hhead : ghostHead u = 7) : u % 3^100 = pi100_fam1 :=
  pin100_of_W_congruence u pi100_fam1 (3^100 - 5)
    (ghost_W100_congruence_fam1 u hg hhead)
    (Nat.dvd_of_mod_eq_zero pi100_fam1_receipt) pi100_fam1_lt

/-! ## §7 THE SIZE LAW — every ghost on the rider sheet is astronomical -/
#print axioms GhostExtinction406.every_ghost_is_its_pi100_point_fam1  -- CK75 SECTION BOUNDARY

theorem pi100_fam4_gt : 3^99 < pi100_fam4 := by decide
theorem pi100_fam7_gt : 3^99 < pi100_fam7 := by decide
theorem pi100_fam1_gt : 3^98 < pi100_fam1 := by decide

/-- **THE SIZE LAW, FAMILY FOUR (NEW).**  Every ghost ray with head one
exceeds `3^99`. -/
theorem ghost_size_fam4 (u : Nat) (hg : GhostRay u)
    (hhead : ghostHead u = 1) : 3^99 < u := by
  have hpin := every_ghost_is_its_pi100_point_fam4 u hg hhead
  have hdm := Nat.div_add_mod u (3^100)
  have hgt := pi100_fam4_gt
  omega

/-- **THE SIZE LAW, FAMILY SEVEN (NEW).**  Every ghost ray with head
four exceeds `3^99`. -/
theorem ghost_size_fam7 (u : Nat) (hg : GhostRay u)
    (hhead : ghostHead u = 4) : 3^99 < u := by
  have hpin := every_ghost_is_its_pi100_point_fam7 u hg hhead
  have hdm := Nat.div_add_mod u (3^100)
  have hgt := pi100_fam7_gt
  omega

/-- **THE SIZE LAW, FAMILY ONE (NEW).**  Every ghost ray with head seven
exceeds `3^98`. -/
theorem ghost_size_fam1 (u : Nat) (hg : GhostRay u)
    (hhead : ghostHead u = 7) : 3^98 < u := by
  have hpin := every_ghost_is_its_pi100_point_fam1 u hg hhead
  have hdm := Nat.div_add_mod u (3^100)
  have hgt := pi100_fam1_gt
  omega

/-- **THE UNIFORM SIZE LAW (NEW).**  Every ghost ray on the rider sheet
(`u ≡ 1 mod 3`) exceeds `3^98`. -/
theorem ghost_size_rider_sheet (u : Nat) (hg : GhostRay u)
    (hu3 : u % 3 = 1) : 3^98 < u := by
  rcases ghost_head_split u hg hu3 with h | h | h
  · have h4 := ghost_size_fam4 u hg h
    have hle : 3^98 ≤ 3^99 := three_pow_le_of_le 98 99 (by omega)
    omega
  · have h7 := ghost_size_fam7 u hg h
    have hle : 3^98 ≤ 3^99 := three_pow_le_of_le 98 99 (by omega)
    omega
  · exact ghost_size_fam1 u hg h

/-! ## §8 The finite base — every exponent 8..500 fires -/

/-- The digit-two scan: `hasTwoScan n B = true` iff some ternary digit
of `n` at a position `< B` equals two. -/
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
      · intro h; exact absurd h (by decide)
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
          rfl
      · have hbeq : (n % 3 == 2) = false := by
          cases hbb : (n % 3 == 2) with
          | true => exact absurd (Nat.eq_of_beq_eq_true hbb) hb
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

/-- **THE FINITE BASE.**  Every exponent `8 ≤ K ≤ 500` owns a ternary
digit two: the kernel-decided census, both chunks, the full scan. -/
theorem cantorian_base (K : Nat) (hK8 : 8 ≤ K) (hK500 : K ≤ 500) :
    ∃ p : Nat, digit3 (4^K) p = 2 := by
  rcases Nat.lt_or_ge K (8 + 251) with hlt | hge
  · have hc := (List.all_eq_true.mp base_chunk_one) (K - 8)
      (List.mem_range.mpr (by omega))
    exact (hasTwoScan_iff 632 _).mp hc
  · have hc := (List.all_eq_true.mp base_chunk_two) (K - 8 - 251)
      (List.mem_range.mpr (by omega))
    have hsplit : 4^(8 + (251 + (K - 8 - 251))) = 4^K := by
      congr 1
      omega
    rw [hsplit] at hc
    exact (hasTwoScan_iff 632 _).mp hc

/-! ## §9 THE CROWN V2 — one-and-a-half grants -/
#print axioms GhostExtinction406.cantorian_base  -- CK75 SECTION BOUNDARY

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

/-- A ternary digit two at any position certifies the Arsenal's
has-reader. -/
theorem hasTwo_of_digit : ∀ (n p : Nat), digit3 n p = 2 →
    hasTernaryTwo n = true := by
  intro n p
  induction p generalizing n with
  | zero =>
      intro h
      have h0 : digit3 n 0 = n % 3 := by
        unfold digit3
        rw [Nat.pow_zero, Nat.div_one]
      rw [h0] at h
      have hn0 : n ≠ 0 := by
        intro hne
        rw [hne, Nat.zero_mod] at h
        exact absurd h (by decide)
      rw [hasTernaryTwo.eq_def n, if_neg hn0, if_pos h]
  | succ p ih =>
      intro h
      have hsh : digit3 n (p+1) = digit3 (n / 3) p := by
        unfold digit3
        rw [Nat.pow_succ, Nat.div_div_eq_div_mul, Nat.mul_comm (3^p) (3:Nat)]
      rw [hsh] at h
      have hne : n ≠ 0 := by
        intro h0
        rw [h0, Nat.zero_div] at h
        unfold digit3 at h
        rw [Nat.zero_div, Nat.zero_mod] at h
        exact absurd h (by decide)
      rw [hasTernaryTwo.eq_def n, if_neg hne]
      by_cases h2 : n % 3 = 2
      · rw [if_pos h2]
      · rw [if_neg h2]
        exact ih _ h

/-- **THE CROWN V2 (NEW).**  The FULL Erdős #406 statement —
`∀ n ≥ 9, noTernaryTwo (2^n) = false` — follows from the WEAKENED
grant pair:
* (G1') **ghost extinction on the rider sheet only**: no `u ≡ 1 mod 3`
  is a ghost ray (the `u ≡ 2` sheet is irrelevant — by the rider's
  core law, riders ride only the `u ≡ 1` sheet);
* (G2) **residual ghost compression** (unchanged).
Everything else is unconditional and machine-checked here. -/
theorem erdos406_crown_v2
    (hNoGhostOne : ∀ u : Nat, u % 3 = 1 → ¬ GhostRay u)
    (hComp : ∀ (K σ u : Nat), 500 < K → K = 3^σ * u → ¬ (3:Nat) ∣ u →
      CantorianPower K → GhostRay u) :
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
      exact hNoGhostOne u hu1 (hComp K σ u (by omega) hKu hufree hCant)
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

/-- **THE COMPOSED WALL (NEW).**  Under the single grant (G2), every
Cantorian power above 500 exceeds `3^98` — the remaining content of
Erdős #406 is at most THREE astronomically large exponents, one per
π-family (at most one each, by the uniqueness collapse). -/
theorem rider_wall_v2
    (hComp : ∀ (K σ u : Nat), 500 < K → K = 3^σ * u → ¬ (3:Nat) ∣ u →
      CantorianPower K → GhostRay u)
    (K : Nat) (hK : 500 < K) (hCant : CantorianPower K) :
    3^98 < K := by
  obtain ⟨σ, u, hKu, hufree, hu1⟩ := rider_core_one K (by omega) hCant
  have hghost := hComp K σ u hK hKu hufree hCant
  have hsize := ghost_size_rider_sheet u hghost hu1
  have hmul : u ≤ 3^σ * u := by
    have hle : u ≤ u * 3^σ := Nat.le_mul_of_pos_right u (Nat.pow_pos (by decide))
    rw [Nat.mul_comm] at hle
    exact hle
  omega

/-! ## §10 Receipts -/

#check GhostExtinction406.rider_core_one
#check GhostExtinction406.ghost_head_split
#check GhostExtinction406.ghost_uniqueness
#check GhostExtinction406.W100_receipt
#check GhostExtinction406.pi100_fam4_receipt
#check GhostExtinction406.pi100_fam7_receipt
#check GhostExtinction406.pi100_fam1_receipt
#check GhostExtinction406.every_ghost_is_its_pi100_point_fam4
#check GhostExtinction406.every_ghost_is_its_pi100_point_fam7
#check GhostExtinction406.every_ghost_is_its_pi100_point_fam1
#check GhostExtinction406.ghost_size_rider_sheet
#check GhostExtinction406.cantorian_base
#check GhostExtinction406.erdos406_crown_v2
#check GhostExtinction406.rider_wall_v2

#print axioms GhostExtinction406.rider_core_one
#print axioms GhostExtinction406.ghost_head_split
#print axioms GhostExtinction406.ghost_uniqueness
#print axioms GhostExtinction406.W100_receipt
#print axioms GhostExtinction406.pi100_fam4_receipt
#print axioms GhostExtinction406.pi100_fam7_receipt
#print axioms GhostExtinction406.pi100_fam1_receipt
#print axioms GhostExtinction406.pi100_fam4_trit99
#print axioms GhostExtinction406.pi100_fam7_trit97
#print axioms GhostExtinction406.pi100_fam1_trit98
#print axioms GhostExtinction406.every_ghost_is_its_pi100_point_fam4
#print axioms GhostExtinction406.every_ghost_is_its_pi100_point_fam7
#print axioms GhostExtinction406.every_ghost_is_its_pi100_point_fam1
#print axioms GhostExtinction406.ghost_size_fam4
#print axioms GhostExtinction406.ghost_size_fam7
#print axioms GhostExtinction406.ghost_size_fam1
#print axioms GhostExtinction406.ghost_size_rider_sheet
#print axioms GhostExtinction406.cantorian_base
#print axioms GhostExtinction406.erdos406_crown_v2
#print axioms GhostExtinction406.rider_wall_v2

#eval "ERDOS406_GHOSTEXTINCTION_KERNEL_GREEN"

end GhostExtinction406
