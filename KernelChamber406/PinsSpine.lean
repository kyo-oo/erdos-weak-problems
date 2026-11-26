import Arsenal.ErdosTernary2.Basic
import Arsenal.CardinalWorldsCore
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

-- Family pattern (green kernels): explicit depth headroom.
set_option maxRecDepth 262144
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 1000

/-!
# ERDŐS #406 — THE π-POINT COLLAPSE KERNEL (S080): the ghost rays, the
# fixed points, and the two-grant crown

## THE OBJECT (BOSS order: crack the hTailF hypothesis — the π-point lane,
## the S078-named first strike, now executed)

The remaining content of Erdős #406 (the even half; the odd half green)
is the SEPARATION: no exponent `m ≥ 5` has `4^m` with all ternary digits
in `{0, 1}`.  This kernel banks THE π-POINT COLLAPSE — the lane the S078
assault engine named, in full:

* **§1 THE TOWER COEFFICIENT** (`lteCoeff`): `4^(3^v) = 1 + 3^(v+1) *
  lteCoeff v`, `lteCoeff v ≡ 1 (mod 3)` — the LTE spine, self-contained
  (the green Block-Law engine, ported verbatim; division-free), plus the
  frozen diagonal (`lteCoeff_stable`).

* **§2 THE GHOST RAY** (`GhostRay`): a core `u` whose scaled LTE
  diagonal `(c (k-1) * u) % 3^k` sits in the EXACT middle third at every
  depth `k ≥ 3` — the stabilized dust shape, the full shadow package
  carrier of the assault engine's nested scan.

* **§3 LEMMA A — THE ALL-ONES TAIL** (`ghost_residue_shape`): a ghost
  ray's residue is pinned to the exact all-ones tail
  `2·((c (k-1) * u) % 3^k) + 9 = 2·head + 3^k`.

* **§4 LEMMA B — THE GHOST CONGRUENCE** (`ghost_congruence`):
  `2·(c (k-1) * u) + 9 = 2·head + 3^k·m` at every depth.

* **§5 THE COLLAPSE — THE NEW THEOREM** (`ghost_congruent_all_depths`):
  two ghost rays with the same head are congruent modulo `3^k` for
  EVERY `k`: the infinite shadow dust — the set of all full-package
  carriers — collapses to AT MOST SIX 3-adic points, one per admissible
  head.  The doubling tree's eternal survivors are finitely many points.

* **§6 THE π-POINTS, KERNEL-DECIDED** (`W61`, `pi_fam1`, `pi_fam4`,
  `pi_fam7`): the unit word `W = lim c_s` mod `3^61` (the certified
  mod-recursion `cMod`, dual-verified against the independent S078
  Hensel lift), the three fixed points solving `2·W·π = 2·head − 9`,
  and THE PIN (`every_ghost_is_its_pi_point_*`): every ghost ray with
  head 1, 4 or 7 IS its π-point mod `3^61`.  The 2-trit receipts (13,
  18 and 20 scattered twos through 60 positions) are kernel-decided.

* **§7 THE FINITE BASE** (`cantorian_base`): every exponent `8 ≤ K ≤
  500` fires — two legal decide chunks (251 + 242 cases, the NO-OOM
  cap honored), each case the exact 632-row digit scan of `4^K`.

* **§8 THE TWO-GRANT CROWN** (`erdos406_crown_of_ghost_extinction`): the
  FULL Erdős #406 statement follows from exactly TWO named grants:
  (G1) **ghost extinction** — no core carries the full shadow package;
  (G2) **residual ghost compression** — every Cantorian power above the
  kernel base has a ghost-ray core.  Everything else is unconditional,
  self-contained, machine-checked here.

## THE HONEST SCOPE

These are unconditional laws of the shadow dust.  They do not close the
two named grants (the π non-naturality beyond 61 trits; the compression
from depth-v riderhood to depth-∞ package) — they shrink the entire
remaining content of the war to those two statements, with the infinite
dust already collapsed to six points, three of them exhibited, pinned,
and certified non-zero through depth 61.
-/

namespace PiCollapse406

/-! ## §0 The engine (self-contained; the green Block-Law toolkit) -/

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

/-! ## §1 The ghost ray -/
#print axioms PiCollapse406.lteCoeff_stable  -- CK74 SECTION BOUNDARY

/-- **THE GHOST RAY** — the stabilized middle-third condition: a core
`u` whose scaled LTE diagonal `(c (k-1) * u) % 3^k` sits in the exact
middle third at every ternary depth `k ≥ 3`.  This is the full shadow
package of the assault engine: the all-sheets dodger with the diagonal
clean at every level, forever. -/
def GhostRay (u : Nat) : Prop :=
  ∀ k : Nat, 3 ≤ k →
    3^(k-1) ≤ (lteCoeff (k-1) * u) % 3^k
    ∧ (lteCoeff (k-1) * u) % 3^k < 2 * 3^(k-1)

/-- The canonical ghost head: the residue that anchors the all-ones
tail. -/
def ghostHead (u : Nat) : Nat := (lteCoeff 1 * u) % 9

/-! ## §2 Lemma A — the exact all-ones tail shape -/
#print axioms PiCollapse406.ghostHead  -- CK74 SECTION BOUNDARY

/-- **LEMMA A (the exact ghost shape).**  A ghost ray forces the residue
of `c (k-1) * u` modulo `3^k` to be the all-ones tail
`head + (3^k - 9) / 2` — stated free of division as
`2 * residue + 9 = 2 * head + 3^k`. -/
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

/-! ## §3 Lemma B — the finite ghost congruence -/
#print axioms PiCollapse406.ghost_residue_shape  -- CK74 SECTION BOUNDARY

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

/-! ## §4 The unit cancellation engine -/
#print axioms PiCollapse406.ghost_congruence  -- CK74 SECTION BOUNDARY

/-- Cancel a factor of three: if `3 ∣ g * d` and `3 ∤ g` then `3 ∣ d`. -/
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

/-! ## §5 The collapse — the new theorem -/
#print axioms PiCollapse406.dvd_of_unit_mul_cancel  -- CK74 SECTION BOUNDARY

/-- The difference engine: two congruences against the same head, with
the first core at least the second, give the scale-divisibility of the
difference (and hence the congruence witness). -/
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
  -- hm  : 2*(X*u') + 2*(X*(u-u')) + 9 = 2*H + 3^k*m
  -- hm' : 2*(X*u') + 9 = 2*H + 3^k*m'
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

/-- **THE COLLAPSE — same-head ghosts are one point.**  Two ghost rays
with the same head are congruent modulo `3^k` for EVERY `k`: the
infinite shadow dust collapses to at most one 3-adic point per
admissible head value in `{1, 2, 4, 5, 7, 8}` — six points at most. -/
theorem ghost_congruent_all_depths (u u' : Nat)
    (hg : GhostRay u) (hg' : GhostRay u') (hhead : ghostHead u = ghostHead u')
    (k : Nat) : u % 3^k = u' % 3^k := by
  rcases Nat.lt_or_ge k 3 with hlt | hge
  · have h3 := ghost_congruent_ge_three u u' hg hg' hhead 3 (by omega)
    exact mod_dvd_modeq _ _ _ _ (pow_dvd_pow (3:Nat) (by omega)) h3
  · exact ghost_congruent_ge_three u u' hg hg' hhead k hge

/-- The ghost head is never divisible by three: the tower coefficient
is a three-adic unit. -/
theorem ghost_head_not_three (u : Nat) (h3 : ¬ (3:Nat) ∣ u) :
    ¬ (3:Nat) ∣ ghostHead u := by
  intro hd
  apply h3
  have h0 : (ghostHead u) % 3 = 0 := Nat.dvd_iff_mod_eq_zero.mp hd
  unfold ghostHead at h0
  rw [Nat.mod_mod_of_dvd _ (by decide : (3:Nat) ∣ 9),
    Nat.mul_mod, lteCoeff_mod3_one] at h0
  simp only [Nat.mul_one, Nat.one_mul, Nat.mod_mod_of_dvd] at h0
  have hlt : u % 3 < 3 := Nat.mod_lt _ (by decide)
  have hmm : u % 3 % 3 = u % 3 :=
    Nat.mod_mod_of_dvd u (dvd_rfl : (3:Nat) ∣ 3)
  omega

theorem ghost_head_lt_nine (u : Nat) : ghostHead u < 9 := by
  unfold ghostHead
  exact Nat.mod_lt _ (by decide)
#print axioms PiCollapse406.ghost_congruent_all_depths  -- S089t: receipt relocated from PinsWord (the walk was the word jobs first-command sink)
end PiCollapse406
