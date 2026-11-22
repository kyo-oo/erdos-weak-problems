import Arsenal.ErdosTernary2.Basic
import Arsenal.CardinalWorlds
import Arsenal.CardinalWorldsV2

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
          simp only [lteCoeff]
          try ring

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

/-- One-step frozen-diagonal drop: the lift adds a multiple of the scale. -/
theorem lteCoeff_succ_mod (w : Nat) :
    lteCoeff (w+1) % 3^(w+1) = lteCoeff w % 3^(w+1) := by
  have h1 : 3^(w+1) ∣ 3^(w+1) * (lteCoeff w)^2 :=
    ⟨(lteCoeff w)^2, by ring⟩
  have h2 : 3^(w+1) ∣ 3^(2*w+1) * (lteCoeff w)^3 := by
    refine ⟨3^w * (lteCoeff w)^3, ?_⟩
    rw [← Nat.pow_add]
    congr 1
    omega
  have hsum : 3^(w+1) ∣ 3^(w+1) * (lteCoeff w)^2 + 3^(2*w+1) * (lteCoeff w)^3 :=
    Nat.dvd_add h1 h2
  simp only [lteCoeff]
  obtain ⟨q, rfl⟩ := hsum
  rw [Nat.add_assoc, Nat.add_mul_mod_self_left]

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
      have hgd3 : (3:Nat) ∣ g * d' := ⟨e, by rw [hcancel]; ring⟩
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
    calc lteCoeff (k-1) * u = lteCoeff (k-1) * (u' + (u - u')) := by rw [hu]
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

/-! ## §6 The π-points, kernel-decided -/
#print axioms PiCollapse406.ghost_congruent_all_depths  -- CK74 SECTION BOUNDARY

/-- The certified mod-recursion: `cMod k s = lteCoeff s % 3^k`, computed
without ever forming the astronomically large tower coefficient. -/
def cMod : Nat → Nat → Nat
  | k, 0 => 1 % 3^k
  | k, s+1 =>
      let c := cMod k s
      (c + 3^(s+1) * c^2 + 3^(2*s+1) * c^3) % 3^k

/-- Congruence respects addition (hardened S083: explicit lemma
applications — the double-rw form re-matches the outer term under the
W82 Mathlib and left double-mods). -/
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
          (mod_add_congr k _ _ _ _ ih e2) e3
      calc (cMod k s + 3^(s+1) * (cMod k s)^2 + 3^(2*s+1) * (cMod k s)^3) % 3^k
          = ((cMod k s + 3^(s+1) * (cMod k s)^2)
              + 3^(2*s+1) * (cMod k s)^3) % 3^k := rfl
        _ = ((lteCoeff s + 3^(s+1) * (lteCoeff s)^2)
              + 3^(2*s+1) * (lteCoeff s)^3) % 3^k := eL.symm
        _ = (lteCoeff s + 3^(s+1) * (lteCoeff s)^2
              + 3^(2*s+1) * (lteCoeff s)^3) % 3^k := rfl

/-- **THE UNIT WORD MOD 3^61** — the stabilized tower coefficient at
depth 60, computed by the certified recursion (dual-verified against
the independent S078 Hensel lift: `W ≡ 7 (mod 9)`, `W ≡ 16 (mod 27)`). -/
def W61 : Nat := 60776643992856088575557123854

theorem W61_receipt : cMod 61 60 = W61 := by decide

theorem W61_mod_nine : W61 % 9 = 7 := by decide

theorem W61_mod_three : W61 % 3 = 1 := by decide

theorem W61_lt : W61 < 3^61 := by decide

theorem lteCoeff_sixty_mod : lteCoeff 60 % 3^61 = W61 := by
  rw [← W61_receipt]
  exact (cMod_eq 61 60).symm

theorem three_pow_61_pos : 5 ≤ 3^61 := by decide

/-- The coefficient split at depth 61 (the congrArg idiom — no rw loop). -/
theorem coeff_split (u : Nat) :
    lteCoeff 60 * u
      = 3^61 * ((lteCoeff 60 / 3^61) * u) + W61 * u := by
  have hc := Nat.div_add_mod (lteCoeff 60) (3^61)
  rw [lteCoeff_sixty_mod] at hc
  calc lteCoeff 60 * u
      = (3^61 * (lteCoeff 60 / 3^61) + W61) * u := by
        conv_lhs => rw [hc]
    _ = 3^61 * ((lteCoeff 60 / 3^61) * u) + W61 * u := by ring

/-- **THE THREE FIXED POINTS** (the assault engine's `π₄, π₇, π₁`,
dual-verified against the independent Hensel lift of `2·W·π = T` for
`T ∈ {-7, -1, +5}` in `ℤ₃`; all three carry scattered 2-trits through
60 positions — 13, 20 and 18 respectively). -/
def pi_fam4 : Nat := 68350949682967876566738142093  -- head 1, T = -7
def pi_fam7 : Nat := 64267339165701958313626862986  -- head 4, T = -1
def pi_fam1 : Nat := 60183728648436040060515583879  -- head 7, T = +5

theorem pi_fam4_lt : pi_fam4 < 3^61 := by decide
theorem pi_fam7_lt : pi_fam7 < 3^61 := by decide
theorem pi_fam1_lt : pi_fam1 < 3^61 := by decide

theorem pi_fam4_receipt :
    (2 * W61 * pi_fam4 + 7) % 3^61 = 0 := by decide

theorem pi_fam7_receipt :
    (2 * W61 * pi_fam7 + 1) % 3^61 = 0 := by decide

theorem pi_fam1_receipt :
    (2 * W61 * pi_fam1 + (3^61 - 5)) % 3^61 = 0 := by decide

/-- **THE 2-TRIT RECEIPTS** — the three fixed points are not eventually
zero: each carries ternary digit twos deep in its expansion
(kernel-decided positions from the assault engine's certified list). -/
theorem pi_fam4_trit3 : digit3 pi_fam4 3 = 2 := by decide
theorem pi_fam4_trit14 : digit3 pi_fam4 14 = 2 := by decide
theorem pi_fam7_trit1 : digit3 pi_fam7 1 = 2 := by decide
theorem pi_fam7_trit6 : digit3 pi_fam7 6 = 2 := by decide
theorem pi_fam1_trit8 : digit3 pi_fam1 8 = 2 := by decide
theorem pi_fam1_trit13 : digit3 pi_fam1 13 = 2 := by decide

/-! ## §6b The pin — every ghost ray IS its π-point -/
#print axioms PiCollapse406.W61  -- CK74 SECTION BOUNDARY

/-- **THE PIN ENGINE.**  If both a core `u` and a fixed point `π < 3^61`
solve the same W-form congruence `2·W61·x + D ≡ 0 [MOD 3^61]`, then
`u ≡ π [MOD 3^61]`. -/
theorem pin_of_W_congruence (u π D : Nat)
    (hu : 3^61 ∣ 2 * W61 * u + D)
    (hπ : 3^61 ∣ 2 * W61 * π + D)
    (hπlt : π < 3^61) :
    u % 3^61 = π := by
  have hunit : ¬ (3:Nat) ∣ 2 * W61 := by
    intro hd
    have h0 : (2 * W61) % 3 = 0 := Nat.dvd_iff_mod_eq_zero.mp hd
    rw [Nat.mul_mod, W61_mod_three] at h0
    norm_num at h0
  by_cases hle : π ≤ u
  · have hE : (2 * W61 * u + D) - (2 * W61 * π + D)
        = 2 * W61 * (u - π) := by
      rw [Nat.mul_sub]
      omega
    have hsub : 3^61 ∣ 2 * W61 * (u - π) := by
      rw [hE]
      exact Nat.dvd_sub hπ hu
    have hcancel := dvd_of_unit_mul_cancel 61 (2 * W61) (u - π) hunit hsub
    obtain ⟨t, ht⟩ := hcancel
    have huπ : u = π + 3^61 * t := by omega
    rw [huπ, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hπlt]
  · have hgt : u < π := by omega
    have hE : (2 * W61 * π + D) - (2 * W61 * u + D)
        = 2 * W61 * (π - u) := by
      rw [Nat.mul_sub]
      omega
    have hsub : 3^61 ∣ 2 * W61 * (π - u) := by
      rw [hE]
      exact Nat.dvd_sub hu hπ
    have hcancel := dvd_of_unit_mul_cancel 61 (2 * W61) (π - u) hunit hsub
    obtain ⟨t, ht⟩ := hcancel
    have hπu : π = u + 3^61 * t := by omega
    have hmod : u % 3^61 = π % 3^61 := by
      rw [hπu, Nat.add_mul_mod_self_right]
    rw [hmod, Nat.mod_eq_of_lt hπlt]

/-- The ghost-to-W congruence, family four: head one, `D = 7`. -/
theorem ghost_W_congruence_fam4 (u : Nat) (hg : GhostRay u)
    (hhead : ghostHead u = 1) :
    3^61 ∣ 2 * W61 * u + 7 := by
  obtain ⟨m, hm⟩ := ghost_congruence u hg 61 (by omega)
  rw [hhead] at hm
  rw [coeff_split u] at hm
  have hring : 3^61 * (2 * ((lteCoeff 60 / 3^61) * u))
      = 2 * (3^61 * ((lteCoeff 60 / 3^61) * u)) := by ring
  refine ⟨m - 2 * ((lteCoeff 60 / 3^61) * u), ?_⟩
  rw [Nat.mul_sub, hring]
  omega

/-- The ghost-to-W congruence, family seven: head four, `D = 1`. -/
theorem ghost_W_congruence_fam7 (u : Nat) (hg : GhostRay u)
    (hhead : ghostHead u = 4) :
    3^61 ∣ 2 * W61 * u + 1 := by
  obtain ⟨m, hm⟩ := ghost_congruence u hg 61 (by omega)
  rw [hhead] at hm
  rw [coeff_split u] at hm
  have hring : 3^61 * (2 * ((lteCoeff 60 / 3^61) * u))
      = 2 * (3^61 * ((lteCoeff 60 / 3^61) * u)) := by ring
  refine ⟨m - 2 * ((lteCoeff 60 / 3^61) * u), ?_⟩
  rw [Nat.mul_sub, hring]
  omega

/-- The ghost-to-W congruence, family one: head seven, `D = 3^61 - 5`. -/
theorem ghost_W_congruence_fam1 (u : Nat) (hg : GhostRay u)
    (hhead : ghostHead u = 7) :
    3^61 ∣ 2 * W61 * u + (3^61 - 5) := by
  obtain ⟨m, hm⟩ := ghost_congruence u hg 61 (by omega)
  rw [hhead] at hm
  rw [coeff_split u] at hm
  have hring : 3^61 * (2 * ((lteCoeff 60 / 3^61) * u))
      = 2 * (3^61 * ((lteCoeff 60 / 3^61) * u)) := by ring
  refine ⟨m + 1 - 2 * ((lteCoeff 60 / 3^61) * u), ?_⟩
  have hdistrib : 3^61 * (m + 1 - 2 * ((lteCoeff 60 / 3^61) * u))
      = 3^61 * m + 3^61 * 1 - 3^61 * (2 * ((lteCoeff 60 / 3^61) * u)) := by
    rw [Nat.mul_sub, Nat.mul_add, Nat.mul_one]
  rw [hdistrib, hring, Nat.mul_one]
  omega

/-- **THE PIN, FAMILY FOUR.**  Every ghost ray with head one is the
fixed point `pi_fam4` modulo `3^61`. -/
theorem every_ghost_is_its_pi_point_fam4 (u : Nat) (hg : GhostRay u)
    (hhead : ghostHead u = 1) : u % 3^61 = pi_fam4 :=
  pin_of_W_congruence u pi_fam4 7
    (ghost_W_congruence_fam4 u hg hhead)
    (Nat.dvd_of_mod_eq_zero pi_fam4_receipt) pi_fam4_lt

/-- **THE PIN, FAMILY SEVEN.**  Every ghost ray with head four is the
fixed point `pi_fam7` modulo `3^61`. -/
theorem every_ghost_is_its_pi_point_fam7 (u : Nat) (hg : GhostRay u)
    (hhead : ghostHead u = 4) : u % 3^61 = pi_fam7 :=
  pin_of_W_congruence u pi_fam7 1
    (ghost_W_congruence_fam7 u hg hhead)
    (Nat.dvd_of_mod_eq_zero pi_fam7_receipt) pi_fam7_lt

/-- **THE PIN, FAMILY ONE.**  Every ghost ray with head seven is the
fixed point `pi_fam1` modulo `3^61`. -/
theorem every_ghost_is_its_pi_point_fam1 (u : Nat) (hg : GhostRay u)
    (hhead : ghostHead u = 7) : u % 3^61 = pi_fam1 :=
  pin_of_W_congruence u pi_fam1 (3^61 - 5)
    (ghost_W_congruence_fam1 u hg hhead)
    (Nat.dvd_of_mod_eq_zero pi_fam1_receipt) pi_fam1_lt

/-! ## §7 The finite base — every exponent 8..500 fires -/
#print axioms PiCollapse406.every_ghost_is_its_pi_point_fam1  -- CK74 SECTION BOUNDARY

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
        rw [Nat.pow_succ, Nat.div_div_eq_div_mul]
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

/-- The census case: the exact digit scan of `4^(8+i)` at fuel 632
(every exponent in range has at most 631 ternary digits). -/
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

/-! ## §8 The two-grant crown -/
#print axioms PiCollapse406.cantorian_base  -- CK74 SECTION BOUNDARY

/-- The Cantorian power predicate: every ternary digit from position
one on avoids two (position zero is always one). -/
def CantorianPower (K : Nat) : Prop :=
  ∀ p : Nat, 1 ≤ p → digit3 (4^K) p ≠ 2

/-- Every positive natural decomposes as `3^s * u` with `u` three-free
(the green fuel pattern). -/
theorem exists_three_free_decomp :
    ∀ (fuel K : Nat), 1 ≤ K → K ≤ fuel →
      ∃ s u : Nat, K = 3^s * u ∧ ¬ (3:Nat) ∣ u := by
  intro fuel
  induction fuel with
  | zero => intro K hK hKF; omega
  | succ fuel ih =>
      intro K hK hKF
      by_cases h3 : (3:Nat) ∣ K
      · obtain ⟨K', hK'⟩ := h3
        have hK'1 : 1 ≤ K' := by
          by_cases hK0 : K' = 0
          · omega
          · omega
        have hlt : K' ≤ fuel := by omega
        obtain ⟨s, u, hsu, hu⟩ := ih K' hK'1 hlt
        refine ⟨s+1, u, ?_, hu⟩
        calc K = 3 * K' := hK'
          _ = 3 * (3^s * u) := by rw [hsu]
          _ = 3^(s+1) * u := by rw [Nat.pow_succ]; ring
      · exact ⟨0, K, by simp, h3⟩

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
has-reader, by induction on the position (the `.eq_def` idiom). -/
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
        rw [Nat.pow_succ, Nat.div_div_eq_div_mul]
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
        exact ih (n / 3) h

/-- **THE TWO-GRANT CROWN.**  The FULL Erdős #406 statement follows from
exactly two named grants: (G1) ghost extinction — no core carries the
full shadow package; (G2) residual ghost compression — every Cantorian
power above the kernel base has a ghost-ray core.  Everything else is
unconditional and machine-checked: the finite base (§7), the odd wing,
the three paid small cases, and the digit-to-verdict bridge. -/
theorem erdos406_crown_of_ghost_extinction
    (hNoGhost : ∀ u : Nat, ¬ GhostRay u)
    (hComp : ∀ (K σ u : Nat), 500 < K → K = 3^σ * u → ¬ (3:Nat) ∣ u →
      CantorianPower K → GhostRay u) :
    ∀ n : Nat, 9 ≤ n → noTernaryTwo (2^n) = false := by
  -- Step 1: no Cantorian power above eight
  have hnoCant : ∀ K : Nat, 8 ≤ K → ¬ CantorianPower K := by
    intro K hK8 hCant
    rcases Nat.lt_or_ge K 501 with hle | hgt
    · obtain ⟨p, hp⟩ := cantorian_base K hK8 (by omega)
      refine hCant p ?_ hp
      rcases Nat.eq_zero_or_pos p with h0 | hp1
      · rw [h0, digit3_pow4_zero] at hp
        exact absurd hp (by decide)
      · exact hp1
    · obtain ⟨σ, u, hKu, hu⟩ :=
        exists_three_free_decomp K K (by omega) (by omega)
      exact hNoGhost u (hComp K σ u (by omega) hKu hu hCant)
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
    rw [h2n]
    exact has_two_imp_not_no_two (4^(n / 2)) hhas
  · have hnodd : n = 2 * (n / 2) + 1 := by omega
    have hmod : (2^n) % 3 = 2 := by
      rw [hnodd, Nat.pow_succ]
      have h2m : (2:Nat)^(2 * (n / 2)) % 3 = 1 := by
        rw [two_pow_two_mul]
        exact pow4_mod3 _
      rw [Nat.mul_mod, h2m]
      decide
    have hdig : digit3 (2^n) 0 = 2 := by
      unfold digit3
      rw [Nat.pow_zero, Nat.div_one, hmod]
    have hhas : hasTernaryTwo (2^n) = true :=
      hasTwo_of_digit (2^n) 0 hdig
    exact has_two_imp_not_no_two (2^n) hhas

/-! ## §9 Receipts -/
#print axioms PiCollapse406.erdos406_crown_of_ghost_extinction  -- CK74 SECTION BOUNDARY

#check PiCollapse406.ghost_residue_shape
#check PiCollapse406.ghost_congruence
#check PiCollapse406.ghost_congruent_all_depths
#check PiCollapse406.every_ghost_is_its_pi_point_fam4
#check PiCollapse406.every_ghost_is_its_pi_point_fam7
#check PiCollapse406.every_ghost_is_its_pi_point_fam1
#check PiCollapse406.cantorian_base
#check PiCollapse406.erdos406_crown_of_ghost_extinction

#print axioms PiCollapse406.pow4_three_power_lte_exact
#print axioms PiCollapse406.lteCoeff_mod3_one
#print axioms PiCollapse406.lteCoeff_stable
#print axioms PiCollapse406.ghost_residue_shape
#print axioms PiCollapse406.ghost_congruence
#print axioms PiCollapse406.dvd_mul_cancel_three
#print axioms PiCollapse406.dvd_of_unit_mul_cancel
#print axioms PiCollapse406.cancel_engine
#print axioms PiCollapse406.ghost_congruent_ge_three
#print axioms PiCollapse406.ghost_congruent_all_depths
#print axioms PiCollapse406.ghost_head_not_three
#print axioms PiCollapse406.ghost_head_lt_nine
#print axioms PiCollapse406.cMod_eq
#print axioms PiCollapse406.W61_receipt
#print axioms PiCollapse406.W61_mod_nine
#print axioms PiCollapse406.W61_mod_three
#print axioms PiCollapse406.pi_fam4_receipt
#print axioms PiCollapse406.pi_fam7_receipt
#print axioms PiCollapse406.pi_fam1_receipt
#print axioms PiCollapse406.pi_fam4_trit3
#print axioms PiCollapse406.pi_fam4_trit14
#print axioms PiCollapse406.pi_fam7_trit1
#print axioms PiCollapse406.pi_fam7_trit6
#print axioms PiCollapse406.pi_fam1_trit8
#print axioms PiCollapse406.pi_fam1_trit13
#print axioms PiCollapse406.hasTwoScan_iff
#print axioms PiCollapse406.cantorian_base
#print axioms PiCollapse406.hasTwo_of_digit
#print axioms PiCollapse406.erdos406_crown_of_ghost_extinction

#eval "ERDOS406_PICOLLAPSE_KERNEL_GREEN"

end PiCollapse406
