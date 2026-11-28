import Arsenal.ErdosTernary2.Basic
import Arsenal.CardinalWorlds

-- Family pattern (green kernels CapLaw406/CapLawK406): explicit depth headroom.
set_option maxRecDepth 262144
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 1000

/-!
# ERDŐS #406 — THE DYADIC CASCADE LAWS (S097, the S096 council's queued
ATTACKER mission: the parity-lattice cascade theory, opened in Lean)

## THE ORDER

BOSS order (S096/S097): crack the HFTAIL hypothesis completely — use MY
maths, combine the Lean files, create the new theorem/law.  The S096 war
council ranked the routes and named the shortest kill: **CAP(185)** — the
2-adic cap law on primitive Cantor numbers, the only transcendence-free
lane, its composition with the green Kernel-38 census already
machine-checked (`CapLaw406.lean:389`).  The council's fresh structural
lead, queued as this round's first dispatch:

> "v₂(Σ_{i∈S} 3^i) is governed by the DYADIC SUBSET-PARITY LATTICE of S —
> via 3^i = Σ_j binom(i,j) 2^j and Lucas, the valuation cascade reads off
> the binomial moments of the position set — the cascade-sustainability
> question (how long can S ⊆ [0,M) sustain it) is the CAP theorem in its
> purest form."

This kernel opens that theory.  Every law here is UNCONDITIONAL — all
positions, all scales, zero hypotheses — built only on the Arsenal's own
readers (`v2r`, the compiled `CardinalWorlds`) and core Nat lemmas.

## THE NEW MATHEMATICS (what this kernel proves)

* **§0 THE DIVISIBILITY BRIDGE** (`v2r_lt_of_not_two_pow_dvd`): the exact
  dictionary between the Arsenal's reader and divisibility —
  `2^t ∤ n ⟹ v2r n < t`.  The kill theorems' engine.

* **§1 THE BINOMIAL RESOLUTION** (`three_pow_eq_sum_choose`): the exact
  identity
  $$3^i \;=\; \sum_{k=0}^{i} \binom{i}{k} 2^k,$$
  the resolution of every power of three into dyadic binomial moments —
  Pascal's rule, self-contained, zero external theory.

* **§2 THE MOMENT TOWER** (`three_pow_mod_two_pow`, `moment_tower`): for
  every position list `S` and every depth `t`,
  $$\Bigl(\sum_{i \in S} 3^i\Bigr) \;\equiv\; \sum_{k < t} M_k(S)\, 2^k
  \pmod{2^t}, \qquad M_k(S) := \sum_{i \in S} \binom{i}{k}.$$
  The value of a 0/1-ternary number mod `2^t` IS its binomial-moment
  generating sum truncated at `t` — the parity-lattice cascade in exact
  integer form, stronger than the Lucas parity reading (which it subsumes
  as the carry layers).

* **§3 THE CENSUS RUNGS** (`bridge_two/three/four`, list forms): the first
  three rungs of the tower, unfolded into explicit census constraints:
  mod 4 the sum reads `|S| + 2·Σi`; mod 8 it reads `|S| + 2·Σi + 4·ΣC(i,2)`;
  mod 16 it adds `8·ΣC(i,3)`.  Three moment scans of the position set.

* **§4 THE ANTI-CASCADE KILLS** (`census_kill_two/three/four`,
  `anti_cascade_kill`): any position set whose moment sums MISS the
  congruence has valuation strictly below that rung — the machine-checkable
  kill family.  In zero-sum form: a subset of {3^0..3^{M-1}} can reach
  valuation `t` ONLY by solving the moment congruences at every rung ≤ t.
  This is the CAP theorem's exact shape: CAP(185) falls the day the
  moment lattice is shown unsatisfiable at t = M+186 for every
  S ⊆ [0,M).

* **§5 THE RIDER LATTICE PINS** (`rider_census_pin_two/three/four`,
  `rider_moment_pin`): every rider — every representation of a power of
  four as a 0/1-ternary sum — is PINNED to the full moment lattice at
  every depth `t ≤ 2K` (its valuation is exactly `2K`).  The riders live
  on the binomial-moment congruence tower; every rung is a new necessary
  condition, machine-checked.  (Hand-verified receipt: the rider
  `4^4 = 256 = {0,1,2,5}` satisfies all three census rungs —
  `4+2·8+4·11 = 64 ≡ 0 (8)`, `+8·10 = 144 ≡ 0 (16)`.)

## THE HONEST SCOPE (BOSS's law: never dress a partial as complete)

The sustainability bound — proving the moment lattice unsatisfiable at
the CAP rung for all large M — is NOT proven here; it is the same
anti-concentration wall the council named (weeks-months class).  What IS
proven, unconditionally: the cascade theory's exact opening block — the
resolution, the tower, the census rungs, the kills, the rider pins.  The
CAP question now lives entirely inside this lattice: it is the statement
that the rider pins' congruence system has no solution at the deep rungs.
-/

namespace CascadeLaw406

-- (the family receipt: Arsenal/CardinalWorlds.lean declares everything at
-- ROOT — `v2r` resolves directly, no namespace to open.)

/-! ## §0 The engine — the reader/divisibility dictionary -/

/-- **THE DIVISIBILITY KILL.**  If `2^t` does not divide a positive `n`,
the Arsenal's reader lands strictly below `t`: `v2r n < t`. -/
theorem v2r_lt_of_not_two_pow_dvd (n t : Nat) (hn : 0 < n)
    (h : n % 2 ^ t ≠ 0) : v2r n < t := by
  induction t generalizing n with
  | zero =>
      exact absurd (by rw [Nat.pow_zero, Nat.mod_one]) h
  | succ t ih =>
      by_contra hcon
      push_neg at hcon
      have hne : ¬ n = 0 := by omega
      rw [v2r.eq_def n, if_neg hne] at hcon
      by_cases h2 : n % 2 = 0
      · rw [if_pos h2] at hcon
        have hdivpos : 0 < n / 2 := by omega
        have hdiv : n / 2 % 2 ^ t = 0 := by
          by_contra hdl
          have hlt := ih (n / 2) hdivpos hdl
          omega
        obtain ⟨m, hm⟩ := Nat.dvd_of_mod_eq_zero hdiv
        have hnd : n = 2 * (n / 2) := by omega
        have hzero : n % 2 ^ (t + 1) = 0 := by
          rw [hnd, hm, Nat.pow_succ]
          have hre : 2 * (2 ^ t * m) = 2 ^ t * 2 * m := by ring
          rw [hre]
          exact Nat.mul_mod_right _ _
        exact h hzero
      · rw [if_neg h2] at hcon
        omega

/-! ## §1 The binomial resolution — 3^i as a dyadic moment sum -/

/-- **THE PEEL-FIRST LAW** (helper): summing over `range (n+1)` peels the
zeroth term first.  Self-contained, from the compiled `sum_range_succ`. -/
theorem sum_range_succ_first (f : Nat → Nat) (n : Nat) :
    ∑ k ∈ Finset.range (n + 1), f k = f 0 + ∑ k ∈ Finset.range n, f (k + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
      ring

/-- **THE BINOMIAL RESOLUTION.**  Every power of three is exactly its
dyadic binomial-moment sum: `3^i = Σ_{k ≤ i} C(i,k) · 2^k` — Pascal's
rule, self-contained.  The resolution that turns 2-adic valuation
questions into moment-lattice questions. -/
theorem three_pow_eq_sum_choose (i : Nat) :
    ∑ k ∈ Finset.range (i + 1), Nat.choose i k * 2 ^ k = 3 ^ i := by
  induction i with
  | zero => norm_num
  | succ i ih =>
      have hpascal : ∀ k ∈ Finset.range (i + 1),
          Nat.choose (i + 1) (k + 1) * 2 ^ (k + 1)
            = Nat.choose i (k + 1) * 2 ^ (k + 1)
                + Nat.choose i k * 2 ^ (k + 1) := by
        intro k _
        rw [Nat.choose_succ_succ]
        ring
      have hshift : ∀ k ∈ Finset.range (i + 1),
          Nat.choose i k * 2 ^ (k + 1) = 2 * (Nat.choose i k * 2 ^ k) := by
        intro k _
        rw [Nat.pow_succ]
        ring
      have hzero : Nat.choose (i + 1) 0 * 2 ^ 0 = 1 := by
        rw [Nat.choose_zero_right, Nat.pow_zero, Nat.one_mul]
      have hvanish : Nat.choose i (i + 1) * 2 ^ (i + 1) = 0 := by
        rw [Nat.choose_eq_zero_of_lt (Nat.lt_succ_self i), Nat.zero_mul]
      calc ∑ k ∈ Finset.range (i + 2), Nat.choose (i + 1) k * 2 ^ k
          = Nat.choose (i + 1) 0 * 2 ^ 0
              + ∑ k ∈ Finset.range (i + 1),
                  Nat.choose (i + 1) (k + 1) * 2 ^ (k + 1) := by
            rw [sum_range_succ_first (fun k => Nat.choose (i + 1) k * 2 ^ k) (i + 1)]
      _ = 1 + (∑ k ∈ Finset.range (i + 1), Nat.choose i (k + 1) * 2 ^ (k + 1))
              + (∑ k ∈ Finset.range (i + 1), Nat.choose i k * 2 ^ (k + 1)) := by
            rw [hzero, Finset.sum_congr rfl hpascal, Finset.sum_add_distrib]
            ring
      _ = 1 + (∑ k ∈ Finset.range (i + 1), Nat.choose i (k + 1) * 2 ^ (k + 1))
              + 2 * (∑ k ∈ Finset.range (i + 1), Nat.choose i k * 2 ^ k) := by
            rw [Finset.sum_congr rfl hshift, ← Finset.mul_sum]
      _ = (∑ k ∈ Finset.range (i + 2), Nat.choose i k * 2 ^ k)
              + 2 * (∑ k ∈ Finset.range (i + 1), Nat.choose i k * 2 ^ k) := by
            rw [sum_range_succ_first (fun k => Nat.choose i k * 2 ^ k) (i + 1)]
            simp only [Nat.choose_zero_right, Nat.pow_zero, Nat.one_mul]
      _ = (∑ k ∈ Finset.range (i + 1), Nat.choose i k * 2 ^ k)
              + 2 * (∑ k ∈ Finset.range (i + 1), Nat.choose i k * 2 ^ k) := by
            rw [Finset.sum_range_succ, hvanish, Nat.add_zero]
      _ = 3 ^ i + 2 * 3 ^ i := by rw [ih]
      _ = 3 ^ (i + 1) := by rw [Nat.pow_succ]; ring

/-! ## §2 The moment tower — the cascade in exact form -/

/-- The parity law for powers of three (engine helper, green idiom). -/
theorem three_pow_mod_two (i : Nat) : 3 ^ i % 2 = 1 := by
  induction i with
  | zero => rfl
  | succ i ih => rw [Nat.pow_succ, Nat.mul_mod, ih]

/-- **THE PER-POSITION TOWER.**  For every position `i` and depth `t`:
`3^i ≡ Σ_{k<t} C(i,k) 2^k (mod 2^t)` — the truncated binomial resolution. -/
theorem three_pow_mod_two_pow (i t : Nat) :
    3 ^ i % 2 ^ t = (∑ k ∈ Finset.range t, Nat.choose i k * 2 ^ k) % 2 ^ t := by
  rcases t with _ | t
  · simp [Nat.mod_one]
  · rcases t with _ | t''
    · rw [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty,
        Nat.zero_add, Nat.choose_zero_right, Nat.pow_zero, Nat.one_mul,
        Nat.pow_one, three_pow_mod_two]
      norm_num
    · -- the deep case: depth t'' + 1 + 1 ≥ 2, induction on the position
      suffices h : ∀ j : Nat, 3 ^ j % 2 ^ (t'' + 1 + 1)
          = (∑ k ∈ Finset.range (t'' + 1 + 1), Nat.choose j k * 2 ^ k)
              % 2 ^ (t'' + 1 + 1) by
        exact h i
      intro j
      induction j with
      | zero =>
          have hvan : ∀ k ∈ Finset.range (t'' + 1 + 1),
              Nat.choose 0 k * 2 ^ k = if k = 0 then 1 else 0 := by
            intro k hk
            rcases Nat.eq_zero_or_pos k with h0 | h0
            · rw [h0, Nat.choose_zero_right, Nat.pow_zero, Nat.one_mul,
                if_pos rfl]
            · rw [Nat.choose_eq_zero_of_lt h0, Nat.zero_mul,
                if_neg (by omega : ¬ k = 0)]
          rw [Finset.sum_congr rfl hvan]
          have hsum : (∑ k ∈ Finset.range (t'' + 1 + 1),
              (if k = 0 then 1 else 0)) = 1 := by
            rw [sum_range_succ_first (fun k => if k = 0 then (1:Nat) else 0)
              (t'' + 1)]
            simp
          rw [hsum]
          simp only [Nat.pow_zero]
      | succ j ih =>
          -- the cascade step: Pascal at the first rung, the carry divides
          have hA : ∑ k ∈ Finset.range (t'' + 1 + 1), Nat.choose (j + 1) k * 2 ^ k
              = 1 + (∑ k ∈ Finset.range (t'' + 1), Nat.choose j (k + 1) * 2 ^ (k + 1))
                  + 2 * (∑ k ∈ Finset.range (t'' + 1), Nat.choose j k * 2 ^ k) := by
            rw [sum_range_succ_first
              (fun k => Nat.choose (j + 1) k * 2 ^ k) (t'' + 1)]
            simp only [Nat.choose_zero_right, Nat.pow_zero, Nat.one_mul]
            have hpascal : ∀ k ∈ Finset.range (t'' + 1),
                Nat.choose (j + 1) (k + 1) * 2 ^ (k + 1)
                  = Nat.choose j (k + 1) * 2 ^ (k + 1)
                      + Nat.choose j k * 2 ^ (k + 1) := by
              intro k _
              rw [Nat.choose_succ_succ]
              ring
            have hshift : ∀ k ∈ Finset.range (t'' + 1),
                Nat.choose j k * 2 ^ (k + 1) = 2 * (Nat.choose j k * 2 ^ k) := by
              intro k _
              rw [Nat.pow_succ]
              ring
            rw [Finset.sum_congr rfl hpascal, Finset.sum_add_distrib,
              Finset.sum_congr rfl hshift, ← Finset.mul_sum]
            ring
          have hApeel : ∑ k ∈ Finset.range (t'' + 1 + 1), Nat.choose j k * 2 ^ k
              = (∑ k ∈ Finset.range (t'' + 1), Nat.choose j k * 2 ^ k)
                  + Nat.choose j (t'' + 1) * 2 ^ (t'' + 1) := by
            rw [Finset.sum_range_succ]
          have hAfirst : (∑ k ∈ Finset.range (t'' + 1 + 1), Nat.choose j k * 2 ^ k)
              = 1 + (∑ k ∈ Finset.range (t'' + 1), Nat.choose j (k + 1) * 2 ^ (k + 1)) := by
            rw [sum_range_succ_first (fun k => Nat.choose j k * 2 ^ k) (t'' + 1)]
            simp only [Nat.choose_zero_right, Nat.pow_zero, Nat.one_mul]
          have hRewrite : (∑ k ∈ Finset.range (t'' + 1 + 1), Nat.choose (j + 1) k * 2 ^ k)
              = (∑ k ∈ Finset.range (t'' + 1 + 1), Nat.choose j k * 2 ^ k)
                  + 2 * (∑ k ∈ Finset.range (t'' + 1), Nat.choose j k * 2 ^ k) := by
            rw [hA, ← hAfirst]
          have hcarry : 3 * (∑ k ∈ Finset.range (t'' + 1 + 1), Nat.choose j k * 2 ^ k)
              = (∑ k ∈ Finset.range (t'' + 1 + 1), Nat.choose j k * 2 ^ k)
                  + 2 * (∑ k ∈ Finset.range (t'' + 1), Nat.choose j k * 2 ^ k)
                  + 2 ^ (t'' + 1 + 1) * Nat.choose j (t'' + 1) := by
            rw [hApeel, Nat.pow_succ]
            ring
          have h4 : 4 ≤ 2 ^ (t'' + 1 + 1) := by
            have hpow : 2 ^ (t'' + 1 + 1) = 4 * 2 ^ t'' := by
              rw [Nat.pow_succ, Nat.pow_succ]
              ring
            have hpos : 0 < 2 ^ t'' := Nat.pow_pos (by decide : 0 < (2:Nat))
            rw [hpow]
            omega
          have h3mod : 3 % 2 ^ (t'' + 1 + 1) = 3 :=
            Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (by decide : 3 < 4) h4)
          have hlhs : 3 ^ (j + 1) % 2 ^ (t'' + 1 + 1)
              = (3 * (∑ k ∈ Finset.range (t'' + 1 + 1), Nat.choose j k * 2 ^ k))
                  % 2 ^ (t'' + 1 + 1) := by
            rw [Nat.pow_succ, Nat.mul_mod (3 ^ j) 3 (2 ^ (t'' + 1 + 1)), ih, h3mod,
              Nat.mul_comm 3 (∑ k ∈ Finset.range (t'' + 1 + 1), Nat.choose j k * 2 ^ k),
              Nat.mul_mod (∑ k ∈ Finset.range (t'' + 1 + 1), Nat.choose j k * 2 ^ k) 3
                (2 ^ (t'' + 1 + 1)), h3mod]
          rw [hRewrite, hlhs, hcarry, Nat.add_mul_mod_self_left]

/-- **THE MOMENT TOWER.**  For every position list `S` and every depth
`t`: the 0/1-ternary sum satisfies
`(Σ_{i∈S} 3^i) % 2^t = (Σ_{i∈S} Σ_{k<t} C(i,k) 2^k) % 2^t` — the value
mod `2^t` IS the truncated binomial-moment sum.  The parity-lattice
cascade in exact integer form. -/
theorem moment_tower (l : List Nat) (t : Nat) :
    (l.map (fun i => 3 ^ i)).sum % 2 ^ t
      = (l.map (fun i => ∑ k ∈ Finset.range t, Nat.choose i k * 2 ^ k)).sum
          % 2 ^ t := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.map_cons, List.sum_cons]
      have h1 : (3 ^ a + (List.map (fun i => 3 ^ i) l).sum) % 2 ^ t
          = (3 ^ a % 2 ^ t + (List.map (fun i => 3 ^ i) l).sum % 2 ^ t) % 2 ^ t :=
        Nat.add_mod _ _ _
      have h2 : ((∑ k ∈ Finset.range t, Nat.choose a k * 2 ^ k)
            + (List.map (fun i => ∑ k ∈ Finset.range t, Nat.choose i k * 2 ^ k) l).sum)
            % 2 ^ t
          = ((∑ k ∈ Finset.range t, Nat.choose a k * 2 ^ k) % 2 ^ t
            + (List.map (fun i => ∑ k ∈ Finset.range t, Nat.choose i k * 2 ^ k) l).sum
                % 2 ^ t) % 2 ^ t :=
        Nat.add_mod _ _ _
      rw [h1, h2, three_pow_mod_two_pow, ih]

/-! ## §3 The census rungs — the tower unfolded at depths 2, 3, 4 -/

/-- **THE MOD-FOUR RUNG** (single position). -/
theorem bridge_two (i : Nat) :
    (∑ k ∈ Finset.range 2, Nat.choose i k * 2 ^ k) = 1 + 2 * i := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.range_zero,
    Finset.sum_empty, Nat.zero_add, Nat.choose_zero_right,
    Nat.choose_one_right]
  ring

/-- **THE MOD-EIGHT RUNG** (single position). -/
theorem bridge_three (i : Nat) :
    (∑ k ∈ Finset.range 3, Nat.choose i k * 2 ^ k)
      = 1 + 2 * i + 4 * Nat.choose i 2 := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.range_zero, Finset.sum_empty, Nat.zero_add,
    Nat.choose_zero_right, Nat.choose_one_right]
  ring

/-- **THE MOD-SIXTEEN RUNG** (single position). -/
theorem bridge_four (i : Nat) :
    (∑ k ∈ Finset.range 4, Nat.choose i k * 2 ^ k)
      = 1 + 2 * i + 4 * Nat.choose i 2 + 8 * Nat.choose i 3 := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty,
    Nat.zero_add, Nat.choose_zero_right, Nat.choose_one_right]
  ring

/-- The mod-4 census rung, list form. -/
theorem list_bridge_two (l : List Nat) :
    (l.map (fun i => ∑ k ∈ Finset.range 2, Nat.choose i k * 2 ^ k)).sum
      = l.length + 2 * l.sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      rw [bridge_two, ih]
      ring

/-- The mod-8 census rung, list form. -/
theorem list_bridge_three (l : List Nat) :
    (l.map (fun i => ∑ k ∈ Finset.range 3, Nat.choose i k * 2 ^ k)).sum
      = l.length + 2 * l.sum + 4 * (l.map (fun i => Nat.choose i 2)).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      rw [bridge_three, ih]
      ring

/-- The mod-16 census rung, list form. -/
theorem list_bridge_four (l : List Nat) :
    (l.map (fun i => ∑ k ∈ Finset.range 4, Nat.choose i k * 2 ^ k)).sum
      = l.length + 2 * l.sum + 4 * (l.map (fun i => Nat.choose i 2)).sum
          + 8 * (l.map (fun i => Nat.choose i 3)).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      rw [bridge_four, ih]
      ring

/-! ## §4 The anti-cascade kills — the lattice as a weapon -/

/-- **THE GENERAL ANTI-CASCADE KILL.**  Any position set whose truncated
moment sum misses the `2^t` congruence has valuation strictly below `t`:
the cascade cannot jump the lattice. -/
theorem anti_cascade_kill (l : List Nat) (t : Nat)
    (h : (l.map (fun i => ∑ k ∈ Finset.range t, Nat.choose i k * 2 ^ k)).sum
          % 2 ^ t ≠ 0) :
    v2r ((l.map (fun i => 3 ^ i)).sum) < t := by
  cases l with
  | nil => simp at h
  | cons a l' =>
      have hpos : 0 < (List.map (fun i => 3 ^ i) (a :: l')).sum := by
        have hp : 0 < 3 ^ a := Nat.pow_pos (by decide)
        simp only [List.map_cons, List.sum_cons]
        omega
      apply v2r_lt_of_not_two_pow_dvd _ t hpos
      rw [moment_tower]
      exact h

/-- **THE MOD-FOUR CENSUS KILL.**  A position set with
`|S| + 2·Σi ≢ 0 (mod 4)` has `v₂ ≤ 1`. -/
theorem census_kill_two (l : List Nat)
    (h : (l.length + 2 * l.sum) % 4 ≠ 0) :
    v2r ((l.map (fun i => 3 ^ i)).sum) ≤ 1 := by
  have hkill : v2r ((l.map (fun i => 3 ^ i)).sum) < 2 := by
    apply anti_cascade_kill l 2
    rw [list_bridge_two]
    exact h
  omega

/-- **THE MOD-EIGHT CENSUS KILL.**  A position set with
`|S| + 2·Σi + 4·ΣC(i,2) ≢ 0 (mod 8)` has `v₂ ≤ 2`. -/
theorem census_kill_three (l : List Nat)
    (h : (l.length + 2 * l.sum + 4 * (l.map (fun i => Nat.choose i 2)).sum) % 8 ≠ 0) :
    v2r ((l.map (fun i => 3 ^ i)).sum) ≤ 2 := by
  have hkill : v2r ((l.map (fun i => 3 ^ i)).sum) < 3 := by
    apply anti_cascade_kill l 3
    rw [list_bridge_three]
    exact h
  omega

/-- **THE MOD-SIXTEEN CENSUS KILL.**  A position set with
`|S| + 2·Σi + 4·ΣC(i,2) + 8·ΣC(i,3) ≢ 0 (mod 16)` has `v₂ ≤ 3`. -/
theorem census_kill_four (l : List Nat)
    (h : (l.length + 2 * l.sum + 4 * (l.map (fun i => Nat.choose i 2)).sum
        + 8 * (l.map (fun i => Nat.choose i 3)).sum) % 16 ≠ 0) :
    v2r ((l.map (fun i => 3 ^ i)).sum) ≤ 3 := by
  have hkill : v2r ((l.map (fun i => 3 ^ i)).sum) < 4 := by
    apply anti_cascade_kill l 4
    rw [list_bridge_four]
    exact h
  omega

/-! ## §5 The rider lattice pins — riders live on the tower -/

/-- **THE GENERAL RIDER PIN.**  Every representation of a power of four
as a 0/1-ternary sum satisfies the FULL moment-lattice congruence at
every depth `t ≤ 2K` (its valuation is exactly `2K`). -/
theorem rider_moment_pin (K : Nat) (l : List Nat)
    (hl : (l.map (fun i => 3 ^ i)).sum = 4 ^ K) (t : Nat) (ht : t ≤ 2 * K) :
    (l.map (fun i => ∑ k ∈ Finset.range t, Nat.choose i k * 2 ^ k)).sum
        % 2 ^ t = 0 := by
  have h4 : 4 ^ K = 2 ^ (2 * K) := by
    rw [show (4 : Nat) = 2 ^ 2 from rfl, ← Nat.pow_mul]
  have hdvd : (2 : Nat) ^ t ∣ 2 ^ (2 * K) := Nat.pow_dvd_pow 2 ht
  rw [← h4, ← hl] at hdvd
  have hmod : (l.map (fun i => 3 ^ i)).sum % 2 ^ t = 0 :=
    Nat.mod_eq_zero_of_dvd hdvd
  rw [moment_tower] at hmod
  exact hmod

/-- **THE MOD-FOUR RIDER PIN.**  Every rider `K ≥ 1` obeys
`|S| + 2·Σi ≡ 0 (mod 4)`. -/
theorem rider_census_pin_two (K : Nat) (l : List Nat)
    (hl : (l.map (fun i => 3 ^ i)).sum = 4 ^ K) (hK : 1 ≤ K) :
    (l.length + 2 * l.sum) % 4 = 0 := by
  have hpin := rider_moment_pin K l hl 2 (by omega)
  rw [list_bridge_two] at hpin
  exact hpin

/-- **THE MOD-EIGHT RIDER PIN.**  Every rider `K ≥ 2` obeys
`|S| + 2·Σi + 4·ΣC(i,2) ≡ 0 (mod 8)`. -/
theorem rider_census_pin_three (K : Nat) (l : List Nat)
    (hl : (l.map (fun i => 3 ^ i)).sum = 4 ^ K) (hK : 2 ≤ K) :
    (l.length + 2 * l.sum + 4 * (l.map (fun i => Nat.choose i 2)).sum) % 8 = 0 := by
  have hpin := rider_moment_pin K l hl 3 (by omega)
  rw [list_bridge_three] at hpin
  exact hpin

/-- **THE MOD-SIXTEEN RIDER PIN.**  Every rider `K ≥ 2` obeys
`|S| + 2·Σi + 4·ΣC(i,2) + 8·ΣC(i,3) ≡ 0 (mod 16)`. -/
theorem rider_census_pin_four (K : Nat) (l : List Nat)
    (hl : (l.map (fun i => 3 ^ i)).sum = 4 ^ K) (hK : 2 ≤ K) :
    (l.length + 2 * l.sum + 4 * (l.map (fun i => Nat.choose i 2)).sum
        + 8 * (l.map (fun i => Nat.choose i 3)).sum) % 16 = 0 := by
  have hpin := rider_moment_pin K l hl 4 (by omega)
  rw [list_bridge_four] at hpin
  exact hpin

/-! ## §6 The receipts -/

#check v2r_lt_of_not_two_pow_dvd
#check sum_range_succ_first
#check three_pow_eq_sum_choose
#check three_pow_mod_two
#check three_pow_mod_two_pow
#check moment_tower
#check bridge_two
#check bridge_three
#check bridge_four
#check list_bridge_two
#check list_bridge_three
#check list_bridge_four
#check anti_cascade_kill
#check census_kill_two
#check census_kill_three
#check census_kill_four
#check rider_moment_pin
#check rider_census_pin_two
#check rider_census_pin_three
#check rider_census_pin_four

#print axioms v2r_lt_of_not_two_pow_dvd
#print axioms sum_range_succ_first
#print axioms three_pow_eq_sum_choose
#print axioms three_pow_mod_two
#print axioms three_pow_mod_two_pow
#print axioms moment_tower
#print axioms bridge_two
#print axioms bridge_three
#print axioms bridge_four
#print axioms list_bridge_two
#print axioms list_bridge_three
#print axioms list_bridge_four
#print axioms anti_cascade_kill
#print axioms census_kill_two
#print axioms census_kill_three
#print axioms census_kill_four
#print axioms rider_moment_pin
#print axioms rider_census_pin_two
#print axioms rider_census_pin_three
#print axioms rider_census_pin_four

end CascadeLaw406
