import Arsenal.ErdosTernary2.Basic
import Arsenal.CardinalWorlds
import Arsenal.CardinalWorldsV2

-- Family pattern (green kernels): explicit depth headroom.
set_option maxRecDepth 262144
set_option maxHeartbeats 4000000

/-!
# ERDŐS #406 — THE DUST-LAW KERNEL (S075, the exact doubling of the survivor tree)

## THE OBJECT (the dust tree of the 406 campaign)

The dust tree lives on the exponent classes of the riders: a node at level
`j` is a residue class `r mod 3^j` whose members `K` have the first `j+1`
ternary digits of `4^K` all in `{0,1}`.  The census engine
(`caplaw/dust_census.md`) built this tree level by level and verified the
doubling `|alive[j]| = 2^j` to level 12 — this kernel proves it **for every
level, forever**, by identifying the engine: the digit-shift law
`digit_{j+1}(4^{r + t·3^j}) = (digit_{j+1}(4^r) + t) mod 3`, whose engine is
the certificate `4^{3^j} ≡ 1 + 3^{j+1} (mod 3^{j+2})`.

## WHAT THIS KERNEL PROVES, UNCONDITIONALLY AND IN FULL

* **THE CERTIFICATE** (`four_pow_3j_struct`): `4^(3^j) = 1 + 3^(j+1)·c`
  with `c ≡ 1 mod 3` — the near-unity structure of the ternary powers of 4,
  by the cube induction on the Arsenal's own `cubic_expansion`.

* **THE BINOMIAL CONGRUENCE** (`binom_cong`): `(1 + 3^{j+1}·z)^t ≡
  1 + t·3^{j+1}·z (mod 3^{j+2})`, carried as the existential decomposition.

* **THE SHIFT LAW** (`dust_shift`): for every `j r t`,
  `digit3 (4^(r + t·3^j)) (j+1) = (digit3 (4^r) (j+1) + t) mod 3`.
  The three children of a node move their new digit by `t` — a complete
  residue system — so **exactly one child is dead**.

* **THE PERIOD LAW** (`digit_period`): `digit3 (4^(k + 3^q·m)) q =
  digit3 (4^k) q` — the level-`q` digit is a function of the class mod
  `3^q` alone (the multiplicative order structure).

* **THE EXACT DOUBLING** (`dust_doubling`, `dust_card`): the survivor tree
  has exactly `2·|alive[j]|` children alive at level `j+1`, hence
  **`|alive[j]| = 2^j` at every level, forever**.  The census's verified
  doubling (level 12) is now a theorem with no ceiling.

* **THE FULL SPECIFICATION** (`dust_spec`): `r ∈ dust j ↔ r < 3^j ∧ every
  digit3 (4^r) q (q ≤ j) ≠ 2` — the tree IS the survivor set, exactly.

* **THE RIDER COROLLARY** (`dust_rider_classes`): every rider `K` (with
  all ternary digits of `4^K` in `{0,1}`) lies in `dust j` at every level
  `j` with `3^j > K` — the riders are the integer points of the tree.

The empirical `2.482^p` growth row of the WORKLOG registry is hereby
closed: the branching is exactly 2, at every level, forever.  What remains
open (the anti-concentration wall) is the *distribution* of the `2^j`
survivor classes, not their count.

All arithmetic uses the Arsenal's own laws (`cubic_expansion`,
`mul_add_div_lemma`, `lt_three_cases`) plus core Nat lemmas — no external
theory, no classical imports, BOSS's mathematics only.
-/

/-! ## §0 The digit reader and the digit-algebra lemma -/

/-- The ternary digit at position `p` (self-contained twin of the Arsenal's
`gstDigit`). -/
def digit3 (x p : Nat) : Nat := x / 3^p % 3

/-- Adding a multiple of `3^p` shifts the `p`-th digit by the multiplier's
residue mod 3 — the one-line engine of the whole dust law. -/
theorem digit_add_mul (p y V : Nat) :
    digit3 (y + 3^p * V) p = (digit3 y p + V % 3) % 3 := by
  have hp : 0 < 3^p := Nat.pow_pos (by decide)
  unfold digit3
  rw [Nat.add_comm y (3^p * V), mul_add_div_lemma V y (3^p) hp,
    Nat.add_comm V (y / 3^p), Nat.add_mod]

/-- The digit reader is ranged: every `digit3` value is a genuine ternary
digit (the range law the omegas of this kernel consume). -/
theorem digit3_lt_three (x p : Nat) : digit3 x p < 3 := by
  unfold digit3
  exact Nat.mod_lt _ (show 0 < 3 by decide)

/-! ## §1 The certificate: the near-unity structure of `4^(3^j)` -/

/-- **THE CERTIFICATE.** `4^(3^j) = 1 + 3^(j+1)·c` with `c ≡ 1 mod 3`.
Engine: the cube induction on the Arsenal's `cubic_expansion`. -/
theorem four_pow_3j_struct : ∀ j : Nat, ∃ c : Nat,
    4^(3^j) = 1 + 3^(j+1) * c ∧ c % 3 = 1 := by
  intro j
  induction j with
  | zero => exact ⟨1, by decide, by decide⟩
  | succ j ih =>
    obtain ⟨u, hu, hu3⟩ := ih
    have e1 : (3:Nat)^(j+1) = 3^j * 3 := Nat.pow_succ 3 j
    have e2 : (3:Nat)^(j+2) = 3^j * 9 := by rw [Nat.pow_add]
    have hpow : 4^(3^(j+1)) = (4^(3^j))^3 := by
      rw [show 3^(j+1) = 3^j * 3 from Nat.pow_succ 3 j, Nat.pow_mul]
    have hc := cubic_expansion (3^(j+1) * u)
    refine ⟨u + 3 * (3^j * u * u + 3^j * 3^j * u * u * u), ?_, ?_⟩
    · rw [hpow, hu, hc, e1, e2]
      ring
    · omega

/-! ## §2 The binomial congruence (the near-identity raised to a power) -/

/-- **THE BINOMIAL CONGRUENCE.** `(1 + 3^{j+1}·z)^t = 1 + t·(3^{j+1}·z) +
3^{j+2}·K` for some `K`: the `t`-th power of a near-1 unit moves by exactly
`t` steps of `3^{j+1}` modulo `3^{j+2}`. -/
theorem binom_cong (j t z : Nat) : ∃ K : Nat,
    (1 + 3^(j+1) * z)^t = 1 + t * (3^(j+1) * z) + 3^(j+2) * K := by
  induction t with
  | zero =>
    refine ⟨0, ?_⟩
    rw [Nat.pow_zero]
    ring
  | succ t ih =>
    obtain ⟨K, hK⟩ := ih
    have e1 : (3:Nat)^(j+1) = 3^j * 3 := Nat.pow_succ 3 j
    have e2 : (3:Nat)^(j+2) = 3^j * 9 := by rw [Nat.pow_add]
    rw [Nat.pow_succ, hK]
    refine ⟨K + t * 3^j * z * z + 3^(j+1) * K * z, ?_⟩
    rw [e1, e2]
    ring

/-! ## §3 THE SHIFT LAW — the three children move as a residue system -/

/-- `4^r ≡ 1 mod 3` for every `r` (the rider primitivity). -/
theorem four_pow_mod3 (r : Nat) : (4:Nat)^r % 3 = 1 := by
  induction r with
  | zero => decide
  | succ r ih => rw [Nat.pow_succ, Nat.mul_mod, ih]

/-- **THE SHIFT LAW.** `digit_{j+1}(4^{r + t·3^j}) = (digit_{j+1}(4^r) + t)
mod 3`.  The children `r, r+3^j, r+2·3^j` of a level-`j` node present the
three digit values `d, d+1, d+2` (mod 3) at the new position — exactly one
of them is the dead digit 2. -/
theorem dust_shift (j r t : Nat) :
    digit3 (4^(r + t * 3^j)) (j+1) = (digit3 (4^r) (j+1) + t) % 3 := by
  obtain ⟨c1, hc1, hc1m⟩ := four_pow_3j_struct j
  obtain ⟨K, hK⟩ := binom_cong j t c1
  have e1 : (3:Nat)^(j+1) = 3^j * 3 := Nat.pow_succ 3 j
  have e2 : (3:Nat)^(j+2) = 3^j * 9 := by rw [Nat.pow_add]
  have h4 : 4^(r + t * 3^j) = 4^r * ((4^(3^j))^t) := by
    rw [Nat.mul_comm t (3^j), Nat.pow_add, Nat.pow_mul]
  have hdecomp : 4^(r + t * 3^j)
      = 4^r + 3^(j+1) * (t * c1 * 4^r + 3 * K * 4^r) := by
    rw [h4, hc1, hK, e1, e2]
    ring
  rw [hdecomp, digit_add_mul]
  have h4m : (4:Nat)^r % 3 = 1 := four_pow_mod3 r
  have hmod : (t * c1 * 4^r + 3 * K * 4^r) % 3 = t % 3 := by
    have hW : (c1 * 4^r) % 3 = 1 := by
      rw [Nat.mul_mod, h4m, hc1m]
    have e : t * c1 * 4^r = t * (c1 * 4^r) := by ring
    rw [e, Nat.add_mod]
    rw [Nat.mul_mod]
    rw [hW]
    have hz : (3 * K * 4^r) % 3 = 0 :=
      Nat.mod_eq_zero_of_dvd ⟨K * 4^r, by ring⟩
    rw [hz]
    omega
  rw [hmod]
  omega

/-! ## §4 The period law — the digit is a class function -/

/-- **THE PERIOD LAW.** `digit_q(4^(k + 3^q·m)) = digit_q(4^k)`: the level-`q`
digit of `4^K` depends only on `K mod 3^q`. -/
theorem digit_period (q k m : Nat) :
    digit3 (4^(k + 3^q * m)) q = digit3 (4^k) q := by
  obtain ⟨c1, hc1, _⟩ := four_pow_3j_struct q
  obtain ⟨K, hK⟩ := binom_cong q m c1
  have h4 : 4^(k + 3^q * m) = 4^k * ((4^(3^q))^m) := by
    rw [Nat.pow_add, Nat.pow_mul]
  have e1 : (3:Nat)^(q+1) = 3^q * 3 := Nat.pow_succ 3 q
  have e2 : (3:Nat)^(q+2) = 3^q * 9 := by rw [Nat.pow_add]
  have hdecomp : 4^(k + 3^q * m)
      = 4^k + 3^q * (3 * (m * c1 * 4^k + 3 * K * 4^k)) := by
    rw [h4, hc1, hK, e1, e2]
    ring
  rw [hdecomp, digit_add_mul]
  have h0 : (3 * (m * c1 * 4^k + 3 * K * 4^k)) % 3 = 0 :=
    Nat.mod_eq_zero_of_dvd ⟨m * c1 * 4^k + 3 * K * 4^k, by ring⟩
  have hdig3 : digit3 (4^k) q < 3 := digit3_lt_three _ _
  rw [h0]
  omega

/-! ## §5 THE DUST TREE — the definition and the exact doubling -/

/-- One node's live children: the dead child (the one whose new digit is 2)
is dropped; exactly two survive. -/
def dustStep (j r : Nat) : List Nat :=
  match (digit3 (4^r) (j+1)) % 3 with
  | 0 => [r, r + 3^j]
  | 1 => [r, r + 2 * 3^j]
  | _ => [r + 3^j, r + 2 * 3^j]

/-- The level join (self-contained `++` fold). -/
def dustJoin : Nat → List Nat → List Nat
  | _, [] => []
  | j, r :: rest => dustStep j r ++ dustJoin j rest

/-- The dust tree: the survivor classes at every level. -/
def dust : Nat → List Nat
  | 0 => [0]
  | j+1 => dustJoin j (dust j)

theorem dustJoin_nil (j : Nat) : dustJoin j [] = [] := rfl
theorem dustJoin_cons (j r : Nat) (rest : List Nat) :
    dustJoin j (r :: rest) = dustStep j r ++ dustJoin j rest := rfl
theorem dust_zero_eq : dust 0 = [0] := rfl
theorem dust_succ_eq (j : Nat) : dust (j+1) = dustJoin j (dust j) := rfl

/-- Each node owns exactly two live children. -/
theorem dustStep_length (j r : Nat) : (dustStep j r).length = 2 := by
  have hlt : (digit3 (4^r) (j+1)) % 3 < 3 :=
    Nat.mod_lt _ (show 0 < 3 by decide)
  rcases ErdosTernary2.lt_three_cases _ hlt with h | h | h
  · unfold dustStep; rw [h]; rfl
  · unfold dustStep; rw [h]; rfl
  · unfold dustStep; rw [h]; rfl

/-- The join doubles the count. -/
theorem dustJoin_length (j : Nat) : ∀ l : List Nat,
    (dustJoin j l).length = 2 * l.length := by
  intro l
  induction l with
  | nil => rfl
  | cons r rest ih =>
    rw [dustJoin_cons, List.length_append, dustStep_length, ih,
      List.length_cons]
    omega

/-- **THE EXACT DOUBLING.** The survivor tree doubles at every level,
forever. -/
theorem dust_doubling (j : Nat) : (dust (j+1)).length = 2 * (dust j).length :=
  dustJoin_length j (dust j)

/-- **THE CARDINALITY LAW.** `|alive[j]| = 2^j` at every level, forever. -/
theorem dust_card (j : Nat) : (dust j).length = 2^j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [dust_doubling, ih, Nat.pow_succ]; omega

/-! ## §6 The semantic specification — the tree IS the survivor set -/

/-- The three dustStep value laws: the step list is pinned by the parent's
own new-digit value (the `dustStep_length` idiom, made reusable). -/
theorem dustStep_val0 (j r : Nat) (h : (digit3 (4^r) (j+1)) % 3 = 0) :
    dustStep j r = [r, r + 3^j] := by unfold dustStep; rw [h]; rfl

theorem dustStep_val1 (j r : Nat) (h : (digit3 (4^r) (j+1)) % 3 = 1) :
    dustStep j r = [r, r + 2 * 3^j] := by unfold dustStep; rw [h]; rfl

theorem dustStep_val2 (j r : Nat) (h : (digit3 (4^r) (j+1)) % 3 = 2) :
    dustStep j r = [r + 3^j, r + 2 * 3^j] := by unfold dustStep; rw [h]; rfl

/-- The live children are exactly the children whose new digit is not 2. -/
theorem dustStep_spec (j r t : Nat) (ht : t ≤ 2) :
    (r + t * 3^j ∈ dustStep j r ↔ digit3 (4^(r + t * 3^j)) (j+1) ≠ 2) := by
  have hB : 0 < 3^j := Nat.pow_pos (by decide)
  have hdig : digit3 (4^r) (j+1) < 3 := digit3_lt_three _ _
  have hd3 : (digit3 (4^r) (j+1)) % 3 = digit3 (4^r) (j+1) :=
    Nat.mod_eq_of_lt hdig
  rw [dust_shift, ← hd3]
  rcases ErdosTernary2.lt_three_cases t (by omega) with ht0 | ht1 | ht2
  · -- the t = 0 child: dead exactly when the parent digit is 2
    rw [ht0]
    rcases ErdosTernary2.lt_three_cases ((digit3 (4^r) (j+1)) % 3)
        (Nat.mod_lt _ (show 0 < 3 by decide)) with hd | hd | hd
    · rw [hd, dustStep_val0 j r hd]
      exact ⟨fun _ => by omega,
        fun _ => List.mem_cons.2 (Or.inl (by rw [Nat.zero_mul, Nat.add_zero]))⟩
    · rw [hd, dustStep_val1 j r hd]
      exact ⟨fun _ => by omega,
        fun _ => List.mem_cons.2 (Or.inl (by rw [Nat.zero_mul, Nat.add_zero]))⟩
    · rw [hd, dustStep_val2 j r hd]
      constructor
      · intro hm
        rcases List.mem_cons.1 hm with he | htail
        · exfalso; omega
        · rcases List.mem_cons.1 htail with he | hnil
          · exfalso; omega
          · cases hnil
      · intro hQ
        exact absurd (by decide) hQ
  · -- the t = 1 child: dead exactly when the parent digit is 1
    rw [ht1]
    rcases ErdosTernary2.lt_three_cases ((digit3 (4^r) (j+1)) % 3)
        (Nat.mod_lt _ (show 0 < 3 by decide)) with hd | hd | hd
    · rw [hd, dustStep_val0 j r hd]
      exact ⟨fun _ => by omega,
        fun _ => List.mem_cons.2 (Or.inr
          (List.mem_singleton.2 (by rw [Nat.one_mul])))⟩
    · rw [hd, dustStep_val1 j r hd]
      constructor
      · intro hm
        rcases List.mem_cons.1 hm with he | htail
        · exfalso; omega
        · rcases List.mem_cons.1 htail with he | hnil
          · exfalso; omega
          · cases hnil
      · intro hQ
        exact absurd (by decide) hQ
    · rw [hd, dustStep_val2 j r hd]
      exact ⟨fun _ => by omega,
        fun _ => List.mem_cons.2 (Or.inl (by rw [Nat.one_mul]))⟩
  · -- the t = 2 child: dead exactly when the parent digit is 0
    rw [ht2]
    rcases ErdosTernary2.lt_three_cases ((digit3 (4^r) (j+1)) % 3)
        (Nat.mod_lt _ (show 0 < 3 by decide)) with hd | hd | hd
    · rw [hd, dustStep_val0 j r hd]
      constructor
      · intro hm
        rcases List.mem_cons.1 hm with he | htail
        · exfalso; omega
        · rcases List.mem_cons.1 htail with he | hnil
          · exfalso; omega
          · cases hnil
      · intro hQ
        exact absurd (by decide) hQ
    · rw [hd, dustStep_val1 j r hd]
      exact ⟨fun _ => by omega,
        fun _ => List.mem_cons.2 (Or.inr
          (List.mem_singleton.2 rfl))⟩
    · rw [hd, dustStep_val2 j r hd]
      exact ⟨fun _ => by omega,
        fun _ => List.mem_cons.2 (Or.inr
          (List.mem_singleton.2 rfl))⟩

/-- Membership in the join. -/
theorem dustJoin_mem (j : Nat) : ∀ (l : List Nat) (r : Nat),
    (r ∈ dustJoin j l ↔ ∃ r₀ : Nat, r₀ ∈ l ∧ r ∈ dustStep j r₀) := by
  intro l
  induction l with
  | nil =>
    intro r
    rw [dustJoin_nil]
    simp
  | cons r₁ rest ih =>
    intro r
    rw [dustJoin_cons, List.mem_append]
    constructor
    · intro hm
      rcases hm with h | h
      · exact ⟨r₁, List.mem_cons.2 (Or.inl rfl), h⟩
      · obtain ⟨r₀, hr₀, hr⟩ := (ih r |>.1) h
        exact ⟨r₀, List.mem_cons.2 (Or.inr hr₀), hr⟩
    · intro ⟨r₀, hr₀, hr⟩
      rcases List.mem_cons.1 hr₀ with he | hrest
      · rw [he] at hr
        exact Or.inl hr
      · exact Or.inr ((ih r |>.2) ⟨r₀, hrest, hr⟩)

/-! ## §7 THE FULL SPECIFICATION and the rider corollary -/

/-- **THE FULL SPEC.** The tree at level `j` is exactly the survivor set:
`r ∈ dust j ↔ r < 3^j ∧ every digit3 (4^r) q (q ≤ j) ≠ 2`. -/
theorem dust_spec (j : Nat) : ∀ r : Nat,
    (r ∈ dust j ↔ r < 3^j ∧ ∀ q ≤ j, digit3 (4^r) q ≠ 2) := by
  induction j with
  | zero =>
    intro r
    constructor
    · intro hm
      have hr : r = 0 := by simpa [dust] using hm
      refine ⟨by omega, ?_⟩
      intro q _
      rw [hr, Nat.pow_zero]
      show (1 / 3^q) % 3 ≠ 2
      match q with
      | .zero => decide
      | .succ q =>
        have hq : 3 ≤ 3^(q+1) := by
          have hp : 0 < 3^q := Nat.pow_pos (by decide)
          have hps := Nat.pow_succ 3 q
          omega
        have hd : 1 / 3^(q+1) = 0 := Nat.div_eq_of_lt (by omega)
        rw [hd]; omega
    · intro ⟨hlt, _⟩
      have hr : r = 0 := by omega
      rw [hr]
      exact List.mem_singleton.2 rfl
  | succ j ih =>
    intro r
    have hB : 0 < 3^j := Nat.pow_pos (by decide)
    have hB1 : (3:Nat)^(j+1) = 3 * 3^j := by rw [Nat.pow_succ]; ring
    rw [dust_succ_eq, dustJoin_mem]
    constructor
    · intro ⟨r₀, hr₀, hstep⟩
      obtain ⟨t, ht, hrt⟩ :
          ∃ t : Nat, t ≤ 2 ∧ r = r₀ + t * 3^j := by
        unfold dustStep at hstep
        rcases ErdosTernary2.lt_three_cases
          ((digit3 (4^r₀) (j+1)) % 3) (Nat.mod_lt _ (show 0 < 3 by decide)) with
          hd | hd | hd
        · rw [hd] at hstep
          rcases List.mem_cons.1 hstep with he | htail
          · exact ⟨0, by omega, by rw [he, Nat.zero_mul, Nat.add_zero]⟩
          · have he := List.mem_singleton.1 htail
            exact ⟨1, by omega, by omega⟩
        · rw [hd] at hstep
          rcases List.mem_cons.1 hstep with he | htail
          · exact ⟨0, by omega, by rw [he, Nat.zero_mul, Nat.add_zero]⟩
          · have he := List.mem_singleton.1 htail
            exact ⟨2, by omega, by omega⟩
        · rw [hd] at hstep
          rcases List.mem_cons.1 hstep with he | htail
          · exact ⟨1, by omega, by omega⟩
          · have he := List.mem_singleton.1 htail
            exact ⟨2, by omega, by omega⟩
      have hbound : t * 3^j ≤ 2 * 3^j := Nat.mul_le_mul_right _ ht
      have hparent₀ := (ih r₀ |>.1 hr₀).1
      refine ⟨by omega, ?_⟩
      intro q hq
      rcases Nat.lt_or_ge q (j+1) with hqj | hqj
      · -- q ≤ j: the period law
        obtain ⟨d, hd⟩ : ∃ d, j = q + d := ⟨j - q, by omega⟩
        have hpe : 3^j = 3^q * 3^d := by rw [hd, Nat.pow_add]
        have hsplit : r = r₀ + 3^q * (t * 3^d) := by
          have hp2 : 3^q * (t * 3^d) = t * 3^j := by rw [hpe]; ring
          rw [hrt]
          omega
        have hdig₀ := (ih r₀ |>.1 hr₀).2 q (by omega)
        rw [hsplit, digit_period q r₀ (t * 3^d)]
        exact hdig₀
      · -- q = j+1: the step spec
        have hqe : q = j+1 := by omega
        rw [hqe, hrt]
        have hstep' : r₀ + t * 3^j ∈ dustStep j r₀ := by
          rw [← hrt]; exact hstep
        exact (dustStep_spec j r₀ t ht |>.1) hstep'
    · intro ⟨hlt, hdig⟩
      -- split r into its parent class and child index
      have hdm : 3^j * (r / 3^j) + r % 3^j = r := Nat.div_add_mod r (3^j)
      have hmodlt : r % 3^j < 3^j := Nat.mod_lt _ hB
      have htb : r / 3^j < 3 := by
        by_contra hc
        push_neg at hc
        have hle : 3 * 3^j ≤ (r / 3^j) * 3^j :=
          Nat.mul_le_mul hc (Nat.le_refl _)
        have hle2 : (3:Nat)^(j+1) ≤ 3^j * (r / 3^j) := by
          rw [hB1]
          calc 3 * 3^j ≤ (r / 3^j) * 3^j := hle
            _ = 3^j * (r / 3^j) := Nat.mul_comm _ _
        omega
      have ht : r / 3^j ≤ 2 := by omega
      have hchild : (r % 3^j) + (r / 3^j) * 3^j = r := by
        have hcomm : (r / 3^j) * 3^j = 3^j * (r / 3^j) := Nat.mul_comm _ _
        omega
      refine ⟨r % 3^j, ?_, ?_⟩
      · -- parent membership: its digits below j+1 match r's
        refine (ih (r % 3^j) |>.2) ⟨hmodlt, ?_⟩
        intro q hq
        obtain ⟨d, hd⟩ : ∃ d, j = q + d := ⟨j - q, by omega⟩
        have hpe : 3^j = 3^q * 3^d := by rw [hd, Nat.pow_add]
        have hperiod := digit_period q (r % 3^j) ((r / 3^j) * 3^d)
        have hrew : (r % 3^j) + 3^q * ((r / 3^j) * 3^d) = r := by
          have hp2 : 3^q * ((r / 3^j) * 3^d) = 3^j * (r / 3^j) := by
            rw [hpe]; ring
          omega
        rw [hrew] at hperiod
        rw [← hperiod]
        exact hdig q (by omega)
      · -- the child membership: the new digit is not 2
        have hmem : (r % 3^j) + (r / 3^j) * 3^j ∈ dustStep j (r % 3^j) :=
          (dustStep_spec j (r % 3^j) (r / 3^j) ht |>.2) (by
            rw [hchild]
            exact hdig (j+1) (by omega))
        rw [hchild] at hmem
        exact hmem

/-- **THE RIDER COROLLARY.** Every `K` whose `4^K` has only 0/1 ternary
digits (the rider condition, in digit form) is a member of the dust tree
at every level `j` with `3^j > K`: the riders are the integer points of the
tree. -/
theorem dust_rider_classes (K j : Nat) (hj : K < 3^j)
    (hDigits : ∀ q, digit3 (4^K) q ≠ 2) : K ∈ dust j :=
  (dust_spec j K |>.2) ⟨hj, fun q _ => hDigits q⟩

/-! ## §7b THE DUST-EDGE THEOREM (S077, the Strategist's Frame D) -/

/-- The unit digit is the residue. -/
theorem digit3_zero (n : Nat) : digit3 n 0 = n % 3 := by
  unfold digit3
  rw [Nat.pow_zero, Nat.div_one]

/-- The digit shift law: the digits of `n / 3` are the digits of `n` above
position zero. -/
theorem digit3_succ (n M : Nat) : digit3 n (M+1) = digit3 (n / 3) M := by
  unfold digit3
  rw [show (3:Nat)^(M+1) = 3 * 3^M from by rw [Nat.pow_succ]; ring,
    ← Nat.div_div_eq_div_mul]

/-- The power monotonicity law, self-contained (the pin's
`Nat.pow_le_pow_right` drift avoided). -/
theorem three_pow_le_of_le (a b : Nat) (h : a ≤ b) : 3^a ≤ 3^b := by
  obtain ⟨d, hd⟩ : ∃ d : Nat, b = a + d := ⟨b - a, by omega⟩
  rw [hd, Nat.pow_add]
  have hp : 0 < 3^d := Nat.pow_pos (by decide)
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
  rfl

/-- Every number whose ternary digits avoid 2 passes the Cantor verdict
(the verdict bridge). -/
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

/-- **THE DUST-EDGE THEOREM.** A dust member whose power fits inside `j+1`
ternary digits is a rider outright: `noTernaryTwo (4^r) = true`. Composed
with the Kernel-38 census (in `noTernaryTwo` form — the named bridge lane),
this pins `dust j ∩ [0, 0.79·j)` to the three known riders at every level
— the first infinite-family anti-clustering law. -/
theorem dust_edge (j r : Nat) (hdust : r ∈ dust j) (hsmall : 4^r < 3^(j+1)) :
    noTernaryTwo (4^r) = true := by
  obtain ⟨_, hdig⟩ := dust_spec j r |>.1 hdust
  refine noTernaryTwo_of_digits _ (fun q => ?_)
  rcases Nat.lt_or_ge q (j+1) with hq | hq
  · exact hdig q (by omega)
  · have h0 : digit3 (4^r) q = 0 := digit3_of_lt (4^r) j q hsmall (by omega)
    rw [h0]
    omega

/-! ## §8 The receipts -/

#check digit_add_mul
#check four_pow_3j_struct
#check binom_cong
#check four_pow_mod3
#check dust_shift
#check digit_period
#check dustStep_length
#check dustJoin_length
#check dust_doubling
#check dust_card
#check dustStep_spec
#check dustJoin_mem
#check dust_spec
#check dust_rider_classes
#check dust_edge

#print axioms digit_add_mul
#print axioms four_pow_3j_struct
#print axioms binom_cong
#print axioms four_pow_mod3
#print axioms dust_shift
#print axioms digit_period
#print axioms dustStep_length
#print axioms dustJoin_length
#print axioms dust_doubling
#print axioms dust_card
#print axioms dustStep_spec
#print axioms dustJoin_mem
#print axioms dust_spec
#print axioms dust_rider_classes
#print axioms dust_edge

-- Level receipts (kernel-decided, matching the Python census):
theorem dust_1_receipt : dust 1 = [0, 1] := by decide
theorem dust_2_receipt : dust 2 = [0, 3, 1, 4] := by decide
theorem dust_3_receipt : dust 3 = [0, 9, 12, 21, 1, 10, 4, 13] := by decide
