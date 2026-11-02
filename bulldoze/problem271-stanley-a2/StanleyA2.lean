/-
# ERDŐS #271 — THE STANLEY SEQUENCE S(0,2): COMPLETE CHARACTERIZATION

The greedy 3-term-arithmetic-progression-free sequence seeded with {0, 2}
(the Stanley sequence A(2)) admits the exact closed form

    A(2) = { 3m + d  :  m ∈ C,  d ∈ {0, 2} },

where C is the Cantor set of nonnegative integers carrying no ternary
digit 2.  Membership is decided by the digit predicate

    inD m  ↔  (m % 3 ∈ {0, 2})  ∧  noTwo (m / 3).

## Proof architecture (the Cantor top-witness engine)

* §1  `noTwo` — the Cantor predicate (well-founded digit recursion).
* §2  `inD`  — the digit predicate for A(2); intro/elim plumbing.
* §3  Cantor AP-freeness — mod-3 digit descent: of the eight digit
  triples in {0,1}³ only (0,0,0) and (1,1,1) survive x + z ≡ 2y
  (mod 3); both descend to a strictly smaller AP of quotients.
* §4  A(2) AP-freeness — digit triples in {0,2}: only (0,0,0) and
  (2,2,2) survive; each collapses in ONE step onto a Cantor AP.
* §5  Cantor maximality (the C-witness): every m ≥ 2 outside C is
  blocked by a pair below it — direct witness at the lowest offending
  digit, otherwise lifted from the quotient by offset-normalized
  stepping (r = 0: ⟨3a, 3b⟩, r = 1: ⟨3a+1, 3b+1⟩, r = 2: ⟨3a, 3b+1⟩).
* §6  A(2) maximality (the top witness): every m ≥ 3 outside D is
  blocked — the m ≡ 1 (mod 3) face uses the self-pair ⟨3r, 3r+2⟩ at
  r = m/3 − 1 (or a C-lift when r ∉ C); the r ∈ {0,2} faces lift the
  C-witness of the quotient by ⟨3a, 3b⟩ / ⟨3a+2, 3b+2⟩.
* §7  The greedy oracle `gp f m` (fuel f) scans blocking pairs exactly
  as the Stanley greedy does.
* §8  Headline: `stanley_a2_greedy (m : Nat) : gp m m = inD m`.

Core Lean 4 only.  No Mathlib.  No `sorry`.  No custom axioms.
-/

-- ===========================================================================
-- §0  DIVISION HELPERS
-- ===========================================================================

theorem div3_mul3 (x : Nat) : (3 * x) / 3 = x := by omega

theorem div3_mul3_add1 (x : Nat) : (3 * x + 1) / 3 = x := by omega

theorem div3_mul3_add2 (x : Nat) : (3 * x + 2) / 3 = x := by omega

-- ===========================================================================
-- §1  THE CANTOR PREDICATE
-- ===========================================================================

/-- `noTwo n = true` iff no ternary digit of `n` equals 2. -/
def noTwo : Nat → Bool
  | 0 => true
  | n + 1 => if (n + 1) % 3 = 2 then false else noTwo ((n + 1) / 3)
termination_by n => n
decreasing_by omega

theorem noTwo_intro (n : Nat) (h1 : n % 3 ≠ 2) (h2 : noTwo (n / 3) = true) :
    noTwo n = true := by
  cases n with
  | zero => simp [noTwo]
  | succ k =>
    simp only [noTwo]
    rw [if_neg (by omega : (k + 1) % 3 ≠ 2)]
    exact h2

theorem noTwo_true_inv (n : Nat) (h : noTwo n = true) :
    n % 3 ≠ 2 ∧ noTwo (n / 3) = true := by
  cases n with
  | zero => exact ⟨by omega, by simp [noTwo]⟩
  | succ k =>
    simp only [noTwo] at h
    split at h
    · exact absurd h Bool.false_ne_true
    · next c => exact ⟨c, h⟩

theorem noTwo_false_inv (n : Nat) (h : noTwo n = false) :
    n % 3 = 2 ∨ noTwo (n / 3) = false := by
  cases n with
  | zero => exact absurd h (by simp [noTwo])
  | succ k =>
    simp only [noTwo] at h
    split at h
    · left; assumption
    · right; exact h

theorem noTwo_small (m : Nat) (hm : m ≤ 1) : noTwo m = true := by
  cases m with
  | zero => simp [noTwo]
  | succ k =>
    cases k with
    | zero => simp [noTwo]
    | succ k' => omega

/-- Everything outside the Cantor set is at least 2. -/
theorem noTwo_false_ge (m : Nat) (h : noTwo m = false) : 2 ≤ m := by
  by_cases hm : m ≤ 1
  · rw [noTwo_small m hm] at h
    exact absurd h (by simp)
  · omega

-- ===========================================================================
-- §2  THE DIGIT PREDICATE FOR A(2)
-- ===========================================================================

/-- `inD m = true` iff m lies in A(2) = {3m + d : m ∈ C, d ∈ {0,2}}. -/
def inD (m : Nat) : Bool :=
  if m % 3 = 0 ∨ m % 3 = 2 then noTwo (m / 3) else false

theorem inD_intro (m : Nat) (h1 : m % 3 = 0 ∨ m % 3 = 2)
    (h2 : noTwo (m / 3) = true) : inD m = true := by
  simp only [inD]
  rw [if_pos h1]
  exact h2

theorem inD_elim (m : Nat) (h : inD m = true) :
    (m % 3 = 0 ∨ m % 3 = 2) ∧ noTwo (m / 3) = true := by
  simp only [inD] at h
  split at h
  · next c => exact ⟨c, h⟩
  · exact absurd h Bool.false_ne_true

theorem inD_false_inv (m : Nat) (h : inD m = false) :
    m % 3 = 1 ∨ noTwo (m / 3) = false := by
  simp only [inD] at h
  split at h
  · right; exact h
  · next c => left; omega

-- ===========================================================================
-- §3  CANTOR AP-FREENESS (mod-3 digit descent)
-- ===========================================================================

/-- No nontrivial 3-term AP lies in the Cantor set.  Fuel induction. -/
theorem noTwo_no_ap_fuel : ∀ (f x y z : Nat), z ≤ f →
    noTwo x = true → noTwo y = true → noTwo z = true →
    x + z = 2 * y → x < z → False
  | 0, _, _, z, hzf, _, _, _, _, hlt => by omega
  | f + 1, x, y, z, hzf, hx, hy, hz, hsum, hlt => by
    have ex := noTwo_true_inv x hx
    have ey := noTwo_true_inv y hy
    have ez := noTwo_true_inv z hz
    have key : (x % 3 = 0 ∧ y % 3 = 0 ∧ z % 3 = 0) ∨
        (x % 3 = 1 ∧ y % 3 = 1 ∧ z % 3 = 1) := by omega
    cases key with
    | inl k =>
      exact noTwo_no_ap_fuel f (x / 3) (y / 3) (z / 3) (by omega)
        ex.2 ey.2 ez.2 (by omega) (by omega)
    | inr k =>
      exact noTwo_no_ap_fuel f (x / 3) (y / 3) (z / 3) (by omega)
        ex.2 ey.2 ez.2 (by omega) (by omega)

/-- No nontrivial 3-term AP lies in the Cantor set (fuel-free form). -/
theorem noTwo_no_ap (x y z : Nat) (hx : noTwo x = true) (hy : noTwo y = true)
    (hz : noTwo z = true) (hsum : x + z = 2 * y) (hlt : x < z) : False :=
  noTwo_no_ap_fuel z x y z (Nat.le_refl _) hx hy hz hsum hlt

-- ===========================================================================
-- §4  A(2) AP-FREENESS (one-step collapse onto a Cantor AP)
-- ===========================================================================

/-- No nontrivial 3-term AP lies in A(2). -/
theorem inD_no_ap (x y z : Nat) (hx : inD x = true) (hy : inD y = true)
    (hz : inD z = true) (hsum : x + z = 2 * y) (hlt : x < z) : False := by
  have ex := inD_elim x hx
  have ey := inD_elim y hy
  have ez := inD_elim z hz
  have key : (x % 3 = 0 ∧ y % 3 = 0 ∧ z % 3 = 0) ∨
      (x % 3 = 2 ∧ y % 3 = 2 ∧ z % 3 = 2) := by omega
  cases key with
  | inl k =>
    exact noTwo_no_ap (x / 3) (y / 3) (z / 3) ex.2 ey.2 ez.2 (by omega)
      (by omega)
  | inr k =>
    exact noTwo_no_ap (x / 3) (y / 3) (z / 3) ex.2 ey.2 ez.2 (by omega)
      (by omega)

-- ===========================================================================
-- §5  CANTOR MAXIMALITY (the C-witness, offset-normalized stepping)
-- ===========================================================================

/-- Every m ≥ 2 outside the Cantor set is blocked: some Cantor pair
a < b < m straddles it in an AP (a, b, m).  Fuel induction. -/
theorem cBlocked_fuel : ∀ (f m : Nat), m ≤ f → 2 ≤ m → noTwo m = false →
    ∃ a b, a < b ∧ b < m ∧ noTwo a = true ∧ noTwo b = true ∧ a + m = 2 * b
  | 0, m, hm, h2, _ => by omega
  | f + 1, m, hm, h2, hn => by
    by_cases hq : noTwo (m / 3) = false
    · -- LIFT FACE: the quotient is outside C; recurse and lift by m % 3.
      have hq2 : 2 ≤ m / 3 := noTwo_false_ge _ hq
      have hqle : m / 3 ≤ f := by omega
      have ⟨a, b, h1, h2', h3', h4', h5'⟩ := cBlocked_fuel f (m / 3) hqle hq2 hq
      have hr : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by omega
      cases hr with
      | inl hr =>
        refine ⟨3 * a, 3 * b, by omega, by omega, ?_, ?_, by omega⟩
        · exact noTwo_intro _ (by omega) (by rw [div3_mul3]; exact h3')
        · exact noTwo_intro _ (by omega) (by rw [div3_mul3]; exact h4')
      | inr hr =>
        cases hr with
        | inl hr =>
          refine ⟨3 * a + 1, 3 * b + 1, by omega, by omega, ?_, ?_, by omega⟩
          · exact noTwo_intro _ (by omega) (by rw [div3_mul3_add1]; exact h3')
          · exact noTwo_intro _ (by omega) (by rw [div3_mul3_add1]; exact h4')
        | inr hr =>
          refine ⟨3 * a, 3 * b + 1, by omega, by omega, ?_, ?_, by omega⟩
          · exact noTwo_intro _ (by omega) (by rw [div3_mul3]; exact h3')
          · exact noTwo_intro _ (by omega) (by rw [div3_mul3_add1]; exact h4')
    · -- DIRECT FACE: the quotient is in C, so the units digit is the offense.
      have hc : m % 3 = 2 := by
        cases noTwo_false_inv m hn with
        | inl h => exact h
        | inr h => exact absurd h hq
      have hqt : noTwo (m / 3) = true := by
        cases hbb : noTwo (m / 3) with
        | true => rfl
        | false => exact absurd hbb hq
      refine ⟨3 * (m / 3), 3 * (m / 3) + 1, by omega, by omega, ?_, ?_,
        by omega⟩
      · exact noTwo_intro _ (by omega) (by rw [div3_mul3]; exact hqt)
      · exact noTwo_intro _ (by omega) (by rw [div3_mul3_add1]; exact hqt)

-- ===========================================================================
-- §6  A(2) MAXIMALITY (the top witness)
-- ===========================================================================

/-- Every m ≥ 3 outside A(2) is blocked by an A(2)-pair below it. -/
theorem dBlocked (m : Nat) (hm : 3 ≤ m) (hd : inD m = false) :
    ∃ a b, a < b ∧ b < m ∧ inD a = true ∧ inD b = true ∧ a + m = 2 * b := by
  by_cases hr1 : m % 3 = 1
  · -- SELF-PAIR FACE: the witness lives at r = m/3 − 1.
    by_cases hs : noTwo (m / 3 - 1) = true
    · -- the self-pair ⟨3r, 3r+2⟩ itself
      refine ⟨3 * (m / 3 - 1), 3 * (m / 3 - 1) + 2, by omega, by omega, ?_,
        ?_, by omega⟩
      · exact inD_intro _ (Or.inl (by omega))
          (by rw [div3_mul3]; exact hs)
      · exact inD_intro _ (Or.inr (by omega))
          (by rw [div3_mul3_add2]; exact hs)
    · -- C-lift: r = m/3 − 1 is outside C
      have hsf : noTwo (m / 3 - 1) = false := by
        cases hbb : noTwo (m / 3 - 1) with
        | false => rfl
        | true => exact absurd hbb hs
      have hsge : 2 ≤ m / 3 - 1 := noTwo_false_ge _ hsf
      have ⟨a, b, h1, h2', h3', h4', h5'⟩ :=
        cBlocked_fuel (m / 3 - 1) (m / 3 - 1) (Nat.le_refl _) hsge hsf
      refine ⟨3 * a, 3 * b + 2, by omega, by omega, ?_, ?_, by omega⟩
      · exact inD_intro _ (Or.inl (by omega)) (by rw [div3_mul3]; exact h3')
      · exact inD_intro _ (Or.inr (by omega)) (by rw [div3_mul3_add2]; exact h4')
  · -- LIFT FACE: m % 3 ∈ {0, 2} and the quotient is outside C.
    have hcf : noTwo (m / 3) = false := by
      by_cases hx : m % 3 = 0 ∨ m % 3 = 2
      · simp only [inD] at hd
        rw [if_pos hx] at hd
        exact hd
      · omega
    have hq2 : 2 ≤ m / 3 := noTwo_false_ge _ hcf
    have ⟨a, b, h1, h2', h3', h4', h5'⟩ :=
      cBlocked_fuel (m / 3) (m / 3) (Nat.le_refl _) hq2 hcf
    by_cases hr : m % 3 = 0
    · refine ⟨3 * a, 3 * b, by omega, by omega, ?_, ?_, by omega⟩
      · exact inD_intro _ (Or.inl (by omega)) (by rw [div3_mul3]; exact h3')
      · exact inD_intro _ (Or.inl (by omega)) (by rw [div3_mul3]; exact h4')
    · refine ⟨3 * a + 2, 3 * b + 2, by omega, by omega, ?_, ?_, by omega⟩
      · exact inD_intro _ (Or.inr (by omega)) (by rw [div3_mul3_add2]; exact h3')
      · exact inD_intro _ (Or.inr (by omega)) (by rw [div3_mul3_add2]; exact h4')

-- ===========================================================================
-- §7  THE GREEDY ORACLE
-- ===========================================================================

/-- `someBelow n f m t = true` iff some a < n with a < t, f a, a + m = 2*t. -/
def someBelow : Nat → (Nat → Bool) → Nat → Nat → Bool
  | 0, _, _, _ => false
  | n + 1, f, m, t =>
    (decide (n < t) && (f n && decide (n + m = 2 * t))) || someBelow n f m t

/-- `scanPairs n f m = true` iff some pair a < b ≤ n with f a, f b,
a + m = 2*b. -/
def scanPairs : Nat → (Nat → Bool) → Nat → Bool
  | 0, _, _ => false
  | n + 1, f, m =>
    (f (n + 1) && someBelow (n + 1) f m (n + 1)) || scanPairs n f m

/-- `anyBlocker m f = true` iff some pair a < b < m with f a, f b
blocks m ( a + m = 2 * b ). -/
def anyBlocker (m : Nat) (f : Nat → Bool) : Bool :=
  match m with
  | 0 => false
  | m' + 1 => scanPairs m' f (m' + 1)

theorem someBelow_congr : ∀ (n : Nat) (f g : Nat → Bool) (m t : Nat),
    (∀ x, x < n → f x = g x) → someBelow n f m t = someBelow n g m t
  | 0, _, _, _, _, _ => rfl
  | n + 1, f, g, m, t, h => by
    simp only [someBelow]
    rw [h n (by omega), someBelow_congr n f g m t (fun x hx => h x (by omega))]

theorem scanPairs_congr : ∀ (n : Nat) (f g : Nat → Bool) (m : Nat),
    (∀ x, x ≤ n → f x = g x) → scanPairs n f m = scanPairs n g m
  | 0, _, _, _, _ => rfl
  | n + 1, f, g, m, h => by
    simp only [scanPairs]
    rw [h (n + 1) (Nat.le_refl _),
      someBelow_congr (n + 1) f g m (n + 1) (fun x hx => h x (by omega)),
      scanPairs_congr n f g m (fun x hx => h x (by omega))]

theorem anyBlocker_congr (m : Nat) (f g : Nat → Bool)
    (h : ∀ x, x < m → f x = g x) : anyBlocker m f = anyBlocker m g := by
  cases m with
  | zero => rfl
  | succ m' =>
    show scanPairs m' f (m' + 1) = scanPairs m' g (m' + 1)
    exact scanPairs_congr m' f g (m' + 1) (fun x hx => h x (by omega))

theorem someBelow_true : ∀ (n : Nat) (f : Nat → Bool) (m t : Nat),
    someBelow n f m t = true ↔
    ∃ a, a < n ∧ a < t ∧ f a = true ∧ a + m = 2 * t
  | 0, _, _, _ => by
    simp [someBelow]
  | n + 1, f, m, t => by
    simp only [someBelow]
    rw [Bool.or_eq_true]
    constructor
    · intro h
      cases h with
      | inl h1 =>
        rw [Bool.and_eq_true, Bool.and_eq_true] at h1
        exact ⟨n, by omega, of_decide_eq_true h1.1, h1.2.1,
          of_decide_eq_true h1.2.2⟩
      | inr h2 =>
        have ⟨a, ha1, ha2, ha3, ha4⟩ := (someBelow_true n f m t).mp h2
        exact ⟨a, by omega, ha2, ha3, ha4⟩
    · intro h
      have ⟨a, ha1, ha2, ha3, ha4⟩ := h
      have hac : a < n ∨ a = n := by omega
      cases hac with
      | inl hl =>
        exact Or.inr ((someBelow_true n f m t).mpr ⟨a, hl, ha2, ha3, ha4⟩)
      | inr hr =>
        subst hr
        apply Or.inl
        rw [Bool.and_eq_true, Bool.and_eq_true]
        exact ⟨decide_eq_true ha2, ⟨ha3, decide_eq_true ha4⟩⟩

theorem scanPairs_true : ∀ (n : Nat) (f : Nat → Bool) (m : Nat),
    scanPairs n f m = true ↔
    ∃ a b, a < b ∧ b ≤ n ∧ f a = true ∧ f b = true ∧ a + m = 2 * b
  | 0, _, _ => by
    constructor
    · intro h
      exact absurd h (show ¬(scanPairs 0 _ _ = true) from by simp [scanPairs])
    · intro h
      have ⟨a, b, h1, h2, _, _, _⟩ := h
      have hf : False := by omega
      exact hf.elim
  | n + 1, f, m => by
    simp only [scanPairs]
    rw [Bool.or_eq_true, Bool.and_eq_true]
    constructor
    · intro h
      cases h with
      | inl h1 =>
        have ⟨a, ha1, ha2, ha3, ha4⟩ :=
          (someBelow_true (n + 1) f m (n + 1)).mp h1.2
        exact ⟨a, n + 1, ha1, Nat.le_refl _, ha3, h1.1, ha4⟩
      | inr h2 =>
        have ⟨a, b, h1, h2', h3, h4, h5⟩ := (scanPairs_true n f m).mp h2
        exact ⟨a, b, h1, by omega, h3, h4, h5⟩
    · intro h
      have ⟨a, b, h1, h2', h3, h4, h5⟩ := h
      have hbc : b < n + 1 ∨ b = n + 1 := by omega
      cases hbc with
      | inl hl =>
        exact Or.inr
          ((scanPairs_true n f m).mpr ⟨a, b, h1, by omega, h3, h4, h5⟩)
      | inr hr =>
        subst hr
        apply Or.inl
        exact ⟨h4, (someBelow_true (n + 1) f m (n + 1)).mpr
          ⟨a, h1, h1, h3, h5⟩⟩

theorem anyBlocker_true (m : Nat) (f : Nat → Bool) :
    anyBlocker m f = true ↔
    ∃ a b, a < b ∧ b < m ∧ f a = true ∧ f b = true ∧ a + m = 2 * b := by
  cases m with
  | zero => simp [anyBlocker]
  | succ m' =>
    simp only [anyBlocker]
    refine (scanPairs_true m' f (m' + 1)).trans ?_
    apply Iff.intro
    · intro h
      have ⟨a, b, h1, h2, h3, h4, h5⟩ := h
      exact ⟨a, b, h1, by omega, h3, h4, h5⟩
    · intro h
      have ⟨a, b, h1, h2, h3, h4, h5⟩ := h
      exact ⟨a, b, h1, by omega, h3, h4, h5⟩

/-- The greedy membership oracle: `gp f m` decides membership of m in the
Stanley sequence S(0,2) with `f` steps of fuel. -/
def gp : Nat → Nat → Bool
  | 0, m => decide (m = 0 ∨ m = 2)
  | f + 1, m =>
    if m < 3 then decide (m = 0 ∨ m = 2)
    else !(anyBlocker m (fun x => gp f x))

theorem gp_correct : ∀ (f m : Nat), m ≤ f → gp f m = inD m
  | 0, m, hm => by
    have hm0 : m = 0 := by omega
    subst hm0
    simp [gp, inD, noTwo]
  | f + 1, m, hm => by
    by_cases hm3 : m < 3
    · have hm012 : m = 0 ∨ m = 1 ∨ m = 2 := by omega
      cases hm012 with
      | inl h => subst h; simp [gp, inD, noTwo]
      | inr h =>
        cases h with
        | inl h => subst h; simp [gp, inD]
        | inr h => subst h; simp [gp, inD, noTwo]
    · show (if m < 3 then decide (m = 0 ∨ m = 2)
          else !(anyBlocker m (fun x => gp f x))) = inD m
      rw [if_neg hm3]
      have hcongr : anyBlocker m (fun x => gp f x) = anyBlocker m (fun x => inD x) :=
        anyBlocker_congr m _ _ (fun x hx => gp_correct f x (by omega))
      have hm3' : 3 ≤ m := by omega
      have hab : anyBlocker m (fun x => inD x) = !(inD m) := by
        cases hb : inD m with
        | true =>
          have hnone : anyBlocker m (fun x => inD x) = false := by
            cases hbb : anyBlocker m (fun x => inD x) with
            | false => rfl
            | true =>
              have ⟨a, b, h1, h2, h3, h4, h5⟩ := (anyBlocker_true m _).mp hbb
              exact (inD_no_ap a b m h3 h4 hb h5 (by omega)).elim
          rw [hnone]
          decide
        | false =>
          have ⟨a, b, h1, h2, h3, h4, h5⟩ := dBlocked m hm3' hb
          rw [(anyBlocker_true m _).mpr ⟨a, b, h1, h2, h3, h4, h5⟩]
          decide
      rw [hcongr, hab, Bool.not_not]

-- ===========================================================================
-- §8  THE HEADLINE
-- ===========================================================================

/-- **Erdős #271 (Stanley S(0,2))**: the greedy oracle with full fuel
agrees exactly with the Cantor digit predicate — the Stanley sequence
seeded at {0, 2} is {3m + d : m ∈ C, d ∈ {0,2}}. -/
theorem stanley_a2_greedy (m : Nat) : gp m m = inD m :=
  gp_correct m m (Nat.le_refl m)

-- ===========================================================================
-- RECEIPTS
-- ===========================================================================

-- The first 16 members of A(2) below 45: exact closed-form enumeration.
#eval (List.range 45).filter inD
-- expected: [0, 2, 3, 5, 9, 11, 12, 14, 27, 29, 30, 32, 36, 38, 39, 41]

-- |A(2) ∩ [0, 3^k)| = 2^k exactly, for k ≤ 7.
#eval (List.range 8).map (fun k =>
  ((List.range (3 ^ k)).filter inD).length)
-- expected: [1, 2, 4, 8, 16, 32, 64, 128]

#print axioms stanley_a2_greedy
#print axioms inD_no_ap
#print axioms dBlocked
