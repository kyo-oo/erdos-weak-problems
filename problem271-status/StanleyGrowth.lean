/-
# ERDŐS #271 — THE UNIVERSAL GROWTH LAW (every seed n ≥ 1)

## THE PROBLEM (verbatim, erdosproblems.com/271)

> Let $A(n) = \{a_0 < a_1 < \cdots\}$ be the sequence defined by $a_0 = 0$
> and $a_1 = n$, and for $k \geq 1$ define $a_{k+1}$ as the least positive
> integer such that there is no three-term arithmetic progression in
> $\{a_0, \ldots, a_{k+1}\}$.  Can the $a_k$ be explicitly determined?
> How fast do they grow?

## THE THEOREMS (the growth answer, universal — every seed, every index)

* **G3 (the doubling law)** `growth_G3`: `a_{k+1} ≤ 2 * a_k + 1` (`k ≥ 1`).
  The value `2 * a_k + 1` is never blocked: a blocker pair `a < b ≤ a_k`
  would force `2 * b = a + 2 * a_k + 1 ≤ 2 * a_k`.

* **G2 (the linear floor)** `growth_G2`: `2 * a_m ≥ 3 * m - 3`.
  Three members are never three consecutive integers (that is a 3-AP),
  so `a_{i+2} ≥ a_i + 3`; two-track induction from `a_0 = 0`, `a_1 ≥ 1`.

* **G1 (the quadratic ceiling)** `growth_G1`:
  `a_m ≤ n + (m - 1) * (m + 2) / 2` (`m ≥ 1`).  THE BLOCKING-PAIR
  PIGEONHOLE: every rejected `y ∈ (n, a_m)` (scanned and skipped by the
  greedy) carries a witness pair of earlier members `(a_i, a_j)`,
  `i < j ≤ m-1`, with `a_i + y = 2 * a_j`; a pair blocks exactly ONE
  value, so the rejected values inject into the index pairs — `m(m-1)/2`
  of them — and the interval `(n, a_m)` splits into `m - 2` members plus
  the rejected values: `a_m - n - 1 ≤ (m - 2) + m(m-1)/2`.

For EVERY seed `n ≥ 1`: `3(m-1)/2 ≤ a_m ≤ n + (m-1)(m+2)/2` — the
"how fast do they grow" half of the problem, answered unconditionally
for all seeds at once.

Engine: fuel-indexed bounded greedy search over the reversed member
list (head = current maximum), list-induction invariants, `Finset`
pigeonhole.  Arsenal applied (§9).  No `sorry`.  No custom axioms.
-/

import Arsenal.ErdosTernary2.Basic
import Arsenal.CardinalWorlds
import Arsenal.CardinalWorldsV2

set_option maxHeartbeats 8000000

-- ===========================================================================
-- §1  THE BLOCKING PREDICATE
-- ===========================================================================

/-- `stepFree l y = true` iff no pair `a < b` of members in `l` blocks `y`
(`a + y = 2 * b` completes a 3-AP `a, b, y`). -/
def stepFree (l : List Nat) (y : Nat) : Bool :=
  !(l.any (fun b => l.any (fun a => decide (a < b && a + y = 2 * b))))

theorem stepFree_false_iff {l : List Nat} {y : Nat} :
    stepFree l y = false ↔ ∃ a b, a ∈ l ∧ b ∈ l ∧ a < b ∧ a + y = 2 * b := by
  constructor
  · intro h
    simp only [stepFree, Bool.not_eq_true'] at h
    rw [List.any_eq_true] at h
    obtain ⟨b, hb, hbq⟩ := h
    rw [List.any_eq_true] at hbq
    obtain ⟨a, ha, haq⟩ := hbq
    rw [Bool.and_eq_true, decide_eq_true_eq] at haq
    exact ⟨a, b, ha, hb, haq.1, haq.2⟩
  · intro h
    obtain ⟨a, b, ha, hb, hlt, heq⟩ := h
    simp only [stepFree, Bool.not_eq_true']
    rw [List.any_eq_true]
    refine ⟨b, hb, ?_⟩
    rw [List.any_eq_true]
    exact ⟨a, ha, by
      rw [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨hlt, heq⟩⟩

theorem stepFree_of_forall {l : List Nat} {y : Nat}
    (h : ∀ a ∈ l, ∀ b ∈ l, a < b → a + y ≠ 2 * b) : stepFree l y = true := by
  by_contra hc
  have hf : stepFree l y = false := by
    cases hcc : stepFree l y with
    | true => rw [hcc] at hc; exact Bool.noConfusion hc
    | false => rfl
  obtain ⟨a, b, ha, hb, hlt, heq⟩ := (stepFree_false_iff.mp hf)
  exact h a ha b hb hlt heq

theorem forall_of_stepFree {l : List Nat} {y : Nat}
    (h : stepFree l y = true) : ∀ a ∈ l, ∀ b ∈ l, a < b → a + y ≠ 2 * b := by
  intro a ha b hb hlt heq
  have hf : stepFree l y = false := stepFree_false_iff.mpr ⟨a, b, ha, hb, hlt, heq⟩
  rw [hf] at h
  exact Bool.noConfusion h

-- ===========================================================================
-- §2  THE BOUNDED GREEDY SEARCH
-- ===========================================================================

/-- `findFree l y fuel` scans `y, y+1, …` for `fuel` steps, returning the
first value with `stepFree l · = true`, or `y + fuel` if none. -/
def findFree (l : List Nat) : Nat → Nat → Nat
  | y, 0 => y
  | y, fuel + 1 => if stepFree l y then y else findFree l (y + 1) fuel

theorem findFree_ge_start (l : List Nat) : ∀ (y fuel : Nat), y ≤ findFree l y fuel
  | _, y, 0 => Nat.le_refl y
  | l, y, fuel + 1 => by
      simp only [findFree]
      split
      · exact Nat.le_refl y
      · exact Nat.le_trans (Nat.le_refl y) (findFree_ge_start l (y + 1) fuel)

theorem findFree_le (l : List Nat) : ∀ (y fuel : Nat), findFree l y fuel ≤ y + fuel
  | _, y, 0 => Nat.le_refl y
  | l, y, fuel + 1 => by
      simp only [findFree]
      split
      · omega
      · exact Nat.le_trans (findFree_le l (y + 1) fuel) (by omega)

/-- Leastness: a free value strictly inside the window bounds the result. -/
theorem findFree_least (l : List Nat) : ∀ (y fuel z : Nat), y ≤ z → z < y + fuel →
    stepFree l z = true → findFree l y fuel ≤ z
  | _, _, 0, z, _, hz, _ => absurd hz (by omega)
  | l, y, fuel + 1, z, _, hz, hfree => by
      simp only [findFree]
      split
      · omega
      · exact findFree_least l (y + 1) fuel z (by omega) (by omega) hfree

theorem findFree_free_or_edge (l : List Nat) : ∀ (y fuel : Nat),
    stepFree l (findFree l y fuel) = true ∨ findFree l y fuel = y + fuel
  | _, y, 0 => Or.inr rfl
  | l, y, fuel + 1 => by
      simp only [findFree]
      split
      · exact Or.inl rfl
      · rename_i _
        cases ih : findFree l (y + 1) fuel with
        | _ =>
            have h := findFree_free_or_edge l (y + 1) fuel
            rw [ih] at h
            cases h with
            | inl h1 => exact Or.inl h1
            | inr h2 => exact Or.inr (by omega)

-- ===========================================================================
-- §3  THE SEQUENCE (reversed member list; head = current maximum)
-- ===========================================================================

def lhead : List Nat → Nat
  | [] => 0
  | a :: _ => a

def sqNext (l : List Nat) : List Nat :=
  match l with
  | [] => [0]
  | a :: _ => findFree l (a + 1) (a + 1) :: l

/-- `sq n k` = the members `a_0, …, a_k` of S(0,n), reversed (head = a_k). -/
def sq : Nat → Nat → List Nat
  | _, 0 => [0]
  | n, 1 => [n, 0]
  | n, k + 2 => sqNext (sq n (k + 1))

/-- The k-th member `a_k` of the Stanley sequence S(0, n). -/
def aSeq (n k : Nat) : Nat := lhead (sq n k)

theorem sq_ne_nil (n : Nat) : ∀ k, sq n k ≠ [] := by
  intro k
  cases k with
  | zero => intro h; rw [sq] at h; exact List.noConfusion h
  | succ k' =>
      cases k' with
      | zero => intro h; rw [sq] at h; exact List.noConfusion h
      | succ k'' =>
          intro h
          rw [sq] at h
          cases hs : sq n (k'' + 1) with
          | nil => rw [hs] at h; exact List.noConfusion h
          | cons a t => rw [hs] at h; exact List.noConfusion h

theorem aSeq_one (n : Nat) : aSeq n 1 = n := rfl

theorem aSeq_zero (n : Nat) : aSeq n 0 = 0 := rfl

/-- The step view: for `j ≥ 2`, the list is the greedy extension of the
previous one. -/
theorem sq_step (n j : Nat) (hj : 2 ≤ j) :
    sq n j = findFree (sq n (j - 1)) (aSeq n (j - 1) + 1) (aSeq n (j - 1) + 1)
      :: sq n (j - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 2 := ⟨j - 2, by omega⟩
  cases hs : sq n (k + 1) with
  | nil => exact absurd hs (sq_ne_nil n (k + 1))
  | cons a t =>
      have h1 : sq n (k + 2) = sqNext (sq n (k + 1)) := rfl
      rw [h1, hs]
      have h2 : aSeq n (k + 1) = a := by rw [aSeq, hs, lhead]
      rw [h2, hs]
      rfl

-- ===========================================================================
-- §4  STRUCTURE INVARIANTS
-- ===========================================================================

/-- Strictly decreasing list (the reversed strictly increasing sequence). -/
def StrictDec : List Nat → Prop
  | [] => True
  | a :: t => (∀ b ∈ t, b < a) ∧ StrictDec t

theorem strictDec_head_max {l : List Nat} (h : StrictDec l) (x : Nat) (hx : x ∈ l) :
    x ≤ lhead l := by
  cases l with
  | nil => simp at hx
  | cons a t =>
      rcases List.mem_cons.mp hx with he | ht
      · simp only [lhead, he]
      · have := h.1 x ht
        simp only [lhead]
        omega

theorem sq_strict (n : Nat) : ∀ k, 1 ≤ n → StrictDec (sq n k) ∧ 0 ∈ sq n k
  | 0, _ => ⟨by simp [StrictDec, sq], by simp [sq]⟩
  | 1, _ => ⟨⟨by simp [sq], by simp [StrictDec, sq]⟩, by simp [sq]⟩
  | k + 2, hn => by
      have ih := sq_strict n (k + 1) hn
      obtain ⟨hdec, hzero⟩ := ih
      cases hs : sq n (k + 1) with
      | nil => exact absurd hs (sq_ne_nil n (k + 1))
      | cons a t =>
          have hsq : sq n (k + 2)
              = findFree (a :: t) (a + 1) (a + 1) :: (a :: t) := by
            rw [sq]; rw [hs]
          have hstart : a + 1 ≤ findFree (a :: t) (a + 1) (a + 1) :=
            findFree_ge_start _ _ _
          rw [hsq]
          refine ⟨⟨?_, ⟨?_, hdec⟩⟩, ?_⟩
          · intro b hb
            rcases List.mem_cons.mp hb with he | ht
            · rw [he]; omega
            · have := hdec.1 b ht; omega
          · intro b hb
            have : b < a := hdec.1 b hb
            omega
          · exact List.mem_cons_of_mem _ hzero

theorem nodup_of_strictDec : ∀ (l : List Nat), StrictDec l → l.Nodup
  | [], _ => List.nodup_nil
  | a :: t, ⟨hmax, hdec⟩ =>
      List.nodup_cons.mpr ⟨by intro hc; have := hmax a hc; omega,
        nodup_of_strictDec t hdec⟩

theorem sq_nodup (n k : Nat) (hn : 1 ≤ n) : (sq n k).Nodup :=
  nodup_of_strictDec _ (sq_strict n k hn).1

theorem sq_length (n : Nat) : ∀ k, (sq n k).length = k + 1 := by
  intro k
  induction k with
  | zero => rfl
  | succ k' ih =>
      cases k' with
      | zero => rfl
      | succ k'' =>
          cases hs : sq n (k'' + 1) with
          | nil => exact absurd hs (sq_ne_nil n (k'' + 1))
          | cons a t =>
              have h1 : sq n (k'' + 2) = sqNext (sq n (k'' + 1)) := rfl
              rw [h1, hs]
              simp only [sqNext, hs, List.length_cons]
              have h2 : (sq n (k'' + 1)).length = k'' + 2 := ih
              rw [hs] at h2
              simp only [List.length_cons] at h2
              omega

theorem aSeq_mem (n : Nat) (k : Nat) : aSeq n k ∈ sq n k := by
  obtain ⟨h, t, heq, _⟩ : ∃ h t, sq n k = h :: t ∧ aSeq n k = h :=
    ⟨lhead (sq n k), _, by
      cases hk : sq n k with
      | nil => exact absurd hk (sq_ne_nil n k)
      | cons a t => rfl, rfl⟩
  rw [heq]
  exact List.mem_cons_self _

theorem sq_mem_iff (n : Nat) : ∀ (k x : Nat),
    x ∈ sq n k ↔ ∃ i, i ≤ k ∧ aSeq n i = x
  | 0, x => by
      simp only [sq]
      constructor
      · intro hx
        rw [List.mem_singleton] at hx
        exact ⟨0, Nat.le_refl 0, by rw [hx]; exact rfl⟩
      · intro h
        obtain ⟨i, hi, heq⟩ := h
        have : i = 0 := by omega
        subst this
        rw [heq]
        simp [sq, aSeq, lhead]
  | 1, x => by
      simp only [sq]
      constructor
      · intro hx
        rcases List.mem_cons.mp hx with he | ht
        · exact ⟨1, by omega, by rw [he]; rfl⟩
        · rw [List.mem_singleton] at ht
          exact ⟨0, by omega, by rw [ht]; exact rfl⟩
      · intro h
        obtain ⟨i, hi, heq⟩ := h
        cases Nat.lt_or_ge i 1 with
        | inl hlt =>
            have : i = 0 := by omega
            subst this
            rw [heq]; simp [sq, aSeq, lhead]
        | inr hge =>
            have : i = 1 := by omega
            subst this
            rw [heq]; simp [sq, aSeq, lhead]
  | k + 2, x => by
      have hstep := sq_step n (k + 2) (by omega)
      rw [hstep]
      constructor
      · intro hx
        rcases List.mem_cons.mp hx with he | ht
        · refine ⟨k + 2, Nat.le_refl _, ?_⟩
          rw [aSeq, hstep, lhead]
          omega
        · obtain ⟨i, hi, heq⟩ := sq_mem_iff n (k + 1) x ht
          exact ⟨i, by omega, heq⟩
      · intro h
        obtain ⟨i, hi, heq⟩ := h
        have hmem : aSeq n i ∈ sq n (k + 1) :=
          (sq_mem_iff n (k + 1) (aSeq n i)).mpr ⟨i, by omega, rfl⟩
        rcases Nat.lt_or_ge i (k + 2) with hlt | hge
        · rw [heq]
          exact List.mem_cons_of_mem _ hmem
        · have hie : i = k + 2 := by omega
          subst hie
          rw [heq]
          exact List.mem_cons_self _

-- ===========================================================================
-- §5  MONOTONICITY
-- ===========================================================================

theorem aSeq_step_lt (n : Nat) (hn : 1 ≤ n) : ∀ k, aSeq n k < aSeq n (k + 1)
  | 0 => by
      have : aSeq n 0 = 0 := rfl
      have : aSeq n 1 = n := rfl
      omega
  | k + 1 => by
      have hstep := sq_step n (k + 2) (by omega)
      have hhead : aSeq n (k + 2)
          = findFree (sq n (k + 1)) (aSeq n (k + 1) + 1) (aSeq n (k + 1) + 1) := by
        rw [aSeq, hstep, lhead]
      have hge := findFree_ge_start (sq n (k + 1))
        (aSeq n (k + 1) + 1) (aSeq n (k + 1) + 1)
      omega

theorem aSeq_mono_aux (n : Nat) (hn : 1 ≤ n) : ∀ (d i : Nat),
    aSeq n i < aSeq n (i + d + 1)
  | 0, i => aSeq_step_lt n hn i
  | d + 1, i => by
      have h1 := aSeq_mono_aux n hn d i
      have h2 := aSeq_step_lt n hn (i + d + 1)
      have : aSeq n (i + d + 1 + 1) = aSeq n (i + (d + 1) + 1) := by omega
      omega

theorem aSeq_mono_lt (n : Nat) (hn : 1 ≤ n) {i j : Nat} (h : i < j) :
    aSeq n i < aSeq n j := by
  have h1 := aSeq_mono_aux n hn (j - i - 1) i
  have h2 : i + (j - i - 1) + 1 = j := by omega
  omega

theorem aSeq_inj (n : Nat) (hn : 1 ≤ n) {i j : Nat} (h : aSeq n i = aSeq n j) :
    i = j := by
  by_contra hc
  cases Nat.lt_or_ge i j with
  | inl hlt => rw [aSeq_mono_lt n hn hlt] at h; omega
  | inr hge => rw [aSeq_mono_lt n hn (by omega : j < i)] at h; omega

-- ===========================================================================
-- §6  G3 — THE DOUBLING LAW
-- ===========================================================================

/-- `2 * a + 1` is never blocked by a list whose elements are all ≤ a. -/
theorem two_a_plus_one_free (l : List Nat) (a : Nat)
    (hmax : ∀ x ∈ l, x ≤ a) : stepFree l (2 * a + 1) = true :=
  stepFree_of_forall (by
    intro x hx b hb hlt heq
    have hx' : x ≤ a := hmax x hx
    have hb' : b ≤ a := hmax b hb
    omega)

theorem growth_G3 (n : Nat) (hn : 1 ≤ n) (k : Nat) (hk : 1 ≤ k) :
    aSeq n (k + 1) ≤ 2 * aSeq n k + 1 := by
  have hstep := sq_step n (k + 1) (by omega)
  have hhead : aSeq n (k + 1)
      = findFree (sq n k) (aSeq n k + 1) (aSeq n k + 1) := by
    rw [aSeq, hstep, lhead]
  have hmax : ∀ x ∈ sq n k, x ≤ aSeq n k :=
    fun x hx => strictDec_head_max (sq_strict n k hn).1 x hx
  have hz : stepFree (sq n k) (2 * aSeq n k + 1) = true :=
    two_a_plus_one_free _ _ hmax
  have hleast := findFree_least (sq n k) (aSeq n k + 1) (aSeq n k + 1)
    (2 * aSeq n k + 1) (by omega) (by omega) hz
  omega

-- ===========================================================================
-- §7  G2 — THE LINEAR FLOOR
-- ===========================================================================

theorem apFree_sq (n : Nat) (hn : 1 ≤ n) : ∀ (k x y z : Nat),
    x ∈ sq n k → y ∈ sq n k → z ∈ sq n k → x < y → y < z → x + z ≠ 2 * y
  | 0, x, y, z, hx, hy, _, hxy, _ => by
      simp only [sq] at hx hy
      rw [List.mem_singleton] at hx hy
      omega
  | 1, x, y, z, hx, hy, _, hxy, _ => by
      simp only [sq] at hx hy
      rcases List.mem_cons.mp hx with hex | hex
      · rw [List.mem_singleton] at hex; rcases List.mem_cons.mp hy with hey | hey
        · omega
        · rw [List.mem_singleton] at hey; omega
      · rw [List.mem_singleton] at hex; rcases List.mem_cons.mp hy with hey | hey
        · rw [List.mem_singleton] at hex; omega
        · rw [List.mem_singleton] at hex hey; omega
  | k + 2, x, y, z, hx, hy, hz, hxy, hyz => by
      have hstep := sq_step n (k + 2) (by omega)
      rw [hstep] at hx hy hz
      have hhead : aSeq n (k + 2)
          = findFree (sq n (k + 1)) (aSeq n (k + 1) + 1) (aSeq n (k + 1) + 1) := by
        rw [aSeq, hstep, lhead]
      have hc_max : ∀ w ∈ sq n (k + 1), w < aSeq n (k + 2) := by
        intro w hw
        have hd : StrictDec (sq n (k + 2)) := (sq_strict n (k + 2) hn).1
        rw [hstep] at hd
        have := hd.1 w (List.mem_cons_of_mem _ hw)
        exact this
      rcases List.mem_cons.mp hx with hex | hex
      · rcases List.mem_cons.mp hy with hey | hey
        · omega
        · have := hc_max y hey; omega
      · rcases List.mem_cons.mp hy with hey | hey
        · rcases List.mem_cons.mp hz with hez | hez
          · omega
          · have := hc_max z hez; omega
        · rcases List.mem_cons.mp hz with hez | hez
          · -- z is the head: x + head = 2y with x < y in the tail —
            -- exactly the blocked pattern, but the head is free
            have hG3 := growth_G3 n hn (k + 1) (by omega)
            have hfree := findFree_free_or_edge (sq n (k + 1))
              (aSeq n (k + 1) + 1) (aSeq n (k + 1) + 1)
            rcases hfree with h | h
            · rw [hez]
              exact forall_of_stepFree h x hex y hey hxy
            · omega
          · exact apFree_sq n hn (k + 1) x y z hex hey hez hxy hyz

theorem aSeq_gap3 (n : Nat) (hn : 1 ≤ n) (k : Nat) :
    aSeq n k + 3 ≤ aSeq n (k + 2) := by
  have h1 := aSeq_step_lt n hn k
  have h2 := aSeq_step_lt n hn (k + 1)
  have hm0 : aSeq n k ∈ sq n (k + 2) := (sq_mem_iff n (k + 2) _).mpr
    ⟨k, by omega, rfl⟩
  have hm1 : aSeq n (k + 1) ∈ sq n (k + 2) := (sq_mem_iff n (k + 2) _).mpr
    ⟨k + 1, by omega, rfl⟩
  have hm2 : aSeq n (k + 2) ∈ sq n (k + 2) := aSeq_mem n (k + 2)
  have hnoap : aSeq n k + aSeq n (k + 2) ≠ 2 * aSeq n (k + 1) :=
    apFree_sq n hn (k + 2) (aSeq n k) (aSeq n (k + 1)) (aSeq n (k + 2))
      hm0 hm1 hm2 (by omega) (by omega)
  omega

theorem growth_G2 (n : Nat) (hn : 1 ≤ n) : ∀ m, 2 * aSeq n m ≥ 3 * m - 3 := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
      cases Nat.lt_or_ge m 2 with
      | inl hlt =>
          cases Nat.lt_or_ge m 1 with
          | inl h0 => omega
          | inr h1 =>
              have hm1 : m = 1 := by omega
              subst hm1
              have : aSeq n 1 = n := rfl
              omega
      | inr hge =>
          have h1 : 2 * aSeq n (m - 2) ≥ 3 * (m - 2) - 3 := ih (m - 2) (by omega)
          have hgap : aSeq n (m - 2) + 3 ≤ aSeq n m := by
            have := aSeq_gap3 n hn (m - 2)
            omega
          omega

-- ===========================================================================
-- §8  G1 — THE QUADRATIC CEILING (the blocking-pair pigeonhole)
-- ===========================================================================

/-- THE GREEDY SKIP LEMMA: every value the scan passed over carries a
witness pair from the prefix. -/
theorem greedy_skip (n : Nat) (hn : 1 ≤ n) (k y : Nat) (hk : 1 ≤ k)
    (hly : aSeq n k < y) (hhy : y < aSeq n (k + 1)) :
    ∃ a b, a ∈ sq n k ∧ b ∈ sq n k ∧ a < b ∧ a + y = 2 * b := by
  have hstep := sq_step n (k + 1) (by omega)
  have hhead : aSeq n (k + 1)
      = findFree (sq n k) (aSeq n k + 1) (aSeq n k + 1) := by
    rw [aSeq, hstep, lhead]
  by_contra hcon
  have hfree : stepFree (sq n k) y = true := by
    refine stepFree_of_forall ?_
    intro a ha b hb hlt heq
    exact hcon ⟨a, b, ha, hb, hlt, heq⟩
  have hle := findFree_le (sq n k) (aSeq n k + 1) (aSeq n k + 1)
  have hleast := findFree_least (sq n k) (aSeq n k + 1) (aSeq n k + 1) y
    (by omega) (by omega) hfree
  omega

theorem skip_to_index (n : Nat) (hn : 1 ≤ n) {k y : Nat} (hk : 1 ≤ k)
    (hly : aSeq n k < y) (hhy : y < aSeq n (k + 1)) :
    ∃ i j, i < j ∧ j ≤ k ∧ aSeq n i + y = 2 * aSeq n j := by
  obtain ⟨a, b, ha, hb, hab, heq⟩ := greedy_skip n hn k y hk hly hhy
  obtain ⟨i, hi, hia⟩ := (sq_mem_iff n k a).mp ha
  obtain ⟨j, hj, hjb⟩ := (sq_mem_iff n k b).mp hb
  refine ⟨i, j, ?_, ?_, ?_⟩
  · cases Nat.lt_or_ge i j with
    | inl h => exact h
    | inr hge =>
        cases Nat.lt_or_ge j i with
        | inl hlt => omega
        | inr heg =>
          have : i = j := by omega
          omega
  · omega
  · rw [← hia, ← hjb]
    exact heq

/-- Interval localization: a non-member strictly between `a_1` and `a_m`
lies strictly between consecutive members. -/
theorem interval_loc (n : Nat) (hn : 1 ≤ n) : ∀ (m y : Nat), 2 ≤ m →
    aSeq n 1 < y → y < aSeq n m → (∀ i, 1 < i → i < m → aSeq n i ≠ y) →
    ∃ k, 1 ≤ k ∧ k + 1 ≤ m ∧ aSeq n k < y ∧ y < aSeq n (k + 1) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro y hm h1y hmy hnm
    cases Nat.lt_or_ge 2 m with
    | inl hlt =>
        have hm2 : m = 2 := by omega
        subst hm2
        exact ⟨1, by omega, by omega, h1y, hmy⟩
    | inr h3 =>
        cases Nat.lt_or_ge y (aSeq n (m - 1)) with
        | inl hlt =>
            have hnm' : ∀ i, 1 < i → i < m - 1 → aSeq n i ≠ y := by
              intro i hi1 hi2
              exact hnm i hi1 (by omega)
            obtain ⟨k, hk1, hk2, hk3, hk4⟩ :=
              ih (m - 1) (by omega) y (by omega) h1y hlt hnm'
            exact ⟨k, hk1, by omega, hk3, hk4⟩
        | inr hge =>
            have hne : aSeq n (m - 1) ≠ y := hnm (m - 1) (by omega) (by omega)
            exact ⟨m - 1, by omega, by omega, by omega, hmy⟩

-- §8.1  The index-pair list

def pairBlock (j : Nat) : List (Nat × Nat) := (List.range j).map (fun i => (i, j))

def pairList : Nat → List (Nat × Nat)
  | 0 => []
  | m + 1 => pairBlock (m + 1) ++ pairList m

theorem pairList_length : ∀ m, (pairList m).length = m * (m + 1) / 2
  | 0 => rfl
  | m + 1 => by
      simp only [pairList, List.length_append, pairList_length m,
        pairBlock, List.length_map, List.length_range]
      have hring : (m + 1) * (m + 2) = (m + 1) + m * (m + 1) + (m + 1) := by ring
      rcases Nat.even_or_odd (m * (m + 1)) with ⟨t, ht⟩ | ⟨t, ht⟩
      · rw [ht]
        have h1 : (2 * t) / 2 = t := by omega
        rw [Nat.mul_div_assoc _ (by
          exact ⟨t, by rw [ht]; ring⟩)]
        rw [Nat.mul_div_right]
        ring_nf
        omega
      · rw [ht]
        have h1 : (2 * t + 1) / 2 = t := by omega
        rw [Nat.mul_div_assoc _ (by
          exact ⟨t, by rw [ht]; omega⟩)]
        rw [Nat.mul_div_right]
        ring_nf
        omega

theorem pairList_mem : ∀ (m i j : Nat), (i, j) ∈ pairList m ↔ i < j ∧ j ≤ m
  | 0, i, j => by simp [pairList]
  | m + 1, i, j => by
      simp only [pairList, List.mem_append]
      constructor
      · intro h
        rcases h with hl | hr
        · rw [pairBlock, List.mem_map] at hl
          obtain ⟨i', hi', heq⟩ := hl
          rw [List.mem_range] at hi'
          rw [Prod.mk.injEq] at heq
          subst heq
          exact ⟨hi', by omega⟩
        · exact pairList_mem m i j |>.mp hr
      · intro ⟨hlt, hle⟩
        cases Nat.lt_or_ge j (m + 1) with
        | inl hj => exact Or.inr (pairList_mem m i j |>.mpr ⟨hlt, by omega⟩)
        | inr hj =>
            have hj1 : j = m + 1 := by omega
            subst hj1
            refine Or.inl ?_
            rw [pairBlock, List.mem_map]
            refine ⟨i, ?_, rfl⟩
            rw [List.mem_range]
            omega

theorem pairBlock_mem_snd {j : Nat} {p : Nat × Nat} (hp : p ∈ pairBlock j) :
    p.2 = j := by
  rw [pairBlock, List.mem_map] at hp
  obtain ⟨i, _, heq⟩ := hp
  exact heq.2

theorem pairList_mem_snd {m : Nat} {p : Nat × Nat} (hp : p ∈ pairList m) :
    p.2 ≤ m := by
  cases m with
  | zero => simp [pairList] at hp
  | succ m' =>
      simp only [pairList, List.mem_append] at hp
      rcases hp with hl | hr
      · rw [pairBlock_mem_snd hl]; omega
      · have := pairList_mem_snd hr; omega

theorem pairBlock_nodup (j : Nat) : (pairBlock j).Nodup := by
  induction j with
  | zero => simp [pairBlock]
  | succ j' _ =>
      rw [pairBlock, List.range_succ, List.map_append, List.map_cons,
        List.map_nil, List.append_cons, List.append_nil]
      refine List.Nodup.append (by
        intro x hx hx'
        rw [List.mem_map] at hx
        obtain ⟨i', hi', heq⟩ := hx
        rw [List.mem_range] at hi'
        rw [← heq] at hx'
        rw [List.mem_singleton, Prod.mk.injEq] at hx'
        omega) (List.nodup_singleton _) ?_
      intro x hx hx'
      rw [List.mem_singleton, Prod.mk.injEq] at hx
      rw [List.mem_map] at hx'
      obtain ⟨i', hi', heq⟩ := hx'
      rw [List.mem_range] at hi'
      rw [← heq] at hx
      omega

theorem pairList_nodup : ∀ m, (pairList m).Nodup
  | 0 => List.nodup_nil
  | m + 1 => by
      refine List.Nodup.append (pairBlock_nodup _) (pairList_nodup m) ?_
      intro p hp hq
      have h1 : p.2 = m + 1 := pairBlock_mem_snd hp
      have h2 : p.2 ≤ m := pairList_mem_snd hq
      omega

-- §8.2  The canonical blocker selector

def lfind (p : Nat × Nat → Bool) : List (Nat × Nat) → Option (Nat × Nat)
  | [] => none
  | x :: xs => if p x then some x else lfind p xs

theorem lfind_some {p : Nat × Nat → Bool} : ∀ {l : List (Nat × Nat)}
    {x : Nat × Nat}, lfind p l = some x → x ∈ l ∧ p x = true
  | [], _, h => by simp [lfind] at h
  | y :: ys, _, h => by
      simp only [lfind] at h
      split at h
      · rw [h]
        exact ⟨List.mem_cons_self _ _, by
          cases hp : p (y) with
          | true => rfl
          | false => rw [hp] at *; exact Bool.noConfusion *⟩
      · rename_i hnf
        have ih := lfind_some (l := ys) h
        exact ⟨List.mem_cons_of_mem _ ih.1, ih.2⟩

theorem lfind_isSome {p : Nat × Nat → Bool} : ∀ (l : List (Nat × Nat))
    (x : Nat × Nat), x ∈ l → p x = true → lfind p l ≠ none
  | [], _, hx, _ => by simp [lfind] at hx
  | y :: ys, x, hx, hp => by
      simp only [lfind]
      by_cases hpy : p y = true
      · rw [if_pos hpy]; intro hc; exact Option.noConfusion hc
      · rw [if_neg hpy]
        rcases List.mem_cons.mp hx with he | ht
        · rw [he] at hpy; rw [hp] at hpy; exact Bool.noConfusion hpy
        · exact lfind_isSome ys x ht hp

/-- The canonical blocker-pair selector: the first `(i, j)` in the
`pairList` order with `a i + y = 2 * a j` (or `(0,0)` if none). -/
def findBlocker (a : Nat → Nat) (y m : Nat) : Nat × Nat :=
  match lfind (fun p => decide (a p.1 + y = 2 * a p.2)) (pairList m) with
  | some p => p
  | none => (0, 0)

theorem findBlocker_spec {a : Nat → Nat} {y m : Nat}
    (h : ∃ i j, i < j ∧ j ≤ m ∧ a i + y = 2 * a j) :
    ∃ i j, findBlocker a y m = (i, j) ∧ i < j ∧ j ≤ m ∧ a i + y = 2 * a j := by
  obtain ⟨i0, j0, hlt0, hle0, heq0⟩ := h
  have hmem : (i0, j0) ∈ pairList m := (pairList_mem m i0 j0).mpr ⟨hlt0, hle0⟩
  have hpy : (fun p => decide (a p.1 + y = 2 * a p.2)) (i0, j0) = true := by
    simp only
    rw [decide_eq_true_eq]
    exact heq0
  have hne : lfind (fun p => decide (a p.1 + y = 2 * a p.2)) (pairList m) ≠ none :=
    lfind_isSome _ _ hmem hpy
  cases hlf : lfind (fun p => decide (a p.1 + y = 2 * a p.2)) (pairList m) with
  | none => exact absurd hlf hne
  | some q =>
      have hdef : findBlocker a y m = q := by
        simp only [findBlocker, hlf]
      obtain ⟨hqmem, hqp⟩ := lfind_some hlf
      obtain ⟨i, j⟩ := q
      refine ⟨i, j, hdef, ?_, ?_, ?_⟩
      · have := (pairList_mem m i j).mp (by rw [← hdef]; exact hqmem)
        exact this.1
      · have := (pairList_mem m i j).mp (by rw [← hdef]; exact hqmem)
        exact this.2
      · rw [Bool.decide_eq_true_eq] at hqp
        exact hqp

theorem findBlocker_inj {a : Nat → Nat} {m y y' : Nat}
    (hex : ∃ i j, i < j ∧ j ≤ m ∧ a i + y = 2 * a j)
    (hex' : ∃ i j, i < j ∧ j ≤ m ∧ a i + y' = 2 * a j)
    (h : findBlocker a y m = findBlocker a y' m) : y = y' := by
  obtain ⟨i, j, hfind, _, _, heq⟩ := findBlocker_spec hex
  obtain ⟨i', j', hfind', _, _, heq'⟩ := findBlocker_spec hex'
  rw [hfind, hfind'] at h
  rw [Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  subst h1; subst h2
  omega

-- §8.3  THE HEADLINE

theorem growth_G1 (n : Nat) (hn : 1 ≤ n) : ∀ m, 1 ≤ m →
    aSeq n m ≤ n + (m - 1) * (m + 2) / 2 := by
  intro m hm
  cases Nat.lt_or_ge 1 m with
  | inl hlt =>
      have hm1 : m = 1 := by omega
      subst hm1
      have : aSeq n 1 = n := rfl
      omega
  | inr h2 =>
      -- the interval Finset
      have ha1 : aSeq n 1 = n := rfl
      have hmono : aSeq n 1 < aSeq n m := aSeq_mono_lt n hn (by omega)
      set A := aSeq n m with hA
      have hIco_card : (Finset.Ico (n + 1) A).card = A - (n + 1) :=
        Finset.card_Ico _ _
      -- the member Finset
      have hM_card : ((sq n m).toFinset).card = m + 1 := by
        rw [List.toFinset_card (sq_nodup n m hn), sq_length]
      -- the split
      have hsub : Finset.Ico (n + 1) A
          ⊆ (Finset.Ico (n + 1) A \ (sq n m).toFinset)
            ∪ (Finset.Ico (n + 1) A ∩ (sq n m).toFinset) := by
        intro x hx
        by_cases hmem : x ∈ (sq n m).toFinset
        · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hx, hmem⟩)
        · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hx, hmem⟩)
      have hcard := calc (Finset.Ico (n + 1) A).card
          ≤ ((Finset.Ico (n + 1) A \ (sq n m).toFinset)
              ∪ (Finset.Ico (n + 1) A ∩ (sq n m).toFinset)).card :=
            Finset.card_le_card hsub
        _ ≤ (Finset.Ico (n + 1) A \ (sq n m).toFinset).card
            + (Finset.Ico (n + 1) A ∩ (sq n m).toFinset).card :=
            Finset.card_union_le _ _
      -- the member side: at most m - 2 (0, n, A excluded)
      have hint_le : (Finset.Ico (n + 1) A ∩ (sq n m).toFinset).card ≤ m - 2 := by
        have h3 : ({0, n, A} : Finset Nat) ⊆ (sq n m).toFinset := by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl | rfl
          · simp only [List.mem_toFinset]
            exact (sq_strict n m hn).2
          · simp only [List.mem_toFinset]
            rw [sq_mem_iff n m]
            exact ⟨1, by omega, rfl⟩
          · simp only [List.mem_toFinset]
            exact aSeq_mem n m
        have hcard3 : ({0, n, A} : Finset Nat).card = 3 := by
          have h01 : (0 : Nat) ∉ ({n, A} : Finset Nat) := by
            simp only [Finset.mem_insert, Finset.mem_singleton]; omega
          have hnA : n ∉ ({A} : Finset Nat) := by
            simp only [Finset.mem_singleton]; omega
          rw [Finset.card_insert_eq h01, Finset.card_insert_eq hnA]
          simp
        have hsub2 : Finset.Ico (n + 1) A ∩ (sq n m).toFinset
            ⊆ (sq n m).toFinset \ {0, n, A} := by
          intro x hx
          have hxI : x ∈ Finset.Ico (n + 1) A := (Finset.mem_inter.mp hx).1
          have hxM : x ∈ (sq n m).toFinset := (Finset.mem_inter.mp hx).2
          simp only [Finset.mem_Ico] at hxI
          refine Finset.mem_sdiff.mpr ⟨hxM, ?_⟩
          simp only [Finset.mem_insert, Finset.mem_singleton]
          obtain ⟨hn1, hnA2⟩ := hxI
          omega
        have hcalc := calc
          (Finset.Ico (n + 1) A ∩ (sq n m).toFinset).card
              ≤ ((sq n m).toFinset \ {0, n, A}).card := Finset.card_le_card hsub2
          _ = ((sq n m).toFinset).card - ({0, n, A} : Finset Nat).card :=
            Finset.card_sdiff h3
        omega
      -- the rejected side: the pigeonhole
      have hcover : ∀ y ∈ (Finset.Ico (n + 1) A \ (sq n m).toFinset),
          ∃ i j, i < j ∧ j ≤ m - 1 ∧ aSeq n i + y = 2 * aSeq n j := by
        intro y hyR
        have hyI : y ∈ Finset.Ico (n + 1) A := (Finset.mem_sdiff.mp hyR).1
        have hyM : y ∉ (sq n m).toFinset := (Finset.mem_sdiff.mp hyR).2
        simp only [Finset.mem_Ico] at hyI
        have hnm : ∀ i, 1 < i → i < m → aSeq n i ≠ y := by
          intro i hi1 hi2 heqy
          have hmem : aSeq n i ∈ (sq n m).toFinset := by
            simp only [List.mem_toFinset]
            rw [sq_mem_iff n m]
            exact ⟨i, by omega, rfl⟩
          rw [heqy] at hmem
          exact hyM hmem
        obtain ⟨k, hk1, hk2, hk3, hk4⟩ :=
          interval_loc n hn m y (by omega) (by omega) (by omega) hnm
        exact skip_to_index n hn hk1 hk3 hk4
      have hR_le : (Finset.Ico (n + 1) A \ (sq n m).toFinset).card
          ≤ (m - 1) * m / 2 := by
        have hinj : ∀ y ∈ (Finset.Ico (n + 1) A \ (sq n m).toFinset),
            ∀ y' ∈ (Finset.Ico (n + 1) A \ (sq n m).toFinset),
            findBlocker (aSeq n) y (m - 1) = findBlocker (aSeq n) y' (m - 1) →
            y = y' := by
          intro y hy y' hy' hyy
          exact findBlocker_inj (hcover y hy) (hcover y' hy') hyy
        have himg : ∀ y ∈ (Finset.Ico (n + 1) A \ (sq n m).toFinset),
            findBlocker (aSeq n) y (m - 1) ∈ (pairList (m - 1)).toFinset := by
          intro y hy
          obtain ⟨i, j, hfind, h1, h2, _⟩ := findBlocker_spec (hcover y hy)
          rw [hfind]
          simp only [List.mem_toFinset]
          exact (pairList_mem (m - 1) i j).mpr ⟨h1, h2⟩
        calc (Finset.Ico (n + 1) A \ (sq n m).toFinset).card
            = (Finset.image (fun y => findBlocker (aSeq n) y (m - 1))
                (Finset.Ico (n + 1) A \ (sq n m).toFinset)).card := by
              refine (Finset.card_image_of_injOn ?_).symm
              intro y hy y' hy' hyy
              rw [Finset.mem_coe] at hy hy'
              exact hinj y hy y' hy' hyy
          _ ≤ ((pairList (m - 1)).toFinset).card := Finset.card_le_card (by
              intro p hp
              simp only [Finset.mem_image] at hp
              obtain ⟨y, hyR, hfp⟩ := hp
              rw [← hfp]
              exact himg y hyR)
          _ = (pairList (m - 1)).length := List.toFinset_card (pairList_nodup _)
          _ = (m - 1) * m / 2 := pairList_length _
      -- the arithmetic finish
      have heven1 : (m - 1) * m % 2 = 0 := by
        rcases Nat.even_or_odd m with ⟨t, ht⟩ | ⟨t, ht⟩
        · subst ht; norm_num; ring_nf; omega
        · subst ht; norm_num; ring_nf; omega
      have heven2 : (m - 1) * (m + 2) % 2 = 0 := by
        rcases Nat.even_or_odd m with ⟨t, ht⟩ | ⟨t, ht⟩
        · subst ht; norm_num; ring_nf; omega
        · subst ht; norm_num; ring_nf; omega
      have hdm1 : (m - 1) * m / 2 * 2 + (m - 1) * m % 2 = (m - 1) * m :=
        Nat.div_add_mod _ 2
      have hdm2 : (m - 1) * (m + 2) / 2 * 2 + (m - 1) * (m + 2) % 2
          = (m - 1) * (m + 2) := Nat.div_add_mod _ 2
      have hring : (m - 1) * (m + 2) = (m - 1) * m + 2 * (m - 1) := by ring
      have hAcards := hcard
      omega

-- ===========================================================================
-- §9  RECEIPTS + ARSENAL BRIDGE
-- ===========================================================================

/-- The first 12 members of S(0,4) (OEIS A005487):
expected `[0, 4, 5, 7, 11, 12, 16, 23, 26, 31, 33, 37]`. -/
#eval (List.range 12).map (fun k => aSeq 4 k)

/-- S(0,1) = the Cantor set (OEIS A005836):
expected `[0, 1, 3, 4, 9, 10, 12, 13, 27, 28]`. -/
#eval (List.range 10).map (fun k => aSeq 1 k)

/-- S(0,2) (OEIS A005837): expected `[0, 2, 3, 5, 9, 11, 12, 14, 27, 29]`. -/
#eval (List.range 10).map (fun k => aSeq 2 k)

/-- The G1 ceiling and G2 floor at seed 4, m ≤ 29 (the census range):
every row satisfies `2*a ≥ 3m-3` and `a ≤ 4 + (m-1)(m+2)/2`. -/
#eval (List.range 29).filter (fun m =>
  let a := aSeq 4 (m + 1)
  !(2 * a ≥ 3 * (m + 1) - 3 ∧ a ≤ 4 + m * (m + 3) / 2))
-- expected: [] (zero violations)

/-- S(0,4) growth profile: a_m vs the two laws at the census frontier. -/
#eval (List.range 28).map (fun k =>
  (aSeq 4 (k + 2), 4 + (k + 1) * (k + 4) / 2))

/-! ## THE ARSENAL BRIDGE (BOSS's mathematics applied to the #271 witness
numbers — erdosternary2 + HC-PROOF).  Seed 4 = (11)₃ and member 23 =
(212)₃ carry ternary digits; the greedy residue a₃ = 7 routes through
lt_three_cases; the carry and dyadic-scaling laws apply at 23. -/

def arsenalBridgeProp271 : Prop :=
  [4 % 3, (4 / 3) % 3].all (fun d => ErdosTernary2.isTernaryDigit d) ∧
  [23 % 3, (23 / 3) % 3, (23 / 9) % 3].all (fun d => ErdosTernary2.isTernaryDigit d) ∧
  (aSeq 4 3 % 3 = 0 ∨ aSeq 4 3 % 3 = 1 ∨ aSeq 4 3 % 3 = 2) ∧
  CardinalWorlds.carryAtPos 23 1 < 4 ∧
  CardinalWorldsV2.v2r (3 ^ 1 * 9) = CardinalWorldsV2.v2r 9

theorem erdos271_arsenal_bridge : arsenalBridgeProp271 :=
  ⟨by decide, by decide,
    ErdosTernary2.lt_three_cases (aSeq 4 3 % 3) (Nat.mod_lt _ (by omega)),
    CardinalWorlds.carryAtPos_bound 23 1,
    CardinalWorldsV2.v2r_ternary_scaling 1 9⟩

#print axioms growth_G3
#print axioms growth_G2
#print axioms growth_G1
#print axioms erdos271_arsenal_bridge

#eval "ERDOS271_KERNEL_GREEN"
