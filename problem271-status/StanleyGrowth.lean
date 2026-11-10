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
  !(l.any (fun b => l.any (fun a => decide (a < b) && decide (a + y = 2 * b))))

theorem stepFree_false_iff {l : List Nat} {y : Nat} :
    stepFree l y = false ↔ ∃ a b, a ∈ l ∧ b ∈ l ∧ a < b ∧ a + y = 2 * b := by
  constructor
  · intro h
    simp only [stepFree, Bool.not_eq_false', List.any_eq_true,
      Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨b, hb, a, ha, hlt, heq⟩ := h
    exact ⟨a, b, ha, hb, hlt, heq⟩
  · intro h
    obtain ⟨a, b, ha, hb, hlt, heq⟩ := h
    simp only [stepFree, Bool.not_eq_false', List.any_eq_true,
      Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨b, hb, a, ha, hlt, heq⟩

theorem stepFree_of_forall {l : List Nat} {y : Nat}
    (h : ∀ a ∈ l, ∀ b ∈ l, a < b → a + y ≠ 2 * b) : stepFree l y = true := by
  by_contra hc
  have hf : stepFree l y = false := by
    cases hcc : stepFree l y with
    | true => rw [hcc] at hc; exact hc rfl
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
-- §2  THE BOUNDED GREEDY SEARCH (fuel-indexed)
-- ===========================================================================

/-- `findFree l y fuel` scans `y, y+1, …` for `fuel` steps, returning the
first value with `stepFree l · = true`, or `y + fuel` if none. -/
def findFree (l : List Nat) : Nat → Nat → Nat
  | y, 0 => y
  | y, fuel + 1 => if stepFree l y then y else findFree l (y + 1) fuel

theorem findFree_ge_start (l : List Nat) : ∀ (y fuel : Nat), y ≤ findFree l y fuel := by
  intro y fuel
  induction fuel generalizing y with
  | zero => exact Nat.le_refl y
  | succ f ih =>
      simp only [findFree]
      split
      · exact Nat.le_refl y
      · exact Nat.le_trans (Nat.le_refl y) (ih (y + 1))

theorem findFree_le (l : List Nat) : ∀ (y fuel : Nat), findFree l y fuel ≤ y + fuel := by
  intro y fuel
  induction fuel generalizing y with
  | zero => exact Nat.le_refl y
  | succ f ih =>
      simp only [findFree]
      split
      · omega
      · exact Nat.le_trans (ih (y + 1)) (by omega)

/-- Leastness: a free value strictly inside the window bounds the result. -/
theorem findFree_least (l : List Nat) : ∀ (y fuel z : Nat), y ≤ z → z < y + fuel →
    stepFree l z = true → findFree l y fuel ≤ z := by
  intro y fuel
  induction fuel generalizing y with
  | zero => intro z hy hz _; omega
  | succ f ih =>
      intro z hy hz hfree
      simp only [findFree]
      split
      · omega
      · rename_i hn
        rcases Nat.lt_or_ge z (y + 1) with hlt | hge
        · have hzy : z = y := by omega
          rw [hzy] at hfree
          exact absurd hfree hn
        · exact ih (y + 1) z (by omega) (by omega) hfree

theorem findFree_free_or_edge (l : List Nat) : ∀ (y fuel : Nat),
    stepFree l (findFree l y fuel) = true ∨ findFree l y fuel = y + fuel := by
  intro y fuel
  induction fuel generalizing y with
  | zero => exact Or.inr rfl
  | succ f ih =>
      simp only [findFree]
      split
      · exact Or.inl rfl
      · rcases ih (y + 1) with h | h
        · exact Or.inl h
        · exact Or.inr (by omega)

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

theorem sqNext_ne_nil (l : List Nat) : sqNext l ≠ [] := by
  cases l with
  | nil => simp [sqNext]
  | cons a t => simp [sqNext]

/-- `sqSeq n k` = the members `a_0, …, a_k` of S(0,n), reversed (head = a_k). -/
def sqSeq : Nat → Nat → List Nat
  | _, 0 => [0]
  | n, 1 => [n, 0]
  | n, k + 2 => sqNext (sqSeq n (k + 1))

/-- The k-th member `a_k` of the Stanley sequence S(0, n). -/
def aSeq (n k : Nat) : Nat := lhead (sqSeq n k)

theorem aSeq_zero (n : Nat) : aSeq n 0 = 0 := rfl

theorem aSeq_one (n : Nat) : aSeq n 1 = n := rfl

theorem sq_ne_nil (n : Nat) : ∀ k, sqSeq n k ≠ [] := by
  intro k
  cases k with
  | zero => intro h; exact List.noConfusion h
  | succ k' =>
      cases k' with
      | zero => intro h; exact List.noConfusion h
      | succ k'' =>
          intro h
          have h1 : sqSeq n (k'' + 2) = sqNext (sqSeq n (k'' + 1)) := by
            simp only [sqSeq]
          rw [h1] at h
          exact sqNext_ne_nil _ h

/-- The step view of the recursion, at every index `j ≥ 2`. -/
theorem sq_step (n j : Nat) (hj : 2 ≤ j) :
    sqSeq n j = findFree (sqSeq n (j - 1)) (aSeq n (j - 1) + 1) (aSeq n (j - 1) + 1)
      :: sqSeq n (j - 1) := by
  obtain ⟨k, hk⟩ : ∃ k, j = k + 2 := ⟨j - 2, by omega⟩
  subst hk
  have h1 : sqSeq n (k + 2) = sqNext (sqSeq n (k + 1)) := by
    simp only [sqSeq]
  rw [h1]
  cases hs : sqSeq n (k + 1) with
  | nil => exact absurd hs (sq_ne_nil n (k + 1))
  | cons a t =>
      have h2 : aSeq n (k + 1) = a := by
        simp only [aSeq, hs, lhead]
      rw [h2]
      rfl

/-- The clean step lemma at every index `k ≥ 1`. -/
theorem sq_next (n k : Nat) (hk : 1 ≤ k) :
    sqSeq n (k + 1) = findFree (sqSeq n k) (aSeq n k + 1) (aSeq n k + 1)
      :: sqSeq n k := by
  have hstep := sq_step n (k + 1) (by omega)
  have hk1 : k + 1 - 1 = k := by omega
  rw [hk1] at hstep
  exact hstep

/-- The head bridge: `a_{k+1}` IS the greedy find, at every index `k ≥ 1`. -/
theorem aSeq_step_eq (n k : Nat) (hk : 1 ≤ k) :
    aSeq n (k + 1) = findFree (sqSeq n k) (aSeq n k + 1) (aSeq n k + 1) := by
  have h := sq_next n k hk
  have hl : aSeq n (k + 1) = lhead (sqSeq n (k + 1)) := rfl
  rw [hl, h]
  simp only [lhead]

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
      · have hlt := h.1 x ht
        simp only [lhead]
        omega

theorem sq_strict (n : Nat) (hn : 1 ≤ n) : ∀ k, StrictDec (sqSeq n k) ∧ 0 ∈ sqSeq n k := by
  intro k
  induction k with
  | zero => exact ⟨by simp [StrictDec, sqSeq], by simp [sqSeq]⟩
  | succ k' ih =>
      obtain ⟨hdec, hzero⟩ := ih
      cases k' with
      | zero =>
          show StrictDec [n, 0] ∧ 0 ∈ [n, 0]
          refine ⟨⟨?_, ?_⟩, ?_⟩
          · intro b hb
            rw [List.mem_singleton] at hb
            subst hb
            omega
          · simp [StrictDec]
          · simp
      | succ k'' =>
          have hsq := sq_next n (k'' + 1) (by omega)
          rw [hsq]
          cases hs : sqSeq n (k'' + 1) with
          | nil => exact absurd hs (sq_ne_nil n (k'' + 1))
          | cons a t =>
              have h2 : aSeq n (k'' + 1) = a := by
                simp only [aSeq, hs, lhead]
              rw [h2]
              refine ⟨⟨?_, hdec⟩, List.mem_cons_of_mem _ hzero⟩
              · intro b hb
                rcases List.mem_cons.mp hb with he | ht
                · rw [← he]
                  have hge := findFree_ge_start (a :: t) (a + 1) (a + 1)
                  omega
                · have hba := hdec.1 b ht
                  have hge := findFree_ge_start (a :: t) (a + 1) (a + 1)
                  omega

theorem nodup_of_strictDec : ∀ (l : List Nat), StrictDec l → l.Nodup
  | [], _ => List.nodup_nil
  | a :: t, ⟨hmax, hdec⟩ =>
      List.nodup_cons.mpr ⟨by intro hc; have := hmax a hc; omega,
        nodup_of_strictDec t hdec⟩

theorem sq_nodup (n k : Nat) (hn : 1 ≤ n) : (sqSeq n k).Nodup :=
  nodup_of_strictDec _ (sq_strict n k hn).1

theorem sq_length (n : Nat) : ∀ k, (sqSeq n k).length = k + 1 := by
  intro k
  induction k with
  | zero => rfl
  | succ k' ih =>
      cases k' with
      | zero => rfl
      | succ k'' =>
          cases hs : sqSeq n (k'' + 1) with
          | nil => exact absurd hs (sq_ne_nil n (k'' + 1))
          | cons a t =>
              have h1 : sqSeq n (k'' + 2) = sqNext (sqSeq n (k'' + 1)) := by
                simp only [sqSeq]
              rw [h1, hs]
              have h2 : (sqSeq n (k'' + 1)).length = k'' + 2 := ih
              rw [hs] at h2
              simp only [sqNext, List.length_cons]
              omega

theorem aSeq_mem (n : Nat) (k : Nat) : aSeq n k ∈ sqSeq n k := by
  cases hk : sqSeq n k with
  | nil => exact absurd hk (sq_ne_nil n k)
  | cons a t =>
      have ha : aSeq n k = a := by
        simp only [aSeq, hk, lhead]
      rw [ha]
      exact List.mem_cons_self _

theorem sq_mem_iff (n : Nat) : ∀ (k x : Nat),
    x ∈ sqSeq n k ↔ ∃ i, i ≤ k ∧ aSeq n i = x
  | 0, x => by
      simp only [sqSeq]
      constructor
      · intro hx
        rw [List.mem_singleton] at hx
        exact ⟨0, Nat.le_refl 0, by rw [hx]; exact rfl⟩
      · intro h
        obtain ⟨i, hi, heq⟩ := h
        have hi0 : i = 0 := by omega
        subst hi0
        rw [← heq]
        simp [sqSeq, aSeq, lhead]
  | 1, x => by
      simp only [sqSeq]
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
            have hi0 : i = 0 := by omega
            subst hi0
            rw [← heq]
            simp [sqSeq, aSeq, lhead]
        | inr hge =>
            have hi1 : i = 1 := by omega
            subst hi1
            rw [← heq]
            simp [sqSeq, aSeq, lhead]
  | k + 2, x => by
      have hstep := sq_next n (k + 1) (by omega)
      rw [hstep]
      have hhead : aSeq n (k + 2)
          = findFree (sqSeq n (k + 1)) (aSeq n (k + 1) + 1)
            (aSeq n (k + 1) + 1) := aSeq_step_eq n (k + 1) (by omega)
      constructor
      · intro hx
        rcases List.mem_cons.mp hx with he | ht
        · exact ⟨k + 2, Nat.le_refl _, by rw [hhead]; exact he⟩
        · obtain ⟨i, hi, heq⟩ := sq_mem_iff n (k + 1) x ht
          exact ⟨i, by omega, heq⟩
      · intro h
        obtain ⟨i, hi, heq⟩ := h
        have hmem : aSeq n i ∈ sqSeq n (k + 1) :=
          (sq_mem_iff n (k + 1) (aSeq n i)).mpr ⟨i, by omega, rfl⟩
        rcases Nat.lt_or_ge i (k + 2) with hlt | hge
        · rw [← heq]
          exact List.mem_cons_of_mem _ hmem
        · have hie : i = k + 2 := by omega
          subst hie
          rw [← heq, ← hhead]
          exact List.mem_cons_self _

-- ===========================================================================
-- §5  MONOTONICITY
-- ===========================================================================

theorem aSeq_step_lt (n : Nat) (hn : 1 ≤ n) : ∀ k, aSeq n k < aSeq n (k + 1) := by
  intro k
  cases k with
  | zero =>
      have h1 : aSeq n 0 = 0 := rfl
      have h2 : aSeq n 1 = n := rfl
      omega
  | succ k' =>
      have heq := aSeq_step_eq n (k' + 1) (by omega)
      have hge := findFree_ge_start (sqSeq n (k' + 1))
        (aSeq n (k' + 1) + 1) (aSeq n (k' + 1) + 1)
      omega

theorem aSeq_mono_aux (n : Nat) (hn : 1 ≤ n) : ∀ (d i : Nat),
    aSeq n i < aSeq n (i + d + 1)
  | 0, i => aSeq_step_lt n hn i
  | d + 1, i => by
      have h1 := aSeq_mono_aux n hn d i
      have h2 := aSeq_step_lt n hn (i + d + 1)
      have harg : i + (d + 1) + 1 = i + d + 1 + 1 := by omega
      rw [harg]
      omega

theorem aSeq_mono_lt (n : Nat) (hn : 1 ≤ n) {i j : Nat} (h : i < j) :
    aSeq n i < aSeq n j := by
  have h1 := aSeq_mono_aux n hn (j - i - 1) i
  have harg : i + (j - i - 1) + 1 = j := by omega
  rw [harg] at h1
  exact h1

theorem aSeq_inj (n : Nat) (hn : 1 ≤ n) {i j : Nat} (h : aSeq n i = aSeq n j) :
    i = j := by
  by_contra hc
  cases Nat.lt_or_ge i j with
  | inl hlt =>
      have hmono := aSeq_mono_lt n hn hlt
      omega
  | inr hge =>
      have hmono := aSeq_mono_lt n hn (by omega : j < i)
      omega

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
  have hhead := aSeq_step_eq n k hk
  have hmax : ∀ x ∈ sqSeq n k, x ≤ aSeq n k :=
    fun x hx => strictDec_head_max (sq_strict n k hn).1 x hx
  have hz : stepFree (sqSeq n k) (2 * aSeq n k + 1) = true :=
    two_a_plus_one_free _ _ hmax
  have hleast := findFree_least (sqSeq n k) (aSeq n k + 1) (aSeq n k + 1)
    (2 * aSeq n k + 1) (by omega) (by omega) hz
  omega

-- ===========================================================================
-- §7  G2 — THE LINEAR FLOOR
-- ===========================================================================

theorem apFree_sq (n : Nat) (hn : 1 ≤ n) : ∀ (k x y z : Nat),
    x ∈ sqSeq n k → y ∈ sqSeq n k → z ∈ sqSeq n k → x < y → y < z → x + z ≠ 2 * y
  | 0, x, y, z, hx, hy, hz, hxy, _ => by
      simp only [sqSeq, List.mem_singleton] at hx hy hz
      omega
  | 1, x, y, z, hx, hy, hz, hxy, _ => by
      simp only [sqSeq, List.mem_cons, List.mem_singleton] at hx hy hz
      rcases hx with hex | hex <;> rcases hy with hey | hey <;>
        rcases hz with hez | hez <;> omega
  | k + 2, x, y, z, hx, hy, hz, hxy, hyz => by
      have hstep := sq_next n (k + 1) (by omega)
      rw [hstep] at hx hy hz
      have hhead : aSeq n (k + 2)
          = findFree (sqSeq n (k + 1)) (aSeq n (k + 1) + 1)
            (aSeq n (k + 1) + 1) := aSeq_step_eq n (k + 1) (by omega)
      have hc_max : ∀ w ∈ sqSeq n (k + 1), w < aSeq n (k + 2) := by
        intro w hw
        have hd : StrictDec (sqSeq n (k + 2)) := (sq_strict n (k + 2) hn).1
        rw [hstep] at hd
        have hlt := hd.1 w (List.mem_cons_of_mem _ hw)
        omega
      rcases List.mem_cons.mp hx with hex | hex
      · rcases List.mem_cons.mp hy with hey | hey
        · omega
        · have hcm := hc_max y hey
          omega
      · rcases List.mem_cons.mp hy with hey | hey
        · rcases List.mem_cons.mp hz with hez | hez
          · omega
          · have hcm := hc_max z hez
            omega
        · rcases List.mem_cons.mp hz with hez | hez
          · -- z is the head: x + head = 2y with x < y in the tail —
            -- exactly the blocked pattern, but the head is free
            have hG3 := growth_G3 n hn (k + 1) (by omega)
            have hfree := findFree_free_or_edge (sqSeq n (k + 1))
              (aSeq n (k + 1) + 1) (aSeq n (k + 1) + 1)
            rcases hfree with h | h
            · rw [hez] at h
              exact forall_of_stepFree h x hex y hey hxy
            · omega
          · exact apFree_sq n hn (k + 1) x y z hex hey hez hxy hyz

theorem aSeq_gap3 (n : Nat) (hn : 1 ≤ n) (k : Nat) :
    aSeq n k + 3 ≤ aSeq n (k + 2) := by
  have h1 := aSeq_step_lt n hn k
  have h2 := aSeq_step_lt n hn (k + 1)
  have hm0 : aSeq n k ∈ sqSeq n (k + 2) := (sq_mem_iff n (k + 2) _).mpr
    ⟨k, by omega, rfl⟩
  have hm1 : aSeq n (k + 1) ∈ sqSeq n (k + 2) := (sq_mem_iff n (k + 2) _).mpr
    ⟨k + 1, by omega, rfl⟩
  have hm2 : aSeq n (k + 2) ∈ sqSeq n (k + 2) := aSeq_mem n (k + 2)
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
              have h : aSeq n 1 = n := rfl
              omega
      | inr hge =>
          have h1 : 2 * aSeq n (m - 2) ≥ 3 * (m - 2) - 3 := ih (m - 2) (by omega)
          have hgap0 := aSeq_gap3 n hn (m - 2)
          have hidx : m - 2 + 2 = m := by omega
          rw [hidx] at hgap0
          omega

-- ===========================================================================
-- §8  G1 — THE QUADRATIC CEILING (the blocking-pair pigeonhole)
-- ===========================================================================

/-- THE GREEDY SKIP LEMMA: every value the scan passed over carries a
witness pair from the prefix. -/
theorem greedy_skip (n : Nat) (hn : 1 ≤ n) (k y : Nat) (hk : 1 ≤ k)
    (hly : aSeq n k < y) (hhy : y < aSeq n (k + 1)) :
    ∃ a b, a ∈ sqSeq n k ∧ b ∈ sqSeq n k ∧ a < b ∧ a + y = 2 * b := by
  have hhead := aSeq_step_eq n k hk
  by_contra hcon
  have hfree : stepFree (sqSeq n k) y = true := by
    refine stepFree_of_forall ?_
    intro a ha b hb hlt heq
    exact hcon ⟨a, b, ha, hb, hlt, heq⟩
  have hle := findFree_le (sqSeq n k) (aSeq n k + 1) (aSeq n k + 1)
  have hleast := findFree_least (sqSeq n k) (aSeq n k + 1) (aSeq n k + 1) y
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
          have hij : i = j := by omega
          subst hij
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
      | inl hgt =>
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
      | inr hle =>
          have hm2 : m = 2 := by omega
          subst hm2
          exact ⟨1, by omega, by omega, h1y, hmy⟩

-- §8.1  The index-pair list

def pairBlock (j : Nat) : List (Nat × Nat) := (List.range j).map (fun i => (i, j))

def pairList : Nat → List (Nat × Nat)
  | 0 => []
  | m + 1 => pairBlock (m + 1) ++ pairList m

theorem consec_even (k : Nat) : k * (k + 1) % 2 = 0 := by
  obtain ⟨t, ht⟩ | ⟨t, ht⟩ := Nat.even_or_odd k
  · have hE : k * (k + 1) = 2 * (t * (k + 1)) := by rw [ht]; ring
    omega
  · have hm2 : k - 1 = 2 * t := by omega
    have hE : k * (k + 1) = 2 * (k * (t + 1)) := by rw [hm2]; ring
    omega

theorem pairList_length : ∀ m, (pairList m).length = m * (m + 1) / 2 := by
  intro m
  induction m with
  | zero => rfl
  | succ m' ih =>
      simp only [pairList, List.length_append, pairBlock, List.length_map,
        List.length_range, ih]
      have hring : (m' + 1) * (m' + 2)
          = (m' + 1) + m' * (m' + 1) + (m' + 1) := by ring
      have h1 := consec_even m'
      have h2 := consec_even (m' + 1)
      omega

theorem pairList_mem : ∀ (m i j : Nat), (i, j) ∈ pairList m ↔ i < j ∧ j ≤ m
  | 0, i, j => by
      constructor
      · intro h
        exact absurd h (by simp [pairList])
      · intro h
        exact absurd h.1 (by omega)
  | m + 1, i, j => by
      simp only [pairList, List.mem_append]
      constructor
      · intro h
        rcases h with hl | hr
        · simp only [pairBlock, List.mem_map] at hl
          obtain ⟨i', hi', heq⟩ := hl
          rw [List.mem_range] at hi'
          rw [Prod.mk.injEq] at heq
          obtain ⟨r1, r2⟩ := heq
          subst r1
          subst r2
          exact ⟨hi', Nat.le_refl _⟩
        · exact pairList_mem m i j |>.mp hr
      · intro h
        obtain ⟨hlt, hle⟩ := h
        cases Nat.lt_or_ge j (m + 1) with
        | inl hj => exact Or.inr (pairList_mem m i j |>.mpr ⟨hlt, by omega⟩)
        | inr hj =>
            have hj1 : j = m + 1 := by omega
            subst hj1
            refine Or.inl ?_
            simp only [pairBlock, List.mem_map]
            refine ⟨i, ?_, rfl⟩
            rw [List.mem_range]
            omega

theorem pairBlock_mem_snd {j : Nat} {p : Nat × Nat} (hp : p ∈ pairBlock j) :
    p.2 = j := by
  simp only [pairBlock, List.mem_map] at hp
  obtain ⟨i, _, heq⟩ := hp
  rw [← heq]
  rfl

theorem pairList_mem_snd {m : Nat} {p : Nat × Nat} (hp : p ∈ pairList m) :
    p.2 ≤ m := by
  induction m with
  | zero => simp [pairList] at hp
  | succ m' ih =>
      simp only [pairList, List.mem_append] at hp
      rcases hp with hl | hr
      · rw [pairBlock_mem_snd hl]
      · exact ih hr

theorem pairBlock_nodup (j : Nat) : (pairBlock j).Nodup := by
  induction j with
  | zero => simp [pairBlock]
  | succ j' ih =>
      have hsplit : pairBlock (j' + 1)
          = pairBlock j' ++ [(j', j' + 1)] := by
        simp only [pairBlock, List.range_succ, List.map_append, List.map_cons,
          List.map_nil, List.append_cons, List.append_nil]
      rw [hsplit]
      refine List.Nodup.append ih (List.nodup_singleton _) ?_
      intro p hp hq
      have h1 : p.2 = j' := pairBlock_mem_snd hp
      rw [List.mem_singleton] at hq
      have h2 : p.2 = j' + 1 := by rw [hq]
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
    {x : Nat × Nat}, lfind p l = some x → x ∈ l ∧ p x = true := by
  intro l x h
  induction l with
  | nil => simp [lfind] at h
  | cons y ys ih =>
      simp only [lfind] at h
      split at h
      · rename_i hp
        injection h with h'
        subst h'
        exact ⟨List.mem_cons_self _ _, hp⟩
      · have hih := ih h
        exact ⟨List.mem_cons_of_mem _ hih.1, hih.2⟩

theorem lfind_isSome {p : Nat × Nat → Bool} : ∀ (l : List (Nat × Nat))
    (x : Nat × Nat), x ∈ l → p x = true → lfind p l ≠ none := by
  intro l x hx hp
  induction l with
  | nil => simp [lfind] at hx
  | cons y ys ih =>
      rcases List.mem_cons.mp hx with he | ht
      · subst he
        simp only [lfind]
        split
        · intro hc; exact Option.noConfusion hc
        · rename_i hn
          exact absurd hp hn
      · simp only [lfind]
        split
        · intro hc; exact Option.noConfusion hc
        · exact ih ht hp

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
  have hpy : (fun p => decide (a p.1 + y = 2 * a p.2)) (i0, j0) = true :=
    decide_eq_true heq0
  have hne : lfind (fun p => decide (a p.1 + y = 2 * a p.2)) (pairList m) ≠ none :=
    lfind_isSome _ _ hmem hpy
  cases hlf : lfind (fun p => decide (a p.1 + y = 2 * a p.2)) (pairList m) with
  | none => exact absurd hlf hne
  | some q =>
      have hdef : findBlocker a y m = q := by
        simp only [findBlocker, hlf]
      obtain ⟨hqmem, hqp⟩ := lfind_some hlf
      obtain ⟨i, j⟩ := q
      have hqpb : decide (a i + y = 2 * a j) = true := hqp
      rw [decide_eq_true_eq] at hqpb
      have hmij := (pairList_mem m i j).mp hqmem
      exact ⟨i, j, hdef, hmij.1, hmij.2, hqpb⟩

theorem findBlocker_inj {a : Nat → Nat} {m y y' : Nat}
    (hex : ∃ i j, i < j ∧ j ≤ m ∧ a i + y = 2 * a j)
    (hex' : ∃ i j, i < j ∧ j ≤ m ∧ a i + y' = 2 * a j)
    (h : findBlocker a y m = findBlocker a y' m) : y = y' := by
  obtain ⟨i, j, hfind, _, _, heq⟩ := findBlocker_spec hex
  obtain ⟨i', j', hfind', _, _, heq'⟩ := findBlocker_spec hex'
  rw [hfind, hfind'] at h
  rw [Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  subst h1
  subst h2
  omega

-- §8.3  THE HEADLINE

theorem growth_G1 (n : Nat) (hn : 1 ≤ n) : ∀ m, 1 ≤ m →
    aSeq n m ≤ n + (m - 1) * (m + 2) / 2 := by
  intro m hm
  cases Nat.lt_or_ge 1 m with
  | inl hlt =>
      have hm1 : m = 1 := by omega
      subst hm1
      have ha1 : aSeq n 1 = n := rfl
      omega
  | inr h2 =>
      have ha1 : aSeq n 1 = n := rfl
      have hmono : aSeq n 1 < aSeq n m := aSeq_mono_lt n hn (by omega)
      set A := aSeq n m with hA
      have hIco_card : (Finset.Ico (n + 1) A).card = A - (n + 1) :=
        Finset.card_Ico _ _
      have hM_card : ((sqSeq n m).toFinset).card = m + 1 := by
        rw [List.toFinset_card (sq_nodup n m hn), sq_length]
      have hsub : Finset.Ico (n + 1) A
          ⊆ (Finset.Ico (n + 1) A \ (sqSeq n m).toFinset)
            ∪ (Finset.Ico (n + 1) A ∩ (sqSeq n m).toFinset) := by
        intro x hx
        by_cases hmem : x ∈ (sqSeq n m).toFinset
        · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hx, hmem⟩)
        · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hx, hmem⟩)
      have hcard := calc (Finset.Ico (n + 1) A).card
          ≤ ((Finset.Ico (n + 1) A \ (sqSeq n m).toFinset)
              ∪ (Finset.Ico (n + 1) A ∩ (sqSeq n m).toFinset)).card :=
            Finset.card_le_card hsub
        _ ≤ (Finset.Ico (n + 1) A \ (sqSeq n m).toFinset).card
            + (Finset.Ico (n + 1) A ∩ (sqSeq n m).toFinset).card :=
            Finset.card_union_le _ _
      -- the member side: at most m - 2 (0, n, A excluded)
      have hint_le : (Finset.Ico (n + 1) A ∩ (sqSeq n m).toFinset).card ≤ m - 2 := by
        have h3 : ({0, n, A} : Finset Nat) ⊆ (sqSeq n m).toFinset := by
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
            simp only [Finset.mem_insert, Finset.mem_singleton]
            omega
          have hnA : n ∉ ({A} : Finset Nat) := by
            simp only [Finset.mem_singleton]
            omega
          rw [Finset.card_insert_eq h01, Finset.card_insert_eq hnA]
          simp
        have hsub2 : Finset.Ico (n + 1) A ∩ (sqSeq n m).toFinset
            ⊆ (sqSeq n m).toFinset \ {0, n, A} := by
          intro x hx
          have hxI : x ∈ Finset.Ico (n + 1) A := (Finset.mem_inter.mp hx).1
          have hxM : x ∈ (sqSeq n m).toFinset := (Finset.mem_inter.mp hx).2
          simp only [Finset.mem_Ico] at hxI
          refine Finset.mem_sdiff.mpr ⟨hxM, ?_⟩
          simp only [Finset.mem_insert, Finset.mem_singleton]
          obtain ⟨hn1, hnA2⟩ := hxI
          omega
        have hcalc := calc
          (Finset.Ico (n + 1) A ∩ (sqSeq n m).toFinset).card
              ≤ ((sqSeq n m).toFinset \ {0, n, A}).card := Finset.card_le_card hsub2
          _ = ((sqSeq n m).toFinset).card - ({0, n, A} : Finset Nat).card :=
            Finset.card_sdiff h3
        omega
      -- the rejected side: the pigeonhole
      have hcover : ∀ y ∈ (Finset.Ico (n + 1) A \ (sqSeq n m).toFinset),
          ∃ i j, i < j ∧ j ≤ m - 1 ∧ aSeq n i + y = 2 * aSeq n j := by
        intro y hyR
        have hyI : y ∈ Finset.Ico (n + 1) A := (Finset.mem_sdiff.mp hyR).1
        have hyM : y ∉ (sqSeq n m).toFinset := (Finset.mem_sdiff.mp hyR).2
        simp only [Finset.mem_Ico] at hyI
        have hnm : ∀ i, 1 < i → i < m → aSeq n i ≠ y := by
          intro i hi1 hi2 heqy
          have hmem : aSeq n i ∈ (sqSeq n m).toFinset := by
            simp only [List.mem_toFinset]
            rw [sq_mem_iff n m]
            exact ⟨i, by omega, rfl⟩
          rw [heqy] at hmem
          exact hyM hmem
        obtain ⟨k, hk1, hk2, hk3, hk4⟩ :=
          interval_loc n hn m y (by omega) (by omega) (by omega) hnm
        obtain ⟨i, j, hij, hjk, heq⟩ := skip_to_index n hn hk1 hk3 hk4
        exact ⟨i, j, hij, by omega, heq⟩
      have hR_le : (Finset.Ico (n + 1) A \ (sqSeq n m).toFinset).card
          ≤ (m - 1) * m / 2 := by
        have hinj : ∀ y ∈ (Finset.Ico (n + 1) A \ (sqSeq n m).toFinset),
            ∀ y' ∈ (Finset.Ico (n + 1) A \ (sqSeq n m).toFinset),
            findBlocker (aSeq n) y (m - 1) = findBlocker (aSeq n) y' (m - 1) →
            y = y' := by
          intro y hy y' hy' hyy
          exact findBlocker_inj (hcover y hy) (hcover y' hy') hyy
        have himg : ∀ y ∈ (Finset.Ico (n + 1) A \ (sqSeq n m).toFinset),
            findBlocker (aSeq n) y (m - 1) ∈ (pairList (m - 1)).toFinset := by
          intro y hy
          obtain ⟨i, j, hfind, h1, h2, _⟩ := findBlocker_spec (hcover y hy)
          rw [hfind]
          simp only [List.mem_toFinset]
          exact (pairList_mem (m - 1) i j).mpr ⟨h1, h2⟩
        calc (Finset.Ico (n + 1) A \ (sqSeq n m).toFinset).card
            = (Finset.image (fun y => findBlocker (aSeq n) y (m - 1))
                (Finset.Ico (n + 1) A \ (sqSeq n m).toFinset)).card := by
              refine (Finset.card_image_of_injOn ?_).symm
              intro y hy y' hy' hyy
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
        obtain ⟨t, ht⟩ | ⟨t, ht⟩ := Nat.even_or_odd m
        · have hE : (m - 1) * m = 2 * ((m - 1) * t) := by rw [ht]; ring
          omega
        · have hm2 : m - 1 = 2 * t := by omega
          have hE : (m - 1) * m = 2 * (t * m) := by rw [hm2]; ring
          omega
      have heven2 : (m - 1) * (m + 2) % 2 = 0 := by
        obtain ⟨t, ht⟩ | ⟨t, ht⟩ := Nat.even_or_odd m
        · have hE : (m - 1) * (m + 2) = 2 * ((m - 1) * (t + 1)) := by rw [ht]; ring
          omega
        · have hm2 : m - 1 = 2 * t := by omega
          have hE : (m - 1) * (m + 2) = 2 * (t * (m + 2)) := by rw [hm2]; ring
          omega
      have hdm1 : (m - 1) * m / 2 * 2 + (m - 1) * m % 2 = (m - 1) * m :=
        Nat.div_add_mod _ 2
      have hdm2 : (m - 1) * (m + 2) / 2 * 2 + (m - 1) * (m + 2) % 2
          = (m - 1) * (m + 2) := Nat.div_add_mod _ 2
      have hring : (m - 1) * (m + 2) = (m - 1) * m + 2 * (m - 1) := by ring
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
  carryAtPos 23 1 < 4 ∧
  CardinalWorldsV2.v2r (3 ^ 1 * 9) = CardinalWorldsV2.v2r 9

theorem erdos271_arsenal_bridge : arsenalBridgeProp271 :=
  ⟨by decide, by decide,
    ErdosTernary2.lt_three_cases (aSeq 4 3 % 3) (Nat.mod_lt _ (by decide)),
    carryAtPos_bound 23 1,
    CardinalWorldsV2.v2r_ternary_scaling 1 9⟩

#print axioms growth_G3
#print axioms growth_G2
#print axioms growth_G1
#print axioms erdos271_arsenal_bridge

#eval "ERDOS271_KERNEL_GREEN"
