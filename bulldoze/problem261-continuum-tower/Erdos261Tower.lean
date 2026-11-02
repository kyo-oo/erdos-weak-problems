import Init
/-
# ERDŐS #261 — THE CONTINUUM QUESTION (REAL-x VARIANT): KILLED — CORE-ONLY

The second question of Erdős #261 [Er74b, ErGr80, Er88c] asks whether some
x admits at least 2^{ℵ₀} distinct representations

    x  =  Σ_k a_k / 2^{a_k}          (distinct positive integers a_k).

Kill #5 (`problem261-two-solutions`) settled the weakened sub-question of
[Er88c] (two representations; x = 1/2 with three witnesses). This module
kills the CONTINUUM question for unrestricted (real) x — CORE-ONLY,
fully computable, zero-dependency.

## THE TOWER

Let  m k = 2^(k+2) − k − 3   (k ≥ 0):  1, 4, 11, 26, 57, 120, 247, …

**Halving identity (scaled, pure Nat).** With
`intSum m j = Σ_{i=1..j} (m+i)·2^(j−i)`:

    intSum m j + (m + j + 2) = (m + 2)·2^j,

so at m = m k, j = k+1 (where m k + k + 3 = 2^{k+2}):

    Σ_{i=1..k+1} (m k + i)·2^{k+1−i}  =  m k·2^{k+1}.

Region k = [m k, m k + k + 1] is EXACTLY halved by its endpoint against
its interior. Regions are pairwise disjoint (gaps 2, 5, 12, 27, … grow).

**The tower map.** F σ : on region k take the left piece {m k} when σ k,
the right piece {m k+1, …, m k+k+1} when ¬σ k; nothing on gaps.

**Scaled partials.** P f M = Σ_{a ≤ M, f a} a·2^{M−a} (a natural number);
the rational partial value of f at M is (P f M)/2^M. The theorems:

* `checkpoint_eq` : P (F σ) (m K − 1) = P (F τ) (m K − 1) for ALL σ, τ, K.
* `tower_sameValue`: for all p/q > 0 and large M, the values of F σ and
  F τ agree within p/q — in the completion ALL F σ represent the SAME
  real x* = Σ_k m k/2^{m k}.
* `tower_cauchy` : M ↦ (P (F σ) M)/2^M is Cauchy (x* exists).
* `F_injective`  : σ ↦ F σ is injective — 2^{ℵ₀} distinct representations.

x* is irrational (isolated bit-clusters, growing zero-gaps; DERIVATION.md
§5). If the intended reading requires x RATIONAL, that case remains open
(walls mapped in DERIVATION.md §6).

## §-MAP

* §1  list helpers (map congruence, sum pulls, range shifts)
* §2  pow2 engine
* §3  the family m k: separation arithmetic
* §4  the scaled-halving identity
* §5  the tower map F (computable region search)
* §6  scaled partials P, segments, splitting law
* §7  the region law and the checkpoint theorem
* §8  tail bound, sameValue, Cauchy
* §9  injectivity + MAIN THEOREM
* §10 receipts (#eval) + axiom gates
-/

namespace Erdos261Tower
-- ===========================================================================
-- §1  LIST HELPERS (core-only)
-- ===========================================================================

theorem listMapCongr {α β : Type} {l : List α} {f g : α → β}
    (h : ∀ x ∈ l, f x = g x) : l.map f = l.map g := by
  induction l with
  | nil => rfl
  | cons a t ih =>
      rw [List.map_cons, List.map_cons, h a (by simp),
          ih (fun x hx => h x (by simp [hx]))]

/-- Pull a constant out of an ite-guarded sum. -/
theorem sum_ite_mul_const {l : List Nat} {fb : Nat → Bool} {g : Nat → Nat} (c : Nat) :
    (l.map (fun a => if fb a = true then g a * c else 0)).sum
      = (l.map (fun a => if fb a = true then g a else 0)).sum * c := by
  induction l with
  | nil => simp
  | cons a t ih =>
      rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, ih]
      cases hfa : fb a with
      | true =>
          show g a * c + (t.map (fun a => if fb a = true then g a else 0)).sum * c
              = (g a + (t.map (fun a => if fb a = true then g a else 0)).sum) * c
          rw [Nat.add_mul]
      | false =>
          show (0 : Nat) + (t.map (fun a => if fb a = true then g a else 0)).sum * c
              = ((0 : Nat) + (t.map (fun a => if fb a = true then g a else 0)).sum) * c
          simp only [Nat.zero_add]

/-- Pull a constant out of a plain mapped sum. -/
theorem sum_map_mul {l : List Nat} {g : Nat → Nat} (c : Nat) :
    (l.map (fun x => g x * c)).sum = (l.map g).sum * c := by
  induction l with
  | nil => simp
  | cons a t ih =>
      rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, ih]
      show g a * c + (t.map g).sum * c = (g a + (t.map g).sum) * c
      rw [Nat.add_mul]

/-- Shift a range sum. -/
theorem sum_range_shift (h : Nat → Nat) (n : Nat) :
    ((List.range (n + 1)).map h).sum
      = h 0 + ((List.range n).map (fun x => h (x + 1))).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hr : List.range (n + 1 + 1) = List.range (n + 1) ++ [n + 1] :=
        List.range_succ
      rw [hr, List.map_append, List.sum_append, ih,
          List.range_succ, List.map_append, List.sum_append]
      simp only [List.map_singleton, List.sum_singleton]
      omega

theorem sum_le_sum_of_forall {l : List Nat} {f g : Nat → Nat} (h : ∀ x ∈ l, f x ≤ g x) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
      rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons]
      have h1 := h a (by simp)
      have h2 := ih (fun x hx => h x (by simp [hx]))
      omega

theorem range_split (n d : Nat) :
    List.range (n + 1 + d) = List.range (n + 1) ++ (List.range d).map (fun x => n + 1 + x) := by
  induction d with
  | zero => simp
  | succ d ih =>
      have h1 : n + 1 + (d + 1) = (n + 1 + d) + 1 := by omega
      have hr1 : List.range ((n + 1 + d) + 1) = List.range (n + 1 + d) ++ [n + 1 + d] :=
        List.range_succ
      have hr2 : List.range (d + 1) = List.range d ++ [d] := List.range_succ
      rw [h1, hr1, ih, List.append_assoc, hr2, List.map_append, List.map_singleton]

-- ===========================================================================
-- §2  THE pow2 ENGINE (pure Nat)
-- ===========================================================================

def pow2 : Nat → Nat
  | 0 => 1
  | k + 1 => 2 * pow2 k

theorem pow2_succ_eq (k : Nat) : pow2 (k + 1) = 2 * pow2 k := rfl

theorem pow2_pos (k : Nat) : 0 < pow2 k := by
  induction k with
  | zero => decide
  | succ k ih => rw [pow2_succ_eq]; omega

theorem pow2_add (a b : Nat) : pow2 (a + b) = pow2 a * pow2 b := by
  induction b with
  | zero =>
      have h0 : pow2 0 = 1 := rfl
      simp [h0, Nat.add_zero, Nat.mul_one]
  | succ b ih =>
      rw [Nat.add_succ, pow2_succ_eq, pow2_succ_eq, ih]
      exact Nat.mul_left_comm 2 (pow2 a) (pow2 b)

theorem two_pow2_ge (k : Nat) : k + 4 ≤ pow2 (k + 2) := by
  induction k with
  | zero => decide
  | succ k ih =>
      have hnorm : k + 1 + 2 = k + 3 := by omega
      have h : pow2 (k + 3) = 2 * pow2 (k + 2) := pow2_succ_eq (k + 2)
      rw [hnorm, h]
      omega

theorem two_pow2_gt3 (k : Nat) : 2 * k + 3 < pow2 (k + 2) := by
  induction k with
  | zero => decide
  | succ k ih =>
      have hnorm : k + 1 + 2 = k + 3 := by omega
      have h : pow2 (k + 3) = 2 * pow2 (k + 2) := pow2_succ_eq (k + 2)
      rw [hnorm, h]
      omega

/-- Quadratic growth: k² ≤ 2^k for k ≥ 4. -/
theorem pow2_sq (k : Nat) (hk : 4 ≤ k) : k * k ≤ pow2 k := by
  induction k with
  | zero => omega
  | succ k ih =>
      rcases Nat.lt_or_ge 4 k with h4 | h4
      · have h := ih (show 4 ≤ k by omega)
        have hp : pow2 (k + 1) = 2 * pow2 k := pow2_succ_eq k
        rw [hp]
        have h4k : 4 * k ≤ k * k := Nat.mul_le_mul (show 4 ≤ k by omega) (Nat.le_refl k)
        have h2k : 2 * k + 1 ≤ k * k := by omega
        have hexp : (k + 1) * (k + 1) = k * k + k + (k + 1) := by
          rw [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]
        omega
      · rcases Nat.eq_or_lt_of_le h4 with heq | hlt
        · subst heq
          decide
        · have hk3 : k = 3 := by omega
          subst hk3
          have hp : pow2 (3 + 1) = 2 * pow2 3 := pow2_succ_eq 3
          have hp3 : pow2 3 = 8 := by decide
          rw [hp, hp3]
          decide

-- ===========================================================================
-- §3  THE HALVING FAMILY — SEPARATION ARITHMETIC (pure Nat)
-- ===========================================================================

/-- m k = 2^(k+2) − k − 3 : 1, 4, 11, 26, 57, 120, 247, 502, … -/
def mfun (k : Nat) : Nat := pow2 (k + 2) - k - 3

theorem mfun_eq (k : Nat) : mfun k + k + 3 = pow2 (k + 2) := by
  have h := two_pow2_ge k
  unfold mfun
  omega

theorem mfun_pos (k : Nat) : 1 ≤ mfun k := by
  have h := two_pow2_ge k
  unfold mfun
  omega

theorem mfun_ge_succ (k : Nat) : k + 1 ≤ mfun k := by
  have h := two_pow2_gt3 k
  unfold mfun
  omega

theorem mfun_sep (k : Nat) : mfun k + k + 1 < mfun (k + 1) := by
  have e1 := mfun_eq k
  have e2 := mfun_eq (k + 1)
  have hnorm : k + 1 + 2 = k + 3 := by omega
  rw [hnorm] at e2
  have hp : pow2 (k + 3) = 2 * pow2 (k + 2) := pow2_succ_eq (k + 2)
  omega

theorem mfun_lt_succ (k : Nat) : mfun k < mfun (k + 1) := by
  have h := mfun_sep k
  omega

theorem mfun_lt_of_lt {a b : Nat} (h : a < b) : mfun a < mfun b := by
  induction b generalizing a with
  | zero => omega
  | succ b ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.mp h with h' | h'
      · have hlt := ih h'
        have hs := mfun_lt_succ b
        omega
      · rw [h']
        exact mfun_lt_succ b

theorem mfun_le_of_le {a b : Nat} (h : a ≤ b) : mfun a ≤ mfun b := by
  rcases Nat.eq_or_lt_of_le h with heq | hlt
  · rw [heq]
    exact Nat.le_refl _
  · exact Nat.le_of_lt (mfun_lt_of_lt hlt)

theorem mfun_inj {a b : Nat} (h : mfun a = mfun b) : a = b := by
  rcases Nat.lt_or_ge a b with hlt | hgt
  · exact absurd h (Nat.ne_of_lt (mfun_lt_of_lt hlt))
  · rcases Nat.lt_or_ge b a with hlt' | hge'
    · exact absurd h.symm (Nat.ne_of_lt (mfun_lt_of_lt hlt'))
    · exact Nat.le_antisymm hge' hgt

theorem region_disj {k j : Nat} (hjk : j < k) (a : Nat)
    (h1 : mfun k ≤ a) (h2 : a ≤ mfun k + k + 1)
    (h3 : mfun j < a) (h4 : a ≤ mfun j + j + 1) : False := by
  have hle : mfun (j + 1) ≤ mfun k := mfun_le_of_le (by omega)
  have hsep := mfun_sep j
  omega

theorem region_unique {k j : Nat} (a : Nat)
    (h1 : mfun k ≤ a) (h2 : a ≤ mfun k + k + 1)
    (h1' : mfun j ≤ a) (h2' : a ≤ mfun j + j + 1) : k = j := by
  rcases Nat.lt_or_ge k j with hlt | hge
  · have hmono : mfun (k + 1) ≤ mfun j := mfun_le_of_le (by omega)
    have hsep := mfun_sep k
    exact (region_disj hlt a h1' h2' (by omega) h2).elim
  · rcases Nat.lt_or_ge j k with hlt' | hge'
    · have hmono : mfun (j + 1) ≤ mfun k := mfun_le_of_le (by omega)
      have hsep := mfun_sep j
      exact (region_disj hlt' a h1 h2 (by omega) h2').elim
    · omega

-- ===========================================================================
-- §4  THE SCALED-HALVING IDENTITY (pure Nat)
-- ===========================================================================

/-- Scaled interior sum: Σ_{i=1..j} (m+i)·2^{j−i}. -/
def intSum (m j : Nat) : Nat :=
  ((List.range j).map (fun i => (m + i + 1) * pow2 (j - i - 1))).sum

theorem intSum_succ (m j : Nat) :
    intSum m (j + 1) = 2 * intSum m j + (m + j + 1) := by
  have hlast : (m + j + 1) * pow2 (j + 1 - j - 1) = m + j + 1 := by
    have hz : j + 1 - j - 1 = 0 := by omega
    have hp0 : pow2 0 = 1 := rfl
    rw [hz, hp0, Nat.mul_one]
  unfold intSum
  rw [List.range_succ, List.map_append, List.sum_append,
      List.map_singleton, List.sum_singleton, hlast]
  have hcongr : (List.range j).map (fun i => (m + i + 1) * pow2 (j + 1 - i - 1))
      = (List.range j).map (fun i => (m + i + 1) * pow2 (j - i - 1) * 2) := by
    refine listMapCongr (fun i hi => ?_)
    have hilt : i < j := List.mem_range.mp hi
    have hidx : j + 1 - i - 1 = (j - i - 1) + 1 := by omega
    rw [hidx, pow2_succ_eq, ← Nat.mul_assoc]
    exact Nat.mul_right_comm (m + i + 1) 2 (pow2 (j - i - 1))
  rw [hcongr, sum_map_mul]
  omega

/-- THE SCALED-HALVING IDENTITY. -/
theorem halving_nat (m j : Nat) :
    intSum m j + (m + j + 2) = (m + 2) * pow2 j := by
  induction j with
  | zero =>
      have hp0 : pow2 0 = 1 := rfl
      show (0 : Nat) + (m + 0 + 2) = (m + 2) * 1
      omega
  | succ j ih =>
      rw [intSum_succ, pow2_succ_eq]
      have hstep : (m + 2) * (2 * pow2 j) = 2 * ((m + 2) * pow2 j) :=
        Nat.mul_left_comm (m + 2) 2 (pow2 j)
      rw [hstep]
      omega

/-- The region-halving corollary. -/
theorem halving_region (k : Nat) :
    intSum (mfun k) (k + 1) = mfun k * pow2 (k + 1) := by
  have h := halving_nat (mfun k) (k + 1)
  have he : mfun k + k + 3 = pow2 (k + 2) := mfun_eq k
  have hp : pow2 (k + 2) = 2 * pow2 (k + 1) := pow2_succ_eq (k + 1)
  have hsplit : (mfun k + 2) * pow2 (k + 1) = mfun k * pow2 (k + 1) + 2 * pow2 (k + 1) := by
    rw [Nat.add_mul]
  omega

-- ===========================================================================
-- §5  THE TOWER MAP F (computable region search — no choice axiom)
-- ===========================================================================

/-- Downward search for the highest region j ≤ k containing a. -/
def findRegion (a : Nat) : Nat → Option Nat
  | 0 => if mfun 0 ≤ a ∧ a ≤ mfun 0 + 0 + 1 then some 0 else none
  | k + 1 =>
      if mfun (k + 1) ≤ a ∧ a ≤ mfun (k + 1) + (k + 1) + 1 then some (k + 1)
      else findRegion a k

theorem findRegion_spec {a k j : Nat} (h : findRegion a k = some j) :
    j ≤ k ∧ mfun j ≤ a ∧ a ≤ mfun j + j + 1 := by
  induction k generalizing j with
  | zero =>
      simp only [findRegion] at h
      split at h
      · next hcon =>
          cases j with
          | zero => exact ⟨Nat.le_refl _, hcon.1, hcon.2⟩
          | succ j' =>
              exact absurd (Option.some.inj h) (by omega)
      · next hcon => exact absurd h (by simp)
  | succ k ih =>
      simp only [findRegion] at h
      split at h
      · next hcon =>
          cases j with
          | zero => exact absurd (Option.some.inj h) (by omega)
          | succ j' =>
              have hkj : k + 1 = j' + 1 := Option.some.inj h
              refine ⟨by omega, ?_, ?_⟩
              · rw [← hkj]; exact hcon.1
              · rw [← hkj]; exact hcon.2
      · next hcon =>
          have hik := ih h
          exact ⟨by omega, hik.2.1, hik.2.2⟩

theorem findRegion_find {a k j : Nat} (hjk : j ≤ k)
    (h1 : mfun j ≤ a) (h2 : a ≤ mfun j + j + 1) :
    findRegion a k = some j := by
  induction k generalizing j with
  | zero =>
      have hj0 : j = 0 := by omega
      subst hj0
      simp only [findRegion]
      rw [if_pos ⟨h1, h2⟩]
  | succ k ih =>
      simp only [findRegion]
      split
      · next hcon =>
          have : k + 1 = j := region_unique a hcon.1 hcon.2 h1 h2
          subst this
          rfl
      · next hcon =>
          have hnot : ¬(j = k + 1) := by
            intro hjk'
            subst hjk'
            exact hcon ⟨h1, h2⟩
          exact ih (by omega) h1 h2

/-- F σ: on region k take {m k} when σ k, the interior when ¬σ k;
nothing on gap indices. -/
def F (σ : Nat → Bool) (a : Nat) : Bool :=
  match findRegion a a with
  | some k => if a = mfun k then σ k else !σ k
  | none => false

theorem F_P (σ : Nat → Bool) (k : Nat) : F σ (mfun k) = σ k := by
  have hk : k ≤ mfun k := by have := mfun_ge_succ k; omega
  have hfound : findRegion (mfun k) (mfun k) = some k :=
    findRegion_find hk (Nat.le_refl _) (by omega)
  simp only [F, hfound, if_true]

theorem F_Q (σ : Nat → Bool) {k a : Nat}
    (h1 : mfun k < a) (h2 : a ≤ mfun k + k + 1) : F σ a = !σ k := by
  have hk : k ≤ a := by have := mfun_ge_succ k; omega
  have hfound : findRegion a a = some k := findRegion_find hk (by omega) h2
  simp only [F, hfound]
  rw [if_neg (by omega)]

theorem F_gap (σ : Nat → Bool) (a : Nat) (h : F σ a = true) :
    ∃ k, mfun k ≤ a ∧ a ≤ mfun k + k + 1 := by
  simp only [F] at h
  split at h
  · next j hr =>
      obtain ⟨hle, hlo, hhi⟩ := findRegion_spec hr
      exact ⟨j, hlo, hhi⟩
  · next => simp at h

theorem F_false_between (σ : Nat → Bool) (K a : Nat)
    (h1 : mfun K + K + 1 < a) (h2 : a < mfun (K + 1)) : F σ a = false := by
  have hnone : findRegion a a = none := by
    cases hh : findRegion a a with
    | none => rfl
    | some j =>
        exfalso
        obtain ⟨hj1, hj2, hj3⟩ := findRegion_spec hh
        rcases Nat.lt_or_ge j (K + 1) with hlt | hge
        · have hmono : mfun j ≤ mfun K := mfun_le_of_le (by omega)
          omega
        · have hmono : mfun (K + 1) ≤ mfun j := mfun_le_of_le (by omega)
          omega
  simp only [F, hnone]

-- ===========================================================================
-- §6  SCALED PARTIALS, SEGMENTS, SPLITTING LAW
-- ===========================================================================

/-- Scaled partial: P f M = Σ_{a ≤ M, f a} a·2^{M−a}. -/
def P (f : Nat → Bool) (M : Nat) : Nat :=
  ((List.range (M + 1)).map (fun a => if f a then a * pow2 (M - a) else 0)).sum

/-- Scaled segment: Σ_{x < M+1−n} [f (n+x)] (n+x)·2^{M−n−x}. -/
def seg (f : Nat → Bool) (n M : Nat) : Nat :=
  ((List.range (M + 1 - n)).map
    (fun x => if f (n + x) then (n + x) * pow2 (M - n - x) else 0)).sum

theorem P_zero (f : Nat → Bool) : P f 0 = 0 := by
  show (if f 0 = true then (0 : Nat) * pow2 (0 - 0) else 0) = 0
  cases f 0 with
  | true => show (0 : Nat) * pow2 (0 - 0) = 0; omega
  | false => rfl

theorem P_split (f : Nat → Bool) (M d : Nat) :
    P f (M + d) = P f M * pow2 d + seg f (M + 1) (M + d) := by
  have hnorm : M + d + 1 = M + 1 + d := by omega
  simp only [P, seg]
  rw [hnorm, range_split M d, List.map_append, List.sum_append]
  have hfirst : (List.range (M + 1)).map (fun a => if f a then a * pow2 (M + d - a) else 0)
      = (List.range (M + 1)).map (fun a => if f a then a * pow2 (M - a) * pow2 d else 0) := by
    refine listMapCongr (fun a ha => ?_)
    have ham : a ≤ M := Nat.le_of_lt_succ (List.mem_range.mp ha)
    have hidx : M + d - a = (M - a) + d := by omega
    rw [hidx, pow2_add, Nat.mul_assoc]
  rw [hfirst, sum_ite_mul_const]
  -- second part: reindex to the seg form
  have hsecond : ((List.range d).map (fun x => M + 1 + x)).map
      (fun a => if f a then a * pow2 (M + d - a) else 0)
      = (List.range d).map
          (fun x => if f (M + 1 + x) then (M + 1 + x) * pow2 (M + d - (M + 1 + x)) else 0) := by
    rw [List.map_map]
    exact listMapCongr (fun x _ => rfl)
  rw [hsecond]
  have hcount : M + 1 + d - (M + 1) = d := by omega
  rw [hcount]
  have hexp : ∀ x ∈ List.range d,
      (fun x => if f (M + 1 + x) then (M + 1 + x) * pow2 (M + d - (M + 1) - x) else 0) x
        = (fun x => if f (M + 1 + x) then (M + 1 + x) * pow2 (M + d - (M + 1 + x)) else 0) x := by
    intro x hx
    have hxd : x < d := List.mem_range.mp hx
    show (if f (M + 1 + x) then (M + 1 + x) * pow2 (M + d - (M + 1) - x) else 0)
        = (if f (M + 1 + x) then (M + 1 + x) * pow2 (M + d - (M + 1 + x)) else 0)
    have : M + d - (M + 1) - x = M + d - (M + 1 + x) := by omega
    rw [this]
  rw [listMapCongr hexp]

theorem P_split' (f : Nat → Bool) (M N : Nat) (hMN : M ≤ N) (hM : 1 ≤ M) :
    P f N = P f (M - 1) * pow2 (N - M + 1) + seg f M N := by
  have hd : (M - 1) + (N - M + 1) = N := by omega
  rw [← hd]
  have hM1 : M - 1 + 1 = M := by omega
  have hpow : pow2 (M - 1 + (N - M + 1) - M + 1) = pow2 (N - M + 1) := by rw [hd]
  rw [P_split, hM1, hpow]

-- ===========================================================================
-- §7  THE REGION LAW AND THE CHECKPOINT THEOREM
-- ===========================================================================

/-- THE REGION LAW: region k contributes m k·2^{k+1} at its own scale,
regardless of σ. This is the halving identity in action. -/
theorem seg_region (σ : Nat → Bool) (k : Nat) :
    seg (F σ) (mfun k) (mfun k + k + 1) = mfun k * pow2 (k + 1) := by
  have hcount : mfun k + k + 1 + 1 - mfun k = k + 2 := by omega
  simp only [seg, hcount]
  cases hσ : σ k
  · -- σ k = false: x = 0 term is 0; x ≥ 1 terms are the intSum terms
    have hv : ∀ x, 1 ≤ x → x ≤ k + 1 → F σ (mfun k + x) = true := by
      intro x hx1 hx2
      rw [F_Q σ (by omega : mfun k < mfun k + x)
            (by omega : mfun k + x ≤ mfun k + k + 1), hσ]
      rfl
    have h0 : F σ (mfun k + 0) = false := by
      rw [Nat.add_zero, F_P σ k, hσ]
    have hr : k + 1 + 1 = k + 2 := by omega
    rw [← hr]
    have hsegform : (List.range (k + 1 + 1)).map
          (fun x => if F σ (mfun k + x) then (mfun k + x) * pow2 (mfun k + k + 1 - mfun k - x) else 0)
        = (List.range (k + 1 + 1)).map
          (fun x => if F σ (mfun k + x) then (mfun k + x) * pow2 (k + 1 - x) else 0) := by
      refine listMapCongr (fun x _ => ?_)
      have hexp : mfun k + k + 1 - mfun k - x = k + 1 - x := by omega
      rw [hexp]
    rw [hsegform, sum_range_shift
      (fun x => if F σ (mfun k + x) then (mfun k + x) * pow2 (k + 1 - x) else 0) (k + 1)]
    show (if F σ (mfun k + 0) then (mfun k + 0) * pow2 (k + 1 - 0) else 0)
        + ((List.range (k + 1)).map
            (fun x => if F σ (mfun k + (x + 1)) then (mfun k + (x + 1)) * pow2 (k + 1 - (x + 1)) else 0)).sum
        = mfun k * pow2 (k + 1)
    have hterm0 : (if F σ (mfun k + 0) then (mfun k + 0) * pow2 (k + 1 - 0) else 0) = 0 := by
      rw [h0]
      rfl
    rw [hterm0, Nat.zero_add]
    have hcongr : (List.range (k + 1)).map
          (fun x => if F σ (mfun k + (x + 1)) then (mfun k + (x + 1)) * pow2 (k + 1 - (x + 1)) else 0)
        = (List.range (k + 1)).map (fun i => (mfun k + i + 1) * pow2 (k + 1 - i - 1)) := by
      refine listMapCongr (fun x hx => ?_)
      have hxk : x < k + 1 := List.mem_range.mp hx
      have hvx := hv (x + 1) (by omega) (by omega)
      rw [hvx]
      simp only [if_pos]
      have hbr2 : mfun k + (x + 1) = mfun k + x + 1 := by omega
      have hexp : k + 1 - (x + 1) = k + 1 - x - 1 := by omega
      rw [hbr2, hexp]
    rw [hcongr]
    exact halving_region k
  · -- σ k = true: x = 0 term is the answer; x ≥ 1 terms are 0
    have hv : ∀ x, 1 ≤ x → x ≤ k + 1 → F σ (mfun k + x) = false := by
      intro x hx1 hx2
      rw [F_Q σ (by omega : mfun k < mfun k + x)
            (by omega : mfun k + x ≤ mfun k + k + 1), hσ]
      rfl
    have h0 : F σ (mfun k + 0) = true := by
      rw [Nat.add_zero, F_P σ k, hσ]
    have hr : k + 1 + 1 = k + 2 := by omega
    rw [← hr]
    have hsegform : (List.range (k + 1 + 1)).map
          (fun x => if F σ (mfun k + x) then (mfun k + x) * pow2 (mfun k + k + 1 - mfun k - x) else 0)
        = (List.range (k + 1 + 1)).map
          (fun x => if F σ (mfun k + x) then (mfun k + x) * pow2 (k + 1 - x) else 0) := by
      refine listMapCongr (fun x _ => ?_)
      have hexp : mfun k + k + 1 - mfun k - x = k + 1 - x := by omega
      rw [hexp]
    rw [hsegform, sum_range_shift
      (fun x => if F σ (mfun k + x) then (mfun k + x) * pow2 (k + 1 - x) else 0) (k + 1)]
    show (if F σ (mfun k + 0) then (mfun k + 0) * pow2 (k + 1 - 0) else 0)
        + ((List.range (k + 1)).map
            (fun x => if F σ (mfun k + (x + 1)) then (mfun k + (x + 1)) * pow2 (k + 1 - (x + 1)) else 0)).sum
        = mfun k * pow2 (k + 1)
    have hterm0 : (if F σ (mfun k + 0) then (mfun k + 0) * pow2 (k + 1 - 0) else 0)
        = mfun k * pow2 (k + 1) := by
      rw [h0]
      rfl
    rw [hterm0]
    have hzero : (List.range (k + 1)).map
          (fun x => if F σ (mfun k + (x + 1)) then (mfun k + (x + 1)) * pow2 (k + 1 - (x + 1)) else 0)
        = (List.range (k + 1)).map (fun _ => 0) := by
      refine listMapCongr (fun x hx => ?_)
      have hxk : x < k + 1 := List.mem_range.mp hx
      have hvx := hv (x + 1) (by omega) (by omega)
      rw [hvx]
      rfl
    rw [hzero]
    have hsum0 : ((List.range (k + 1)).map (fun _ => 0)).sum = 0 := by
      induction (List.range (k + 1)) with
      | nil => rfl
      | cons a t ih => rw [List.map_cons, List.sum_cons, ih]
    rw [hsum0, Nat.add_zero]

/-- Scale reduction of a segment whose tail lies in a gap. -/
theorem seg_scale (f : Nat → Bool) (n c M' : Nat) (hnc : n + c ≤ M')
    (hgap : ∀ a, n + c < a → a ≤ M' → f a = false) :
    seg f n M' = seg f n (n + c) * pow2 (M' - n - c) := by
  have hcount : M' + 1 - n = (c + 1) + (M' - n - c) := by omega
  simp only [seg]
  rw [hcount, range_split c (M' - n - c), List.map_append, List.sum_append]
  -- second part: all zeros (gap)
  have hzero : ((List.range (M' - n - c)).map (fun x => c + 1 + x)).map
      (fun x => if f (n + x) then (n + x) * pow2 (M' - n - x) else 0)
      = (List.range (M' - n - c)).map (fun _ => 0) := by
    rw [List.map_map]
    refine listMapCongr (fun x hx => ?_)
    have hx2 : x < M' - n - c := List.mem_range.mp hx
    have hx : n + (c + 1 + x) = n + c + 1 + x := by omega
    have hfalse := hgap (n + c + 1 + x) (by omega) (by omega)
    rw [← hx] at hfalse
    show (if f (n + (c + 1 + x)) then (n + (c + 1 + x)) * pow2 (M' - n - (c + 1 + x)) else 0) = 0
    rw [hfalse]
    rfl
  rw [hzero]
  have hsum0 : ((List.range (M' - n - c)).map (fun _ => 0)).sum = 0 := by
    induction (List.range (M' - n - c)) with
    | nil => rfl
    | cons a t ih => rw [List.map_cons, List.sum_cons, ih]
  rw [hsum0, Nat.add_zero]
  -- first part: rescale by 2^{M'−n−c}
  have hfirst : (List.range (c + 1)).map
        (fun x => if f (n + x) then (n + x) * pow2 (M' - n - x) else 0)
      = (List.range (c + 1)).map
          (fun x => if f (n + x) then (n + x) * pow2 (n + c - n - x) * pow2 (M' - n - c) else 0) := by
    refine listMapCongr (fun x hx => ?_)
    have hxc : x ≤ c := Nat.le_of_lt_succ (List.mem_range.mp hx)
    have hexp : M' - n - x = (n + c - n - x) + (M' - n - c) := by omega
    rw [hexp, pow2_add, ← Nat.mul_assoc]
  rw [hfirst, sum_ite_mul_const]
  -- the remaining seg-def normalization
  have hcount2 : n + c + 1 - n = c + 1 := by omega
  rw [← hcount2]

/-- The segment over [m K, m (K+1) − 1] is σ-free. -/
theorem seg_tower (σ : Nat → Bool) (K : Nat) :
    seg (F σ) (mfun K) (mfun (K + 1) - 1)
      = mfun K * pow2 (mfun (K + 1) - 1 - mfun K) := by
  have hgap : ∀ a, mfun K + K + 1 < a → a ≤ mfun (K + 1) - 1 → F σ a = false := by
    intro a h1 h2
    exact F_false_between σ K a h1 (by omega)
  have hle : mfun K + (K + 1) ≤ mfun (K + 1) - 1 := by
    have := mfun_sep K
    omega
  rw [seg_scale (F σ) (mfun K) (K + 1) (mfun (K + 1) - 1) hle hgap]
  have hbr : mfun K + (K + 1) = mfun K + K + 1 := by omega
  rw [hbr, seg_region]
  have hp : pow2 (K + 1) * pow2 (mfun (K + 1) - 1 - mfun K - (K + 1))
      = pow2 (mfun (K + 1) - 1 - mfun K) := by
    rw [← pow2_add]
    congr 1
    omega
  rw [Nat.mul_assoc, hp]

/-- THE CHECKPOINT THEOREM: partial values at region boundaries are
EXACTLY equal for all tower representations. -/
theorem checkpoint_eq (σ τ : Nat → Bool) (K : Nat) :
    P (F σ) (mfun K - 1) = P (F τ) (mfun K - 1) := by
  induction K with
  | zero =>
      have h0 : mfun 0 - 1 = 0 := by decide
      rw [h0, P_zero, P_zero]
  | succ K ih =>
      have hM : 1 ≤ mfun K := mfun_pos K
      have hsep := mfun_sep K
      have hsplitσ := P_split' (F σ) (mfun K) (mfun (K + 1) - 1) (by omega) hM
      have hsplitτ := P_split' (F τ) (mfun K) (mfun (K + 1) - 1) (by omega) hM
      rw [hsplitσ, hsplitτ, seg_tower σ K, seg_tower τ K, ih]

-- ===========================================================================
-- §8  TAIL BOUND, SELECTION, sameValue, CAUCHY
-- ===========================================================================

/-- Full-segment identity (from the scaled-halving at m = n−1). -/
theorem full_seg_identity (n M : Nat) (hn : 1 ≤ n) (hnM : n ≤ M + 1) :
    ((List.range (M + 1 - n)).map (fun x => (n + x) * pow2 (M - n - x))).sum + (M + 2)
      = (n + 1) * pow2 (M + 1 - n) := by
  have h := halving_nat (n - 1) (M + 1 - n)
  have hconv : intSum (n - 1) (M + 1 - n)
      = ((List.range (M + 1 - n)).map (fun x => (n + x) * pow2 (M - n - x))).sum := by
    unfold intSum
    have hmap : (List.range (M + 1 - n)).map (fun i => (n - 1 + i + 1) * pow2 (M + 1 - n - i - 1))
        = (List.range (M + 1 - n)).map (fun x => (n + x) * pow2 (M - n - x)) := by
      refine listMapCongr (fun i hi => ?_)
      have hilt : i < M + 1 - n := List.mem_range.mp hi
      have h1 : (n - 1) + i + 1 = n + i := by omega
      have h2 : M + 1 - n - i - 1 = M - n - i := by omega
      rw [h1, h2]
    rw [hmap]
  rw [hconv] at h
  have hmid : (n - 1) + (M + 1 - n) + 2 = M + 2 := by omega
  have hrhs : n - 1 + 2 = n + 1 := by omega
  rw [hrhs] at h
  omega

/-- Segment bound. -/
theorem seg_bound (f : Nat → Bool) (n M : Nat) (hn : 1 ≤ n) (hnM : n ≤ M + 1) :
    seg f n M ≤ (n + 1) * pow2 (M + 1 - n) := by
  have hid := full_seg_identity n M hn hnM
  have hle : ((List.range (M + 1 - n)).map
        (fun x => if f (n + x) then (n + x) * pow2 (M - n - x) else 0)).sum
      ≤ ((List.range (M + 1 - n)).map (fun x => (n + x) * pow2 (M - n - x))).sum :=
    sum_le_sum_of_forall (fun x _ => by
      show (if f (n + x) then (n + x) * pow2 (M - n - x) else 0)
          ≤ (n + x) * pow2 (M - n - x)
      split <;> omega)
  unfold seg
  omega

/-- The selection lemma: for every tolerance p/q there is a region K
dominating the bound. -/
theorem tower_select (p q : Nat) (hp : 0 < p) (hq : 0 < q) :
    ∃ K, q * (mfun K + 1) ≤ p * pow2 (mfun K - 1) := by
  refine ⟨2 * q + 5, ?_⟩
  have hK1 : 2 * q + 6 ≤ mfun (2 * q + 5) := by
    have := mfun_ge_succ (2 * q + 5)
    omega
  have ha : 2 * q ≤ mfun (2 * q + 5) - 1 := by omega
  have ha4 : 4 ≤ mfun (2 * q + 5) - 1 := by omega
  have hsq : (mfun (2 * q + 5) - 1) * (mfun (2 * q + 5) - 1)
      ≤ pow2 (mfun (2 * q + 5) - 1) := pow2_sq _ ha4
  have h1 : (2 * q) * (mfun (2 * q + 5) - 1)
      ≤ (mfun (2 * q + 5) - 1) * (mfun (2 * q + 5) - 1) :=
        Nat.mul_le_mul_right _ (by omega)
  have hbridge : (2 * q) * (mfun (2 * q + 5) - 1)
      = 2 * (q * (mfun (2 * q + 5) - 1)) := by
    rw [Nat.mul_assoc]
  have hqa : q * 2 ≤ q * (mfun (2 * q + 5) - 1) := Nat.mul_le_mul_left q (by omega)
  have hlast : pow2 (mfun (2 * q + 5) - 1) ≤ p * pow2 (mfun (2 * q + 5) - 1) := by
    exact Nat.le_mul_of_pos_left _ hp
  have hgoalform : q * (mfun (2 * q + 5) + 1)
      = q * (mfun (2 * q + 5) - 1) + 2 * q := by
    have : mfun (2 * q + 5) + 1 = (mfun (2 * q + 5) - 1) + 2 := by omega
    rw [this, Nat.mul_add]
    omega
  omega

/-- Two representations have the same value (completion sense). -/
def sameValue (f g : Nat → Bool) : Prop :=
  ∀ p q : Nat, 0 < p → 0 < q → ∃ N, ∀ M, N ≤ M →
    q * P f M ≤ q * P g M + p * pow2 M ∧ q * P g M ≤ q * P f M + p * pow2 M

theorem tower_sameValue (σ τ : Nat → Bool) : sameValue (F σ) (F τ) := by
  intro p q hp hq
  obtain ⟨K, hK⟩ := tower_select p q hp hq
  have hmK : 1 ≤ mfun K := mfun_pos K
  refine ⟨mfun K, ?_⟩
  intro M hM
  have hsσ := P_split' (F σ) (mfun K) M hM hmK
  have hsτ := P_split' (F τ) (mfun K) M hM hmK
  have hcp := checkpoint_eq σ τ K
  have hbdσ := seg_bound (F σ) (mfun K) M hmK (by omega)
  have hbdτ := seg_bound (F τ) (mfun K) M hmK (by omega)
  have hnorm : M + 1 - mfun K = M - mfun K + 1 := by omega
  rw [hnorm] at hbdσ hbdτ
  have hpow : pow2 (mfun K - 1) * pow2 (M - mfun K + 1) = pow2 M := by
    rw [← pow2_add]
    congr 1
    omega
  have hqB : q * ((mfun K + 1) * pow2 (M - mfun K + 1)) ≤ p * pow2 M := by
    have hstep1 : q * ((mfun K + 1) * pow2 (M - mfun K + 1))
        = (q * (mfun K + 1)) * pow2 (M - mfun K + 1) := (Nat.mul_assoc q _ _).symm
    have hstep2 : (p * pow2 (mfun K - 1)) * pow2 (M - mfun K + 1) = p * pow2 M := by
      rw [Nat.mul_assoc, hpow]
    have hle : (q * (mfun K + 1)) * pow2 (M - mfun K + 1)
        ≤ (p * pow2 (mfun K - 1)) * pow2 (M - mfun K + 1) :=
          Nat.mul_le_mul_right _ hK
    rw [hstep1]
    exact Nat.le_trans hle (Nat.le_of_eq hstep2)
  -- assembly, direction 1
  have hchain1 : q * P (F σ) M ≤ q * P (F τ) M + p * pow2 M := by
    rw [hsσ, hsτ]
    have hdistr : q * (P (F σ) (mfun K - 1) * pow2 (M - mfun K + 1) + seg (F σ) (mfun K) M)
        = q * (P (F σ) (mfun K - 1) * pow2 (M - mfun K + 1))
            + q * seg (F σ) (mfun K) M := Nat.mul_add q _ _
    have hdistr2 : q * (P (F τ) (mfun K - 1) * pow2 (M - mfun K + 1) + seg (F τ) (mfun K) M)
        = q * (P (F τ) (mfun K - 1) * pow2 (M - mfun K + 1))
            + q * seg (F τ) (mfun K) M := Nat.mul_add q _ _
    have hsegσ : q * seg (F σ) (mfun K) M
        ≤ q * ((mfun K + 1) * pow2 (M - mfun K + 1)) :=
          Nat.mul_le_mul_left q hbdσ
    have hcp' : q * (P (F σ) (mfun K - 1) * pow2 (M - mfun K + 1))
        = q * (P (F τ) (mfun K - 1) * pow2 (M - mfun K + 1)) := by
      rw [hcp]
    have hlow : q * (P (F τ) (mfun K - 1) * pow2 (M - mfun K + 1))
        ≤ q * (P (F τ) (mfun K - 1) * pow2 (M - mfun K + 1) + seg (F τ) (mfun K) M) := by
      have : q * seg (F τ) (mfun K) M ≥ 0 := Nat.zero_le _
      omega
    omega
  have hchain2 : q * P (F τ) M ≤ q * P (F σ) M + p * pow2 M := by
    rw [hsσ, hsτ]
    have hdistr : q * (P (F τ) (mfun K - 1) * pow2 (M - mfun K + 1) + seg (F τ) (mfun K) M)
        = q * (P (F τ) (mfun K - 1) * pow2 (M - mfun K + 1))
            + q * seg (F τ) (mfun K) M := Nat.mul_add q _ _
    have hdistr2 : q * (P (F σ) (mfun K - 1) * pow2 (M - mfun K + 1) + seg (F σ) (mfun K) M)
        = q * (P (F σ) (mfun K - 1) * pow2 (M - mfun K + 1))
            + q * seg (F σ) (mfun K) M := Nat.mul_add q _ _
    have hsegτ : q * seg (F τ) (mfun K) M
        ≤ q * ((mfun K + 1) * pow2 (M - mfun K + 1)) :=
          Nat.mul_le_mul_left q hbdτ
    have hcp' : q * (P (F τ) (mfun K - 1) * pow2 (M - mfun K + 1))
        = q * (P (F σ) (mfun K - 1) * pow2 (M - mfun K + 1)) := by
      rw [hcp]
    have hlow : q * (P (F σ) (mfun K - 1) * pow2 (M - mfun K + 1))
        ≤ q * (P (F σ) (mfun K - 1) * pow2 (M - mfun K + 1) + seg (F σ) (mfun K) M) := by
      have : q * seg (F σ) (mfun K) M ≥ 0 := Nat.zero_le _
      omega
    omega
  exact ⟨hchain1, hchain2⟩

/-- The tower partials are Cauchy (the value x* exists). -/
theorem tower_cauchy (σ : Nat → Bool) :
    ∀ p q : Nat, 0 < p → 0 < q → ∃ N, ∀ M₁ M₂, N ≤ M₁ → M₁ ≤ M₂ →
      q * (P (F σ) M₁ * pow2 (M₂ - M₁)) ≤ q * P (F σ) M₂ + p * pow2 M₂
        ∧ q * P (F σ) M₂ ≤ q * (P (F σ) M₁ * pow2 (M₂ - M₁)) + p * pow2 M₂ := by
  intro p q hp hq
  obtain ⟨K, hK⟩ := tower_select p q hp hq
  have hmK : 1 ≤ mfun K := mfun_pos K
  refine ⟨mfun K, ?_⟩
  intro M₁ M₂ hN h12
  have hs₁ := P_split' (F σ) (mfun K) M₁ hN hmK
  have hs₂ := P_split' (F σ) (mfun K) M₂ (by omega) hmK
  have hbd₁ := seg_bound (F σ) (mfun K) M₁ hmK (by omega)
  have hbd₂ := seg_bound (F σ) (mfun K) M₂ hmK (by omega)
  have hnorm₁ : M₁ + 1 - mfun K = M₁ - mfun K + 1 := by omega
  have hnorm₂ : M₂ + 1 - mfun K = M₂ - mfun K + 1 := by omega
  rw [hnorm₁] at hbd₁
  rw [hnorm₂] at hbd₂
  have hpow : pow2 (mfun K - 1) * pow2 (M₂ - mfun K + 1) = pow2 M₂ := by
    rw [← pow2_add]
    congr 1
    omega
  have hqB : q * ((mfun K + 1) * pow2 (M₂ - mfun K + 1)) ≤ p * pow2 M₂ := by
    have hstep1 : q * ((mfun K + 1) * pow2 (M₂ - mfun K + 1))
        = (q * (mfun K + 1)) * pow2 (M₂ - mfun K + 1) := (Nat.mul_assoc q _ _).symm
    have hstep2 : (p * pow2 (mfun K - 1)) * pow2 (M₂ - mfun K + 1) = p * pow2 M₂ := by
      rw [Nat.mul_assoc, hpow]
    have hle : (q * (mfun K + 1)) * pow2 (M₂ - mfun K + 1)
        ≤ (p * pow2 (mfun K - 1)) * pow2 (M₂ - mfun K + 1) :=
          Nat.mul_le_mul_right _ hK
    rw [hstep1]
    exact Nat.le_trans hle (Nat.le_of_eq hstep2)
  -- rescale the M₁-partial to scale M₂
  have hrescale : P (F σ) M₁ * pow2 (M₂ - M₁)
      = P (F σ) (mfun K - 1) * pow2 (M₂ - mfun K + 1)
          + seg (F σ) (mfun K) M₁ * pow2 (M₂ - M₁) := by
    rw [hs₁]
    have hdistr : P (F σ) (mfun K - 1) * pow2 (M₁ - mfun K + 1) * pow2 (M₂ - M₁)
        = P (F σ) (mfun K - 1) * (pow2 (M₁ - mfun K + 1) * pow2 (M₂ - M₁)) := by
      rw [Nat.mul_assoc]
    have hsum : M₁ - mfun K + 1 + (M₂ - M₁) = M₂ - mfun K + 1 := by omega
    have hp : pow2 (M₁ - mfun K + 1) * pow2 (M₂ - M₁) = pow2 (M₂ - mfun K + 1) := by
      rw [← pow2_add, hsum]
    have hdistr2 : (P (F σ) (mfun K - 1) * pow2 (M₁ - mfun K + 1) + seg (F σ) (mfun K) M₁)
        * pow2 (M₂ - M₁)
        = P (F σ) (mfun K - 1) * pow2 (M₁ - mfun K + 1) * pow2 (M₂ - M₁)
            + seg (F σ) (mfun K) M₁ * pow2 (M₂ - M₁) := Nat.add_mul _ _ _
    rw [hdistr2, hdistr, hp]
  -- assembly
  have hchain1 : q * (P (F σ) M₁ * pow2 (M₂ - M₁)) ≤ q * P (F σ) M₂ + p * pow2 M₂ := by
    rw [hrescale, hs₂]
    have hdistr1 : q * (P (F σ) (mfun K - 1) * pow2 (M₂ - mfun K + 1)
        + seg (F σ) (mfun K) M₁ * pow2 (M₂ - M₁))
        = q * (P (F σ) (mfun K - 1) * pow2 (M₂ - mfun K + 1))
            + q * (seg (F σ) (mfun K) M₁ * pow2 (M₂ - M₁)) := Nat.mul_add q _ _
    have hdistr2 : q * (P (F σ) (mfun K - 1) * pow2 (M₂ - mfun K + 1)
        + seg (F σ) (mfun K) M₂)
        = q * (P (F σ) (mfun K - 1) * pow2 (M₂ - mfun K + 1))
            + q * seg (F σ) (mfun K) M₂ := Nat.mul_add q _ _
    have hsegle : seg (F σ) (mfun K) M₁ * pow2 (M₂ - M₁)
        ≤ (mfun K + 1) * pow2 (M₂ - mfun K + 1) := by
      have hresc : (mfun K + 1) * pow2 (M₁ - mfun K + 1) * pow2 (M₂ - M₁)
          = (mfun K + 1) * pow2 (M₂ - mfun K + 1) := by
        rw [Nat.mul_assoc, ← pow2_add]
        have hsum : M₁ - mfun K + 1 + (M₂ - M₁) = M₂ - mfun K + 1 := by omega
        rw [hsum]
      have hstep : seg (F σ) (mfun K) M₁ * pow2 (M₂ - M₁)
          ≤ (mfun K + 1) * pow2 (M₁ - mfun K + 1) * pow2 (M₂ - M₁) :=
            Nat.mul_le_mul_right _ hbd₁
      rw [hresc] at hstep
      exact hstep
    have hqseg : q * (seg (F σ) (mfun K) M₁ * pow2 (M₂ - M₁))
        ≤ q * ((mfun K + 1) * pow2 (M₂ - mfun K + 1)) := Nat.mul_le_mul_left q hsegle
    have hlow : q * (P (F σ) (mfun K - 1) * pow2 (M₂ - mfun K + 1))
        ≤ q * (P (F σ) (mfun K - 1) * pow2 (M₂ - mfun K + 1) + seg (F σ) (mfun K) M₂) := by
      have : q * seg (F σ) (mfun K) M₂ ≥ 0 := Nat.zero_le _
      omega
    omega
  have hchain2 : q * P (F σ) M₂ ≤ q * (P (F σ) M₁ * pow2 (M₂ - M₁)) + p * pow2 M₂ := by
    rw [hrescale, hs₂]
    have hdistr1 : q * (P (F σ) (mfun K - 1) * pow2 (M₂ - mfun K + 1)
        + seg (F σ) (mfun K) M₂)
        = q * (P (F σ) (mfun K - 1) * pow2 (M₂ - mfun K + 1))
            + q * seg (F σ) (mfun K) M₂ := Nat.mul_add q _ _
    have hdistr2 : q * (P (F σ) (mfun K - 1) * pow2 (M₂ - mfun K + 1)
        + seg (F σ) (mfun K) M₁ * pow2 (M₂ - M₁))
        = q * (P (F σ) (mfun K - 1) * pow2 (M₂ - mfun K + 1))
            + q * (seg (F σ) (mfun K) M₁ * pow2 (M₂ - M₁)) := Nat.mul_add q _ _
    have hsegle : seg (F σ) (mfun K) M₂
        ≤ (mfun K + 1) * pow2 (M₂ - mfun K + 1) := hbd₂
    have hqseg : q * seg (F σ) (mfun K) M₂
        ≤ q * ((mfun K + 1) * pow2 (M₂ - mfun K + 1)) := Nat.mul_le_mul_left q hsegle
    have hlow : q * (P (F σ) (mfun K - 1) * pow2 (M₂ - mfun K + 1))
        ≤ q * (P (F σ) (mfun K - 1) * pow2 (M₂ - mfun K + 1)
            + seg (F σ) (mfun K) M₁ * pow2 (M₂ - M₁)) := by
      have : q * (seg (F σ) (mfun K) M₁ * pow2 (M₂ - M₁)) ≥ 0 := Nat.zero_le _
      omega
    omega
  exact ⟨hchain1, hchain2⟩

-- ===========================================================================
-- §9  INJECTIVITY + THE MAIN THEOREM
-- ===========================================================================

theorem F_injective : Function.Injective (F) := by
  intro σ τ hστ
  apply funext
  intro n
  have h1 : F σ (mfun n) = σ n := F_P σ n
  have h2 : F τ (mfun n) = τ n := F_P τ n
  rw [← h1, ← h2, hστ]

/-- **ERDŐS #261 — THE CONTINUUM QUESTION (REAL-x VARIANT): YES.**
There is an explicit real x* = Σ_k m k/2^{m k} (the tower value, the
completion limit of the Cauchy partials (P (F σ) M)/2^M) and an injective
map σ ↦ F σ from binary sequences into representations of x* — all
tower representations carry the SAME value (tower_sameValue, with the
value existing by tower_cauchy). Since there are 2^{ℵ₀} binary
sequences, x* has at least 2^{ℵ₀} distinct representations. -/
theorem erdos261_continuum :
    ∃ G : (Nat → Bool) → (Nat → Bool),
      Function.Injective G ∧ ((∀ σ τ, sameValue (G σ) (G τ))
        ∧ ∀ σ, ∀ p q : Nat, 0 < p → 0 < q → ∃ N, ∀ M₁ M₂, N ≤ M₁ → M₁ ≤ M₂ →
          q * (P (G σ) M₁ * pow2 (M₂ - M₁)) ≤ q * P (G σ) M₂ + p * pow2 M₂
            ∧ q * P (G σ) M₂ ≤ q * (P (G σ) M₁ * pow2 (M₂ - M₁)) + p * pow2 M₂) := by
  exact Exists.intro F (And.intro F_injective
    (And.intro (fun σ τ => tower_sameValue σ τ) (fun σ => tower_cauchy σ)))

-- ===========================================================================
-- §10  RECEIPTS (all #eval — compiler-evaluated, exact) + AXIOM GATES
-- ===========================================================================

namespace Receipts

-- The halving family positions: 1, 4, 11, 26, 57, 120, 247, 502
#eval (mfun 0, mfun 1, mfun 2, mfun 3, mfun 4, mfun 5, mfun 6, mfun 7)

-- Scaled-halving receipts: intSum (m k) (k+1) = m k · 2^{k+1}
#eval (intSum (mfun 0) 1, mfun 0 * pow2 1)          -- (2, 2)
#eval (intSum (mfun 1) 2, mfun 1 * pow2 2)          -- (16, 16)
#eval (intSum (mfun 2) 3, mfun 2 * pow2 3)          -- (88, 88)
#eval (intSum (mfun 3) 4, mfun 3 * pow2 4)          -- (416, 416)
#eval (intSum (mfun 4) 5, mfun 4 * pow2 5)          -- (1824, 1824)

-- Checkpoint receipts: P (F σ) (m K − 1) is σ-independent
def allTrue : Nat → Bool := fun _ => true
def allFalse : Nat → Bool := fun _ => false
def altSeq : Nat → Bool := fun k => decide (k % 2 == 0)

#eval (P (F allTrue) (mfun 4 - 1), P (F allFalse) (mfun 4 - 1),
       P (F altSeq) (mfun 4 - 1))                    -- all three equal
#eval (P (F allTrue) (mfun 5 - 1), P (F allFalse) (mfun 5 - 1),
       P (F altSeq) (mfun 5 - 1))                    -- all three equal

-- The tower value in rational form at K = 6 (all σ agree):
def towerRat (σ : Nat → Bool) (K : Nat) : Rat :=
  (Nat.cast (P (F σ) (mfun K - 1)) : Rat) / (Nat.cast (pow2 (mfun K - 1)) : Rat)

#eval (towerRat allTrue 6, towerRat allFalse 6, towerRat altSeq 6)
-- all equal; the value ≈ 0.7553714811… (the tower x*)

end Receipts

#print axioms erdos261_continuum
#print axioms checkpoint_eq
#print axioms tower_sameValue
#print axioms tower_cauchy
#print axioms halving_nat

end Erdos261Tower
