/-! # Erdos394_Data — the t_k oracle + the certified exact tables (Kill candidate, S034)

Erdős #394: t_k(n) = least m ≥ 1 with n ∣ m(m+1)···(m+k−1). This module
defines the computation (structural scan, NO well-founded recursion — the
L95 discipline; `0 < r` branch conditions only — no Bool/Prop ambiguity;
`rfl`-step unfolding — no simp-equation roulette) and decides the four
certified tables:

- t_2 for all odd n = 3..101 (50 exact values);
- t_3 for all (n,6)=1, n = 5..97 (32 exact values);
- t_4 for all (n,24)=1, n = 5..99 (32 exact values);
- t_5 for all (n,120)=1, n = 7..99 (25 exact values).

Table values certified by the S034 dual-method engine (brute-force least-m
== min-CRT-class, 1015/1015 agreements, k = 2..6, n ≤ 600) and re-verified
by the independent battery `battery394.py` inside CI. -/

set_option maxRecDepth 65536

namespace Erdos394Data

/-- prodCons m k = m·(m+1)···(m+k−1) — the length-k consecutive product. -/
def prodCons : Nat → Nat → Nat
  | _, 0 => 1
  | m, k + 1 => (m + k) * prodCons m k

/-- The divisibility oracle: n ∣ prodCons m k (n divides the product). -/
def divAt (n m k : Nat) : Bool := prodCons m k % n == 0

/-- Structural scan: the least m ∈ [1, j] with n ∣ prodCons m k (0 = none). -/
def tKfind : Nat → Nat → Nat → Nat
  | _, _, 0 => 0
  | n, k, j + 1 =>
    if 0 < tKfind n k j then tKfind n k j
    else if divAt n (j + 1) k then j + 1 else 0

/-- tKb n k = the least m ≥ 1 with n ∣ prodCons m k (search capped at n). -/
def tKb (n k : Nat) : Nat := tKfind n k n

/-- The definitional step of the scan (rfl-unfolds the structural match). -/
theorem tKstep (n k j : Nat) : tKfind n k (j + 1)
    = if 0 < tKfind n k j then tKfind n k j
      else if divAt n (j + 1) k then j + 1 else 0 := rfl

/-! ## The oracle correctness (bound + soundness + leastness). -/

/-- The scan result is always an index ≤ j. -/
theorem tKfind_bound (n k j : Nat) : tKfind n k j ≤ j := by
  induction j with
  | zero => have h0 : tKfind n k 0 = 0 := rfl; omega
  | succ j ih =>
    by_cases hprev : 0 < tKfind n k j
    · rw [tKstep, if_pos hprev]; omega
    · rw [tKstep, if_neg hprev]
      by_cases hdd : divAt n (j + 1) k = true
      · rw [if_pos hdd]; omega
      · rw [if_neg hdd]; omega

/-- Every nonzero result of the scan is a valid m. -/
theorem tKfind_sound (n k j : Nat) (h : tKfind n k j ≠ 0) :
    divAt n (tKfind n k j) k = true := by
  induction j with
  | zero => have h0 : tKfind n k 0 = 0 := rfl; exact absurd h0 h
  | succ j ih =>
    by_cases hprev : 0 < tKfind n k j
    · rw [tKstep, if_pos hprev] at h ⊢
      exact ih h
    · rw [tKstep, if_neg hprev] at h ⊢
      by_cases hdd : divAt n (j + 1) k = true
      · rw [if_pos hdd] at h ⊢; exact hdd
      · rw [if_neg hdd] at h
        exact absurd rfl h

/-- Any valid m ≤ j forces a nonzero result, itself ≤ m (leastness). -/
theorem tKfind_least (n k j m : Nat) (h1 : 1 ≤ m) (hmj : m ≤ j)
    (hd : divAt n m k = true) : tKfind n k j ≠ 0 ∧ tKfind n k j ≤ m := by
  induction j with
  | zero => omega
  | succ j ih =>
    by_cases hmj' : m ≤ j
    · have hp := ih hmj'
      have hprev : 0 < tKfind n k j := by have := hp.1; omega
      rw [tKstep, if_pos hprev]
      exact hp
    · have hmj1 : m = j + 1 := by omega
      by_cases hprev : 0 < tKfind n k j
      · rw [tKstep, if_pos hprev]
        have hb := tKfind_bound n k j
        have hne : tKfind n k j ≠ 0 := by omega
        exact ⟨hne, by omega⟩
      · rw [tKstep, if_neg hprev]
        have hd' : divAt n (j + 1) k = true := by rw [← hmj1]; exact hd
        rw [if_pos hd']
        omega

/-! ## The certified exact tables (S034 engine, dual-method verified). -/

/-- t_2 for odd n = 3, 5, ..., 101 (index j ↦ n = 2j+3). -/
def t2v : List Nat :=
  [2, 4, 6, 8, 10, 12, 5, 16, 18, 6, 22, 24, 26, 28, 30, 11, 14, 36, 12,
   40, 42, 9, 46, 48, 17, 52, 10, 18, 58, 60, 27, 25, 66, 23, 70, 72, 24,
   21, 78, 80, 82, 34, 29, 88, 13, 30, 19, 96, 44, 100]

theorem t2_table :
    ((List.range 50).all (fun j => (tKb (2 * j + 3) 2 == t2v.getD j 0))) = true := by
  decide

/-- t_3 for (n,6)=1, n = 5..97 (index j ↦ the j-th such n). -/
def t3v : List Nat :=
  [3, 5, 9, 11, 15, 17, 21, 23, 27, 29, 5, 35, 39, 41, 45, 47, 51, 9, 57,
   59, 13, 65, 69, 71, 20, 77, 81, 15, 87, 12, 18, 95]

def n3v : List Nat :=
  [5, 7, 11, 13, 17, 19, 23, 25, 29, 31, 35, 37, 41, 43, 47, 49, 53, 55,
   59, 61, 65, 67, 71, 73, 77, 79, 83, 85, 89, 91, 95, 97]

theorem t3_table :
    ((List.range 32).all (fun j => (tKb (n3v.getD j 0) 3 == t3v.getD j 0))) = true := by
  decide

/-- t_4 for (n,24)=1, n = 5..99. -/
def t4v : List Nat :=
  [2, 4, 8, 10, 14, 16, 20, 22, 26, 28, 4, 34, 38, 40, 44, 46, 50, 8, 56,
   58, 10, 64, 68, 70, 11, 76, 80, 14, 86, 11, 17, 94]

def n4v : List Nat :=
  [5, 7, 11, 13, 17, 19, 23, 25, 29, 31, 35, 37, 41, 43, 47, 49, 53, 55,
   59, 61, 65, 67, 71, 73, 77, 79, 83, 85, 89, 91, 95, 97]

theorem t4_table :
    ((List.range 32).all (fun j => (tKb (n4v.getD j 0) 4 == t4v.getD j 0))) = true := by
  decide

/-- t_5 for (n,120)=1, n = 7..99. -/
def t5v : List Nat :=
  [3, 7, 9, 13, 15, 19, 25, 27, 33, 37, 39, 43, 45, 49, 55, 57, 63, 67,
   69, 7, 75, 79, 85, 10, 93]

def n5v : List Nat :=
  [7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 49, 53, 59, 61, 67, 71,
   73, 77, 79, 83, 89, 91, 97]

theorem t5_table :
    ((List.range 25).all (fun j => (tKb (n5v.getD j 0) 5 == t5v.getD j 0))) = true := by
  decide

#eval "ERDOS394_DATA_GREEN"

end Erdos394Data
