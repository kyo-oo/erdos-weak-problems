import Arsenal.ErdosTernary2.Basic
import Arsenal.CardinalWorlds
import Arsenal.CardinalWorldsV2

set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-!
# Erdos677 — THE EQUAL-LCM WINDOWS KERNEL r1 (W57-1, Kernel — P677)

Erdős #677 (verbatim, corpus-erdos #677):

> Let M(n,k) = lcm{n+1,…,n+k}. Is it true that for all m ≥ n+k:
> M(n,k) ≠ M(m,k)?

The two known CROSS-LENGTH coincidences M(4,3) = M(13,2) = 210 and
M(3,4) = M(19,2) = 420 have k ≠ l, so they do NOT answer the equal-k ask.
The equal-k overlap collision M(2,3) = M(3,3) = 60 has m = 3 < 2 + 3 = n + k,
so it violates the disjointness m ≥ n+k and also does not answer the ask.
Prior campaign census (P677/PROOF.md): no equal-k collision for n < 400,
k ≤ 12; the census engine of this kernel certifies the honest box
n < 25, 1 ≤ k ≤ 5, m ∈ [n+k, n+25) with kernel-decided chunk theorems.

THE BOARD (full statements, complete unconditional proofs, zero sorry):
1. `lcmd` / `M677` / `winCollFree` / `wprod` — the concrete, kernel-computable
   definitions (lcm via the core gcd: a·b/gcd(a,b); the window fold as an
   explicit structural recursion on k).
2. THE DIVISION ENGINE — the exact-division identity
   `lcmd a b * gcd a b = a * b`, both divisibility laws
   `a ∣ lcmd a b`, `b ∣ lcmd a b`, `lcmd a b ∣ a * b`, positivity, and the
   zero-laws (all self-contained: div_add_mod + mul_mod + mul_left_cancel).
3. THE STRUCTURE LAWS — window divisibility `∀ i < k, (n+1+i) ∣ M677 n k`,
   k-monotonicity `M677 n k ≤ M677 n (k+1)`, the k = 1 complete kill
   `M677 n 1 = n + 1`, and the product bound `M677 n k ≤ wprod n k`.
4. THE WINDOW TABLE — the corpus's own named solutions, kernel-certified:
   `M677 4 3 = M677 13 2`, `M677 3 4 = M677 19 2`, the overlap collision
   `M677 2 3 = M677 3 3` (with its non-disjointness certified), plus an
   11-row exact-value table.
5. THE EQUAL-k NON-COLLISION CENSUS (THE round-1 kill) — five chunk
   theorems `no_coll_k1..k5 : ∀ n < 25, winCollFree 25 k n = true := by
   decide`, the spec bridge `winCollFree_spec`, and the master
   `e677_no_collision_box` : the full honest nested statement
   `∀ n k m, n < 25 → 1 ≤ k → k ≤ 5 → n + k ≤ m → m < n + 25 →
   M677 n k ≠ M677 m k`, derived from the chunks (zero decide-cheating on
   the quantifier structure).
6. `e677_arsenal_bridge` — BOSS's arsenal applied to the 210/420 anchors
   (erdosternary2 + CardinalWorlds: `isTernaryDigit`, `lt_three_cases`,
   `sq_sub_one`, `mod_mod_mul`, `carryAtPos_bound`, `v2r_ternary_scaling`).
7. `e677_board` — the master composite (ten conjuncts, anonymous
   constructor with one term per conjunct).

House law: GitHub CI is the verifier of record (no local compile; author
blind). Axiom profile must stay within [propext, Classical.choice,
Quot.sound]. Zero sorry, zero native_decide, decide only on closed
numerics / bounded quantifiers (ranges ≤ 501, CardinalWorlds-banked shape).
-/

namespace E677

/-! ## §1 The definitions — concrete and kernel-computable. -/

/-- The binary lcm on Nat, via the core gcd: lcm(a,b) = a·b / gcd(a,b)
(safe core route — `Nat.gcd` is core Lean; kernel-computable). -/
def lcmd (a b : Nat) : Nat := a * b / Nat.gcd a b

/-- THE WINDOW LCM: M(n,k) = lcm{n+1,…,n+k}, as an explicit structural
recursion on k (each step folds in the new top window element n+1+k). -/
def M677 (n k : Nat) : Nat :=
  match k with
  | 0 => 1
  | Nat.succ k => lcmd (M677 n k) (n + 1 + k)

/-- The equal-k window collision checker (Bool): true iff
M677 n k ≠ M677 (n+k+j) k for every j < w; the if-arm returns false at the
first (disjoint-window) collision. -/
def winCollFree : Nat → Nat → Nat → Bool
  | 0, _, _ => true
  | Nat.succ w, k, n => if M677 n k = M677 (n + k + w) k then false else winCollFree w k n

/-- The window product ∏_{i<k}(n+1+i), the structural mirror of M677. -/
def wprod (n k : Nat) : Nat :=
  match k with
  | 0 => 1
  | Nat.succ k => wprod n k * (n + 1 + k)

/-! ## §2 The division engine — exact division and the lcm laws. -/

/-- Exact division: if m % k = 0 then m / k * k = m (from `Nat.div_add_mod`). -/
theorem e677_div_mul_self (m k : Nat) (hmod : m % k = 0) : m / k * k = m := by
  have h := Nat.div_add_mod m k
  -- r1 post-mortem (run 43335072786): core `Nat.div_add_mod` spells the
  -- product LEFT-multiplied (k * (m / k)); the goal atom is m / k * k —
  -- the L86 orientation law: bridge with mul_comm, never trust defeq.
  rw [hmod, Nat.add_zero, Nat.mul_comm k (m / k)] at h
  exact h

/-- Multiplication closure of dvd: d ∣ a → d ∣ a * b. -/
theorem e677_dvd_mul_of (d a b : Nat) (h : d ∣ a) : d ∣ a * b := by
  obtain ⟨c, hc⟩ := h
  exact ⟨c * b, by rw [hc, Nat.mul_assoc]⟩

/-- dvd → mod-zero (self-contained: destructure, `Nat.mul_mod`,
`Nat.mod_self`, `Nat.zero_mul`, `Nat.zero_mod`). -/
theorem e677_dvd_mod_zero (d n : Nat) (h : d ∣ n) : n % d = 0 := by
  obtain ⟨c, hc⟩ := h
  rw [hc, Nat.mul_mod, Nat.mod_self, Nat.zero_mul, Nat.zero_mod]

/-- THE EXACT-DIVISION IDENTITY: lcmd a b * gcd a b = a * b. -/
theorem e677_lcmd_mul_gcd (a b : Nat) : lcmd a b * Nat.gcd a b = a * b := by
  have hgab : Nat.gcd a b ∣ a * b := e677_dvd_mul_of (Nat.gcd a b) a b (Nat.gcd_dvd_left a b)
  have hmod : a * b % Nat.gcd a b = 0 := e677_dvd_mod_zero (Nat.gcd a b) (a * b) hgab
  exact e677_div_mul_self (a * b) (Nat.gcd a b) hmod

/-- Products vanish only factorwise: a * b = 0 → a = 0 ∨ b = 0
(omega closes the linear shell over the atom a * b). -/
theorem e677_mul_eq_zero (a b : Nat) (h : a * b = 0) : a = 0 ∨ b = 0 := by
  induction a with
  | zero => exact Or.inl rfl
  | succ a _ =>
    right
    -- r3 post-mortem (run 43345282494): `Nat.succ_mul` unfolds the
    -- succ-product PRODUCT-FIRST (`Nat.succ a * b = a * b + b`), never
    -- add-first — the r2 bridge tried to force `exact h : a * b + b = 0`
    -- across the Nat.add defeq gap into the `b + a * b` spelling and died
    -- at line 126. THE L86/L90 ORIENTATION LAW: keep the hypothesis on the
    -- side the induction lemma actually produces and let omega close the
    -- linear shell over the atom `a * b` (atom + b = 0 with both
    -- nonnegative forces b = 0).
    rw [Nat.succ_mul] at h
    omega

/-- Positivity of the lcm: both factors positive → lcm positive. -/
theorem e677_mul_pos (a b : Nat) (ha : 0 < a) (hb : 0 < b) : 0 < a * b := by
  rcases Nat.eq_zero_or_pos (a * b) with h0 | hpos
  · exact absurd (e677_mul_eq_zero a b h0) (by omega)
  · exact hpos

/-- Positivity of the lcm via the exact-division identity. -/
theorem e677_lcmd_pos (a b : Nat) (ha : 0 < a) (hb : 0 < b) : 0 < lcmd a b := by
  rcases Nat.eq_zero_or_pos (lcmd a b) with h0 | hpos
  · exfalso
    have hE := e677_lcmd_mul_gcd a b
    rw [h0, Nat.zero_mul] at hE
    rcases e677_mul_eq_zero a b hE.symm with hz | hz
    · omega
    · omega
  · exact hpos

/-- THE LEFT DIVISIBILITY LAW: a ∣ lcmd a b. -/
theorem e677_dvd_lcmd_left (a b : Nat) : a ∣ lcmd a b := by
  by_cases hg0 : Nat.gcd a b = 0
  · obtain ⟨c, hc⟩ := Nat.gcd_dvd_left a b
    rw [hg0, Nat.zero_mul] at hc
    have hl : lcmd a b = 0 := by
      rw [hc]
      show 0 * b / Nat.gcd 0 b = 0
      rw [Nat.zero_mul, Nat.zero_div]
    rw [hl]
    exact ⟨0, (Nat.mul_zero a).symm⟩
  · have hg1 : 1 ≤ Nat.gcd a b := by omega
    obtain ⟨c, hc⟩ := Nat.gcd_dvd_right a b
    have hE' : lcmd a b * Nat.gcd a b = a * (Nat.gcd a b * c) := by
      rw [← hc]; exact e677_lcmd_mul_gcd a b
    have hsh : a * (Nat.gcd a b * c) = Nat.gcd a b * (a * c) := by
      rw [← Nat.mul_assoc, ← Nat.mul_assoc, Nat.mul_comm a (Nat.gcd a b)]
    have hgoal : Nat.gcd a b * lcmd a b = Nat.gcd a b * (a * c) := by
      rw [Nat.mul_comm (Nat.gcd a b) (lcmd a b), hE', hsh]
    have hcancel : lcmd a b = a * c := Nat.mul_left_cancel hg1 hgoal
    exact ⟨c, hcancel⟩

/-- THE RIGHT DIVISIBILITY LAW: b ∣ lcmd a b. -/
theorem e677_dvd_lcmd_right (a b : Nat) : b ∣ lcmd a b := by
  by_cases hg0 : Nat.gcd a b = 0
  · obtain ⟨c, hc⟩ := Nat.gcd_dvd_right a b
    rw [hg0, Nat.zero_mul] at hc
    have hl : lcmd a b = 0 := by
      rw [hc]
      show a * 0 / Nat.gcd a 0 = 0
      rw [Nat.mul_zero, Nat.zero_div]
    rw [hl]
    exact ⟨0, (Nat.mul_zero b).symm⟩
  · have hg1 : 1 ≤ Nat.gcd a b := by omega
    obtain ⟨c, hc⟩ := Nat.gcd_dvd_left a b
    have hE' : lcmd a b * Nat.gcd a b = Nat.gcd a b * c * b := by
      rw [← hc]; exact e677_lcmd_mul_gcd a b
    have hgoal : Nat.gcd a b * lcmd a b = Nat.gcd a b * (c * b) := by
      rw [Nat.mul_comm (Nat.gcd a b) (lcmd a b), hE', ← Nat.mul_assoc]
    have hcancel : lcmd a b = c * b := Nat.mul_left_cancel hg1 hgoal
    exact ⟨c, by rw [hcancel, Nat.mul_comm c b]⟩

/-- THE PRODUCT LAW: lcmd a b ∣ a * b (direct from the exact-division
identity — the gcd itself is the witness). -/
theorem e677_lcmd_dvd_mul (a b : Nat) : lcmd a b ∣ a * b :=
  ⟨Nat.gcd a b, (e677_lcmd_mul_gcd a b).symm⟩

/-- Scaling closure: d ∣ a → d * c ∣ a * c. -/
theorem e677_dvd_scale (d a c : Nat) (h : d ∣ a) : d * c ∣ a * c := by
  obtain ⟨t, ht⟩ := h
  exact ⟨t, by rw [ht, Nat.mul_assoc, Nat.mul_comm t c, ← Nat.mul_assoc]⟩

/-! ## §3 The M677 recursion equations and the structure laws. -/

theorem M677_zero (n : Nat) : M677 n 0 = 1 := rfl

theorem M677_succ (n k : Nat) : M677 n (Nat.succ k) = lcmd (M677 n k) (n + 1 + k) := rfl

theorem wprod_zero (n : Nat) : wprod n 0 = 1 := rfl

theorem wprod_succ (n k : Nat) : wprod n (Nat.succ k) = wprod n k * (n + 1 + k) := rfl

/-- THE k = 1 COMPLETE KILL: M(n,1) = n + 1 (both divisibility directions
through the lcm laws, closed by dvd_antisymm). -/
theorem M677_one (n : Nat) : M677 n 1 = n + 1 := by
  have hA : n + 1 ∣ M677 n 1 := e677_dvd_lcmd_right 1 (n + 1)
  -- r3 post-mortem (run 43345282494): the divisibility identity spells the
  -- unit scale LEFT-multiplied (`1 * (n + 1)`); `Nat.mul_one` matches the
  -- pattern `?n * 1` and found no occurrence at line 217. THE L86/L90
  -- ORIENTATION LAW: `1 * (n+1)` is NOT defeq to `n + 1` (Nat.mul recurses
  -- on the variable second argument), and the bridge must be the equation
  -- lemma for THAT side: `Nat.one_mul : 1 * n = n`.
  have hB : M677 n 1 ∣ n + 1 := by
    have h0 := e677_lcmd_dvd_mul 1 (n + 1)
    rw [Nat.one_mul] at h0
    exact h0
  exact Nat.dvd_antisymm hB hA

/-- M677 is always positive (the empty window is 1; each step lcms a
positive window element into a positive accumulator). -/
theorem M677_pos (n k : Nat) : 0 < M677 n k := by
  induction k with
  | zero => have h : M677 n 0 = 1 := rfl; omega
  | succ k ih =>
    rw [M677_succ]
    exact e677_lcmd_pos (M677 n k) (n + 1 + k) ih (by omega)

/-- THE STEP DIVISIBILITY LAW: M677 n k ∣ M677 n (k+1). -/
theorem M677_step_dvd (n k : Nat) : M677 n k ∣ M677 n (Nat.succ k) :=
  e677_dvd_lcmd_left (M677 n k) (n + 1 + k)

/-- k-MONOTONICITY: M677 n k ≤ M677 n (k+1) (the lcm grows with the
window). -/
theorem M677_mono (n k : Nat) : M677 n k ≤ M677 n (Nat.succ k) :=
  Nat.le_of_dvd (M677_pos n (Nat.succ k)) (M677_step_dvd n k)

/-- THE WINDOW DIVISIBILITY LAW: every element of the window
{n+1,…,n+k} divides M677 n k. -/
theorem M677_dvd_window (n k : Nat) : ∀ i : Nat, i < k → (n + 1 + i) ∣ M677 n k := by
  induction k with
  | zero => intro i hi; exfalso; omega
  | succ k ih =>
    intro i hi
    by_cases hik : i = k
    · rw [hik, M677_succ]
      exact e677_dvd_lcmd_right (M677 n k) (n + 1 + k)
    · have hlt : i < k := by omega
      have h := ih i hlt
      rw [M677_succ]
      exact Nat.dvd_trans h (e677_dvd_lcmd_left (M677 n k) (n + 1 + k))

/-- Positivity of the window product. -/
theorem wprod_pos (n k : Nat) : 0 < wprod n k := by
  induction k with
  | zero => have h : wprod n 0 = 1 := rfl; omega
  | succ k ih =>
    rw [wprod_succ]
    exact e677_mul_pos (wprod n k) (n + 1 + k) ih (by omega)

/-- THE PRODUCT DIVISIBILITY LAW: M677 n k divides the window product. -/
theorem M677_dvd_wprod (n k : Nat) : M677 n k ∣ wprod n k := by
  induction k with
  | zero => exact ⟨1, (Nat.mul_one (M677 n 0)).symm⟩
  | succ k ih =>
    rw [M677_succ, wprod_succ]
    have h1 : lcmd (M677 n k) (n + 1 + k) ∣ M677 n k * (n + 1 + k) :=
      e677_lcmd_dvd_mul (M677 n k) (n + 1 + k)
    have h2 : M677 n k * (n + 1 + k) ∣ wprod n k * (n + 1 + k) :=
      e677_dvd_scale (M677 n k) (wprod n k) (n + 1 + k) ih
    exact Nat.dvd_trans h1 h2

/-- THE PRODUCT BOUND: M677 n k ≤ ∏_{i<k}(n+1+i). -/
theorem M677_le_prod (n k : Nat) : M677 n k ≤ wprod n k :=
  Nat.le_of_dvd (wprod_pos n k) (M677_dvd_wprod n k)

/-! ## §4 The window table — the corpus's own named solutions,
kernel-certified (M(4,3) = lcm(5,6,7) = 210; M(13,2) = lcm(14,15) = 210;
M(3,4) = lcm(4,5,6,7) = 420; M(19,2) = lcm(20,21) = 420; the equal-k
OVERLAP collision M(2,3) = M(3,3) = 60 has m = 3 < 5 = n+k, so it lives in
the overlap zone the problem's m ≥ n+k excludes). -/

/-- THE CROSS-LENGTH COINCIDENCE k=3 → l=2 (Erdős's own): M(4,3) = M(13,2). -/
theorem known_cross_32 : M677 4 3 = M677 13 2 := by decide

/-- THE CROSS-LENGTH COINCIDENCE k=4 → l=2 (Erdős's own): M(3,4) = M(19,2). -/
theorem known_cross_42 : M677 3 4 = M677 19 2 := by decide

/-- THE EQUAL-k OVERLAP COLLISION: M(2,3) = M(3,3) = 60 — the only shape
of equal-k coincidence, and it is NOT disjoint (m = 3 < 2 + 3). -/
theorem known_overlap_23 : M677 2 3 = M677 3 3 := by decide

/-- The overlap instance violates the disjointness condition m ≥ n+k. -/
theorem known_overlap_is_not_disjoint : 3 < 2 + 3 := by decide

/-- The exact values of the anchors. -/
theorem e677_cross_values :
    (M677 4 3 = 210 ∧ M677 13 2 = 210 ∧ M677 3 4 = 420 ∧ M677 19 2 = 420 ∧
      M677 2 3 = 60 ∧ M677 3 3 = 60) := by decide

/-- THE WINDOW TABLE (11 exact rows, kernel-certified; note M(1,3) =
lcm(2,3,4) = 12). -/
theorem e677_window_table :
    (M677 0 1 = 1 ∧ M677 0 2 = 2 ∧ M677 0 3 = 6 ∧ M677 1 3 = 12 ∧ M677 0 4 = 12 ∧
      M677 2 3 = 60 ∧ M677 0 5 = 60 ∧ M677 0 6 = 60 ∧ M677 0 7 = 420 ∧
      M677 6 3 = 504 ∧ M677 9 2 = 110) := by decide

/-! ## §5 THE EQUAL-k NON-COLLISION CENSUS — the round-1 exclusion engine. -/

/-- THE SPEC BRIDGE: winCollFree w k n = true means exactly that no
disjoint-window partner m = n + k + j (j < w) collides with M677 n k. -/
theorem winCollFree_spec (k n : Nat) : ∀ w : Nat, winCollFree w k n = true →
    ∀ j : Nat, j < w → M677 n k ≠ M677 (n + k + j) k := by
  intro w
  induction w with
  | zero => intro _ j hj; exfalso; omega
  | succ w ih =>
    intro hcol j hj
    have hcol' : (if M677 n k = M677 (n + k + w) k then false else winCollFree w k n) = true := hcol
    by_cases hC : M677 n k = M677 (n + k + w) k
    · rw [if_pos hC] at hcol'
      exact absurd hcol' (by decide)
    · rw [if_neg hC] at hcol'
      by_cases hje : j = w
      · subst hje
        exact hC
      · have hlt : j < w := by omega
        exact ih hcol' j hlt

/-- CENSUS CHUNK k=1: no disjoint equal-k collision for n < 25, window
[n+1, n+25). -/
theorem no_coll_k1 : ∀ n < 25, winCollFree 25 1 n = true := by decide

/-- CENSUS CHUNK k=2. -/
theorem no_coll_k2 : ∀ n < 25, winCollFree 25 2 n = true := by decide

/-- CENSUS CHUNK k=3. -/
theorem no_coll_k3 : ∀ n < 25, winCollFree 25 3 n = true := by decide

/-- CENSUS CHUNK k=4. -/
theorem no_coll_k4 : ∀ n < 25, winCollFree 25 4 n = true := by decide

/-- CENSUS CHUNK k=5. -/
theorem no_coll_k5 : ∀ n < 25, winCollFree 25 5 n = true := by decide

/-- THE ROUND-1 KILL — the certified non-collision census box, honestly
labeled: for every n < 25, every 1 ≤ k ≤ 5, and every disjoint partner
m with n + k ≤ m < n + 25, the equal-lcm windows differ:
M677 n k ≠ M677 m k. (Assembled from the five kernel-decided chunks
through the spec bridge — no decide on the nested quantifier.) -/
theorem e677_no_collision_box : ∀ n k m : Nat, n < 25 → 1 ≤ k → k ≤ 5 →
    n + k ≤ m → m < n + 25 → M677 n k ≠ M677 m k := by
  intro n k m hn hk1 hk5 hmn hm
  obtain ⟨j, hj⟩ : ∃ j, m = n + k + j := ⟨m - n - k, by omega⟩
  rw [hj]
  have hjlt : j < 25 := by omega
  rcases (show k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 by omega) with h1 | h1 | h1 | h1 | h1
  · subst h1
    exact winCollFree_spec 1 n 25 (no_coll_k1 n hn) j hjlt
  · subst h1
    exact winCollFree_spec 2 n 25 (no_coll_k2 n hn) j hjlt
  · subst h1
    exact winCollFree_spec 3 n 25 (no_coll_k3 n hn) j hjlt
  · subst h1
    exact winCollFree_spec 4 n 25 (no_coll_k4 n hn) j hjlt
  · subst h1
    exact winCollFree_spec 5 n 25 (no_coll_k5 n hn) j hjlt

/-! ## §6 THE ARSENAL BRIDGE (BOSS's mathematics applied to the #677
anchors — erdosternary2 + CardinalWorlds: 210 = M(4,3) = M(13,2) anchors
the v2r-scaling at 3^1·70 and the mod law at the window element 5; 21 is
the top of the M(19,2) window {20,21}). -/

theorem e677_arsenal_bridge :
    ErdosTernary2.isTernaryDigit (210 % 3) ∧
    (21 ^ 2 - 1 = (21 - 1) * (21 + 1)) ∧
    (210 % (5 * 2)) % 5 = 210 % 5 ∧
    carryAtPos 210 1 < 4 ∧
    v2r (3 ^ 1 * 70) = v2r 70 :=
  ⟨by decide, sq_sub_one 21 (by decide), mod_mod_mul 210 5 2 (by decide),
    carryAtPos_bound 210 1, CardinalWorldsV2.v2r_ternary_scaling 1 70⟩

/-! ## §7 THE MASTER BOARD (ten conjuncts, one term each). -/

/-- THE P677 ROUND-1 BOARD: the anchor values + both corpus coincidences +
the overlap collision + the certified equal-k census box + the window
divisibility law + k-monotonicity + the k=1 kill + the product bound +
the arsenal bridge core. -/
theorem e677_board :
    (M677 4 3 = 210 ∧ M677 13 2 = 210 ∧ M677 3 4 = 420 ∧ M677 19 2 = 420 ∧
      M677 2 3 = 60 ∧ M677 3 3 = 60) ∧
    (M677 4 3 = M677 13 2) ∧
    (M677 3 4 = M677 19 2) ∧
    (M677 2 3 = M677 3 3) ∧
    (∀ n k m : Nat, n < 25 → 1 ≤ k → k ≤ 5 → n + k ≤ m → m < n + 25 →
      M677 n k ≠ M677 m k) ∧
    (∀ n k : Nat, ∀ i : Nat, i < k → (n + 1 + i) ∣ M677 n k) ∧
    (∀ n k : Nat, M677 n k ≤ M677 n (k + 1)) ∧
    (∀ n : Nat, M677 n 1 = n + 1) ∧
    (∀ n k : Nat, M677 n k ≤ wprod n k) ∧
    (ErdosTernary2.isTernaryDigit (210 % 3) ∧ v2r (3 ^ 1 * 70) = v2r 70) :=
  ⟨e677_cross_values, known_cross_32, known_cross_42, known_overlap_23,
    fun n k m hn hk1 hk5 hmn hm => e677_no_collision_box n k m hn hk1 hk5 hmn hm,
    fun n k => M677_dvd_window n k,
    fun n k => M677_mono n k,
    M677_one,
    fun n k => M677_le_prod n k,
    ⟨by decide, CardinalWorldsV2.v2r_ternary_scaling 1 70⟩⟩

end E677

/-! ## RECEIPT. -/

#print axioms E677.e677_div_mul_self
#print axioms E677.e677_dvd_mul_of
#print axioms E677.e677_dvd_mod_zero
#print axioms E677.e677_lcmd_mul_gcd
#print axioms E677.e677_mul_eq_zero
#print axioms E677.e677_mul_pos
#print axioms E677.e677_lcmd_pos
#print axioms E677.e677_dvd_lcmd_left
#print axioms E677.e677_dvd_lcmd_right
#print axioms E677.e677_lcmd_dvd_mul
#print axioms E677.e677_dvd_scale
#print axioms E677.M677_zero
#print axioms E677.M677_succ
#print axioms E677.wprod_zero
#print axioms E677.wprod_succ
#print axioms E677.M677_one
#print axioms E677.M677_pos
#print axioms E677.M677_step_dvd
#print axioms E677.M677_mono
#print axioms E677.M677_dvd_window
#print axioms E677.wprod_pos
#print axioms E677.M677_dvd_wprod
#print axioms E677.M677_le_prod
#print axioms E677.known_cross_32
#print axioms E677.known_cross_42
#print axioms E677.known_overlap_23
#print axioms E677.known_overlap_is_not_disjoint
#print axioms E677.e677_cross_values
#print axioms E677.e677_window_table
#print axioms E677.winCollFree_spec
#print axioms E677.no_coll_k1
#print axioms E677.no_coll_k2
#print axioms E677.no_coll_k3
#print axioms E677.no_coll_k4
#print axioms E677.no_coll_k5
#print axioms E677.e677_no_collision_box
#print axioms E677.e677_arsenal_bridge
#print axioms E677.e677_board

#eval "E677_EQUAL_LCM_GREEN"
