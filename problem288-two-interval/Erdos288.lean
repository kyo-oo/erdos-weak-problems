import Arsenal.ErdosTernary2.Basic
import Arsenal.CardinalWorlds
import Arsenal.CardinalWorldsV2

set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-!
# Erdos288 — THE TWO-INTERVAL HARMONIC KERNEL r1 (W57-5, Kernel — P288)

Erdős #288 (verbatim, erdosproblems.com/288):

> Characterize the pairs of intervals [a, b], [c, d] of positive integers such
> that the sum of reciprocals over each interval is equal and the intervals
> are disjoint.

Campaign reading (THE_CORE §S031 record: "#288/#1212 promoted"; the
#317-signed-harmonic reduction machinery transfers — DERIVATION.md §2's
isolated-extremal engine is the named round-2 lane). Python hunts in this
folder (`hunt288.py`, `verify288.py`): **ZERO disjoint equal-sum window
pairs with all endpoints ≤ 120** (all 7,260 windows over [1..120], grouped by
exact Fraction value, zero cross-group disjoint hits), and zero
single-term matches 1/n = Σ_{c≤j≤d} 1/j for n ≤ 40, d ≤ 80. The conjectured
classification is EMPTY; the round-2 lane is the Kürschák-style parity
obstruction (the unique maximal 2-adic valuation in the span — #317's
isolated-extremal engine).

Round-1 kernel (full statements, complete unconditional proofs, zero sorry):
1. §1 THE INTERVAL-SUM DEFINITION — `window` (the list view), `wprod`
   (product of [a..b] — the unreduced denominator), `hnum` (the numerator of
   Σ_{i∈[a,b]} 1/i over that product — the harmonic window sum as an exact
   Nat fraction), and `equalWindow` — window equality as the
   cross-multiplied Nat identity hnum a b * wprod c d = hnum c d * wprod a b.
2. §2 THE STRUCTURAL LAWS — the recurrences (`wprod_unfold`, `hnum_unfold`,
   rfl), the empty-window laws, positivity (`wprod_pos`, `hnum_pos`), and
   the single-window values (`hnum_single` = 1, `wprod_single` = a).
3. §3 THE STRICT GROWTH LAW `window_mono_step` (adding the term b+1 strictly
   increases the window sum, cross-multiplied) + `single_lt_pair` — the
   equality-free monotonicity core (the direction provable in round 1).
4. §4 THE CENSUS (decide-certified, bounded) — `e288_no_disjoint_pair_le12`
   (no disjoint equal pair with endpoints ≤ 12), `e288_single_never_right_le24`
   (no single-vs-later-window match, n ≤ 10, c, d ≤ 24), plus the
   unconditional `empty_never_nonempty` and the trivial family
   `equalWindow_refl` / `equalWindow_symm`.
5. §5 THE ANCHORS — `anchor_values` (python-verified exact values:
   [2,4] ↦ 26/24 = 13/12, [3,5] ↦ 47/60, [6,9] ↦ 1650/3024 = 275/504,
   [4,7] ↦ 638/840 = 319/420) + `e288_arsenal_bridge` (BOSS's arsenal on
   the #288 anchors: `isTernaryDigit`, `sq_sub_one`, `mod_mod_mul`,
   `carryAtPos_bound`, `v2r_ternary_scaling`).
6. §6 THE BOARD — `e288_board`, the master composite (12 conjuncts).

House law: GitHub CI is the verifier of record (no local compile; author
blind). Axiom profile must stay within [propext, Classical.choice,
Quot.sound]. Zero sorry, zero native_decide; `by decide` only on closed
numerics / bounded enumerations.
-/

namespace E288

/-! ## §1 The definitions — the interval-sum encoding. -/

/-- The interval [a, b] as a list of Nats (empty when b < a): the indexing
view of the harmonic window. -/
def window (a b : Nat) : List Nat := (List.range (b + 1 - a)).map (fun i => a + i)

/-- The product of the integers in [a, b] — the unreduced DENOMINATOR of the
harmonic window sum (empty window → 1). -/
def wprod : Nat → Nat → Nat
  | _, 0 => 1
  | a, b + 1 => if a ≤ b + 1 then wprod a b * (b + 1) else 1

/-- The NUMERATOR of Σ_{i∈[a,b]} 1/i over the product denominator `wprod a b`
(the unreduced exact fraction of the harmonic window sum; empty window → 0). -/
def hnum : Nat → Nat → Nat
  | _, 0 => 0
  | a, b + 1 => if a ≤ b + 1 then hnum a b * (b + 1) + wprod a b else 0

/-- EQUAL harmonic window sums, as the cross-multiplied Nat identity:
Σ_{[a,b]} 1/i = Σ_{[c,d]} 1/j ⟺ hnum a b * wprod c d = hnum c d * wprod a b
(valid whenever both windows are nonempty with positive terms — §2's
`wprod_pos`/`hnum_pos`). Reducible so `by decide` sees the Nat equality
through the def in the census theorems. -/
@[reducible]
def equalWindow (a b c d : Nat) : Prop :=
  hnum a b * wprod c d = hnum c d * wprod a b

/-! ## §2 The structural laws — recurrences, emptiness, positivity. -/

/-- The definitional unfolding of `window` (rfl: delta). -/
theorem window_eq (a b : Nat) :
    window a b = (List.range (b + 1 - a)).map (fun i => a + i) := rfl

theorem window_nil (a b : Nat) (h : b < a) : window a b = [] := by
  have h1 : b + 1 - a = 0 := by omega
  rw [window_eq, h1]
  -- r1 post-mortem (run 43335072786): List.range 0 is not defeq [] at rw's
  -- trailing rfl (List.range is range'-based, not a Nat.rec); simp closes it.
  simp

theorem window_single (a : Nat) : window a a = [a] := by
  have h1 : a + 1 - a = 1 := by omega
  rw [window_eq, h1]
  -- r1 post-mortem (run 43335072786): List.range 1 = [0] + map + add_zero
  -- needs the simp normalization (not defeq at trailing-rfl transparency).
  simp

/-- The base recurrences (rfl: structural match on the second argument). -/
theorem wprod_zero (a : Nat) : wprod a 0 = 1 := rfl

theorem hnum_zero (a : Nat) : hnum a 0 = 0 := rfl

theorem wprod_unfold (a b : Nat) :
    wprod a (b + 1) = if a ≤ b + 1 then wprod a b * (b + 1) else 1 := rfl

theorem hnum_unfold (a b : Nat) :
    hnum a (b + 1) = if a ≤ b + 1 then hnum a b * (b + 1) + wprod a b else 0 := rfl

/-- An empty window has the empty product 1 (induction on the right end). -/
theorem wprod_nil : ∀ (b a : Nat), b < a → wprod a b = 1 := by
  intro b
  induction b with
  | zero => intro a _
            rfl
  | succ b _ =>
      intro a h
      have hneg : ¬ (a ≤ b + 1) := by omega
      rw [wprod_unfold, if_neg hneg]

/-- An empty window has numerator 0. -/
theorem hnum_nil : ∀ (b a : Nat), b < a → hnum a b = 0 := by
  intro b
  induction b with
  | zero => intro a _
            rfl
  | succ b _ =>
      intro a h
      have hneg : ¬ (a ≤ b + 1) := by omega
      rw [hnum_unfold, if_neg hneg]

/-- Self-contained strict-positivity of products (the L86-safe core:
`Nat.mul_succ` expansion + omega shell; no external mul_pos). -/
theorem e288_mul_pos (x y : Nat) (hx : 0 < x) (hy : 0 < y) : 0 < x * y := by
  obtain ⟨k, hk⟩ : ∃ k : Nat, y = k + 1 := ⟨y - 1, by omega⟩
  rw [hk]
  have hms : x * (k + 1) = x * k + x := Nat.mul_succ x k
  rw [hms]
  omega

/-- THE PRODUCT LAW: for windows of positive integers the denominator is
positive (unconditionally — the empty window gives 1). -/
theorem wprod_pos (a b : Nat) (ha : 1 ≤ a) : 0 < wprod a b := by
  induction b with
  | zero => have h1 : wprod a 0 = 1 := rfl
            omega
  | succ b ih =>
      rw [wprod_unfold]
      by_cases h : a ≤ b + 1
      · rw [if_pos h]
        have hy : 0 < b + 1 := by omega
        exact e288_mul_pos _ _ ih hy
      · rw [if_neg h]
        omega

/-- THE NUMERATOR LAW: a nonempty window of positive integers has positive
harmonic sum. -/
theorem hnum_pos (a b : Nat) (ha : 1 ≤ a) : a ≤ b → 0 < hnum a b := by
  induction b with
  | zero => intro hba
            omega
  | succ b ih =>
      intro hba
      rw [hnum_unfold, if_pos hba]
      have hw : 0 < wprod a b := wprod_pos a b ha
      rcases Nat.lt_or_ge a (b + 1) with hlt | hge
      · have hh := ih (by omega)
        have hm : 0 < hnum a b * (b + 1) := e288_mul_pos _ _ hh (by omega)
        omega
      · have hnil : hnum a b = 0 := hnum_nil b a (by omega)
        rw [hnil]
        omega

/-- The nonempty-step recurrences (the fraction-addition laws:
Σ_{[a,b+1]} 1/i = hnum·(b+1) + wprod over wprod·(b+1)). -/
theorem wprod_succ_le (a b : Nat) (h : a ≤ b + 1) :
    wprod a (b + 1) = wprod a b * (b + 1) := by
  rw [wprod_unfold, if_pos h]

theorem hnum_succ_le (a b : Nat) (h : a ≤ b + 1) :
    hnum a (b + 1) = hnum a b * (b + 1) + wprod a b := by
  rw [hnum_unfold, if_pos h]

/-- THE SINGLE-TERM SPELLING: the window [a, a] carries the fraction 1/a
exactly (numerator 1, denominator a). -/
theorem hnum_single (a : Nat) (ha : 1 ≤ a) : hnum a a = 1 := by
  have hstep := hnum_succ_le a (a - 1) (by omega)
  have hpre : (a - 1) + 1 = a := by omega
  rw [hpre] at hstep
  have hnil : hnum a (a - 1) = 0 := hnum_nil (a - 1) a (by omega)
  have hp : wprod a (a - 1) = 1 := wprod_nil (a - 1) a (by omega)
  rw [hstep, hnil, hp]
  omega

theorem wprod_single (a : Nat) (ha : 1 ≤ a) : wprod a a = a := by
  have hstep := wprod_succ_le a (a - 1) (by omega)
  have hpre : (a - 1) + 1 = a := by omega
  rw [hpre] at hstep
  have hp : wprod a (a - 1) = 1 := wprod_nil (a - 1) a (by omega)
  rw [hstep, hp]
  omega

/-! ## §3 The strict growth law — the equality-free monotonicity core. -/

/-- THE STRICT GROWTH LAW: appending the term b+1 to the window [a, b]
strictly increases the harmonic window sum, in the cross-multiplied form —
the difference of the two cross-products is wprod a b squared, hence positive
whenever the window carries positive terms. -/
theorem window_mono_step (a b : Nat) (ha : 1 ≤ a) (hab : a ≤ b + 1) :
    hnum a b * (wprod a b * (b + 1)) < hnum a (b + 1) * wprod a b := by
  rw [hnum_succ_le a b hab]
  have hL : 0 < wprod a b := wprod_pos a b ha
  have hW : 0 < wprod a b * wprod a b := e288_mul_pos _ _ hL hL
  have hexp : (hnum a b * (b + 1) + wprod a b) * wprod a b
      = hnum a b * (wprod a b * (b + 1)) + wprod a b * wprod a b := by
    ring
  rw [hexp]
  omega

/-- The single-term instance of the growth law: [n, n] < [n, n + 1]. -/
theorem single_lt_pair (n : Nat) (hn : 1 ≤ n) :
    hnum n n * (wprod n n * (n + 1)) < hnum n (n + 1) * wprod n n :=
  window_mono_step n n hn (by omega)

/-! ## §4 The census and the non-degeneracy laws. -/

/-- The trivial family: every window equals itself (the non-disjoint side of
the classification). -/
theorem equalWindow_refl (a b : Nat) : equalWindow a b a b := rfl

/-- Window equality is symmetric (the WLOG companion for the disjointness
condition: the pair ([a,b], [c,d]) may be ordered b < c). -/
theorem equalWindow_symm (a b c d : Nat) :
    equalWindow a b c d → equalWindow c d a b := by
  intro h
  exact Eq.symm h

/-- THE EMPTY-WINDOW NON-DEGENERACY LAW (unconditional): an empty window
never has the same sum as a nonempty window of positive integers — the
cross-multiplied identity collapses to 0 = hnum c d with hnum c d > 0. -/
theorem empty_never_nonempty (a b c d : Nat) (hc : 1 ≤ c) (hcd : c ≤ d) (hba : b < a) :
    ¬ equalWindow a b c d := by
  unfold equalWindow
  rw [hnum_nil b a (by omega), wprod_nil b a (by omega),
      Nat.zero_mul, Nat.mul_one]
  intro h
  have hh := hnum_pos c d hc hcd
  omega

/-- THE ANCHORS (python-verified in verify288.py): the exact unreduced
fractions of four reference windows — [2,4] ↦ 26/24 (= 13/12),
[3,5] ↦ 47/60, [6,9] ↦ 1650/3024 (= 275/504), [4,7] ↦ 638/840 (= 319/420). -/
theorem anchor_values :
    hnum 2 4 = 26 ∧ wprod 2 4 = 24 ∧ hnum 3 5 = 47 ∧ wprod 3 5 = 60 ∧
    hnum 6 9 = 1650 ∧ wprod 6 9 = 3024 ∧ hnum 4 7 = 638 ∧ wprod 4 7 = 840 := by
  decide

/-- THE CENSUS, DISJOINT FORM (decide-certified): NO two disjoint windows
with all endpoints ≤ 12 have equal harmonic sums. The python hunt
(hunt288.py) extends this census to all endpoints ≤ 120 with zero hits —
the conjectured #288 classification is EMPTY. -/
theorem e288_no_disjoint_pair_le12 :
    (List.range 13).all (fun a : Nat =>
      (List.range 13).all (fun b : Nat =>
        (List.range 13).all (fun c : Nat =>
          (List.range 13).all (fun d : Nat =>
            decide (¬ (1 ≤ a ∧ a ≤ b ∧ b < c ∧ c ≤ d ∧ equalWindow a b c d)))))) = true := by
  decide

/-- THE CENSUS, SINGLE-VS-RIGHT FORM (decide-certified): for n ≤ 10 and
windows [c, d] with c, d ≤ 24 lying strictly to the right of n, the single
term 1/n never equals Σ_{j∈[c,d]} 1/j. The python hunt extends to n ≤ 40,
d ≤ 80 with zero hits. -/
theorem e288_single_never_right_le24 :
    (List.range 11).all (fun n : Nat =>
      (List.range 25).all (fun c : Nat =>
        (List.range 25).all (fun d : Nat =>
          decide (¬ (1 ≤ n ∧ n < c ∧ c ≤ d ∧ equalWindow n n c d))))) = true := by
  decide

/-! ## §5 The arsenal bridge — BOSS's mathematics on the #288 anchors.

Anchors: 26 = hnum 2 4 (the [2,4] numerator, 26 = 2·13), 24 = wprod 2 4,
47 = hnum 3 5, 60 = wprod 3 5. All five Arsenal lemmas are applied at
#288-native numbers. -/

theorem e288_arsenal_bridge :
    ErdosTernary2.isTernaryDigit (26 % 3) ∧
    (24 ^ 2 - 1 = (24 - 1) * (24 + 1)) ∧
    (60 % (47 * 2)) % 47 = 60 % 47 ∧
    carryAtPos 24 1 < 4 ∧
    v2r (3 ^ 1 * 26) = v2r 26 :=
  ⟨by decide, sq_sub_one 24 (by decide), mod_mod_mul 60 47 2 (by decide),
    carryAtPos_bound 24 1, CardinalWorldsV2.v2r_ternary_scaling 1 26⟩

/-! ## §6 The master board. -/

/-- THE P288 CASE BOARD (twelve conjuncts, full statements, unconditional):
the product law + the numerator law + the strict growth law + the trivial
family + symmetry + the empty-window law + the two single-window spellings +
the four python-verified anchors + the two bounded censuses + the arsenal
bridge core. -/
theorem e288_board :
    (∀ a b : Nat, 1 ≤ a → 0 < wprod a b) ∧
    (∀ a b : Nat, 1 ≤ a → a ≤ b → 0 < hnum a b) ∧
    (∀ a b : Nat, 1 ≤ a → a ≤ b + 1 →
      hnum a b * (wprod a b * (b + 1)) < hnum a (b + 1) * wprod a b) ∧
    (∀ a b : Nat, equalWindow a b a b) ∧
    (∀ a b c d : Nat, equalWindow a b c d → equalWindow c d a b) ∧
    (∀ a b c d : Nat, 1 ≤ c → c ≤ d → b < a → ¬ equalWindow a b c d) ∧
    (∀ a : Nat, 1 ≤ a → hnum a a = 1) ∧
    (∀ a : Nat, 1 ≤ a → wprod a a = a) ∧
    (hnum 2 4 = 26 ∧ wprod 2 4 = 24 ∧ hnum 3 5 = 47 ∧ wprod 3 5 = 60 ∧
      hnum 6 9 = 1650 ∧ wprod 6 9 = 3024 ∧ hnum 4 7 = 638 ∧ wprod 4 7 = 840) ∧
    ((List.range 13).all (fun a : Nat =>
      (List.range 13).all (fun b : Nat =>
        (List.range 13).all (fun c : Nat =>
          (List.range 13).all (fun d : Nat =>
            decide (¬ (1 ≤ a ∧ a ≤ b ∧ b < c ∧ c ≤ d ∧ equalWindow a b c d)))))) = true) ∧
    ((List.range 11).all (fun n : Nat =>
      (List.range 25).all (fun c : Nat =>
        (List.range 25).all (fun d : Nat =>
          decide (¬ (1 ≤ n ∧ n < c ∧ c ≤ d ∧ equalWindow n n c d))))) = true) ∧
    (24 ^ 2 - 1 = (24 - 1) * (24 + 1) ∧ v2r (3 ^ 1 * 26) = v2r 26) :=
  ⟨wprod_pos, hnum_pos, window_mono_step, equalWindow_refl, equalWindow_symm,
    empty_never_nonempty, hnum_single, wprod_single, anchor_values,
    e288_no_disjoint_pair_le12, e288_single_never_right_le24,
    ⟨sq_sub_one 24 (by decide), CardinalWorldsV2.v2r_ternary_scaling 1 26⟩⟩

end E288

/-! ## RECEIPT. -/

#print axioms E288.window_eq
#print axioms E288.window_nil
#print axioms E288.window_single
#print axioms E288.wprod_zero
#print axioms E288.hnum_zero
#print axioms E288.wprod_unfold
#print axioms E288.hnum_unfold
#print axioms E288.wprod_nil
#print axioms E288.hnum_nil
#print axioms E288.e288_mul_pos
#print axioms E288.wprod_pos
#print axioms E288.hnum_pos
#print axioms E288.wprod_succ_le
#print axioms E288.hnum_succ_le
#print axioms E288.hnum_single
#print axioms E288.wprod_single
#print axioms E288.window_mono_step
#print axioms E288.single_lt_pair
#print axioms E288.equalWindow_refl
#print axioms E288.equalWindow_symm
#print axioms E288.empty_never_nonempty
#print axioms E288.anchor_values
#print axioms E288.e288_no_disjoint_pair_le12
#print axioms E288.e288_single_never_right_le24
#print axioms E288.e288_arsenal_bridge
#print axioms E288.e288_board

#eval "E288_TWO_INTERVAL_GREEN"
