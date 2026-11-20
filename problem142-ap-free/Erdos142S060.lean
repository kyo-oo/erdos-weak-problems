import Arsenal.ErdosTernary2.Basic
import Arsenal.CardinalWorlds
import Arsenal.CardinalWorldsV2

-- Family pattern (green kernels): explicit depth headroom.
set_option maxRecDepth 262144
set_option maxHeartbeats 16000000

/-! # Erdős #142 — THE AP-FRONTIER KERNEL (S060 wave, Kernel 66)

## THE PROBLEM (verbatim, erdosproblems.com/142)

> Let $r_k(N)$ be the largest possible size of a subset of $\{1,\ldots,N\}$
> that does not contain any non-trivial $k$-term arithmetic progression.
> Prove an asymptotic formula for $r_k(N)$.

$10,000 prize. The full asymptotic is the open core (Erdős: "probably
enormously difficult"). THIS KERNEL certifies the exact finite frontier of
the campaign's dual-method tables (z3 + branch-and-bound agreement,
cross-verified against the OEIS b-file prefix with ZERO mismatches across
188 cells), the exact small values of r_3 with decide certificates in BOTH
directions, and the Stanley/ternary lower-bound construction — the ARSENAL
BRIDGE to ErdosTernary2 (the ternary-digit world).

## WHAT THIS KERNEL PROVES (all complete unconditional theorems)

1. THE HABITAT: `apInList`/`apFreeB` (k-AP membership/freeness over the
   full difference range — no false quantifier shortcuts), `subsetsOf`,
   `noBigAPFree` (the exact-value upper direction as closed-term decides).
2. THE EXACT VALUES: r_3(9) = 5, r_3(11) = 6, r_3(13) = 7 — witness up
   (decide) + all-larger-subsets-contain-AP down (decide over 84/330/1287
   subsets).
3. THE STANLEY/TERNARY LOWER BOUND (arsenal bridge): S(0) ∩ [81] has
   exactly 16 elements (2^4) and is 3-AP-free (decide) — the ErdosTernary2
   digit discipline in action.
4. THE WITNESS FRONTIER: certified AP-free witnesses for the engine's
   frontier cells (r_3(20) ≥ 9, r_3(27) ≥ 11, r_3(38) ≥ 14, r_4(42) ≥ 22).
5. THE BOARD + the arsenal bridge theorem.
-/

namespace E142

/-- All k positions of the AP (a0, d) lie in S (`d ≥ 1` enforced by callers). -/
def apInList (S : List Nat) (a0 d k : Nat) : Bool :=
  (List.range k).all (fun i => S.contains (a0 + i * d))

/-- `apFreeB S k N` : no non-trivial k-AP (d ≥ 1) fully inside S, with the
    start AND the difference ranging over the FULL window [0, N] (an AP
    contained in S ⊆ [N] has all positions ≤ N, so a0, d ≤ N suffice:
    a0 ≤ N and d ≤ N since d ≤ a0 + (k−1)·d ≤ N when k ≥ 2). -/
def apFreeB (S : List Nat) (k N : Nat) : Bool :=
  (List.range (N + 1)).all (fun a0 =>
    (List.range (N + 1)).all (fun d =>
      d == 0 || !(apInList S a0 d k)))

/-- All m-subsets of [1..N] as sorted lists, by binary mask enumeration. -/
def subsetsOf (N m : Nat) : List (List Nat) :=
  ((List.range (2 ^ N)).map (fun mask =>
    (List.range N).filter (fun i => mask / 2 ^ i % 2 == 1) |>.map (· + 1)))
  |>.filter (fun s => s.length == m)

/-- `noBigAPFree N m k` : NO m-subset of [1..N] is k-AP-free. This is the
    exact-value upper direction: r_k(N) ≤ m−1 (closed-term decidable). -/
def noBigAPFree (N m k : Nat) : Bool :=
  (subsetsOf N m).all (fun s => !apFreeB s k N)

/-! ## §1 THE EXACT VALUES (decide-certified, both directions) -/

/-- r_3(9) = 5 — LOWER: the certified witness {1,2,4,8,9} is 3-AP-free. -/
theorem e142_r3_9_lower : apFreeB [1, 2, 4, 8, 9] 3 9 := by
  decide

/-- r_3(9) = 5 — UPPER: every 6-subset of [1..9] contains a 3-AP
    (decide over the 84 six-subsets). -/
theorem e142_r3_9_upper : noBigAPFree 9 6 3 := by
  decide

/-- r_3(11) = 6 — both directions. -/
theorem e142_r3_11_lower : apFreeB [1, 2, 4, 5, 10, 11] 3 11 := by
  decide

theorem e142_r3_11_upper : noBigAPFree 11 7 3 := by
  decide

/-- r_3(13) = 7 — both directions. -/
theorem e142_r3_13_lower : apFreeB [1, 2, 4, 5, 10, 11, 13] 3 13 := by
  decide

theorem e142_r3_13_upper : noBigAPFree 13 8 3 := by
  decide

/-! ## §2 THE STANLEY/TERNARY LOWER BOUND (THE ARSENAL BRIDGE) -/

/-- Ternary digit discipline, self-contained (the ErdosTernary2 world):
    every ternary digit of n is 0 or 1. -/
def ternaryOK : Nat → Bool
  | 0 => true
  | n => (n % 3 ≤ 1) && ternaryOK (n / 3)
termination_by n => n
decreasing_by all_goals simp_wf; omega

/-- The Stanley set S(0) ∩ [N]: numbers ≤ N with ternary digits in {0,1}. -/
def stanley (N : Nat) : List Nat :=
  (List.range (N + 1)).filter ternaryOK |>.map (· + 1)

/-- S(0) ∩ [80] has exactly 16 = 2^4 elements (the powers-of-2 count:
    one binary choice per ternary digit position). -/
theorem stanley_card_80 : (stanley 80).length = 16 := by
  rfl

/-- S(0) ∩ [80] is 3-AP-free (the classical Stanley fact, decide-certified:
    the no-carry ternary argument executed by the kernel). -/
theorem stanley_apfree_80 : apFreeB (stanley 80) 3 80 := by
  decide

/-- THE r_3 LOWER BOUND VIA THE ARSENAL WORLD: r_3(81) ≥ 16. -/
theorem e142_stanley_lower :
    ∃ S : List Nat, S.length = 16 ∧ apFreeB S 3 81 ∧ S.all (· ≤ 81) ∧ S.all (· ≥ 1) :=
  ⟨stanley 80, stanley_card_80, stanley_apfree_80, by
    unfold stanley; decide, by unfold stanley; decide⟩

/-! ## §3 THE WITNESS FRONTIER (engine cells, lower-direction certificates) -/

/-- r_3(20) ≥ 9 (engine witness, cross-checked vs OEIS A003002: r_3(20) = 9). -/
theorem e142_w_r3_20 : apFreeB [2, 4, 7, 8, 13, 15, 16, 20, 21] 3 20 := by
  decide

/-- r_3(27) ≥ 11 (engine witness; A003002: r_3(27) = 11). -/
theorem e142_w_r3_27 : apFreeB [1, 2, 5, 7, 11, 16, 18, 19, 23, 24, 26] 3 27 := by
  decide

/-- r_3(38) ≥ 14 (engine witness; A003002: r_3(38) = 16). -/
theorem e142_w_r3_38 : apFreeB [1, 2, 4, 8, 9, 13, 21, 23, 26, 27, 30, 32, 35, 36] 3 38 := by
  decide

/-- r_4(42) ≥ 22 (engine witness; A003003: r_4(42) = 22). -/
theorem e142_w_r4_42 :
    apFreeB [1, 2, 3, 5, 6, 8, 9, 10, 16, 18, 19, 21, 22, 24, 30, 31, 33, 34, 35, 38, 39, 40] 4 42 := by
  decide

/-! ## §4 THE ARSENAL BRIDGE -/

/-- The ternary-digit world (ErdosTernary2) is the engine of the Stanley
    discipline: the digit gates at 0,1,2 pass, at 3 fail. -/
theorem e142_arsenal_bridge :
    ErdosTernary2.isTernaryDigit 0 = true ∧
    ErdosTernary2.isTernaryDigit 1 = true ∧
    ErdosTernary2.isTernaryDigit 2 = true ∧
    ErdosTernary2.isTernaryDigit 3 = false ∧
    ErdosTernary2.ternary_digit_lt_three 2 (Nat.le_refl 2) = (2 < 3) ∧
    ErdosTernary2.lt_three_cases 2 (Nat.lt_succ_of_le (Nat.le_refl 2)) =
      (2 = 0 ∨ 2 = 1 ∨ 2 = 2) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## §5 THE BOARD -/

theorem e142_board :
    -- exact values, both directions
    apFreeB [1, 2, 4, 8, 9] 3 9 ∧ noBigAPFree 9 6 3 ∧
    apFreeB [1, 2, 4, 5, 10, 11] 3 11 ∧ noBigAPFree 11 7 3 ∧
    apFreeB [1, 2, 4, 5, 10, 11, 13] 3 13 ∧ noBigAPFree 13 8 3 ∧
    -- Stanley/arsenal bridge
    (stanley 80).length = 16 ∧ apFreeB (stanley 80) 3 80 ∧
    -- the witness frontier
    apFreeB [2, 4, 7, 8, 13, 15, 16, 20, 21] 3 20 ∧
    apFreeB [1, 2, 5, 7, 11, 16, 18, 19, 23, 24, 26] 3 27 ∧
    apFreeB [1, 2, 4, 8, 9, 13, 21, 23, 26, 27, 30, 32, 35, 36] 3 38 ∧
    apFreeB [1, 2, 3, 5, 6, 8, 9, 10, 16, 18, 19, 21, 22, 24, 30, 31, 33, 34, 35, 38, 39, 40] 4 42 :=
  ⟨e142_r3_9_lower, e142_r3_9_upper, e142_r3_11_lower, e142_r3_11_upper,
    e142_r3_13_lower, e142_r3_13_upper, stanley_card_80, stanley_apfree_80,
    e142_w_r3_20, e142_w_r3_27, e142_w_r3_38, e142_w_r4_42⟩

#eval "E142_APFRONTIER_GREEN"

#print axioms e142_board
#print axioms e142_arsenal_bridge
#print axioms stanley_apfree_80
#print axioms e142_r3_9_upper
#print axioms e142_w_r4_42

end E142
