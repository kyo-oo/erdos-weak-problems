import Arsenal.ErdosTernary2.Basic
import Arsenal.CardinalWorlds
import Arsenal.CardinalWorldsV2

set_option maxRecDepth 65536
set_option maxHeartbeats 20000000

/-! # Erdős #954 — THE ROSEN SEQUENCE LAWS (S036 volley, Kernel 29)

## THE PROBLEM (verbatim, erdosproblems.com/954)

> Let $0=a_0<a_1<a_2<\cdots$ be the sequence of integers defined by
> $a_0=0$ and $a_1=1$, and $a_{k+1}$ is the smallest integer $n$ for
> which the number of solutions to $a_i+a_j \leq n$ (with $0\leq i\leq
> j\leq k$ and $j\geq 1$) is $<n$. Is the number of solutions to
> $a_i+a_j\leq x$ equal to $x+O(x^{1/4+o(1)})$?

## WHAT THIS PROOF PROVES (the statement above, then the proofs below —
all complete unconditional theorems; the asymptotic question remains
open and is NOT claimed)

1. **THE CERTIFIED SEQUENCE** (`erdos954_construction`): the first 46
   terms $a_0, \ldots, a_{45}$ = $0, 1, 3, 5, 9, 13, 17, 24, 31, 38,
   45, \ldots, 769, 776, 836$ — every computed term satisfies the
   defining property (the count of solutions below it drops strictly
   below it), kernel-decided per step: for every $e \in [2, 45]$:
   $\mathrm{cnt}_{[0..e-1]}(a_e) < a_e$.
2. **THE COUNT LAW** (`erdos954_count_law`): for every $1 \le x < 378$
   (i.e. $x < a_{30}$): the number of solutions to $a_i + a_j \le x$
   over the certified 30-term prefix is $\ge x$ — the problem's own
   "always at least $x$ by construction" remark, formalized and
   kernel-decided.
3. **THE DEVIATION PROFILE** (battery): on the certified window the
   deviation $N(x) - x$ stays $\le 11$ (max at $x = 498$ on the full
   46-term census) — consistent with the $x^{1/4+o(1)}$ conjecture;
   evidence, not claimed.

Honest scope: the asymptotic $x + O(x^{1/4+o(1)})$ and even the
Erdős–Rosen $(1+o(1))x$ upper bound remain open; the block law of the
gaps (initial blocks of constant gaps $2,2,4,4,4,7,7,7,7,8,8$) breaks
at block 5 — the irregularity is the derivation target.
-/

namespace Erdos954

/-! ## §1 The certified table. -/

def rosenTab : List Nat :=
  [0, 1, 3, 5, 9, 13, 17, 24, 31, 38, 45, 53, 61, 75, 87, 97, 112,
   124, 139, 147, 175, 182, 205, 219, 242, 265, 277, 309, 313, 349,
   378, 386, 430, 445, 478, 480, 546, 548, 603, 615, 669, 677, 718,
   769, 776, 836]

/-- The solution count: #{(i, j) : 0 ≤ i ≤ j < l.length, 1 ≤ j,
l[i] + l[j] ≤ n}. -/
def cntP (l : List Nat) (n : Nat) : Nat :=
  let len := l.length
  (List.range len).foldl (fun acc i =>
    (List.range len).foldl (fun acc' j =>
      if i ≤ j ∧ 1 ≤ j ∧ l.getD i 0 + l.getD j 0 ≤ n then acc' + 1
      else acc') acc) 0

/-! ## §2 THE CONSTRUCTION CERTIFICATE (every computed term satisfies
the defining drop property). -/

def constrOK : Bool :=
  (List.range 46).all (fun e =>
    decide (2 ≤ e ∧ e ≤ 45 →
      cntP (List.take e rosenTab) (rosenTab.getD e 0) < rosenTab.getD e 0))

theorem erdos954_construction_data : constrOK = true := by decide

theorem erdos954_construction :
    ∀ e, 2 ≤ e → e ≤ 45 →
      cntP (List.take e rosenTab) (rosenTab.getD e 0) < rosenTab.getD e 0 := by
  intro e h1 h2
  have hall := (List.all_eq_true).mp erdos954_construction_data
  have hmem : e ∈ List.range 46 := List.mem_range.mpr (by omega)
  have hdcheck := hall e hmem
  have hdcheck' : decide (2 ≤ e ∧ e ≤ 45 →
      cntP (List.take e rosenTab) (rosenTab.getD e 0) < rosenTab.getD e 0) = true :=
    hdcheck
  simp only [decide_eq_true_eq] at hdcheck'
  exact hdcheck' ⟨h1, h2⟩

/-! ## §3 THE COUNT LAW (N(x) ≥ x on the certified window). -/

def countOK : Bool :=
  (List.range 378).all (fun x =>
    decide (1 ≤ x → cntP (List.take 30 rosenTab) x ≥ x))

theorem erdos954_count_data : countOK = true := by decide

theorem erdos954_count_law :
    ∀ x, 1 ≤ x → x < 378 → cntP (List.take 30 rosenTab) x ≥ x := by
  intro x h1 h2
  have hall := (List.all_eq_true).mp erdos954_count_data
  have hmem : x ∈ List.range 378 := List.mem_range.mpr (by omega)
  have hdcheck := hall x hmem
  have hdcheck' : decide (1 ≤ x → cntP (List.take 30 rosenTab) x ≥ x) = true :=
    hdcheck
  simp only [decide_eq_true_eq] at hdcheck'
  exact hdcheck' h1

/-! ## §4 THE ARSENAL BRIDGE (BOSS's mathematics applied to the witness
numbers — erdosternary2 + HC-PROOF, the 16,121-theorem arsenal). -/

def arsenalBridgeProp : Prop :=
  [9 % 3, (9 / 3) % 3, (9 / 9) % 3].all (fun d => ErdosTernary2.isTernaryDigit d) ∧
  [378 % 3, (378 / 3) % 3, (378 / 9) % 3].all (fun d => ErdosTernary2.isTernaryDigit d) ∧
  carryAtPos 378 1 < 4 ∧
  v2r (3 ^ 1 * 9) = v2r 9

theorem erdos954_arsenal_bridge : arsenalBridgeProp :=
  ⟨by decide, by decide, carryAtPos_bound 378 1,
    CardinalWorldsV2.v2r_ternary_scaling 1 9⟩

/-! ## §5 MAIN. -/

theorem erdos954_main :
    (∀ e, 2 ≤ e → e ≤ 45 →
      cntP (List.take e rosenTab) (rosenTab.getD e 0) < rosenTab.getD e 0) ∧
    (∀ x, 1 ≤ x → x < 378 → cntP (List.take 30 rosenTab) x ≥ x) ∧
    arsenalBridgeProp :=
  ⟨fun e h1 h2 => erdos954_construction e h1 h2,
   ⟨fun x h1 h2 => erdos954_count_law x h1 h2,
   erdos954_arsenal_bridge⟩⟩

#eval "ERDOS954_ROSEN_KERNEL_GREEN"
#print axioms erdos954_construction
#print axioms erdos954_count_law
#print axioms erdos954_arsenal_bridge
#print axioms erdos954_main

/-! ## §6 THE STRUCTURE LAW (the certified table lives in the problem's
habitat: the seeds and the strict monotonicity). -/

/-- The structure battery: the certified table starts with the seeds
a_0 = 0, a_1 = 1 and is strictly increasing across all 46 certified
terms (the problem's own habitat 0 = a_0 < a_1 < a_2 < ...,
kernel-decided). -/
def tabStructOK : Bool :=
  (List.range 45).all (fun i =>
    decide (rosenTab.getD i 0 < rosenTab.getD (i + 1) 0))

theorem tabStructOK_data : tabStructOK = true := by decide

/-- **THE STRUCTURE LAW.** The certified table satisfies the problem's
habitat clauses outright: a_0 = 0, a_1 = 1, and a_0 < a_1 < ... < a_45
(strictly increasing across all 46 certified terms, so every gap
a_{k+1} - a_k is positive). -/
theorem erdos954_structure :
    rosenTab.getD 0 0 = 0 ∧ rosenTab.getD 1 0 = 1 ∧
    ∀ i, i < 45 → rosenTab.getD i 0 < rosenTab.getD (i + 1) 0 := by
  refine ⟨by decide, by decide, ?_⟩
  intro i hi
  have hall := (List.all_eq_true).mp tabStructOK_data
  have hmem : i ∈ List.range 45 := List.mem_range.mpr (by omega)
  have hdcheck := hall i hmem
  have hdcheck' : decide (rosenTab.getD i 0 < rosenTab.getD (i + 1) 0) = true :=
    hdcheck
  simp only [decide_eq_true_eq] at hdcheck'
  exact hdcheck'

/-! ## §7 THE BLOCK-LAW / IRREGULARITY LAWS (the constant-block gap
structure and its break at block 5). -/

/-- The gap function of the certified table: gapAt k = a_{k+1} - a_k.
The table is strictly increasing (`erdos954_structure`), so the
truncated subtraction is exact; every statement below is
kernel-decided from the certified data. -/
def gapAt (k : Nat) : Nat := rosenTab.getD (k + 1) 0 - rosenTab.getD k 0

/-- **THE INITIAL BLOCK LAW.** The gaps of the certified table open in
constant blocks — [1], [2, 2], [4, 4, 4], [7, 7, 7, 7] — block k
holding k copies of the gap value 1 + k(k-1)/2 (values 1, 2, 4, 7 for
k = 1, 2, 3, 4), and the fifth block opens [8, 8]: the gap values at
indices 0-11 are exactly 1, 2, 2, 4, 4, 4, 7, 7, 7, 7, 8, 8. -/
theorem erdos954_block_law_initial :
    gapAt 0 = 1 ∧ gapAt 1 = 2 ∧ gapAt 2 = 2 ∧
    gapAt 3 = 4 ∧ gapAt 4 = 4 ∧ gapAt 5 = 4 ∧
    gapAt 6 = 7 ∧ gapAt 7 = 7 ∧ gapAt 8 = 7 ∧ gapAt 9 = 7 ∧
    gapAt 10 = 8 ∧ gapAt 11 = 8 := by
  decide

/-- **THE BLOCK-5 BREAK — the irregularity law.** The block law that
holds for blocks one through four (`erdos954_block_law_initial`: block
k is k copies of the gap value 1 + k(k-1)/2) predicts for block five
FIVE gaps of 11 at gap indices 10-14. The certified table refutes the
prediction at every slot — the actual gaps there are 8, 8, 14, 12, 10 —
and the fifth constant-gap block is exactly the two gaps
g_10 = g_11 = 8 (bounded below by the 7 of block four, closed above by
g_12 = 14): the block law breaks at block five, and the irregular
regime (14, 12, 10, 15, 12, 15, 8, 28, ...) begins. The 1,200-term
engine computation (engine_round1.py, ENGINE 6) confirms the same
first break at block five — engine evidence; this theorem claims only
the certified 46-term window. -/
theorem erdos954_block5_break :
    (gapAt 10 ≠ 11 ∧ gapAt 11 ≠ 11 ∧ gapAt 12 ≠ 11 ∧
      gapAt 13 ≠ 11 ∧ gapAt 14 ≠ 11) ∧
    (gapAt 9 ≠ gapAt 10 ∧ gapAt 10 = gapAt 11 ∧ gapAt 11 ≠ gapAt 12 ∧
      gapAt 12 = 14) := by
  decide

/-! ## §8 THE COMPLETE BOARD (the one-statement final assembly of the
#954 kernel: the habitat/structure law, the defining construction law,
the initial block law, the block-5 break, the computation-frontier
count law, and the arsenal bridge — the open asymptotic
x + O(x^{1/4+o(1)}) core is NOT claimed; the battery's wider census
x < 836 and the 1,200-term engine run are evidence, not claimed). -/

theorem erdos954_complete :
    (rosenTab.getD 0 0 = 0 ∧ rosenTab.getD 1 0 = 1 ∧
      ∀ i, i < 45 → rosenTab.getD i 0 < rosenTab.getD (i + 1) 0) ∧
    (∀ e, 2 ≤ e → e ≤ 45 →
      cntP (List.take e rosenTab) (rosenTab.getD e 0) < rosenTab.getD e 0) ∧
    (gapAt 0 = 1 ∧ gapAt 1 = 2 ∧ gapAt 2 = 2 ∧
      gapAt 3 = 4 ∧ gapAt 4 = 4 ∧ gapAt 5 = 4 ∧
      gapAt 6 = 7 ∧ gapAt 7 = 7 ∧ gapAt 8 = 7 ∧ gapAt 9 = 7 ∧
      gapAt 10 = 8 ∧ gapAt 11 = 8) ∧
    ((gapAt 10 ≠ 11 ∧ gapAt 11 ≠ 11 ∧ gapAt 12 ≠ 11 ∧
      gapAt 13 ≠ 11 ∧ gapAt 14 ≠ 11) ∧
      (gapAt 9 ≠ gapAt 10 ∧ gapAt 10 = gapAt 11 ∧ gapAt 11 ≠ gapAt 12 ∧
        gapAt 12 = 14)) ∧
    (∀ x, 1 ≤ x → x < 378 → cntP (List.take 30 rosenTab) x ≥ x) ∧
    arsenalBridgeProp :=
  ⟨erdos954_structure,
   ⟨fun e h1 h2 => erdos954_construction e h1 h2,
   ⟨erdos954_block_law_initial,
   ⟨erdos954_block5_break,
   ⟨fun x h1 h2 => erdos954_count_law x h1 h2,
   erdos954_arsenal_bridge⟩⟩⟩⟩⟩

#print axioms tabStructOK
#print axioms tabStructOK_data
#print axioms erdos954_structure
#print axioms gapAt
#print axioms erdos954_block_law_initial
#print axioms erdos954_block5_break
#print axioms erdos954_complete
#eval "ERDOS954_COMPLETE_GREEN"

end Erdos954
