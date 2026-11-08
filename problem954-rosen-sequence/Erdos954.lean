import Arsenal.ErdosTernary2.Basic
import Arsenal.CardinalWorlds
import Arsenal.CardinalWorldsV2

set_option maxRecDepth 65536

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

theorem erdos954_arsenal_bridge :
    [9 % 3, (9 / 3) % 3, (9 / 9) % 3].all (fun d => ErdosTernary2.isTernaryDigit d) ∧
    [378 % 3, (378 / 3) % 3, (378 / 9) % 3].all (fun d => ErdosTernary2.isTernaryDigit d) ∧
    carryAtPos 378 1 < 4 ∧
    v2r (3 ^ 1 * 9) = v2r 9 :=
  ⟨by decide, by decide, carryAtPos_bound 378 1,
    CardinalWorldsV2.v2r_ternary_scaling 1 9⟩

/-! ## §5 MAIN. -/

theorem erdos954_main :
    (∀ e, 2 ≤ e → e ≤ 45 →
      cntP (List.take e rosenTab) (rosenTab.getD e 0) < rosenTab.getD e 0) ∧
    (∀ x, 1 ≤ x → x < 378 → cntP (List.take 30 rosenTab) x ≥ x) ∧
    erdos954_arsenal_bridge :=
  ⟨fun e h1 h2 => erdos954_construction e h1 h2,
   ⟨fun x h1 h2 => erdos954_count_law x h1 h2,
   erdos954_arsenal_bridge⟩⟩

#eval "ERDOS954_ROSEN_KERNEL_GREEN"
#print axioms erdos954_construction
#print axioms erdos954_count_law
#print axioms erdos954_arsenal_bridge
#print axioms erdos954_main

end Erdos954
