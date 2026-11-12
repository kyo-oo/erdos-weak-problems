import Arsenal.CardinalWorlds
import FI_Base
import FI_D3a
import FI_D3b
import FI_D3c
import FI_D4a
import FI_D4b
import FI_D4c
import FI_D4d
import FI_D4e
import FI_K10_FINAL
import FI_K11_FINAL

/-! # FI_FINAL — Erdős #1056: THE COMPLETE-PROOF FINAL ASSEMBLY (S050-A5)

**Kill #22, Kernel 18 — the theorem board of `COMPLETE_PROOF.md`, assembled.**
One file importing the whole CI-green FI_* ladder — the `FI_Base` tree-product
oracle (18-B), the k = 10 data `FI_D3a–c`, the k = 11 data `FI_D4a–e`
(18-C/D/E), and the two FINAL assemblies `FI_K10_FINAL`/`FI_K11_FINAL` (18-F) —
stating the COMPLETE UNCONDITIONAL CASE LAW of Erdős #1056:

> **#1056 (verbatim).** Let k ≥ 2. Does there exist a prime p and consecutive
> intervals I_1, …, I_k such that ∏_{n∈I_i} n ≡ 1 (mod p) for all 1 ≤ i ≤ k?

**THE ANSWER ON THE CERTIFIED FRONTIER — the case-frontier law
(`erdos1056_case_frontier`):** for EVERY k with 2 ≤ k ≤ 11 there exist a
prime p and k consecutive nonempty intervals inside [2, p−1] whose block
products are all ≡ 1 (mod p) — quantifier-for-quantifier the problem's own
shape (∀ k, ∃ p, ∃ intervals, ∀ i), one theorem, no sub-cases in the
statement. The case frontier — the largest k with a certified witness —
stands at k = 11.

**THE SMALLEST-WITNESS TABLE** (p_k = the exact smallest prime with
M(p_k) = k + 1; purity and minimality are certified by the dual-method
exhaustive census — C `census1056.c` + independent Python `verify1056.py`,
line-by-line on all 5333 primes ≤ 52163; artifacts banked in this directory):

| k | p_k | v = c₀! mod p_k | cut points c₀ < … < c_k |
|---|---|---|---|
| 2 | 11 | 2 | 2, 4, 7 |
| 3 | 17 | 1 | 1, 5, 11, 15 |
| 4 | 23 | 1 | 1, 4, 8, 11, 21 |
| 5 | 109 | 19 | 9, 11, 39, 58, 73, 85 |
| 6 | 71 | −1 | 7, 9, 19, 51, 61, 63, 70 |
| 7 | 673 | 56 | 159, 316, 354, 393, 397, 506, 545, 647 |
| 8 | 599 | 175 | 28, 50, 122, 183, 250, 289, 500, 539, 555 |
| 9 | 3011 | 1 | 1, 611, 723, 749, 805, 2205, 2261, 2287, 2399, 3009 |
| 10 | 27901 | 20268 | 2451, 2867, 4768, 10383, 18707, 19589, 19965, 22981, 24673, 26322, 27263 |
| 11 | 52163 | 1 | 1, 3924, 7291, 7427, 18519, 24931, 26081, 27231, 33643, 44735, 44871, 52161 |

Blocks are [c_{i−1}+1, c_i] — k consecutive intervals covering [c₀+1, c_k],
every product ≡ 1 (mod p_k), i.e. c₀! ≡ c₁! ≡ … ≡ c_k! ≡ v (mod p_k): the
structure law of COMPLETE_PROOF.md §3.2 (k-system ⟺ chain ⟺ M(p) ≥ k+1).

**THE ASSEMBLY LAW (§4 architecture — zero kernel work at the top).** The
k = 10 / k = 11 theorems chain the 18-F assemblies byte-identically
(`:= erdos1056_k10`, `:= erdos1056_k11`: every block product was decided once
in the FI_D olean ladder); the frontier theorem delegates every block to
those certificates by kernel defeq on the cut literals — no block product is
ever re-ground here. The k = 2..9 theorems re-decide the witness conjunctions
(the exact statements the 18-A modules `FI_K2_K8`/`FI_K9` proved green; those
standalone modules cannot be imported alongside `FI_Base` — each carries its
own copy of the oracle defs — so this file re-decides them under `FI_Base`'s
byte-identical oracle: p ≤ 3011, ≈4.2k block terms total, well under the
~15k-term-per-process CI budget).

**THE BOARD (COMPLETE_PROOF.md §2), Lean status honestly labeled.** T1
structure law: doc §3.2 (pure proof; the Lean route is §4.5 — not compiled,
the kernel decides instances directly). T2 Wilson force-pair: doc §3.3
(the anchors are kernel-decided in `FI_Anchors`/`FI_K9`). T3 gap law: doc
§3.4. **T4 case theorems k = 2..11 (constructions): THIS FILE**; purity
M(p_k) = k+1 and minimality: the census layer. T5 frontier bar below
200,000: census-certified (§4.8 — the honest boundary of the kernel-decide
architecture). T6 decidability: doc §3.7. Arbitrarily large k (the problem's
open core) is untouched.

**RECEIPTS.** `#print axioms` gates at the bottom. Expected: the decide
theorems (`erdos1056_final_k2..k9`) depend on no axioms; the chained
assemblies and the frontier law (`erdos1056_final_k10/k11`,
`erdos1056_case_frontier`) on `[propext, Classical.choice, Quot.sound]`
only. CI: the "Kernel 18-G" step — compile `FI_K10_FINAL`/`FI_K11_FINAL`
to oleans, then `lake env lean FI_FINAL.lean` (the 18-F/Kernel-20 olean
ladder pattern). -/

set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

/-! ## The cut-point data (the witness table above).
`fiCutsK i` = the i-th cut point c_i of the k = K witness; the intervals are
I_i = [c_{i−1}+1, c_i] ⊆ [2, p_k − 1]. Every table is strictly increasing
with c₀ ≥ 1 and c_k ≤ p_k − 1 — exactly the decide obligations discharged in
`erdos1056_case_frontier` below. -/

/-- k = 2: cuts (2, 4, 7) on p = 11. -/
def fiCuts2 : Nat → Nat
  | 0 => 2
  | 1 => 4
  | _ => 7

/-- k = 3: cuts (1, 5, 11, 15) on p = 17. -/
def fiCuts3 : Nat → Nat
  | 0 => 1
  | 1 => 5
  | 2 => 11
  | _ => 15

/-- k = 4: cuts (1, 4, 8, 11, 21) on p = 23. -/
def fiCuts4 : Nat → Nat
  | 0 => 1
  | 1 => 4
  | 2 => 8
  | 3 => 11
  | _ => 21

/-- k = 5: cuts (9, 11, 39, 58, 73, 85) on p = 109. -/
def fiCuts5 : Nat → Nat
  | 0 => 9
  | 1 => 11
  | 2 => 39
  | 3 => 58
  | 4 => 73
  | _ => 85

/-- k = 6: cuts (7, 9, 19, 51, 61, 63, 70) on p = 71. -/
def fiCuts6 : Nat → Nat
  | 0 => 7
  | 1 => 9
  | 2 => 19
  | 3 => 51
  | 4 => 61
  | 5 => 63
  | _ => 70

/-- k = 7: cuts (159, 316, 354, 393, 397, 506, 545, 647) on p = 673. -/
def fiCuts7 : Nat → Nat
  | 0 => 159
  | 1 => 316
  | 2 => 354
  | 3 => 393
  | 4 => 397
  | 5 => 506
  | 6 => 545
  | _ => 647

/-- k = 8: cuts (28, 50, 122, 183, 250, 289, 500, 539, 555) on p = 599. -/
def fiCuts8 : Nat → Nat
  | 0 => 28
  | 1 => 50
  | 2 => 122
  | 3 => 183
  | 4 => 250
  | 5 => 289
  | 6 => 500
  | 7 => 539
  | _ => 555

/-- k = 9: cuts (1, 611, 723, 749, 805, 2205, 2261, 2287, 2399, 3009) on p = 3011. -/
def fiCuts9 : Nat → Nat
  | 0 => 1
  | 1 => 611
  | 2 => 723
  | 3 => 749
  | 4 => 805
  | 5 => 2205
  | 6 => 2261
  | 7 => 2287
  | 8 => 2399
  | _ => 3009

/-- k = 10: cuts (2451, 2867, 4768, 10383, 18707, 19589, 19965, 22981,
24673, 26322, 27263) on p = 27901. -/
def fiCuts10 : Nat → Nat
  | 0 => 2451
  | 1 => 2867
  | 2 => 4768
  | 3 => 10383
  | 4 => 18707
  | 5 => 19589
  | 6 => 19965
  | 7 => 22981
  | 8 => 24673
  | 9 => 26322
  | _ => 27263

/-- k = 11: cuts (1, 3924, 7291, 7427, 18519, 24931, 26081, 27231, 33643,
44735, 44871, 52161) on p = 52163 — THE FRONTIER WITNESS. -/
def fiCuts11 : Nat → Nat
  | 0 => 1
  | 1 => 3924
  | 2 => 7291
  | 3 => 7427
  | 4 => 18519
  | 5 => 24931
  | 6 => 26081
  | 7 => 27231
  | 8 => 33643
  | 9 => 44735
  | 10 => 44871
  | _ => 52161

/-! ## The case theorems k = 2..11 — the witness certifications (the
witness-certification form fed by the FI_D-layers: `Nat.Prime p_k` plus every
block product `prodmod p_k (c_{i−1}+1) c_i = 1`). The blocks match
`fiCutsK` above. Minimality of each p_k — no smaller prime has M = k + 1 —
is the census layer (`census1056.txt`, dual-method, COMPLETE_PROOF.md §5);
each theorem below is the unconditional construction certificate at the
smallest witness. -/

/-- **k = 2** — the smallest witness p₂ = **11** (Erdős 1979):
blocks [3, 4], [5, 7]; chain value 2 = 2! at cuts (2, 4, 7). -/
theorem erdos1056_final_k2 : Nat.Prime 11 ∧
    prodmod 11 3 4 = 1 ∧ prodmod 11 5 7 = 1 := by decide

/-- **k = 3** — the smallest witness p₃ = **17** (Makowski 1983):
blocks [2, 5], [6, 11], [12, 15]; chain value 1 at cuts (1, 5, 11, 15). -/
theorem erdos1056_final_k3 : Nat.Prime 17 ∧
    prodmod 17 2 5 = 1 ∧ prodmod 17 6 11 = 1 ∧ prodmod 17 12 15 = 1 := by
  decide

/-- **k = 4** — the smallest witness p₄ = **23** (NEW, this campaign):
blocks [2, 4], [5, 8], [9, 11], [12, 21]; chain value 1 at cuts
(1, 4, 8, 11, 21); M(23) = 5. -/
theorem erdos1056_final_k4 : Nat.Prime 23 ∧
    prodmod 23 2 4 = 1 ∧ prodmod 23 5 8 = 1 ∧ prodmod 23 9 11 = 1 ∧
    prodmod 23 12 21 = 1 := by decide

/-- **k = 5** — the smallest witness p₅ = **109** (NEW, this campaign):
blocks [10, 11], [12, 39], [40, 58], [59, 73], [74, 85]; chain value 19
at cuts (9, 11, 39, 58, 73, 85); M(109) = 6. -/
theorem erdos1056_final_k5 : Nat.Prime 109 ∧
    prodmod 109 10 11 = 1 ∧ prodmod 109 12 39 = 1 ∧ prodmod 109 40 58 = 1 ∧
    prodmod 109 59 73 = 1 ∧ prodmod 109 74 85 = 1 := by decide

/-- **k = 6** — the smallest witness p₆ = **71** (NEW, this campaign):
blocks [8, 9], [10, 19], [20, 51], [52, 61], [62, 63], [64, 70]; chain
value −1 at cuts (7, 9, 19, 51, 61, 63, 70); M(71) = 7. -/
theorem erdos1056_final_k6 : Nat.Prime 71 ∧
    prodmod 71 8 9 = 1 ∧ prodmod 71 10 19 = 1 ∧ prodmod 71 20 51 = 1 ∧
    prodmod 71 52 61 = 1 ∧ prodmod 71 62 63 = 1 ∧ prodmod 71 64 70 = 1 := by
  decide

/-- **k = 7** — the smallest witness p₇ = **673** (NEW, this campaign):
blocks [160, 316], [317, 354], [355, 393], [394, 397], [398, 506],
[507, 545], [546, 647]; chain value 56; M(673) = 8. -/
theorem erdos1056_final_k7 : Nat.Prime 673 ∧
    prodmod 673 160 316 = 1 ∧ prodmod 673 317 354 = 1 ∧
    prodmod 673 355 393 = 1 ∧ prodmod 673 394 397 = 1 ∧
    prodmod 673 398 506 = 1 ∧ prodmod 673 507 545 = 1 ∧
    prodmod 673 546 647 = 1 := by decide

/-- **k = 8** — the smallest witness p₈ = **599** (NEW, this campaign):
blocks [29, 50], [51, 122], [123, 183], [184, 250], [251, 289], [290, 500],
[501, 539], [540, 555]; chain value 175; M(599) = 9. -/
theorem erdos1056_final_k8 : Nat.Prime 599 ∧
    prodmod 599 29 50 = 1 ∧ prodmod 599 51 122 = 1 ∧ prodmod 599 123 183 = 1 ∧
    prodmod 599 184 250 = 1 ∧ prodmod 599 251 289 = 1 ∧ prodmod 599 290 500 = 1 ∧
    prodmod 599 501 539 = 1 ∧ prodmod 599 540 555 = 1 := by decide

/-- **k = 9** — the smallest witness p₉ = **3011** (NEW, this campaign):
blocks [2, 611], [612, 723], [724, 749], [750, 805], [806, 2205],
[2206, 2261], [2262, 2287], [2288, 2399], [2400, 3009]; chain value 1;
M(3011) = 10. -/
theorem erdos1056_final_k9 : Nat.Prime 3011 ∧
    prodmod 3011 2 611 = 1 ∧ prodmod 3011 612 723 = 1 ∧
    prodmod 3011 724 749 = 1 ∧ prodmod 3011 750 805 = 1 ∧
    prodmod 3011 806 2205 = 1 ∧ prodmod 3011 2206 2261 = 1 ∧
    prodmod 3011 2262 2287 = 1 ∧ prodmod 3011 2288 2399 = 1 ∧
    prodmod 3011 2400 3009 = 1 := by decide

/-- **k = 10** — the smallest witness p₁₀ = **27901** (NEW, this campaign):
blocks [2452, 2867], [2868, 4768], [4769, 10383], [10384, 18707],
[18708, 19589], [19590, 19965], [19966, 22981], [22982, 24673],
[24674, 26322], [26323, 27263]; chain value 20268; M(27901) = 11.
CHAINED from the 18-F assembly `erdos1056_k10` — zero kernel work (the
block products were decided in `FI_D3a–c`). -/
theorem erdos1056_final_k10 : Nat.Prime 27901 ∧
    prodmod 27901 2452 2867 = 1 ∧ prodmod 27901 2868 4768 = 1 ∧
    prodmod 27901 4769 10383 = 1 ∧ prodmod 27901 10384 18707 = 1 ∧
    prodmod 27901 18708 19589 = 1 ∧ prodmod 27901 19590 19965 = 1 ∧
    prodmod 27901 19966 22981 = 1 ∧ prodmod 27901 22982 24673 = 1 ∧
    prodmod 27901 24674 26322 = 1 ∧ prodmod 27901 26323 27263 = 1 :=
  erdos1056_k10

/-- **k = 11** — the smallest witness p₁₁ = **52163** (NEW, this campaign)
— THE FRONTIER: blocks [2, 3924], [3925, 7291], [7292, 7427],
[7428, 18519], [18520, 24931], [24932, 26081], [26082, 27231],
[27232, 33643], [33644, 44735], [44736, 44871], [44872, 52161]; chain
value 1; M(52163) = 12. CHAINED from the 18-F assembly `erdos1056_k11` —
zero kernel work (the block products were decided in `FI_D4a–e`). -/
theorem erdos1056_final_k11 : Nat.Prime 52163 ∧
    prodmod 52163 2 3924 = 1 ∧ prodmod 52163 3925 7291 = 1 ∧
    prodmod 52163 7292 7427 = 1 ∧ prodmod 52163 7428 18519 = 1 ∧
    prodmod 52163 18520 24931 = 1 ∧ prodmod 52163 24932 26081 = 1 ∧
    prodmod 52163 26082 27231 = 1 ∧ prodmod 52163 27232 33643 = 1 ∧
    prodmod 52163 33644 44735 = 1 ∧ prodmod 52163 44736 44871 = 1 ∧
    prodmod 52163 44872 52161 = 1 :=
  erdos1056_k11

/-! ## THE CASE-FRONTIER LAW — the assembled final theorem (COMPLETE_PROOF.md
§1 + §5: the problem's quantifier structure answered on the whole certified
frontier). A k-system on p (the doc's §3.0 definition, standard reading):
cut points c give k consecutive nonempty intervals I_i = [c(i−1)+1, c i]
with a₁ = c 0 + 1 ≥ 2 (so c 0 ≥ 1), b_k = c k ≤ p − 1, I_{i+1} starting at
b_i + 1 automatically, and every block product ≡ 1 (mod p). The witness
data per k is the smallest-witness table above; every block product is
delegated to the per-k certification theorems by kernel defeq on the cut
literals (zero product grind). Scope honesty: this is the construction case
law — purity/minimality of the p_k and the k = 12 bar below 200,000 are the
census layer (COMPLETE_PROOF.md §4.7–4.8, §5); k ≥ 12 is the open core. -/
theorem erdos1056_case_frontier :
    ∀ k : Nat, 2 ≤ k → k ≤ 11 →
      ∃ p : Nat, Nat.Prime p ∧
        ∃ c : Nat → Nat, 1 ≤ c 0 ∧ c k ≤ p - 1 ∧
          (∀ i : Nat, 0 < i → i ≤ k → c (i - 1) < c i) ∧
          (∀ i : Nat, 0 < i → i ≤ k → prodmod p (c (i - 1) + 1) (c i) = 1) := by
  intro k h2 h11
  rcases (by omega : k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · -- k = 2: p₂ = 11, cuts (2, 4, 7), blocks [3, 4], [5, 7].
    obtain ⟨hp, b1, b2⟩ := erdos1056_final_k2
    refine ⟨11, hp, fiCuts2, by decide, by decide, ?_, ?_⟩
    · intro i hi0 hiK
      rcases (by omega : i = 1 ∨ i = 2) with rfl | rfl
      all_goals decide
    · intro i hi0 hiK
      rcases (by omega : i = 1 ∨ i = 2) with rfl | rfl
      · exact b1
      · exact b2
  · -- k = 3: p₃ = 17, cuts (1, 5, 11, 15).
    obtain ⟨hp, b1, b2, b3⟩ := erdos1056_final_k3
    refine ⟨17, hp, fiCuts3, by decide, by decide, ?_, ?_⟩
    · intro i hi0 hiK
      rcases (by omega : i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl
      all_goals decide
    · intro i hi0 hiK
      rcases (by omega : i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl
      · exact b1
      · exact b2
      · exact b3
  · -- k = 4: p₄ = 23, cuts (1, 4, 8, 11, 21).
    obtain ⟨hp, b1, b2, b3, b4⟩ := erdos1056_final_k4
    refine ⟨23, hp, fiCuts4, by decide, by decide, ?_, ?_⟩
    · intro i hi0 hiK
      rcases (by omega : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl
      all_goals decide
    · intro i hi0 hiK
      rcases (by omega : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl
      · exact b1
      · exact b2
      · exact b3
      · exact b4
  · -- k = 5: p₅ = 109, cuts (9, 11, 39, 58, 73, 85).
    obtain ⟨hp, b1, b2, b3, b4, b5⟩ := erdos1056_final_k5
    refine ⟨109, hp, fiCuts5, by decide, by decide, ?_, ?_⟩
    · intro i hi0 hiK
      rcases (by omega : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with rfl | rfl | rfl | rfl | rfl
      all_goals decide
    · intro i hi0 hiK
      rcases (by omega : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with rfl | rfl | rfl | rfl | rfl
      · exact b1
      · exact b2
      · exact b3
      · exact b4
      · exact b5
  · -- k = 6: p₆ = 71, cuts (7, 9, 19, 51, 61, 63, 70).
    obtain ⟨hp, b1, b2, b3, b4, b5, b6⟩ := erdos1056_final_k6
    refine ⟨71, hp, fiCuts6, by decide, by decide, ?_, ?_⟩
    · intro i hi0 hiK
      rcases (by omega : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals decide
    · intro i hi0 hiK
      rcases (by omega : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with rfl | rfl | rfl | rfl | rfl | rfl
      · exact b1
      · exact b2
      · exact b3
      · exact b4
      · exact b5
      · exact b6
  · -- k = 7: p₇ = 673, cuts (159, 316, 354, 393, 397, 506, 545, 647).
    obtain ⟨hp, b1, b2, b3, b4, b5, b6, b7⟩ := erdos1056_final_k7
    refine ⟨673, hp, fiCuts7, by decide, by decide, ?_, ?_⟩
    · intro i hi0 hiK
      rcases (by omega : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals decide
    · intro i hi0 hiK
      rcases (by omega : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact b1
      · exact b2
      · exact b3
      · exact b4
      · exact b5
      · exact b6
      · exact b7
  · -- k = 8: p₈ = 599, cuts (28, 50, 122, 183, 250, 289, 500, 539, 555).
    obtain ⟨hp, b1, b2, b3, b4, b5, b6, b7, b8⟩ := erdos1056_final_k8
    refine ⟨599, hp, fiCuts8, by decide, by decide, ?_, ?_⟩
    · intro i hi0 hiK
      rcases (by omega : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals decide
    · intro i hi0 hiK
      rcases (by omega : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact b1
      · exact b2
      · exact b3
      · exact b4
      · exact b5
      · exact b6
      · exact b7
      · exact b8
  · -- k = 9: p₉ = 3011, cuts (1, 611, 723, 749, 805, 2205, 2261, 2287, 2399, 3009).
    obtain ⟨hp, b1, b2, b3, b4, b5, b6, b7, b8, b9⟩ := erdos1056_final_k9
    refine ⟨3011, hp, fiCuts9, by decide, by decide, ?_, ?_⟩
    · intro i hi0 hiK
      rcases (by omega : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals decide
    · intro i hi0 hiK
      rcases (by omega : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact b1
      · exact b2
      · exact b3
      · exact b4
      · exact b5
      · exact b6
      · exact b7
      · exact b8
      · exact b9
  · -- k = 10: p₁₀ = 27901, cuts (2451, 2867, 4768, 10383, 18707, 19589,
    -- 19965, 22981, 24673, 26322, 27263) — the 18-F assembly, zero kernel work.
    obtain ⟨hp, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := erdos1056_final_k10
    refine ⟨27901, hp, fiCuts10, by decide, by decide, ?_, ?_⟩
    · intro i hi0 hiK
      rcases (by omega : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals decide
    · intro i hi0 hiK
      rcases (by omega : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact b1
      · exact b2
      · exact b3
      · exact b4
      · exact b5
      · exact b6
      · exact b7
      · exact b8
      · exact b9
      · exact b10
  · -- k = 11: p₁₁ = 52163, cuts (1, 3924, 7291, 7427, 18519, 24931, 26081,
    -- 27231, 33643, 44735, 44871, 52161) — THE FRONTIER, the 18-F assembly.
    obtain ⟨hp, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11⟩ := erdos1056_final_k11
    refine ⟨52163, hp, fiCuts11, by decide, by decide, ?_, ?_⟩
    · intro i hi0 hiK
      rcases (by omega : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals decide
    · intro i hi0 hiK
      rcases (by omega : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact b1
      · exact b2
      · exact b3
      · exact b4
      · exact b5
      · exact b6
      · exact b7
      · exact b8
      · exact b9
      · exact b10
      · exact b11

#eval "FI_FINAL_GREEN"
#print axioms erdos1056_final_k2
#print axioms erdos1056_final_k3
#print axioms erdos1056_final_k4
#print axioms erdos1056_final_k5
#print axioms erdos1056_final_k6
#print axioms erdos1056_final_k7
#print axioms erdos1056_final_k8
#print axioms erdos1056_final_k9
#print axioms erdos1056_final_k10
#print axioms erdos1056_final_k11
#print axioms erdos1056_case_frontier
