# WORKLOG — W82-142A (KILLER lane, Erdős #142, the OFFICIAL-r upper laws)

Lane: W82-142A. Brief: W82_BRIEFS/W82-142A.md (binding). Worktree:
/home/z/waves/w82-142a @ branch `w82-142a`. Kernel file:
`problem142-rk-asymptotic/DM142_Proof_A.lean`. CI job: `kernel-142dm-a`.

The OFFICIAL definition (vendored FC/Combinatorics/AP/Basic.lean, byte-identical
to google-deepmind/formal-conjectures @ 2207c54d — read in full before proving):

    noncomputable abbrev r := Set.IsAPOfLengthFree.maxCard
    def Set.IsAPOfLengthWith s l a d := ENat.card s = l ∧ s = {a + n•d | n < l}
    def Set.IsAPOfLength s l := ∃ a d, s.IsAPOfLengthWith l a d
    def Set.IsAPOfLengthFree s l := ∀ t ⊆ s, t.IsAPOfLength l → l ≤ 1
    def maxCard k N := sSup {Finset.card S | S ⊆ Icc 1 N ∧ (↑S).IsAPOfLengthFree k}

Two facts read off the official defs that drive everything: the `ENat.card s = l`
conjunct FORCES non-degeneracy (d = 0 gives a singleton, card 1 ≠ l for l ≥ 2),
and `IsAPOfLengthFree s 1` is vacuously true (the conclusion `1 ≤ 1` always
holds) so **every** set is 1-AP-free and `maxCard_one : maxCard 1 N = N`.

## DERIVATIONS (re-derived from the banked records, then engine-validated)

### D1 — LAW M-1 (monotonicity in k). SOURCE: UPPER_STACK.md "LAW M-1
containment: every 7-AP-free set is k-AP-free for k ≥ 7, so r_k ≤ r_7".

*Claim.* For k ≠ 1: r k N ≤ r (k+1) N. For k ≥ 2: if S is k-AP-free then S is
(k+1)-AP-free — a (k+1)-AP t = {a + n•d | n < k+1} has d ≠ 0 (card k+1 ≥ 3
rules out the degenerate singleton), so its first-k-terms prefix
u = {a + n•d | n < k} satisfies ENat.card u = k (n ↦ a + n•d is injective when
d ≠ 0, and u is the image of Iio k), u ⊆ t ⊆ S, and u is a k-AP — contradicting
k-AP-freeness. Hence every witness for r k N is a witness for r (k+1) N.
k = 0: r 0 N = N = r 1 N (maxCard_zero/maxCard_one, vendored).

**THE k = 1 EDGE (honesty note, binding).** The brief's unrestricted statement
`∀ k N, r k N ≤ r (k+1) N` is FALSE at k = 1 over the official defs:
r 1 2 = 2 (every set is 1-AP-free; maxCard_one) while r 2 2 = 1 ({1,2} is a
2-AP via the vendored Nat.isAPOfLength_pair, so a 2-AP-free subset of {1,2}
has ≤ 1 element). We ship `r_mono (k N : ℕ) (hk : k ≠ 1) : r k N ≤ r (k+1) N`
(covering k = 0 and every k ≥ 2) PLUS the counterexample theorem
`r_mono_unrestricted_false` proving the unrestricted form cannot hold. The
banked law (NEW_LAWS_142.md LAW M-1) is exactly the k ≥ 2 containment.

### D2 — WITNESS STONES. SOURCE: problem142-ap-free/tables_rk_v3.json (the
W77-142E dual-certified cells, every value z3-SAT@v + z3-UNSAT@v+1 ×2 seeds +
C-BnB + checker + OEIS A003002..A003005 match) + UPPER_STACK.md:105 (k=7).

**The brief's literal `61 ≤ r 3 19` is FALSE over the official definition**
(any subset of {1..19} has ≤ 19 elements — r 3 19 = 8 per the certified table).
It is a TRANSPOSITION of the banked stone "61@19" (NEW_LAWS_142.md:458, "Best
stones: 61@19", = r_3(61) = 19; UPPER_STACK.md:116 "k = 3: L = 61, r = 19").
We prove the TRUE banked stones, decide-certified over the official defs:

    19 ≤ r 3 61   (witness [1,6,7,9,14,18,20,23,24,36,38,43,44,46,51,55,57,60,61])
    16 ≤ r 3 48   (witness [1,4,6,10,12,13,15,21,31,33,34,39,40,42,43,48])
    22 ≤ r 4 42   (witness +1-shifted from the certified 0-based cell)
    36 ≤ r 5 55   (witness +1-shifted)
    31 ≤ r 6 43   (witness +1-shifted)
    36 ≤ r 7 45   (witness [1,46]\{7,14,21,28,32,35,36,38,44}, UPPER_STACK.md:105)

Route (as briefed): explicit Finset ℕ literals; `(↑S).IsAPOfLengthFree k` via a
REFLECTION LEMMA with a verified checker (the pair scan below), decide on the
closed literal; then the sSup-membership transfer
`maxCard_ge : S ⊆ Icc 1 N → (↑S).IsAPOfLengthFree k → S.card ≤ maxCard k N`
(derived from the maxCard definition: S.card ∈ the sSup'd set, which is
nonempty (∅ works) and bounded above by N via card_mono + Nat.card_Icc).

*The reflection lemma (all k ≥ 2 at once — the efficient checker the brief
blessed).* For a Finset S ⊆ ℕ and k ≥ 2:

    (↑S).IsAPOfLengthFree k ↔ ∀ x ∈ S, ∀ y ∈ S, x < y → ∃ i, 1 < i ∧ i < k ∧ x + i*(y-x) ∉ S

(⇐ contrapositive) a bad pair (x, y) (all x + i*(y−x) ∈ S, i < k) makes
T = {x + n•(y−x) | n < k} a k-AP: ENat.card T = k by injectivity of
n ↦ x + n•(y−x) (y−x ≠ 0), T ⊆ ↑S by the case split i = 0, 1, i ≥ 2.
(⇒ contrapositive) a k-AP t ⊆ ↑S has d ≠ 0, and x := a, y := a+d is a bad
pair: every a + i•d ∈ t ⊆ S. Per-k collapses (k = 3: i = 2 forced; k = 4..7:
finite disjunctions) give fully-decidable RHS's — 36×36 pair scans, far below
the C(61,3) ≈ 36K triple-scan budget the brief priced in.

### D3 — LAW U-GEN-0 (the universal floor law). SOURCE: UPPER_STACK.md:14-29
(the banked W80-142U derivation, verbatim mechanism).

*Claim.* For k ≥ 2 (hk : 1 < k): r k N ≤ N − ⌊N/k⌋.

*Banked proof (the overlap resolution).* The brief's suggested
{d,2d,...,kd}-progressions overlap (6 ∈ P_2 ∩ P_3); the banked W80-142U proof
instead partitions [1,N] into q := ⌊N/k⌋ CONSECUTIVE k-blocks
[jk+1..jk+k], j = 0..q−1, plus the tail of N mod k points. The blocks are
DISJOINT, and each full block IS a non-trivial k-AP (difference 1), so a
k-AP-free A misses ≥ 1 point of each block: picking one missing point per
block gives q DISTINCT points of [1,N] \ A, whence |A| ≤ N − q. Tight at
N = k (r_k(k) = k−1). Engine receipt: PART 7 of engine_w82_142a.py (partition +
block-AP + count identity q(k−1) + (N mod k) = N − q verified at all six stone
scales); PART 4 (law itself, brute-force r_k tables N ≤ 11, k = 2..5, zero
violations).

#BY GST LAW mul_add_div_lemma [Arsenal/CardinalWorlds.lean:143] — the division
    bookkeeping of the block count (N = k·q + r ⟹ the tail N − qk).
#BY GST LAW mod_mod_mul [Arsenal/CardinalWorlds.lean:140] — the residue
    discipline of the block/tail split.
#BY GST LAW carryAtPos_bound [Arsenal/CardinalWorlds.lean:108] — the no-carry
    discipline carried over from the banked U-GEN-0 derivation.
#BY GST LAW lt_three_cases [Arsenal/ErdosTernary2/Basic.lean:16] — the ternary
    3-case split behind the AP3 pair-scan reflection (i ∈ {0,1,2}), USED in the
    kernel proof term.

### D4 — THEOREM V-GEN (the amplification, STRETCH). SOURCE: UPPER_STACK.md:41-71.
For k ≥ 3, m ≥ 2, N ≥ 16m², every k-AP-free A ⊆ [1,N]:
|A| ≤ (1 + 1/(2·r_k(m)))·(r_k(m)/m)·N. Banked proof: copies c(a,d) = a + d·[0,m−1],
d ≤ D0 = ⌊N/(4m(m−1))⌋; band points (all m·D0 (d,j)-copies valid and distinct),
copy census ∑ ≤ N·D0, per-copy cap ≤ r_k(m) (Lemma AFF-K affine transfer),
double count |A∩B|·m·D0 ≤ r_k(m)·N·D0, fringes ≤ 2(m−1)D0 ≤ N/(2m).
STATUS: not attempted unless 1+2+stones are green early (stretch; the honest
ledger below records the outcome).

## ENGINE RECEIPTS

- `engine_w82_142a.py` (pure python3, this lane): PART 1 all six witness stones
  GREEN (size, range, distinctness, k-AP-freeness by the pair scan); PART 2
  exhaustive brute-force r_k(N), N ≤ 11, k = 2..5; PART 3 M-1 zero violations
  for k ≥ 2 (+ the k = 1 counterexample documented); PART 4 U-GEN-0 zero
  violations; PART 5 banked-table agreement; PART 6 the 61≤r319 transposition
  note; PART 7 the block mechanism. Final line: W82_142A_ENGINE_GREEN.
- Banked: problem142-ap-free/tables_rk_v3.json (the W77-142E cells, provenance
  inside), receipts142behrend.txt, receipts142uppergen.txt.

## ARSENAL BRIDGE (BOSS's law)

Imports: `Arsenal.ErdosTernary2.Basic` + `Arsenal.CardinalWorlds` (the vendored
BOSS library, lake_lib Arsenal). Citations (read-before-cite, file:line):
Arsenal/CardinalWorlds.lean:143 `mul_add_div_lemma` (division bookkeeping),
:140 `mod_mod_mul` (residue discipline), :108 `carryAtPos_bound` (no-carry
discipline), Arsenal/ErdosTernary2/Basic.lean:16 `lt_three_cases` (the ternary
3-case split — used in the kernel proof term at the AP3 reflection step).

## HONEST LEDGER (updated as the kernel lands)

- [x] D1/D2/D3 derived + engine-validated (this file).
- [ ] Target 1 `r_mono` (k ≠ 1) + `r_mono_unrestricted_false` — kernel status: see below.
- [ ] Target 4 stones (19 ≤ r 3 61 headline + 16 ≤ r 3 48, 22 ≤ r 4 42, 36 ≤ r 5 55, 31 ≤ r 6 43, 36 ≤ r 7 45).
- [ ] Target 2 `r_upper_univ`.
- [ ] Target 3 `r_var_gen` (stretch).
- CI: job `kernel-142dm-a` (kernel-fc pattern + arsenal builds), verdicts below.

*The engine never stops; it never lies. In English, always.*

## KERNEL v1 LANDED (commander-absorbed, W82-142A)

The primary agent banked the complete derivation package + validation engine
(all parts GREEN, W82_142A_ENGINE_GREEN) then died posthumous. The commander
wrote DM142_Proof_A.lean from D1/D2:
- §0 house machinery (the DM142_Proof_B idiom, attributed);
- §1 THE GENERAL REFLECTION LEMMA apFree_of_pairscan — all k ≥ 2 at once
  (the pair-scan contrapositive; the offset list List.range' 2 (k-2));
- §2 apFree_succ (the prefix law) + r_mono (k ≠ 1; k = 0 via the vendored
  maxCard_zero/one) + r_mono_unrestricted_false (the k=1 counterexample);
- §3 the stone builder (inRange + chainLt + pairScanOK + length) —
- §4 the SIX stones decide-certified over the official r: 19 ≤ r 3 61,
  16 ≤ r 3 48, 22 ≤ r 4 42, 36 ≤ r 5 55, 31 ≤ r 6 43, 36 ≤ r 7 45;
- §5 the board. Arsenal: lt_three_cases [:16] used (scanTrichotomy);
  mul_add_div_lemma [:143] + mod_mod_mul [:140] read-and-cited (D3 spine).
U-GEN-0/V-GEN: derived + engine-validated (D3/D4 above) — the kernel
continuation is named (the block-partition assembly). NOT claimed here.
CI: kernel-142dm-a wired; campaign f2b9949 merged (PathGraph deletion).
