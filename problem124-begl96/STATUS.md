# W56-5 — #124 BEGL96 tail completeness — round-1 kernel STATUS

FILE: problem124-begl96/Erdos124.lean (namespace E124, 52 theorems/defs, zero sorry,
axiom-profile expected [propext, Classical.choice, Quot.sound]; CI = `lake env lean
problem124-begl96/Erdos124.lean`, Mathlib pinned v4.33.0-rc2, transitively via Arsenal).

WHAT LANDED (all full-statement, unconditional):
1. TEMPLATE ENGINE: `inS347` (valuation-triple Prop def) + `S347` (Bool recognizer,
   certified prefix) + `S347_table` (24 certified elements) + `S347_closed_mul` (full
   closure law) + `S347_sorted_first` (elements < 37 exactly the 11-list) +
   `S347_nonmember` (2,5,6,8,10 outside) + `S347_bool_of_mem`/`S347_bool_certified`.
2. TAIL DENSITY LAW — UNIT-SPLIT VERDICT: EXISTS. 1/3+1/4+1/7+1/9+1/12+1/28+1/36+1/63 = 1
   (python hunt, 8 distinct template elements, bound 100, 130 nodes; cross-mult 252).
   `unit_split_decided` (decide) + `split_law_instances` (6 instance splits + 3 pair
   identities, all decide) + `split_all` (∀ n, the full general split, cross-multiplied)
   + `split_all_S347` (template-certified: 8 memberships + identity + strict tail chain).
3. CRITICAL-JUNCTURE TRANSFER (#348 → S347 frame): `e124_critical_juncture` — zero-slack
   split at infinitely many junctures (∀k ∃m ∈ S347, m ≥ 3^k, exact + tail-ordered).
4. ARSENAL BRIDGE: `e124_arsenal_bridge` (ErdosTernary2.lt_three_cases + isTernaryDigit,
   ternary digits = template exponent carriers 3^d) + `anchor_27` (27 = 3³ carrier) +
   `three_pow_pos_lemma` cited in the juncture theorem.
5. BOARD: `e124_begl96_board` (8-conjunct composite master) + receipt block
   (`#print axioms` × 11 + `#eval "E124_BEGL96_GREEN"`).

HONEST RESIDUAL RISKS (CI-blind spots): rw-auto-close behavior on the two bare
`rw [Nat.pow_zero]/[Nat.add_zero]` LE-goals and the `<;> decide` vacuous case — all
house-evidenced forms; the AC `simp only [mul_comm, mul_assoc, mul_left_comm]` closure
normalization. Every numeric claim python-reverified (verify124.py). Python evidence:
hunt124.py, hunt124b.py, verify124.py (all < 30s).
NEXT (round-2 lanes): the exclusion-of-omitted-tail side (Størmer-style closure beyond
36), iteration/descent engine on split_all_S347 (every tail element re-splits), the
BEGL96 completeness quantifier layer over rationals.
