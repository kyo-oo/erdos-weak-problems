# WORKLOG_W85_142D — THE V-GEN KERNEL (lane W85-142D, commander-written)

Task ID: W85-142D. The W84-named continuation — THEOREM V-GEN kernel'd
(DM142_Proof_D.lean, ~573 lines, zero sorry). The subagent channel died on
context deadlines twice; the commander wrote the kernel in-thread (the W84
precedent).

## The law (frozen, all-integer form — no division after D0)

∀ k ≥ 3, m ≥ 2, N ≥ 16·m²: **2·m·(r k N) ≤ (2·(r k m)+1)·N** over the
official `Set.IsAPOfLengthFree.maxCard`.

## Architecture

| step | lemma | content |
|---|---|---|
| §0 | house machinery | nsmul_nat, coe_sub, apFree_subset, maxCard_ge_of_witness (the DM142A/C green idiom), sum_const_nat (DIY: Finset.induction_on — zero API risk) |
| §1 | `aff_k` | THE COPY CAP: the index set T = {j < m : a+jd ∈ S} has \|T\| ≤ r k m. Route: T+1 is officially k-AP-free — an official k-AP (a', d') in T+1 maps FORWARD through x ↦ a+(x−1)d to the official k-AP (a+(a'−1)d, d'·d) inside S (the full-set-builder form of IsAPOfLengthWith carries the surjectivity); d' = 0 excluded by the encard/singleton argument (the DM142C r_kk_ge pattern); then the green witness transfer |
| §2 | the band + Q + P | bandS := S ∩ {x : (m−1)D0 ≤ x−1 ∧ (m−1)D0 ≤ N−x}; Q := the copy-index Finset {(d,a)}; P := the incidence triples (x, (d, j)) |
| §3 | the double count | LOWER: bandS ×ˢ ([1,D0] ×ˢ [0,m)) ⊆ P (the band makes every triple valid) → \|bandS\|·(D0·m) ≤ \|P\|. UPPER: P = Q.bUnion(fibers) (every p's copy index (p.2.1, p.1−p.2.2·p.2.1) lands in Q); Finset.card_bUnion_le; each fiber ≤ r k m by aff_k + the j-injection (card_image_of_injOn + card_mono into Tq); sum_le_sum + sum_const_nat → \|P\| ≤ (r k m)·\|Q\| ≤ (r k m)·D0·N. CANCEL D0 ≥ 1 (Nat.mul_lt_mul_of_pos_right contrapositive + ring normalizations) → \|bandS\|·m ≤ (r k m)·N |
| §4 | the fringe + assembly | S = bandS ∪ (S ∖ band); the off-band ⊆ Icc 1 ((m−1)D0) ∪ Icc (N−(m−1)D0+1) N (two intervals, card_union_le ×2); 2m\|S\| ≤ 2m\|bandS\| + 4m(m−1)D0 ≤ 2(r k m)N + N (F3: 4m(m−1)D0 ≤ N by Nat.mul_div_le) — all integer, omega-closeable |
| §5 | the sup transfer | the DM142C u_gen_zero idiom verbatim: csSup_le ⟨1, ⟨{1}, …, rfl⟩⟩; every witness card n: 2mn ≤ B → n ≤ B/(2m) (Nat.le_div_iff_mul_le); 2m·(B/(2m)) ≤ B (Nat.mul_div_le). Board: k=3, m=8 → 16·(r 3 N) ≤ (2·(r 3 8)+1)·N for N ≥ 1024 |

## Arithmetic facts

F1 4m(m−1) ≤ 16m² ≤ N (explicit calc + mul_le_mul chains); F2 D0 = ⌊N/(4m(m−1))⌋ ≥ 1 (Nat.div_pos); F3 4m(m−1)·D0 ≤ N (Nat.mul_div_le); F4 (m−1)D0 ≤ N (monotonicity through F3).

## RISK LIST (CI adjudicates; fallbacks ready)

1. `Nat.div_pos` argument order (hba : b ≤ a) vs (hb : 0 < b) — if flipped, swap.
2. `Nat.eq_of_mul_eq_mul_right` (used 3× in aff_k) — (hc) vs (h) order; fallback Nat.mul_right_injective or the flipped order.
3. `Nat.le_div_iff_mul_le (2*m) (by omega)` — the exact form (a ≤ b/c ↔ a*c ≤ b); fallback: Nat.div_le... or by_contra + omega with div_add_mod.
4. `Finset.card_bUnion_le` — existence highly likely (Data/Finset/Card); fallback: Finset.induction_on DIY (5 lines, the sum_const_nat pattern).
5. `Finset.sum_le_sum` — standard.
6. The seteq ↑W = {A + n•D | n < k} — built by ext + rintro on both builder-memberships (the green window_isAP rintro pattern); the truncation identities (a'+i·d'−1 = (a'−1)+i·d') handled per-element by omega with the a' ≥ 1 receipt (derived: a' ∈ u ⊆ T+1).
7. The ENat.card/encard interchange — used exactly as the green DM142C does (hcard' : t.encard = ↑k := hcard direct assignment — the green u_gen_zero line).

## Honest scope

- SLIDE-GEN (r k N ≤ r k m·(N−m+1)/m + 2(m−1)) and T-GEN: NOT here — the named
  continuations for the next wave. The asymptotic formula (the official open
  core): claimed by no one, as ever.
- ARSENAL BRIDGE: honest omission — the D0 arithmetic uses core Nat division
  lemmas; no genuine CardinalWorlds/ErdosTernary2 call site exists in this
  kernel (the 61C precedent: honest omission > fake bridge). The derivation's
  GST citations (UPPER_STACK) are paper-level, not Lean-level.

The engine never stops; it never lies. In English, always.
