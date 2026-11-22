# WORKLOG_W84_142C — U-GEN-0 KERNELLED (lane W84-142A)

Task ID: W84-142A. The W83-named continuation of DM142_Proof_A's honest
scope ("U-GEN-0/V-GEN derived+engine-validated, kernel continuation
named") — now executed: **LAW U-GEN-0 is in Lean** (DM142_Proof_C.lean).

## The law (NEW_LAWS_142.md, complete; derived W80-142U event 3/D3)

For every k ≥ 3, N ≥ 1: **r k N ≤ N − ⌊N/k⌋**, TIGHT at N = k
(**r k k = k − 1**). Partition [1,N] into ⌊N/k⌋ consecutive k-blocks +
tail; each full block is a non-trivial k-AP (d = 1) so a k-AP-free set
misses ≥ 1 point per block.

## The Lean architecture (DM142_Proof_C.lean, ~330 lines)

| step | lemma | content |
|---|---|---|
| §1 | `window_isAP` | a full k-block {m+1..m+k} IS an official `Set.IsAPOfLength k` with a = m+1, d = 1 (card via `Nat.card_Icc` + `Set.encard_coe_eq_coe_finsetCard`; the set-equality by `Nat.add_sub_cancel'` / `Nat.mod`-free omega bounds) |
| §2 | `window_bound` | a k-AP-free S meets each block in ≤ k−1 (if all k: `Finset.eq_of_subset_of_card_le` forces block ⊆ S, then freeness says k ≤ 1) |
| §3 | `window_union_bound` | induction on Q: S ⊆ [1, Q·k] → \|S\| ≤ Q(k−1); one block peeled per succ-step (`Finset.card_union_le` assembly — NO disjointness needed) |
| §4 | `core_bound` | blocks [1, p] (p = ⌊N/k⌋·k) + tail (p, N]: `Nat.div_add_mod`/`Nat.mul_comm` spine, `Nat.mul_sub` for q(k−1) = p − q, truncated-ℕ omega finish |
| §5 | `u_gen_zero` | the csSup transfer (green r_mono's `csSup_le ⟨(Icc 1 N).card, mem_upperBounds.2 _⟩` pattern, verbatim) |
| §6 | `u_gen_zero_tight` | ≤ via U-GEN-0 at N=k with **k/k = 1 by the Arsenal `mul_add_div_lemma`** (CardinalWorlds.lean:143 — the genuine D3 block-count bookkeeping); ≥ via the witness `Ico 1 k` (any (k−1)-set is k-AP-free: ENat-card k cannot fit) |

## API receipts (read-before-use, Mathlib v4.33.0-rc2 sources fetched)

- `Nat.card_Icc : #(Icc a b) = b + 1 - a` — Mathlib/Order/Interval/Finset/Nat.lean:83 (@[simp], namespace Nat confirmed)
- `Nat.card_Ico : #(Ico a b) = b - a` — same file:84
- `Finset.card_mono : Monotone card` — Mathlib/Data/Finset/Card.lean:74
- `Finset.eq_of_subset_of_card_le (h : s ⊆ t) (h₂ : #t ≤ #s) : s = t` — Card.lean:282
- `Finset.card_union_le (s t) : #(s ∪ t) ≤ #s + #t` — Card.lean:576 (replaces the disjointness assembly entirely)
- `Finset.card_inter_add_card_union` — Card.lean:569 (verified, ultimately unused — card_union_le suffices)
- `Set.encard_coe_eq_coe_finsetCard`, `ENat.natCast_le_natCast`, `Finset.mem_coe`, `csSup_le ⟨_, mem_upperBounds.2 _⟩` — green-kernel (DM142A) verified idioms
- `Arsenal.CardinalWorlds.mul_add_div_lemma (k r d) (0 < d) : (d*k + r)/d = k + r/d` — Arsenal/CardinalWorlds.lean:143 (read this session; genuine use in tightness)
- Core Lean: `Nat.div_add_mod`, `Nat.mod_lt`, `Nat.mul_sub`, `Nat.le_mul_of_pos_right`, `Nat.add_sub_cancel'`, `Nat.add_mul`, `Nat.zero_div` — Init/Nat bedrock

## Honest scope

- SLIDE-GEN (d=1 windows): the block engine here IS the d=1 window
  mechanism; NEW_LAWS_142's frozen-form remark (N − ⌊N/k⌋ + 1) follows
  by +1. No separate theorem shipped (no material delta).
- V-GEN (sharp amplification) and T-GEN (Z_p transfer): NOT here —
  the sibling lane W84-142B (DM142_Proof_D) carries them.
- The asymptotic formula itself (the official open core): claimed by no
  one, as ever.

## Residual risks for the warlord

1. `by exact_mod_cast hbad` on `((k:ℕ):ℕ∞) ≤ 1` (OfNat-vs-natCast 1 in
   ℕ∞) — green DM142A used the identical shape at line 434, low risk;
   fallback `ENat.natCast_le_natCast.1`.
2. `Finset.eq_empty_iff_forall_notMem` — NOT used in the final version
   (card_union_le assembly) — risk eliminated.
3. The `rintro ... rfl` maxCard-family destructuring — green-verbatim.

The engine never stops; it never lies. In English, always.

## REPAIR R1 (run 45065271636 post-mortem, 7 defects fixed)

1. zero-case `Nat.card_Icc` omega after auto-rfl close — dropped the omega.
2. §3 hcu: the `rw [hcover]` SELF-REFERENCE (the equation's RHS contains S —
   rw looped the goal into the union-intersected form) — replaced by
   `congrArg Finset.card hcover` + a safe pattern-rewrite of the leading
   `S.card` only.
3. §4 hcu: the same fix.
4. u_gen_zero: `csSup_le` takes a NONEMPTY witness (the green
   r_mono_unrestricted_false pattern ⟨1, ⟨{1}, hsub, hfree, rfl⟩⟩), not a
   BddAbove pair — mirrored verbatim.
5. r_kk_ge: the maxCard unification needed the card equation FIRST
   (h1 : k−1 = (Ico 1 k).card via Nat.card_Ico.symm, then rw + exact).
6. The Arsenal call: `mul_add_div_lemma` is ROOT-namespace (the file has no
   namespace declarations; DM142A's header prose was never a call site).
7. dm142c_board: the hN argument was dropped in the lambda — passed.
