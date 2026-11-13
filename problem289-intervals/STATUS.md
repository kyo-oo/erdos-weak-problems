# Kernel 64 / P289 — STATUS (k-interval Egyptian families, round-1 kernel)

1. **Erdos289.lean** — the round-1 kernel (namespace E289, CI-verdict, zero
   sorry): `longWindow`/`iprod`/`inum` (the #289 shape guard + the harmonic
   interval sum Σ_{i∈[a,b]} 1/i as an exact unreduced Nat fraction),
   `covers2` (the #289 k=2 sum-to-one decomposition as the cross-multiplied
   Nat identity), the structural laws (recurrences rfl, empty-window,
   positivity, single-window spellings, the L86-safe atom kit
   `e289_mul_pos`/`e289_mul_lt_right`/`e289_mul_cancel`), THE JOIN/SPLITTING
   LAW `join_aux`/`join_adjacent` (σ(a,b)+σ(b+1,d) = σ(a,d) — adjacent
   windows merge, the round-2 K2 lane's core), THE ANTI-CLOSURE COLLAPSE LAW
   `adjacent_collapse` (adjacent k=2 decompositions ⟺ a k=1 decomposition of
   the merged window — non-adjacency is exactly the merge-blocker),
   `covers2_comm`, the bounded decide censuses (k=1 and k=2 gapped on
   [2,12]), THE COMPLETE BOUNDED k=2 CLASSIFICATION `e289_no_pair_any_le12`
   (adjacent via collapse + k=1 census; gapped via decide census), the HM
   k=5 total-2 witness family `e289_hm_family` + `e289_anchor_values`
   (python-verified), the arsenal bridge, and the 14-conjunct master board
   `erdos289_board`. Receipt: `E289_INTERVALS_GREEN`.
2. **battery289.py** (output `battery289_output.txt`, ALL GREEN, 9s) — the
   Lean-mirror battery: every decide theorem pre-verified with exact integer
   arithmetic (anchors, k=5 total-2 identity, k=1/k=2 censuses at 12), the
   structural laws full-range (join ≤ 60, collapse iff ≤ 200, comm ≤ 10),
   and THE ENGINE FRONTIER re-certified by two independent methods: k=1 and
   k=2 gapped exclusions at M = 240 (crossing method + monotonicity), k=2
   gapped+adjacent brute-force cross-check at M = 80, crossing machinery
   positively validated (378 hits, 0 misses).
3. **engine289_round1.py** — the exact-rational DFS (Fractions, M = 240):
   k=2 negative at M = 240 is banked (FULL_PROOF_CAMPAIGN/P289/PROOF.md §1)
   and re-certified on disk by the battery's two independent methods; the
   stdout capture (`engine289_round1_output.txt`) is empty — the k ≥ 3 lanes
   are python-infeasible at M = 240 and the sandbox reaps background runs,
   so the battery is the carrier of record for the M = 240/80 frontier.
4. SIBLING COORDINATION: Kernel 56 (Erdos288, GREEN) owns the #288
   two-interval EQUALITY question — nothing restated here.
5. ROUND-2 LANES: (a) the K2 splitting/join law at witnesses beyond all
   used denominators → the all-k ≥ k₀ induction (the LEAP construction,
   full #289 YES-side); (b) the Kürschák/#317 parity transfer for the k=1
   unbounded exclusion; (c) the k=2 unbounded gapped exclusion (the parity
   obstruction on the cross-multiplied identity).
6. NEXT: CI verdict on Erdos289.lean (Kernel 64).
