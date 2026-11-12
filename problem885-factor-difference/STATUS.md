# W56-3 / P885 — STATUS (factor-difference kernel + k5 hunt)

1. **Erdos885.lean** — the case kernel (namespace E885, CI-verdict, zero sorry):
   `dset` (additive encoding) + `dset_mem_iff` + **LEMMA 1 square criterion as a
   FULL iff** (`dset_square_criterion`: for N ≥ 1, d ∈ D(N) ⟺ 4N + d² = m²),
   both directions unconditional, incl. the parity engine `e885_parity`
   (m² = d² + 4k → m ≡ d mod 2) proved by L86 atom-expansion + omega shell.
2. Witness theorems: `k2_witness` (8 < 120, share {2, 7}); `k3_witness`
   (120 < 528 < 4488, share {2, 37, 58}) + `k3_distinct_sorted`; all factor
   pairs explicit (4·2, 8·1, 12·10, 15·8, 24·22, 68·66, 40·3, 48·11, 88·51,
   60·2, 66·8, 102·44 — python-verified before authoring).
3. Arsenal bridge `e885_arsenal_bridge` (sq_sub_one, mod_mod_mul,
   carryAtPos_bound, v2r_ternary_scaling on witness anchors) + master
   `e885_case_board`; receipt = 18× `#print axioms` + `#eval E885_FACTOR_DIFF_GREEN`.
4. **hunt885_k5.py / hunt885_k5.log** — k5 ROUND 1 (≤ 300MB, 272s): k3 engine
   validation **PASS** (in-house K_{4,2} rows {2,22,46,134} / C {1365,3360}
   re-derived; 9771 k3 configs in window); **k5: NO HIT** — no K_{6,4} within
   Δ ≤ 5e6, τ(Δ) ≥ 64, C ≤ 1e8, row-degree ≤ 30; u-window covered 1..500
   (time-capped); best 4-C common-rows = **3 of 6**; maxG = 54; 173,306 rich
   pairs probed — consistent with the B⁰·(log)²⁴ marginality (PROOF.md §2).
5. NEXT: (a) CI verdict on Erdos885.lean; (b) hunt round 2 (widen u-window,
   lower τ gate, rho-factorization for C > 1e8 — needs a bigger time box);
   (c) any k5 witness that lands becomes next round's Lean case theorem via
   the `dset_square_rev` construction machinery.
