# W57-4 STATUS — problem274-coset-tilings (Erdős #274, round-1 kernel)

- FILE: Erdos274.lean (namespace E274, header per house law, zero sorry, zero native_decide). CI verdict PENDING — GitHub renders it; author blind.
- LANDED FULL (unconditional, no search): `two_coset_impossible` + `no_two_coset_tiling`/`no_two_coset_half` — NO 2-coset distinct-size tiling in ANY group of ANY order (b ∣ n → b ∣ n−b = a → b ≤ a, contradiction; Nat.dvd_sub + Nat.le_of_dvd). `divisor_le_half` — proper coset size ≤ n/2. `feasible_structure` ([n] trivial). Arithmetic witnesses: [1,2,3]|6, [2,4,6]|[1,2,3,6]|12.
- LANDED (decide-certified census): `cyclic_6_negative`, `cyclic_12_negative`, `cyclic_census_le_12` — C_n has NO distinct-size coset tiling for all n ≤ 12; search is exhaustive over divisor-subsets × shift-assignments (36 @ n=6, 612 @ n=12, all fail exact cover).
- ARSENAL BRIDGE: `e274_arsenal_bridge` (isTernaryDigit, sq_sub_one, mod_mod_mul, carryAtPos_bound, v2r top-level, CardinalWorldsV2.v2r_ternary_scaling) + `e274_board` (7 conjuncts, one term each).
- BATTERY (battery274.py, runs green): two-coset scan ≤ 200 CONFIRMED; cyclic census ≤ 12 ALL NEGATIVE; cyclic ≤ 36 ALL NEGATIVE (matches campaign abelian ≤ 36).
- ROUND-2 KILL ROUTE (the real one): cyclic coset tilings = EXACT COVERING SYSTEMS — Mirsky–Newman–Davenport–Rado: no exact cover by residue classes with DISTINCT moduli (root-of-unity/generating-function proof, Σ_{m_i=max} ζ^{a_i} = 0). Formalize it → C_n negative for EVERY n, unconditionally.
- REMAINING round-2 items: (1) perm-canonicalization bridge (arbitrary-order cfg → ascending cfg ∈ censusConfigs) to upgrade the decide census to a full ∃-over-lists negative; (2) nonabelian ≤ 24 census; (3) MND-R formalization.
