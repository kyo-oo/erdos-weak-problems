# AUDIT W85-107C — THE COMPLETE DEPENDENCY CONE OF THE #107 LOWER-BOUND KERNEL PORT

TASK ID: W85-107C-A | CONE TRACER + ADVERSARIAL AUDITOR
Entry points traced: `Blueprint107.lean:773` (`f_eq_conjectured_of_le_four`),
`Blueprint107.lean:784` (`conjectured_lower_bound_of_le_five`), `Blueprint107.lean:796`
(`ersz_bounds_of_le_five`), via `Solution.lean:69/74` (`Erdos107.Palomar` delegation,
`f_eq`/`cardSet_eq` are `rfl`-bridges to `Erdos107.*`).

**VERDICT UP FRONT: SHIP.** The vendor cone is **closed (zero sorry/admit/native_decide/axiom)**,
every Mathlib/FC leaf in the fresh cone is **verified present at the campaign toolchain
v4.33.0-rc2** (checked against the actual v4.33 Mathlib tree, not the vendor's v4.35), the
upper side of target 3 is **already GREEN in DM107_Proof_B.lean** (CI job `kernel-107dm-b`,
run-greped `DM107B_ERSZ_GREEN`), and the n=3 anchor `f_three_eq` is **already GREEN in
DM107_Official.lean** (CI job `kernel-fc`, `DM107_ANCHORS_GREEN`). The fresh content is
~950 lines of vanilla-tactic ports (ring/linarith/rcases/decide). One genuine exposure:
the two 4096-case `decide` blocks in the 8-point witness verification (see Risk 1).

---

## 0. CONE SUMMARY (counts)

| Class | Count | Notes |
|---|---|---|
| FRESH-PORT nodes | **75** (incl. the 3 target roots) | from Blueprint107 §1–§4 + Erdos107Unified435 §1/§4 (one 7-line proof REWRITTEN to drop the parabola chain) |
| ALREADY-PORTED (clone from GREEN) | **98 declarations** | 97 from DM107_Proof_B §0–§14 (the ES-1935 upper machinery, CI-GREEN as a unit) + `f_three_eq` from DM107_Official:106–134 (CI-GREEN anchor) |
| MATHLIB/FC leaf calls in the fresh cone | **~40 distinct** | every one verified at v4.33.0-rc2 (§3 below) or attested GREEN by B / DM107_Official |
| **Cone total** | **≈ 210 nodes** | |

The three targets reduce to **four mathematical pillars**, none of which uses the general
ES-1960 lower construction (which the vendor does NOT have — B §15's honest scope marker
correctly says "linrock's public proof [has] only n ≤ 5 witnesses"):

1. **n=3**: `f 3 = 3` — official GREEN anchor (copy verbatim).
2. **n=4 lower**: `4 ∉ cardSet 4` — the Klein 4-point witness (triangle + interior point).
3. **n=4 upper**: `5 ∈ cardSet 4` — Esther Klein's 5-point theorem (the DEDICATED tight
   n=4 argument; the general ES upper would only give `f 4 ≤ C(4,2)+1 = 7 ≠ 5`).
4. **n=5 lower**: `8 ∉ cardSet 5` — the ES-1960 8-point 4-cap+4-cup integer witness.
   Plus the **upper side for n=5** (`f 5 ≤ C(6,3)+1 = 21`), which has NO cheap route in
   the vendor (`f_five_upper_unconditional`, XMP:614, is literally
   `f_le_erdosSzekeresUpper (by decide)`) → the whole B §1–§12 clone is required.

---

## 1. THE CONE TABLE (node → source → status → B-reference / risk)

Status key: **FRESH** = port from vendor; **CLONE-B** = copy namespace-swapped from
DM107_Proof_B.lean (CI-GREEN, v4.33-verified idioms); **CLONE-OFF** = copy verbatim from
DM107_Official.lean (CI-GREEN anchor); **MATHLIB/FC** = library leaf (verified, see §3).

### 1a. Root level (Blueprint §4)

| Node | Source | Status | Notes / B-ref |
|---|---|---|---|
| `f_eq_conjectured_of_le_four` | Bp:773 | FRESH (7 ln) | case-split n=3∨n=4 (omega) + `simpa using f_three_eq` / `simpa using f_four_eq_five_unconditional` |
| `conjectured_lower_bound_of_le_five` | Bp:784 | FRESH (9 ln) | n=3/4: `rw [f_…]; decide`; n=5: `simpa using nine_le_f_five` |
| `ersz_bounds_of_le_five` | Bp:796 | FRESH (7 ln) | ⟨lower, `f_le_erdosSzekeresUpper (by omega)`⟩ — the upper call is CLONE-B:1434 |

### 1b. n=3 lane

| Node | Source | Status | Notes |
|---|---|---|---|
| `f_three_eq` | DM107_Official:106–134 (vendor twin U435:332) | **CLONE-OFF** (~30 ln) | CI-GREEN verbatim; proves BOTH sides: `hmem3 : 3 ∈ cardSet 3` via `convexIndep_triple_of_not_collinear`, and the lower `le_csInf ⟨3,hmem3⟩` via N collinear x-axis points with **vacuous** `NonTrilinear` (`Set.triplewise_of_encard_lt` + `Set.encard_coe_eq_coe_finsetCard`). This REPLACES the vendor's parabola route and kills the whole parabola sub-cone (see §1h Exclusions) |
| `convexIndep_triple_of_not_collinear` | U435:269 = B:1343 | CLONE-B | byte-identical to the official anchor; "any 3 GP points are in convex position" — lives here |

### 1c. n=4 LOWER lane (`4 ∉ cardSet 4` → `5 ≤ f 4`)

| Node | Source | Status | Notes |
|---|---|---|---|
| `f_four_eq_five_unconditional` | Bp:458 | FRESH (3 ln) | `f_four_eq_five.1` |
| `f_four_eq_five` (`∧ f 4 = erdosSzekeresConjectured 4`) | Bp:452 | FRESH (4 ln) | needs `erdosSzekeresConjectured` def (CLONE-B:1466) |
| `f_four_eq_five_of_mem_cardSet` | U435:1610 | FRESH (7 ln) | `Nat.sInf_le h5` + `five_le_f_four ⟨5,h5⟩` + `le_antisymm` |
| `five_le_f_four` | U435:508 | FRESH (4 ln) | `le_csInf (nonempty_cardSet_all 4) fun _ hN => five_le_of_mem_cardSet_four hN` |
| `five_le_of_mem_cardSet_four` | U435:500 | **FRESH-REWRITTEN** (6 ln) | vendor uses `le_of_mem_cardSet` (parabola). REWRITE as the Bp:740 mirror: `by_contra; N ≤ 4; exact four_not_mem_cardSet_four (cardSet_upward_closed hle hN)` — statement-identical, drops the parabola sub-cone |
| `cardSet_upward_closed` | U435:215 | FRESH (8 ln) | `Finset.exists_subset_card_eq` [MATHLIB ✓ Card.lean:664, hyp-shape `∃ t ⊆ s, #t = n` matches] + `nonTrilinear_mono` + `hasConvexNGon_mono_pts` |
| `nonTrilinear_mono` | U435:49 | FRESH (3 ln) | trivial; not in B (B only has `nonTrilinear_iff`) |
| `hasConvexNGon_mono_pts` | U435:207 | FRESH (5 ln) | trivial (NOT `hasConvexNGon_mono_n`/`cardSet_antitone_n`/`f_mono_of_nonempty` — excluded, unused) |
| `four_not_mem_cardSet_four` | U435:487 | FRESH (10 ln) | `Finset.eq_of_subset_of_card_le` [MATHLIB ✓ Card.lean:282] |
| `kleinFourPts` witness block: `ptO ptA ptB ptC kleinFourPts`, `ptO_ne_ptA ptO_ne_ptB ptO_ne_ptC ptA_ne_ptB ptA_ne_ptC ptB_ne_ptC`, `kleinFourPts_card`, `ptC_eq_barycentric`, `ptC_mem_convexHull_triangle`, `not_convexIndep_kleinFourPts`, `kleinFourPts_nonTrilinear` | U435:364–484 | FRESH (13 nodes, ~120 ln) | deps: `mkPt/mkPt_zero/mkPt_one` [CLONE-B:110–119], `convex_convexHull/subset_convexHull/convexHull_mono` [MATHLIB ✓ Hull.lean:50/53/70], `not_collinear_of_cross_ne_zero` (below), `cross_eq_zero_of_collinear` [CLONE-B:126], `norm_num` on coordinates (B-attested idiom) |
| `not_collinear_of_cross_ne_zero` | U435:119 | FRESH (3 ln) | 3-line converse of B:126 — not in B |

### 1d. n=4 UPPER lane — Esther Klein's 5-point theorem (`5 ∈ cardSet 4`)

| Node | Source | Status | Notes |
|---|---|---|---|
| `five_mem_cardSet_four` | Bp:438 | FRESH (12 ln) | unfolds `cardSet` membership; `Finset.mem_coe.mpr` (B-attested) |
| `exists_five_distinct_of_card_eq_five` | Bp:419 | FRESH (17 ln) | `Finset.card_eq_succ` [MATHLIB ✓ Card.lean:776 — signature `∃ a t, a ∉ t ∧ insert a t = s ∧ #t = n` matches the vendor's `⟨e, s₄, he_s₄, rfl, hs₄⟩` destructuring] + `Finset.card_eq_three` [✓ Card.lean:789, B-attested] |
| `hasConvexFourGon_of_five_distinct_nonTrilinear` | Bp:402 | FRESH (15 ln) | `lineSide_pos_or_neg_of_not_collinear` + `lineSide_swap_left` [CLONE-B:237] |
| `hasConvexFourGon_of_pos_outer_and_two_points` | Bp:379 | FRESH (20 ln) | dichotomy + fifth-point lemma |
| `four_point_pos_triangle_dichotomy` | Bp:271 | FRESH (40 ln) | 8-case sign bash; `lineSide_cycle` [B:247], `lineSide_swap_right` [B:242], `lineSide_triangle_sum`, inline `dsimp [lineSide]; ring` identities (B-attested idiom) |
| `hasConvexFourGon_of_two_pos_one_neg` | Bp:250 | FRESH (16 ln) | → `hasConvexFourGon_of_same_open_side_edge` |
| `hasConvexFourGon_of_inPosTriangle_and_fifth_point` | Bp:341 | FRESH (36 ln) | 4-way dichotomy + `inPosTriangle_trans`/`_cycle` |
| `hasConvexFourGon_of_two_inPosTriangle` | Bp:314 | FRESH (25 ln) | → `hasConvexFourGon_of_triangle_two_interior` |
| `hasConvexFourGon_of_same_open_side_edge` | U435:1918 | FRESH (26 ln) | 4-pt Finset packaging + `convexIndep_four_of_same_open_side` |
| `hasConvexFourGon_of_triangle_two_interior` | U435:1948 | FRESH (16 ln) | THE 3-outer+2-interior core |
| `three_vertices_same_open_side_of_line` | U435:1902 | FRESH (14 ln) | 3-sign pigeonhole applied to lineSide signs |
| `pigeonhole_three_signs` | U435:1882 | FRESH (17 ln) | 8-case rcases bash, zero deps |
| `convexIndep_four_of_same_open_side` | U435:1861 | FRESH (18 ln) | |
| `convexIndep_four_of_pos_same_open_side` | U435:1831 | FRESH (26 ln) | set-identity shuffle + `lineSide_swap_left` |
| `convexIndep_four_of_opposite_diagonals` | U435:1805 | FRESH (23 ln) | 4 separations from `lineSide_sep_of_neg_pos` |
| `convexIndep_four_of_strict_sep` | U435:1097 | FRESH (52 ln) | 4×4 rcases; base `convexIndep_of_pointwise_strict_sep` **[CLONE-B:408 — ALREADY-PORTED]** |
| `lineSide_sep_of_neg_pos` | U435:1787 | FRESH (14 ln) | `lineSide_affine_decomp` [B:252] + `lineSide_self_left/right` [B:227/232] |
| `lineSide_pos_or_neg_of_not_collinear` | U435:1773 | FRESH (9 ln) | `lt_trichotomy` + `collinear_of_lineSide_eq_zero` **[CLONE-B:259 — ALREADY-PORTED]** — the ONE lineSide lemma B §4 lacks |

### 1e. InPosTriangle calculus (Blueprint §1 — shared by 1c/1d/1f)

| Node | Source | Status | Notes |
|---|---|---|---|
| `InPosTriangle` (def) | Bp:87 | FRESH (3 ln) | `0 < lineSide a b d ∧ 0 < lineSide b c d ∧ 0 < lineSide c a d` |
| `lineSide_triangle_sum` | Bp:93 | FRESH (6 ln) | `dsimp [lineSide]; ring` |
| `lineSide_cramer_right` | Bp:102 | FRESH (8 ln) | Plücker/Cramer syzygy, `ring` |
| `lineSide_cramer_left` | Bp:112 | FRESH (8 ln) | ditto |
| `inPosTriangle_cycle` | Bp:120 | FRESH (5 ln) | |
| `inPosTriangle_pos_outer` | Bp:127 | FRESH (7 ln) | linarith over triangle-sum |
| `inPosTriangle_trans` | Bp:137 | FRESH (22 ln) | the two Cramer syzygies + `positivity` |
| `barycentric_of_lineSide_ne_zero` | Bp:163 | FRESH (13 ln) | `ext i; fin_cases i`; `PiLp.add_apply/smul_apply` [B-attested B:162–168]; `field_simp [h]` |
| `inPosTriangle_mem_convexHull` | Bp:178 | FRESH (42 ln) | explicit convex combinations; `convex_convexHull`/`subset_convexHull` [MATHLIB ✓]; `Convex` applied as `h_conv x y hx hy (0≤a) (0≤b) (a+b=1)` — same Convex unfolding B runs GREEN |
| `not_convexIndep_of_inPosTriangle` | Bp:223 | FRESH (23 ln) | `convexHull_mono` [MATHLIB ✓ Hull.lean:70] |

### 1f. n=5 LOWER lane — the 8-point ES/Kalbfleisch–Stanton witness (`8 ∉ cardSet 5` → `9 ≤ f 5`)

| Node | Source | Status | Notes |
|---|---|---|---|
| `nine_le_f_five` | Bp:749 | FRESH (4 ln) | `le_csInf (nonempty_cardSet_all 5) fun _ hN => nine_le_of_mem_cardSet_five hN` |
| `nine_le_of_mem_cardSet_five` | Bp:740 | FRESH (6 ln) | the upward-closure mirror (the model for the `five_le_of_mem_cardSet_four` rewrite) |
| `eight_not_mem_cardSet_five` | Bp:732 | FRESH (6 ln) | applies cardSet membership to the witness |
| `not_hasConvexFiveGon_esEightFinset` | Bp:683 | FRESH (44 ln) | THE master proof; `Finset.subset_image_iff` [MATHLIB ✓ Image.lean:717, destructuring `⟨I, _, rfl⟩` matches], `Finset.card_image_of_injective` [B-attested], `Finset.card_pos` [MATHLIB ✓ Card.lean:78], `Finset.mem_filter/mem_sdiff/mem_image_of_mem` [✓ Image.lean:297] |
| `fin8_cap_cup_split` | Bp:656 | FRESH (25 ln) | `Finset.card_sdiff_add_card_eq_card` [MATHLIB ✓ Card.lean:592 — **takes the subset hypothesis**, vendor passes `Finset.filter_subset _ I`, shape verified; also W82-107B worklog §3 attests], `filter_subset_filter`, 2×`decide` (half-sizes), `omega` |
| `esEight_cap_triple_with_cup_pt` | Bp:635 | FRESH (8 ln) | **`decide` — 8⁴ = 4096 quadruples × 3 integer 2×2 determinants. Risk 1** |
| `esEight_cup_triple_with_cap_pt` | Bp:645 | FRESH (8 ln) | **`decide` — 4096 quadruples. Risk 1** |
| `esEightFinset_nonTrilinear` | Bp:615 | FRESH (18 ln) | `cross_eq_zero_of_collinear` [B:126] + `lineSide_esEightPt` + `esEightCross_ne_zero_of_distinct` |
| `esEightCross_ne_zero_of_distinct` | Bp:608 | FRESH (5 ln) | **`decide` — 512 triples** |
| `esEightFinset_card` | Bp:601 | FRESH (5 ln) | `Finset.card_image_of_injective`, `card_univ`, `Fintype.card_fin` |
| `esEightPt_injective` | Bp:591 | FRESH (8 ln) | `mkPt_zero` [B:114] + `Int.cast_inj` [MATHLIB ✓ Int/Cast/Lemmas.lean:67] |
| `esEightX_ne_of_ne` | Bp:585 | FRESH (4 ln) | `decide` — 64 pairs |
| `lineSide_esEightPt` | Bp:576 | FRESH (8 ln) | `lineSide` [B:211] = cast of `esEightCross`: `dsimp; simp only [mkPt_zero, mkPt_one]; push_cast; ring` |
| `esEightX`, `esEightY`, `esEightPt`, `esEightFinset`, `esEightCross` (defs) | Bp:557–573 | FRESH (5 defs, ~18 ln) | THE WITNESS DATA: x = ![0,1,2,3,20,21,22,23], y = ![0,3,5,6,100,97,95,94] |
| `exists_strict_ordered_triple_of_three_le_card` | Bp:538 | FRESH (18 ln) | 8-case order bash over `exists_three_distinct…` |
| `exists_three_distinct_of_three_le_card` | Bp:520 | FRESH (16 ln) | `Finset.card_pos`, `card_erase_of_mem` [B-attested] |

### 1g. UPPER lane (target 3's second conjunct) — **ALREADY-PORTED, clone from GREEN B**

`f_le_erdosSzekeresUpper {k} (hk : 2 ≤ k) : f k ≤ erdosSzekeresUpper k`
(vendor XMP:589–591 ≡ **B:1434–1436**, CI-GREEN). C cannot `import DM107_Proof_B`
(standalone `lake env lean` kernels — same reason B re-declares A's §0–§11, B header
:52–67), so C **clones B §0–§12 + the §14 nonempty block namespace-swapped** (98
declarations, ~1375 lines — mechanical copy of a GREEN unit):

| Block | B lines | Content |
|---|---|---|
| §0 | 96–105 | `cardSet`, `f` — official defs verbatim |
| §1 | 107–172 | `mkPt`, `mkPt_zero/one/ext`, `cross_eq_zero_of_collinear`, `collinear_of_cross_eq_zero` |
| §2 | 174–183 | `nonTrilinear_iff` (Iff.rfl bridge for the Set.Triplewise packaging) |
| §3 | 185–205 | `slopeLt/slopeGt`, `slopeLt_or_slopeGt_of_not_collinear` |
| §4 | 207–368 | `lineSide`, `lineNormX/Y`, `lineConst`, permutation laws, `collinear_of_lineSide_eq_zero`, secant syzygies, slope transitivity |
| §5 | 370–414 | `halfPlaneLe` block → `convexIndep_of_pointwise_strict_sep` (the base of fresh §14) |
| §6 | 416–584 | `IsXMonotone`, `CupChainEnding/CapChainStarting/HasCup/HasCap`, `cup_end_meets_cap_start_on`, `erdos_szekeres_cup_cap_theorem_on`, `erdosSzekeresUpper` def (= `Nat.choose (2*n-4) (n-2) + 1`, B:583) |
| §7 | 586–1030 | `IsCupSet/IsCapSet`, insert/skipped-chord, `convexIndep_of_isCupSet/of_isCapSet` |
| §8 | 1032–1159 | x-sorting bridge (`pointOfX`, `xSortedSeq`, `hasConvexNGon_of_x_injOn_and_nonTrilinear`) |
| §9 | 1161–1311 | shear perturbation (`shearPt`, `goodShearSlope`, `hasConvexNGon_image_shearPt_iff`) — carries the ONE `Set.image_diff` deprecated-alias site (B:1241, silenced by the header's `set_option linter.deprecated false`) |
| §10 | 1313–1378 | `convexIndep_of_card_le_two`, `convexIndep_triple_of_not_collinear`, `self_mem_cardSet_of_le_three` |
| §11 | 1380–1416 | `hasConvexNGon_of_nonTrilinear_and_card_ge`, `erdosSzekeresUpper_mem_cardSet` |
| §12 | 1418–1447 | `f_le_erdosSzekeresUpper_of_mem_cardSet`, `f_le_erdosSzekeresUpper`, (`ersz_upper` optional) |
| §14 | 1545–1563 | `nonempty_cardSet_all`, `nonempty_cardSet` (needed for `le_csInf` nonemptiness at n=4 and n=5). B's version uses the arsenal `ErdosTernary2.lt_three_cases`; the vendor twin XMP:574–577 uses plain `le_or_gt` — either works, cloning B verbatim is the attested route |
| §13 (def only) | 1464–1467 | `erdosSzekeresConjectured` (for `f_four_eq_five`'s second conjunct) |

### 1h. EXCLUDED from the cone (verified unused — do NOT port)

- **Parabola chain**: `parabolaPt/parabolaFinset_card/parabolaFinset_nonTrilinear/le_of_mem_cardSet/le_f_of_nonempty/f_eq_self_of_le_three/f_zero_eq/f_one_eq/f_two_eq` (U435:127–335) — killed by the official-anchor `f_three_eq` + the upward-closure rewrite of `five_le_of_mem_cardSet_four`.
- `hasConvexNGon_mono_n`, `cardSet_antitone_n`, `f_mono_of_nonempty` (U435:197–239).
- The 4 presentational cap/cup lemmas `inPosTriangle_of_three_cap_and_above`, `not_convexIndep_of_three_cap_and_above`, `inPosTriangle_of_three_cup_and_below`, `not_convexIndep_of_three_cup_and_below` (Bp:468–517) — grep-verified: only self-references; `not_hasConvexFiveGon_esEightFinset` builds its `InPosTriangle` witnesses directly from the decide-lemma crosses.
- `ptD/kleinFivePts/kleinFivePts_*` (U435:1178–1249), `ptA6/ptB6/ptP/ptQ/innerQuad6` (U435:1252–1329), `hasConvexFourGon_of_four_extreme` (U435:1152), `kleinFiveOuterQuad_convexIndep` — the 5-point case-split WITNESSES are superseded by the general `five_mem_cardSet_four` argument.
- `cup_four/cap_four_convexIndep`, `erdos_szekeres_seven_points`, Tóth–Valtr block, `dilworthMonotoneBound`, all `kks_*` wedge/pentagon forcing (U435:2028–2947, InductiveKCupKCap107 §2+, XMP §3), `convexIndep_five_of_strict_sep`, `hasConvexFiveGon_*`, `erdos_szekeres_twenty_one_points_*` — pentagon-FORCING machinery (the conditional `9 ∈ cardSet 5` direction), not needed for the three targets.
- `f_five_upper_unconditional` (XMP:614), `f_five_bounds_unconditional` (Bp:756), `f_five_eq_nine_of_nine_mem` (Bp:763) + its dep `f_five_eq_nine_of_eight_not_mem_and_nine_mem` (U435:2962), `erdos_107_of_ge_five`/`erdos_107_of_lower_ge_six_and_upper_ge_five` (Bp:806–834) — conditional reductions, out of scope.

---

## 2. THE WITNESS MACHINERY REPORT (task B)

### 2a. The 8-point ES-1960 witness ("no 5 in convex position")

**Not** decidable enumeration over point subsets, and **not** a black-box computation: it is a
**hybrid** — small `decide` computations at the INDEX level + a structured convexity argument.
Exact chain (all statements):

1. **Witness data** (Bp:557–573): `esEightX : Fin 8 → ℤ := ![0,1,2,3,20,21,22,23]`,
   `esEightY : Fin 8 → ℤ := ![0,3,5,6,100,97,95,94]`, `esEightPt i := mkPt (X i : ℝ) (Y i : ℝ)`,
   `esEightFinset := Finset.univ.image esEightPt`, and the integer determinant
   `esEightCross i j k := (X j − X i)(Y k − Y i) − (Y j − Y i)(X k − X i)`.
   Geometry: indices 0–3 = 4-**cap** (slopes 3,2,1 decreasing), indices 4–7 = 4-**cup**
   (slopes −3,−2,−1 increasing), horizontally separated (x: 0–3 vs 20–23).
2. **Cast bridge** `lineSide_esEightPt` (Bp:576): `lineSide (esEightPt i) (esEightPt j)
   (esEightPt k) = (esEightCross i j k : ℝ)` — `dsimp; simp only [mkPt_zero, mkPt_one];
   push_cast; ring`. Every later step works over ℤ.
3. **General position** by computation: `esEightCross_ne_zero_of_distinct` (Bp:608,
   `decide`, 512 triples) + `esEightPt_injective`/`esEightX_ne_of_ne` (Bp:585/591,
   `decide`, 64 pairs) → `esEightFinset_card : …card = 8` (Bp:601) and
   `esEightFinset_nonTrilinear` (Bp:615, via `cross_eq_zero_of_collinear`).
4. **The no-pentagon argument is structured** (`not_hasConvexFiveGon_esEightFinset`,
   Bp:683, 44 lines): given a 5-element convex-independent `S ↑⊆ esEightFinset`, pull it
   back through the image (`Finset.subset_image_iff`) to `I : Finset (Fin 8)`, `#I = 5`
   (injectivity). **Pigeonhole** `fin8_cap_cup_split` (Bp:656, pure card arithmetic +
   `omega`; the two half-sizes are `decide`): either ≥3 indices in the cap half and ≥1 in
   the cup half, or vice versa. First case: an increasing triple `i<j<k` in the cap half
   (`exists_strict_ordered_triple_of_three_le_card`, Bp:538 — pure order combinatorics)
   plus a cup index `u`; **`esEight_cap_triple_with_cup_pt` (Bp:635, `decide`, 4096
   cases)** certifies the three integer crosses `0 < esEightCross i k j`,
   `0 < esEightCross k u j`, `0 < esEightCross u i j`, i.e. the middle cap vertex j lies
   strictly inside the positively oriented triangle (i, k, u) — `InPosTriangle` via
   `lineSide_esEightPt` + `exact_mod_cast`. Then
   **`not_convexIndep_of_inPosTriangle`** (Bp:223 — barycentric convex-hull membership:
   `barycentric_of_lineSide_ne_zero` (Bp:163) → `inPosTriangle_mem_convexHull` (Bp:178)
   → `convexHull_mono`) kills `ConvexIndep S`. Second case dual
   (`esEight_cup_triple_with_cap_pt`, Bp:645).
5. **Size/complexity**: witness block ≈ 240 lines total, of which 5 `decide` proofs
   (64 + 512 + 4096 + 4096 + 2×1 cases) and one 44-line master proof. Everything else is
   defs and 5–20-line glue.

### 2b. The n=3 witness

There is none needed as data: `f 3 = 3` = the **official GREEN anchor**
(DM107_Official:106–134). Upper `3 ∈ cardSet 3` = "any 3 GP points are in convex
position" = `convexIndep_triple_of_not_collinear` (DM107_Official:78–99 = B:1343,
byte-identical). Lower `3 ≤ f 3`: for `N ∈ cardSet 3` with N < 3, build N points on the
x-axis (`EuclideanSpace.single 0 i`); `NonTrilinear` holds **vacuously** because
`Set.encard < 3` (`Set.triplewise_of_encard_lt`, FC/Data/Set/Triplewise.59 +
`Set.encard_coe_eq_coe_finsetCard`, Mathlib Data/Set/Card.lean:93) — then a 3-subset of
≤2 points is impossible (`Finset.card_le_card`). Note the vendor's OWN `f_three_eq`
(U435:332) instead routes through the parabola chain (`le_of_mem_cardSet`) — the official
anchor is strictly cheaper and CI-attested; port that one.

### 2c. The n=4 witnesses — BOTH directions, and the dedicated tight upper

- **Lower (`4 ∉ cardSet 4`)**: the Klein 4-point witness `kleinFourPts =
  {(0,0),(3,0),(0,3),(1,1)}` (U435:364–495): `(1,1) = ⅓·(0,0) + ⅓·(3,0) + ⅓·(0,3)`
  (`ptC_eq_barycentric`) lies in the hull of the outer triangle
  (`ptC_mem_convexHull_triangle`) → `¬ ConvexIndep` (`not_convexIndep_kleinFourPts`);
  `kleinFivePts_nonTrilinear`-style 4×4×4 case bash gives general position
  (`kleinFourPts_nonTrilinear`, via `not_collinear_of_cross_ne_zero` + `norm_num`).
  → `four_not_mem_cardSet_four` (U435:487).
- **Upper (`5 ∈ cardSet 4`)** — **the DEDICATED tight n=4 argument, FOUND at
  Blueprint107 §2 (Bp:246–461)**, NOT the general ES upper (which gives only
  `f 4 ≤ C(4,2)+1 = 7`). The chain: `exists_five_distinct_of_card_eq_five` (Bp:419)
  extracts 5 distinct points → `hasConvexFourGon_of_five_distinct_nonTrilinear`
  (Bp:402): orient a triple (`lineSide_pos_or_neg_of_not_collinear` + `lineSide_swap_left`)
  → `hasConvexFourGon_of_pos_outer_and_two_points` (Bp:379): apply the
  **`four_point_pos_triangle_dichotomy`** (Bp:271 — for a positively oriented triangle
  (a,b,c) and 4th GP point d: either {a,b,c,d} is a convex 4-gon
  (`hasConvexFourGon_of_two_pos_one_neg` → `hasConvexFourGon_of_same_open_side_edge` →
  `convexIndep_four_of_same_open_side` → … → `convexIndep_of_pointwise_strict_sep`
  [B:408] by strict linear separation), or one of the four points lies strictly inside
  the triangle of the other three). Interior case + 5th point:
  `hasConvexFourGon_of_inPosTriangle_and_fifth_point` (Bp:341) — either the 5th point
  also lands in a common triangle with the interior point (then the two interior points
  + the 3 outer vertices force a 4-gon via the **3-sign pigeonhole**
  `pigeonhole_three_signs`/`three_vertices_same_open_side_of_line` →
  `hasConvexFourGon_of_triangle_two_interior`, U435:1948), or the 5th point is itself
  interior to a triangle containing the first interior point
  (`inPosTriangle_trans`, Bp:137, via the two Cramer syzygies) and the pair argument
  applies. → `five_mem_cardSet_four` (Bp:438) → `f 4 ≤ 5` (`Nat.sInf_le`).
- Assembly: `f_four_eq_five_of_mem_cardSet` (U435:1610) + `five_le_f_four` →
  `f_four_eq_five`/`f_four_eq_five_unconditional` (Bp:452/458).

---

## 3. THE f/sInf MECHANICS REPORT (task C)

The lower-bound derivation "witness of size m with no n-gon ⇒ m ∉ cardSet n ⇒ m+1 ≤ f n"
runs through FOUR shapes, all confirmed against the official `cardSet`/`f`
(DM107_Official:42–47 ≡ B:100–105; vendor U435:65–70 is the same predicate modulo the
`NonTrilinear` packaging, bridged by `B:180 nonTrilinear_iff : Iff.rfl`):

1. **¬mem shape** (`eight_not_mem_cardSet_five : (8:ℕ) ∉ cardSet 5`, Bp:732):
   membership `N ∈ cardSet n` unfolds definitionally to
   `∀ pts : Finset ℝ², pts.card = N → NonTrilinear ↑pts → HasConvexNGon n pts`;
   applying it to the witness (`esEightFinset`, card = 8, NonTrilinear) and the
   no-pentagon theorem yields False. Same for `four_not_mem_cardSet_four`.
2. **Upward closure** (`cardSet_upward_closed : N₁ ≤ N₂ → N₁ ∈ cardSet n → N₂ ∈ cardSet n`,
   U435:215): subsets of a GP set are GP (`nonTrilinear_mono`), `Finset.exists_subset_card_eq`
   cuts the point set down; monotone transport `hasConvexNGon_mono_pts`. This converts
   "8 ∉ cardSet 5" into `nine_le_of_mem_cardSet_five : N ∈ cardSet 5 → 9 ≤ N` (Bp:740,
   by_contra + omega) — and, rewritten identically, into `five_le_of_mem_cardSet_four`.
3. **sInf lower bound** (`nine_le_f_five : 9 ≤ f 5`, Bp:749):
   `le_csInf (nonempty_cardSet_all 5) (fun _ hN => nine_le_of_mem_cardSet_five hN)` —
   ℕ's `ConditionallyCompleteLattice` `le_csInf` needs the Nonempty witness, supplied by
   `nonempty_cardSet_all` (B:1549 clone; itself `erdosSzekeresUpper n ∈ cardSet n` for
   n ≥ 3 — this is why the B §6–§12 machinery is in the cone even for the lower targets).
4. **sInf upper bound** (`f 4 ≤ 5`): `Nat.sInf_le five_mem_cardSet_four`
   (B-attested at B:1429); `f_le_erdosSzekeresUpper` (B:1434) the same for the n=5 upper.

**Def/type check vs official**: `cardSet : ℕ → Set ℕ` predicate identical; `f :=
sInf (cardSet n)` `noncomputable` identical; `HasConvexNGon`
(`∃ S : Finset ℝ², S.card = n ∧ ↑S ⊆ P ∧ ConvexIndep S`) and `ConvexIndep`
(`∀ a ∈ S, a ∉ convexHull ℝ (S \ {a})`) identical; vendor `Plane` abbrev =
`EuclideanSpace ℝ (Fin 2)` = FC scoped `ℝ²` (drop the abbrev, B's pattern). All types
`Type 0`, no universes. **No bridging needed beyond B's GREEN `nonTrilinear_iff` pattern**
(the vendor's explicit 6-binder `NonTrilinear` applications like `hnt x y z hxy hyz hxz`
unfold definitionally through `Set.Triplewise` — B's GREEN `self_mem_cardSet_of_le_three`
B:1376 runs exactly this application pattern over the official def).

---

## 4. THE PORT PLAN FOR DM107_Proof_C.lean (task D)

Standalone file, `lake env lean problem107-happy-ending/DM107_Proof_C.lean`, pattern =
B (which re-declares rather than imports — B header :52–67). Header: `import Mathlib`,
`import FC.Geometry.TwoD`, (+ `Arsenal.ErdosTernary2.Basic` if cloning B's
`nonempty_cardSet_all` verbatim), options exactly B:83–92
(`linter.deprecated/unnecessarySimpa/unusedSimpArgs/unnecessarySeqFocus false`,
`maxHeartbeats 800000`, `noncomputable section`, `open Filter EuclideanGeometry`),
then `namespace Erdos107C`.

| § | Content | Source | Est. lines |
|---|---|---|---|
| header | docstring + imports + options | — | 90 |
| §0 | official defs `cardSet`/`f` verbatim | B:96–105 | 10 |
| §1–§12 | **B-clone**: point arithmetic, NonTrilinear bridge, slope calculus, lineSide, half-plane separation, cup/cap chains + ES pigeonhole core + `erdosSzekeresUpper`, IsCupSet/IsCapSet, x-sorting, shear, small base cases, ES theorem + membership, `f_le_erdosSzekeresUpper` | B:107–1447, ns-swap only | 1350 |
| §13 | B-clone: `erdosSzekeresConjectured` def + `nonempty_cardSet_all`/`nonempty_cardSet` | B:1464–1467, 1545–1563 | 25 |
| §14 | FRESH: `lineSide_pos_or_neg_of_not_collinear`, `lineSide_sep_of_neg_pos`, `convexIndep_four_of_strict_sep`, `_of_opposite_diagonals`, `_of_pos_same_open_side`, `_of_same_open_side`, `pigeonhole_three_signs`, `three_vertices_same_open_side_of_line`, `hasConvexFourGon_of_same_open_side_edge`, `hasConvexFourGon_of_triangle_two_interior` | U435:1773–1962 + 1097–1148 | 210 |
| §15 | FRESH: InPosTriangle calculus (def + 9 lemmas) | Bp:85–244 | 140 |
| §16 | FRESH: Klein 4-pt witness + `nonTrilinear_mono`, `hasConvexNGon_mono_pts`, `cardSet_upward_closed`, `not_collinear_of_cross_ne_zero`, `four_not_mem_cardSet_four`, rewritten `five_le_of_mem_cardSet_four`, `five_le_f_four` | U435:49–223(sub), 364–511 | 145 |
| §17 | FRESH: Klein 5-pt theorem → `five_mem_cardSet_four` → `f_four_eq_five_of_mem_cardSet` → `f_four_eq_five`/`_unconditional` | Bp:246–461 + U435:1610–1615 | 200 |
| §18 | FRESH: `f_three_eq` (official anchor, verbatim) | DM107_Official:101–134 | 32 |
| §19 | FRESH: 8-pt witness block → `eight_not_mem_cardSet_five` → `nine_le_of_mem_cardSet_five` → `nine_le_f_five` | Bp:519–757 (minus the 4 excluded cap/cup lemmas) | 205 |
| §20 | FRESH: **the three targets** (`f_eq_conjectured_of_le_four`, `conjectured_lower_bound_of_le_five`, `ersz_bounds_of_le_five` — vendor signatures) + honest scope marker (open core `erdos_107` NOT claimed; lower side claimed only n ≤ 5, per B §15's ledger discipline) | Bp:769–801 | 45 |
| footer | `#print axioms` (the 3 targets + `f_three_eq`, `f_four_eq_five_unconditional`, `five_mem_cardSet_four`, `nine_le_f_five`, `not_hasConvexFiveGon_esEightFinset`, `f_le_erdosSzekeresUpper`, `nonempty_cardSet`) + `#eval "DM107C_LOWER_GREEN"` | — | 25 |

**Line estimate: ~2450 lines (range 2350–2600).** CI wiring: new step in the `kernel-dm-*`
job family mirroring the 107DM-B step (`lake build FC` (+ Arsenal if used) →
`lake env lean …/DM107_Proof_C.lean` → `! grep -E 'error:|sorryAx|…'` →
`grep -F "DM107C_LOWER_GREEN"` → `#print axioms` greps for the three targets).

Ordering constraint: §14 before §17 (separation base); §15 before §16/§17/§19
(`not_convexIndep_of_inPosTriangle`); §13 before §16/§19 (nonemptiness for `le_csInf`).
Statement shapes: use the vendor/Solution.lean signatures verbatim
(`∀ n, 3 ≤ n → n ≤ 4 → f n = 2 ^ (n - 2) + 1` etc. — Solution.lean:69–78 is the
entry-point form; note Bp:773 uses implicit `{n}` — either is faithful, recommend the
explicit `∀ n` form quoted in the mission).

---

## 5. TOP-3 PORTING RISKS + MITIGATIONS

**RISK 1 (MEDIUM — the only math-bearing exposure): the 4096-case `decide` blocks.**
`esEight_cap_triple_with_cup_pt` / `esEight_cup_triple_with_cap_pt` (Bp:635/645) are
`decide` over `∀ i j k u : Fin 8` with three integer 2×2-determinants each (plus
`esEightCross_ne_zero_of_distinct`, 512 triples, and `esEightX_ne_of_ne`, 64 pairs).
The vendor compiled these at v4.35.0-rc2 with `maxHeartbeats 800000`; B's GREEN run does
NOT attest this pattern (B only decides closed ℕ goals), and v4.33 kernel evaluation of
`![…]` matrix literals + `Fintype.decidableForallFintype` instances on slow CI runners is
the one place the port could time out. **Mitigation**: keep the vendor's
`set_option maxHeartbeats 800000` header; if a decide blows: (a) split each ∀ into two
lemmas (fix the cap/cup half: 4·8·8·8 → 2048 cases each), (b) `exact Decidable.decide …`
with an explicitly-instanced `Fin 8` decidable, or (c) worst case, enumerate the finite
index set as an explicit `decide`-checked list of `Fin 8` literals. The math is integer
arithmetic only — no ℚ/ℝ inside the Decidable instances — so this is a
heartbeats/compilation issue, never a correctness issue.

**RISK 2 (MEDIUM-LOW, scale not math): the ~1375-line namespace-swap clone of B §0–§14.**
Mechanical but error-prone: every internal reference must resolve inside `Erdos107C`,
and the §6–§9 cup/cap/shear machinery is densely interdependent. A missed or cherry-
picked lemma produces `unknown identifier` cascades. **Mitigation**: copy B's text
VERBATIM in one pass (it is CI-GREEN as a unit), change only the `namespace` line, and
keep ALL of B's header `set_option`s (the deprecated `Set.image_diff` alias at B:1241
needs `linter.deprecated false`, exactly as B:83). Do NOT cherry-pick out of §6–§9.

**RISK 3 (LOW): v4.35→v4.33 API/simp drift in the fresh ports.**
Every named Mathlib/FC lemma in the fresh cone was verified present in the v4.33.0-rc2
tree (see §1 table; `Finset.exists_subset_card_eq` Card.lean:664, `card_eq_succ` :776,
`card_eq_three` :789, `eq_of_subset_of_card_le` :282, `card_pos` :78, `card_sdiff_add_card_eq_card` :592
[with the subset hypothesis the vendor passes], `subset_image_iff` Image.lean:717,
`mem_image_of_mem` :297, `Int.cast_inj` Int/Cast/Lemmas.lean:67, the convex-hull trio
Hull.lean:50/53/70, `convexHull_subset_affineSpan` :202, `collinear_iff_of_mem`/
`collinear_pair` AffineSpace/FiniteDimensional.lean:456/502, `Set.encard_coe_eq_coe_finsetCard`
Set/Card.lean:93; FC `Set.Triplewise`/`triplewise_of_encard_lt` FC/Data/Set/Triplewise.lean:26/59).
Residual exposure is unnamed: a `simp`/`simpa` that closed at v4.35 leaving a goal at
v4.33 (e.g. the 4-element Finset card simplifications in `kleinFourPts_card`, the
`Finset.coe_insert/coe_singleton` pushes in the case bashes). **Mitigation**: the fresh
proofs use only tactic idioms B already runs GREEN at v4.33 (`dsimp [lineSide]; ring`,
`linarith`, `ext i; fin_cases i <;> simp only [PiLp.…]; field_simp`, `rcases`, `omega`,
`norm_num [mkPt_zero, mkPt_one]`); every residual simp failure is a one-line fix (add
the missing lemma name to the explicit simp set). Module-system leftovers (`module`,
`@[expose] public section`, `public import`) exist only in the vendor files — strip on
port (B's established transformation).

---

## 6. ADVERSARIAL CHECK — SORRY/AXIOM SCAN (task E)

- `rg '\b(sorry|admit|native_decide|axiom)\b'` over ALL four vendor files
  (Solution.lean, Blueprint107.lean, Erdos107Unified435.lean,
  InductiveKCupKCap107.lean, XMonotonePerturbation107.lean, Statement.lean):
  **ZERO code hits.** The only matches are the doc phrases "zero-`sorry`" at
  Blueprint107.lean:76 and XMonotonePerturbation107.lean:59.
- Every theorem in the traced cone carries a `#print axioms` line in the vendor
  (Bp:780, 792, 801, …; U435 throughout) — the vendor itself audits axiom-cleanliness.
- No `set_option maxRecDepth`/`Trust`compiler hacks, no `native_decide`, no `@[implemented_by]`,
  no `unsafe`, no `partial` in the cone.
- Upstream provenance is pinned (linrock/math-proofs @ cd3cf0b, Apache-2.0, vendored
  verbatim — B header :17–25), and the same chain is already half-landed GREEN in this
  campaign (B §0–§12 = the identical cone, CI-verified).
- **No sorry in the cone. Not a mission-killer — the cone is complete and closed.**

---

## 7. CLOSING LEDGER (for the kernel writer)

- Copy order: header → §0–§13 (B-clone, one verbatim pass, ns-swap) → §14 (U435
  separation block) → §15 (Blueprint §1) → §16 (Klein 4-pt + closure) → §17 (Klein
  5-pt + f 4 = 5) → §18 (official f 3 = 3) → §19 (esEight) → §20 (targets) → footer.
- The two deliberate deviations from the vendor (both recorded, statement-preserving):
  (1) `f_three_eq` from the GREEN official anchor instead of the vendor's parabola
  route; (2) `five_le_of_mem_cardSet_four` rewritten via upward closure instead of
  `le_of_mem_cardSet` — together they delete the entire parabola sub-cone (~45 lines)
  and replace it with CI-attested material.
- Everything else is a verbatim port of vendor proofs over B's GREEN §0 skeleton.
- Ship it.
