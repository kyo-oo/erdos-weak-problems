# DISCOVERY — Task 2-b: Six-Adic Universe + Transport Map

Complete inventory of the SIX-ADIC universe: every def/theorem in the four
`GSTGraphV2SixAdic*` files, plus the adic-related sections of the monolith
`ErdosTernary2.lean` (via `/home/z/agent-work/digest/ADIC.txt`, line numbers
are the monolith's own). Statement text is quoted/normalized exactly as seen.

Sources (only these were read):
1. `src/GSTGraphV2SixAdicOntologicalGeometry.lean` (70 lines)
2. `src/GSTGraphV2SixAdicOntologicalGeometryLaws.lean` (232 lines)
3. `src/GSTGraphV2SixAdicUnitIsometry.lean` (80 lines)
4. `src/GSTGraphV2SixAdicSynchronizedShadows.lean` (228 lines)
5. `digest/ADIC.txt` (19 extracted sections of the 17,041-line monolith)

Namespace abbreviations: GEO = `GSTGraphV2SixAdicOntologicalGeometry`,
LAW = `GSTGraphV2SixAdicOntologicalGeometryLaws`,
ISO = `GSTGraphV2SixAdicUnitIsometry`,
SYN = `GSTGraphV2SixAdicSynchronizedShadows`.

---

## PART A — GEOMETRY (GEO, `GSTGraphV2SixAdicOntologicalGeometry.lean`)

Core relation is *exact divisibility* `6^k ∣ (x − y)` over `Int`; no analytic
completion. Seven-axis vertex ontology untouched; six-adic layer is an overlay.

| # | Name | Kind | Exact statement | File:line |
|---|------|------|-----------------|-----------|
| A1 | `SixAdicIsoAt` | def | `(k : Nat) (x y : Int) : Prop := ∃ q : Int, x - y = (6 : Int) ^ k * q` | GEO:23–24 |
| A2 | `DyadicShadowAt` | def | `(k : Nat) (x y : Int) : Prop := ∃ q : Int, x - y = (2 : Int) ^ k * q` | GEO:27–28 |
| A3 | `TriadicShadowAt` | def | `(k : Nat) (x y : Int) : Prop := ∃ q : Int, x - y = (3 : Int) ^ k * q` | GEO:31–32 |
| A4 | `SixAdicBall` | def | `(k : Nat) (c : Int) : Set Int := {x | SixAdicIsoAt k x c}` | GEO:35–36 |
| A5 | `sixChildCenter` | def | `(k : Nat) (c : Int) (j : Fin 6) : Int := c + (j.val : Int) * (6 : Int) ^ k` — the six canonical refining centers (offsets = residues mod 6) | GEO:40–41 |
| A6 | `GraphIsoAt` | def | `(k : Nat) (G H : GSTGraphV2NonEuclidean.Graph) : Prop := SixAdicIsoAt k (G.energy : Int) (H.energy : Int)` | GEO:45–47 |
| A7 | `physicalEnergy` | def | `(P : GSTGraphV2NonEuclidean.PhysicalProjection) : Int := (4 : Int) ^ P.x4Phase * (P.sourceEnergy : Int)` — **the 4^K / x4-phase chart** | GEO:50–52 |
| A8 | `PhysicalProjectionIsoAt` | def | `(k : Nat) (P Q : …PhysicalProjection) : Prop := SixAdicIsoAt k (physicalEnergy P) (physicalEnergy Q)` | GEO:55–57 |
| A9 | `ResolvedGraph` | structure | `where ambient : GSTGraphV2NonEuclidean.Graph; resolution : Nat` | GEO:60–62 |
| A10 | `resolvedVertex` | def | `(G : ResolvedGraph) (p : Nat) : Vertex := GSTGraphV2NonEuclidean.vertex G.ambient p` (overlay never changes the selected vertex) | GEO:66–68 |

---

## PART B — LAWS (LAW, `GSTGraphV2SixAdicOntologicalGeometryLaws.lean`)

### B.1 Equivalence + non-Archimedean threshold laws
| # | Name | Exact statement | File:line |
|---|------|-----------------|-----------|
| B1 | `six_iso_refl` | `(k : Nat) (x : Int) : SixAdicIsoAt k x x` | LAW:24–26 |
| B2 | `six_iso_symm` | `{k x y} (h : SixAdicIsoAt k x y) : SixAdicIsoAt k y x` | LAW:28–35 |
| B3 | `six_iso_trans` | `{k x y z} (hxy : … x y) (hyz : … y z) : SixAdicIsoAt k x z` | LAW:37–46 |
| B4 | `six_iso_nonarchimedean` | `{k x y z} (hxy) (hyz) : SixAdicIsoAt k x z` (= `six_iso_trans`; threshold form of strong triangle law) | LAW:50–53 |
| B5 | `six_iso_translate` | `(k a x y) (h : SixAdicIsoAt k x y) : SixAdicIsoAt k (a + x) (a + y)` | LAW:55–62 |
| B6 | `six_iso_neg` | `(k x y) (h) : SixAdicIsoAt k (-x) (-y)` | LAW:64–72 |
| B7 | `six_iso_mul` | `(k a x y) (h) : SixAdicIsoAt k (a * x) (a * y)` (non-expansive chart multiplication) | LAW:74–82 |
| B8 | `six_iso_scale_six` | `{k x y} (h : SixAdicIsoAt k x y) : SixAdicIsoAt (k+1) (6*x) (6*y)` (×6 raises resolution exactly one level) | LAW:85–93 |
| B9 | `six_iso_weaken` | `{k x y} (h : SixAdicIsoAt (k+1) x y) : SixAdicIsoAt k x y` | LAW:97–103 |

### B.2 Dyadic / triadic shadow projections
| # | Name | Exact statement | File:line |
|---|------|-----------------|-----------|
| B10 | `six_iso_to_dyadic` | `{k x y} (h : SixAdicIsoAt k x y) : DyadicShadowAt k x y` | LAW:107–116 |
| B11 | `six_iso_to_triadic` | `{k x y} (h : SixAdicIsoAt k x y) : TriadicShadowAt k x y` | LAW:118–127 |

### B.3 Non-Euclidean ball laws
| # | Name | Exact statement | File:line |
|---|------|-----------------|-----------|
| B12 | `six_ball_center` | `(k c) : c ∈ SixAdicBall k c` | LAW:131–132 |
| B13 | `six_ball_recenter` | `{k c x} (hxc : x ∈ SixAdicBall k c) : SixAdicBall k x = SixAdicBall k c` | LAW:134–145 |
| B14 | `intersecting_equal_radius_balls_eq` | `{k c d} (h : (SixAdicBall k c ∩ SixAdicBall k d).Nonempty) : SixAdicBall k c = SixAdicBall k d` (equal-radius balls disjoint or identical) | LAW:148–156 |
| B15 | `six_ball_nested` | `(k c) : SixAdicBall (k+1) c ⊆ SixAdicBall k c` | LAW:159–162 |

### B.4 Six-way rooted refinement
| # | Name | Exact statement | File:line |
|---|------|-----------------|-----------|
| B16 | `six_child_center_in_parent` | `(k c) (j : Fin 6) : sixChildCenter k c j ∈ SixAdicBall k c` | LAW:166–171 |
| B17 | `six_child_centers_injective` | `(k c) : Function.Injective (sixChildCenter k c)` | LAW:174–182 |

### B.5 GST Graph V2 compatibility (merge surface)
| # | Name | Exact statement | File:line |
|---|------|-----------------|-----------|
| B18 | `graph_iso_refl` | `(k G) : GraphIsoAt k G G` | LAW:186–188 |
| B19 | `graph_iso_symm` | `{k G H} (h) : GraphIsoAt k H G` | LAW:190–192 |
| B20 | `graph_iso_trans` | `{k G H J} (hGH) (hHJ) : GraphIsoAt k G J` | LAW:194–197 |
| B21 | `x4_chart_preserves_six_iso` | `(k t E F : Nat) (h : SixAdicIsoAt k (E : Int) (F : Int)) : SixAdicIsoAt k ((4 : Int)^t * (E : Int)) ((4 : Int)^t * (F : Int))` — **every physical x4-phase (4^t) chart is six-adically non-expansive** | LAW:201–206 |
| B22 | `physical_projection_iso_exact` | `(k E F N M t s p q) : PhysicalProjectionIsoAt k (projectPhysicalCell E N t p) (projectPhysicalCell F M s q) ↔ SixAdicIsoAt k ((4:Int)^t * (E:Int)) ((4:Int)^s * (F:Int))` (by `rfl`) | LAW:210–218 |
| B23 | `resolved_vertex_axes_exact` | `(G : ResolvedGraph) (p) : (resolvedVertex G p).axes = GSTGraphV2NonEuclidean.axes G.ambient.energy G.ambient.horizon p` (resolution overlay leaves all seven axes untouched) | LAW:222–225 |
| B24 | `resolved_vertex_exact` | `(G) (p) : resolvedVertex G p = GSTGraphV2NonEuclidean.vertex G.ambient p` | LAW:228–230 |

---

## PART C — UNIT ISOMETRIES (ISO, `GSTGraphV2SixAdicUnitIsometry.lean`)

| # | Name | Exact statement | File:line |
|---|------|-----------------|-----------|
| C1 | `six_iso_translate_iff` | `(k a x y : Int) : SixAdicIsoAt k (a + x) (a + y) ↔ SixAdicIsoAt k x y` — translation is a genuine six-adic isometry (both directions) | ISO:13–22 |
| C2 | `six_iso_mul_reflect_of_mod_inverse` | `{k a b c x y} (hinv : b * a = 1 + (6 : Int)^k * c) (h : SixAdicIsoAt k (a*x) (a*y)) : SixAdicIsoAt k x y` — reflection for multipliers with explicit mod-inverse certificate `b*a = 1 + 6^k*c` | ISO:29–42 |
| C3 | `six_iso_mul_iff_of_mod_inverse` | `{k a b c x y} (hinv : b * a = 1 + (6 : Int)^k * c) : SixAdicIsoAt k (a*x) (a*y) ↔ SixAdicIsoAt k x y` — certified unit = true isometry at level k | ISO:46–53 |
| C4 | `six_scale_exact_iff` | `{k x y} : SixAdicIsoAt (k+1) (6*x) (6*y) ↔ SixAdicIsoAt k x y` — ×6 is an exact similarity of the resolution tree, both directions | ISO:58–69 |

(`#print axioms` checks at ISO:71–78 confirm all four are axiom-clean.)

---

## PART D — SHADOW SYNCHRONIZATION (SYN, `GSTGraphV2SixAdicSynchronizedShadows.lean`)

CRT-style synchronization: six-adic = simultaneous dyadic + triadic at the
SAME depth; plus the exact skew action of the physical 4^t chart.

| # | Name | Exact statement | File:line |
|---|------|-----------------|-----------|
| D1 | `dyadic_triadic_to_six` | `{k x y} (h2 : DyadicShadowAt k x y) (h3 : TriadicShadowAt k x y) : SixAdicIsoAt k x y` (uses `IsCoprime.mul_dvd`) | SYN:19–40 |
| D2 | `six_iso_iff_synchronized_shadows` | `{k x y} : SixAdicIsoAt k x y ↔ DyadicShadowAt k x y ∧ TriadicShadowAt k x y` | SYN:44–52 |
| D3 | `six_ball_membership_iff_shadows` | `{k c x} : x ∈ SixAdicBall k c ↔ DyadicShadowAt k x c ∧ TriadicShadowAt k x c` | SYN:56–60 |
| D4 | `triadic_shadow_mul_four_pow_iff` | `(k t : Nat) (x y : Int) : TriadicShadowAt k ((4:Int)^t * x) ((4:Int)^t * y) ↔ TriadicShadowAt k x y` — **×4^t is a genuine isometry of every triadic shadow (4 is a unit mod every 3^k)** | SYN:68–89 |
| D5 | `dyadic_shadow_mul_four_pow_iff` | `(k t) (hkt : 2*t ≤ k) (x y) : DyadicShadowAt k ((4:Int)^t*x) ((4:Int)^t*y) ↔ DyadicShadowAt (k-2*t) x y` (below saturation, ×4^t = ×2^(2t) shifts dyadic resolution by exactly 2t) | SYN:93–127 |
| D6 | `six_iso_mul_four_pow_iff_skew_shadows` | `(k t) (hkt : 2*t ≤ k) (x y) : SixAdicIsoAt k ((4:Int)^t*x) ((4:Int)^t*y) ↔ DyadicShadowAt (k-2*t) x y ∧ TriadicShadowAt k x y` | SYN:131–137 |
| D7 | `dyadic_shadow_zero` | `(x y : Int) : DyadicShadowAt 0 x y` | SYN:140–143 |
| D8 | `dyadic_shadow_mul_four_pow_of_saturated` | `(k t) (hkt : k ≤ 2*t) (x y) : DyadicShadowAt k ((4:Int)^t*x) ((4:Int)^t*y)` — **once 4^t supplies ≥ k dyadic factors, the dyadic shadow is saturated (no residual condition)** | SYN:147–167 |
| D9 | `dyadic_shadow_mul_four_pow_iff_truncated` | `(k t x y) : DyadicShadowAt k ((4:Int)^t*x) ((4:Int)^t*y) ↔ DyadicShadowAt (k-2*t) x y` (truncated Nat subtraction; both branches) | SYN:171–184 |
| D10 | `six_iso_mul_four_pow_iff_truncated_skew_shadows` | `(k t x y) : SixAdicIsoAt k ((4:Int)^t*x) ((4:Int)^t*y) ↔ DyadicShadowAt (k-2*t) x y ∧ TriadicShadowAt k x y` — **exact six-adic information retained by the x4 chart at EVERY exponent: full triadic depth, dyadic depth shifted by truncated 2t** | SYN:188–194 |
| D11 | `six_pow_dvd_four_pow_mul_sub_iff_truncated` | `(k t x y) : (6:Int)^k ∣ (4:Int)^t*(x-y) ↔ (3:Int)^k ∣ x-y ∧ (2:Int)^(k-2*t) ∣ x-y` — boxed divisibility form of the skew law | SYN:199–225 |

---

## PART E — MONOLITH ADIC SECTIONS (ErdosTernary2.lean, via digest/ADIC.txt)

### E.1 Ternary digit predicates and the K ≥ 5 boundary
| # | Name | Kind | Exact statement | Monolith line |
|---|------|------|-----------------|---------------|
| E1 | `noTernaryTwo` | def | `(n : Nat) : Bool := if n = 0 then true else if n % 3 = 2 then false else noTernaryTwo (n / 3)` (structural recursion) | 147–151 |
| E2 | `noTernaryTwoStruct` | def | `: Nat → Nat → Bool \| _, 0 => true \| n, k+1 => if n = 0 then true else if n % 3 = 2 then false else noTernaryTwoStruct (n/3) k` | 157–161 |
| E3 | `noTernaryTwo_eq_struct` | thm | `(n k : Nat) (hk : n + 1 ≤ k) : noTernaryTwo n = noTernaryTwoStruct n k` | 164–165 |
| E4 | `erdos_exception_n8` | thm | `noTernaryTwo (2^8) = true` — **2^8 = 4^4 has NO ternary digit 2: the reason the four-power statement must start at K ≥ 5** | 846 |
| E5 | `mod_check_K16` | thm | `(a : Nat) (h_struct : hasTwoInFirstKStruct (powMod 4 a (3^16)) 16 = true) : hasTernaryTwo (4^a) = true` | 3019–3021 |
| E6 | `hasTwoInFirstK_imp_hasTernaryTwo` | thm | `(n k) (hn : n < 3^k) (h : hasTwoInFirstK n k = true) : hasTernaryTwo n = true` | 2977–2978 |
| E7 | `has_two_lift_base` | thm | `(m p : Nat) (hp : 1 ≤ p) (hm2 : m % 3 = 2) : hasTernaryTwo (1 + 3^p * m) = true` | 2962–2963 |

### E.2 Cardinal Worlds postulates + c/d towers (2-adic/3-adic dual towers)
| # | Name | Kind | Exact statement | Monolith line |
|---|------|------|-----------------|---------------|
| E8 | POSTULATE I (comment) | — | Bridge Signature: d(j) has a ternary digit 2 for all j ≥ 2, where `d(j) = (3^(2^j) − 1)/2^(j+2)` is the 2-adic dual of the c(j) tower. Status: proven for even j ≥ 2 and j ≡ 3 mod 6, + verification j ∈ [2,200] | 849–864 |
| E9 | POSTULATE II (comment) | — | Valuation Bound: primitive Cantor n (n>0, noTernaryTwo, n%3=1) ⇒ v2(n) ≤ ternaryLog3(n)+3. Status: proven n < 3^9; **universal case is the ONE remaining gap** | 857–868 |
| E10 | `d` | def | `(j : Nat) : Nat := if j = 0 then 1 else (3^(2^j) - 1) / 2^(j+2)` | 876–877 |
| E11 | `two_pow_pos` | thm | `(j) : 0 < 2^j` | 880–883 |
| E12 | `two_pow_factored` | thm | `(j) (hj : 1 ≤ j) : 2^j = 2 * 2^(j-1)` | 885–889 |
| E13 | `two_pow_ge2` | thm | `(j) (hj : 1 ≤ j) : 2 ≤ 2^j` | 891–896 |
| E14 | `three_pow_odd` | thm | `(j) : 3^(2^j) % 2 = 1` | 898–901 |
| E15 | `three_pow_sq` | thm | `(j) : (3^(2^j))^2 = 3^(2^(j+1))` | 903–906 |
| E16 | `sq_sub_one` | thm | `(a) (ha : 1 ≤ a) : a^2 - 1 = (a-1)*(a+1)` | 908–920 |
| E17 | `three_pow_2j_pos` | thm | `(j) : 0 < 3^(2^j)` | 922–925 |
| E18 | `two_dvd_three_pow_2j_plus_1` | thm | `(j) : 2 ∣ 3^(2^j) + 1` | 927–931 |

### E.3 THE CARRY MACHINE — h_creation / GST duality (the witness engine)
Notation below: d_p(R) := R / 3^p % 3 (ternary digit), C(p) := (4*(R % 3^p))/3^p (carry).

| # | Name | Exact statement | Monolith line |
|---|------|-----------------|---------------|
| E19 | `gst_duality` | `(R : Nat) (hR_mod3 : R % 3 = 1) (hR_has : hasTernaryTwo R = true) (h_creation : ∃ p, 1 ≤ p ∧ R / 3^p % 3 = 2 ∧ ((4*(R % 3^p))/3^p % 3 = 0 ∨ ((4*(R % 3^p))/3^p % 3 = 1 ∧ R / 3^(p+1) % 3 = 2))) : hasTernaryTwo (4 * R) = true` — **Full GST Duality: the carry wave theorem (Infinite Paradox)** | 3892–3896 |
| E20 | `gst_duality_carry0` / `gst_duality_carry1` | (referenced) the two branches of E19 | 3899–3901 |
| E21 | `h_creation_4pow_survive` | `(k : Nat) (hk5 : 5 ≤ k) (hv3k : 1 ≤ v3 k) (hb3 : (k / 3^(v3 k)) % 3 = 2) : ∃ p : Nat, 1 ≤ p ∧ (4^k) / 3^p % 3 = 2 ∧ ((4 * ((4^k) % 3^p)) / 3^p % 3 = 0 ∨ ((4 * ((4^k) % 3^p)) / 3^p % 3 = 1 ∧ (4^k) / 3^(p+1) % 3 = 2))` — **THE digit-2 witness theorem for 4^k, k ≥ 5 (SURVIVE case: v3(k) ≥ 1, leading trit ≡ 2)** | 3910–3914 |
| E22 | `h_creation_cascade_lift` | `(k s m : Nat) (hs : 2 ≤ s) (hk : k = 3^s * (1 + 3*m)) (p) (hp1 : 1 ≤ p) (hp_le : p ≤ s-1) (hd2 : (4^(3^(s+1)*m))/3^p % 3 = 2) (hcarry : …0 ∨ (…1 ∧ …(p+1)…=2)) : (4^k)/3^p % 3 = 2 ∧ (carry disjunction for 4^k)` — cascade transport of witnesses along `k = 3^s(1+3m)` | 6372–6381 |
| E23 | `carry_propagation` | (statement inferred from uses) `(R p) (hp : 1 ≤ p) : (4 * (R % 3^(p+1))) / 3^(p+1) = ((4 * (R % 3^p)) / 3^p + 4 * (R / 3^p % 3)) / 3` — **the digit-shift law: how digits of 4R arise from digits + carry of R** | used 4506, 4537, 4549, 4550 (def not in digest — RISK) |
| E24 | `carry_bound` | (statement inferred from uses) `(R p) (hp : 1 ≤ p) : (4*(R % 3^p))/3^p < 4` | used 4541, 4554, 4563 (def not in digest — RISK) |
| E25 | `carry_state_after_zero` | `(R p) (hp : 1 ≤ p) (h_c1 : C(p) = 1 ∨ 2 ∨ 3) (h_digit : R/3^p % 3 = 0) : C(p+1) = 0 ∨ C(p+1) = 1` | 4532–4535 |
| E26 | `carry_state_after_two` | `(R p) (hp : 1 ≤ p) (h_c1 : C(p) = 1 ∨ 2 ∨ 3) (h_digit : R/3^p % 3 = 2) : C(p+1) = 3` | 4545–4548 |
| E27 | `carry_in_123` | `(R p) (hp) (h_ne0 : C(p) ≠ 0) : C(p) = 1 ∨ C(p) = 2 ∨ C(p) = 3` | 4561–4562 |
| E28 | `bridge_forces_non_one` | `(R p N) (hp : 1 ≤ p) (hN : p < N) (h_state3 : C(p) = 3) (h_bridge : C(N) = 0) : ∃ j, p ≤ j ∧ j < N ∧ R / 3^j % 3 ≠ 1` — bridge forces non-one digits | 4513–4516 |
| E29 | `all_ones_imp_c1_false` | `(R start N) (hstart_lt : start < N) (hstart_pos) (hC_start_3) (hC_N_1) (hones : ∀ j, start ≤ j → j < N → R/3^j % 3 = 1) : False` | 6361–6366 |
| E30 | `bridge_carry_zero` | (inferred from use) `(k) (…) : (4 * ((4^k) % 3^(2*k))) / 3^(2*k) = 0` — **the bridge at 2k (i.e. at 6-adic-aligned depth 2k)** | used 6607–6608 (QUARANTINED context) |
| E31 | (inline) `4^k < 3^(2*k)` | `∀ n ≥ 1, 4^n < 9^n` induction — the bridge inequality | 6617–6631 (QUARANTINED context) |

### E.4 QUARANTINED legacy universal chain (commented-out block)
| # | Name | Exact statement | Monolith line |
|---|------|-----------------|---------------|
| E32 | `gst_four_pow_lt_three_pow_twice` | `(k) (hk : 1 ≤ k) : 4^k < 3^(2*k)` | 7490–7513 (inside `/- -/` block: QUARANTINED) |
| E33 | `gst_digit_two_position_lt_twice` | `(k p) (hk : 1 ≤ k) (hd : gstDigit (4^k) p = 2) : p < 2*k` — **witness positions live below the 2k bridge** | 7515–7521 (QUARANTINED) |
| E34 | (quarantine markers) | `BEGIN QUARANTINED LEGACY UNIVERSAL CHAIN` at 6420; `QUARANTINED LEGACY RESIDUAL OMEGA END` at 7486 — the universal h_creation/Ω chain is currently DISABLED | 6420, 7486 |

### E.5 Ω∞ navigation, residual termination (the wave skeleton in the monolith)
| # | Name | Kind | Exact statement | Monolith line |
|---|------|------|-----------------|---------------|
| E35 | `GSTNaturalExponentCone` | def | `(t : Nat) : Set Nat := {m | m < 3^t}` | 7221–7222 |
| E36 | `gst_natural_exponent_mem_terminal_cone` | thm | `(m) : m ∈ GSTNaturalExponentCone m` | 7226–7228 |
| E37 | `gst_natural_exponent_descent_terminates` | thm | `(m) : m / 3^m = 0` | 7231–7233 |
| E38 | `gst_omega_descent_terminates_at_child_value` | thm | `(s k m) : let T := gstNavigationConstant (s+k) m; (gstOmega s k m T).descent = 0` | 7237–7239 |
| E39 | `GSTOmegaChildZeroSet` | def | `(s k m) : Set Nat := {j | (gstOmega s k m j).childDigit = 2 ∧ ((gstOmega s k m j).childCarry = 0 ∨ = 3)}` — **child Happy-Gate set: digit-2 with carry 0 or 3** | 7246–7249 |
| E40 | `gst_omega_childZeroSet_nonempty_of_navigation_witness` | thm | `(s k m) (hchild : GSTNavigationWitness (gstNavigationConstant (s+k) m)) : (GSTOmegaChildZeroSet s k m).Nonempty` — **existence of digit-2 Happy-Gate witnesses** | 7252–7255 |
| E41 | `gst_residual_origin_parameter_strict` | thm | `(k m) (hk : 1 ≤ k) (hm : 1 ≤ m) : m < 1 + 3^k*m` | 7273–7276 |
| E42 | `gst_residual_origin_descent_certificate` | thm | `(s k m) (hs) (hk) (hm) : gstNavigationConstant s (1 + 3^k*m) = c s + 3^k * 4^(3^s) * gstNavigationConstant (s+k) m ∧ …` | 7282–7285 |
| E43 | `gst_omega_termination_s3` / `_stable` / `gst_residual_omega_termination` / `gst_residual_navigation_lift` | thm | Ω∞ termination stack: `¬ GSTOmegaInfiniteBadTrace s k m` for s=3, s≥2 s≠3, then `GSTResidualOmegaTermination`, `GSTResidualNavigationLift` | 7408, 7437, 7466, 7482 |

### E.6 Information geometry / bridge bounds (2-adic↔3-adic scale inequality)
| # | Name | Exact statement | Monolith line |
|---|------|-----------------|---------------|
| E44 | `four_pow_succ_lt_three_pow_doubleS` | `(N : Nat) (hN : 3 ≤ N) : 4^(N+1) < 3^(2*N)` — **exact 2-adic/3-adic scale inequality behind the GST bridge** | 9861–9884 |
| E45 | `gst_information_bridge_boundS` | `(S A N) (hN : 3 ≤ N) (hA : A = 4^N) (hS : S < 4*A) : S < 3^(2*N)` | 9887–9892 |
| E46 | `gst_information_bridge_nullS` | `(S A N) (hN) (hA) (hS) : S / 3^(2*N) = 0` (finite NULL boundary at aligned bridge depth) | 9902–9908 |
| E47 | `gst_affine_block_memoryS` | `(z A c D T) (hD : 0 < D) (hA : A = 1 + D*c) : (z + A*(T % D)) / D = c*(T % D) + (z + T % D) / D` — exact block-memory identity | 9131–9134 |
| E48 | `gst_affine_tail_div_decompositionS` | `(z A T q) : (z + A*T) / 3^q = gstAffineMulCarryS A z T q + A*(T / 3^q)` | 9145–9148 |
| E49 | `gst_shared_information_carry_equationS` | `(A z T q) : gstAffineMulCarryS A (1+4*z) (4*T) q + A*gstCarryS T q = gstAffineMulCarryS 4 1 (z + A*T) q + 4*gstAffineMulCarryS A z T q` — **conserved coupling of the R-chart and 4R-chart realizations** | 9164–9167 |
| E50 | `gst_affine_carry_lt_multiplierS` | `(A z T q) (hA : 0 < A) (hz : z < A) : gstAffineMulCarryS A z T q < A` | 9186–9188 |

### E.7 Pure-power axis + exponent-trit lift (LTE block)
| # | Name | Exact statement | Monolith line |
|---|------|-----------------|---------------|
| E51 | `gst_pow4_mod3_oneS` | `(m : Nat) : 4^m % 3 = 1` — **digit-0 of every 4^m is 1, never 2 (forces p ≥ 1)** | 12426–12428 |
| E52 | `gst_pow4_exponent_lift_one_digitS` | `(p m c) (hA : 4^(3^p) = 1 + 3^(p+1)*c) (hc : c % 3 = 1) : gstDigitS (4^(m + 3^p)) (p+1) = (gstDigitS (4^m) (p+1) + 1) % 3` — **one exponent trit 3^p shifts the exposed power digit by one** | 12432–12437 |
| E53 | `gst_pow4_exponent_lift_two_digitS` | `(p m c) (hA) (hc) : gstDigitS (4^(m + 2*3^p)) (p+1) = (gstDigitS (4^m) (p+1) + 2) % 3` | 12454–12459 |
| E54 | `gst_pow4_exponent_trit_lift_digitS` | `(p m c a) (ha : a < 3) (hA) (hc) : gstDigitS (4^(m + a*3^p)) (p+1) = (gstDigitS (4^m) (p+1) + a) % 3` — unified trit lift a ∈ {0,1,2} | 12471–12477 |
| E55 | `gst_prefix_one_pure_power_axisS` | `(A D c z T E) (hA : A = 1 + D*c) (hc : c = 1 + 3*z) (hE : E = 1 + 3*D*T) : 3*D*(z + A*T) + (1+D) = A*E` | 11165–11170 |
| E56 | `gst_prefix_one_pure_power_axis_powS` | `… (hApow : A = 4^N) (hEpow : E = 4^K) : 3*D*(z + A*T) + (1+D) = 4^(N+K)` | 11176–11183 |
| E57 | `gst_prefix_one_pure_two_axisS` | `… (hApow : A = 2^(2*N)) (hEpow : E = 2^(2*K)) : … = 2^(2*(N+K))` | 11190–11197 |
| E58 | `gst_canonical_prefix_one_recurrenceS` | `(Q : Nat → Nat → Nat) (hQ : GSTCanonicalOriginEnergyS Q) (t n) (ht : 1 ≤ t) : Q t (1 + 3*n) = Q t 1 + 3 * 4^(3^t) * Q (t+1) n` | 11209–11214 |
| E59 | `gst_canonical_prefix_one_energy_squareS` | `(Q) (hQ) …` (parent/child canonical energies form one exact commuting pure-power square) | 11221–11223 (partial in digest) |

### E.8 Pressure / finite-support / digit ceiling
| # | Name | Exact statement | Monolith line |
|---|------|-----------------|---------------|
| E60 | `gst_omega_pressure_no_unbounded_twoS` | `(t T) (hunbounded : ∀ M, ∃ j, M ≤ j ∧ gstDigitS T j = 2) : False` — fixed Ω energy forbids digit-2 information at arbitrarily high ternary heights | 11520–11523 |
| E61 | `gstOmegaNaturalTransferS` | def `(t T i) : Nat := 3^(t+1+i) * gstDigitS T i` | 11545–11546 |
| E62 | `gst_omega_natural_transfer_prefixS` | `(t T K) : (Finset.range K).sum (fun i => gstOmegaNaturalTransferS t T i) = 3^(t+1) * (T % 3^K)` | 11548–11551 |
| E63 | `gst_omega_natural_transfer_totalS` | `(t T) : (Finset.range (T+1)).sum … = 3^(t+1) * T` | 11565–11568 |
| E64 | `gst_omega_natural_transfer_is_energyS` | `(t T) : 1 + (Finset.range (T+1)).sum … = gstOmegaPressureEnergyS t T` | 11573–11576 |
| E65 | `natural_not_infinite_ternary_supportS` | `(n) : ¬ InfiniteTernarySupportS n` | 14087–14088 |
| E66 | `finite_origin_contradictionS` | `(n) (hforce : ∀ K, ∃ k, K ≤ k ∧ ternaryOriginDigitS n k ≠ 0) : False` | 14095–14098 |
| E67 | `gst_digit_zero_above_self_ceilingS` | `(X j) (hj : X + 1 ≤ j) : gstDigitS X j = 0` | 14144–14146 |
| E68 | `GSTSeededHappyS` | def `(D X j) : Prop := gstDigitS X j = 2 ∧ (gstAffineMulCarryS 4 D X j = 0 ∨ gstAffineMulCarryS 4 D X j = 3)` — **seeded Happy Gate = digit 2 with carry ∈ {0,3} (SURVIVE)** | 14107–14110 |
| E69 | `gst_exists_last_seeded_gate_belowS` | `(D X N) (hex : ∃ j, j < N ∧ GSTSeededHappyS D X j) : ∃ q, q < N ∧ GSTSeededHappyS D X q ∧ ∀ r, q < r → r < N → ¬ GSTSeededHappyS D X r` | 14113–14116 |

### E.9 RIGHT CHORD / 36-STATE CELL — the six-adic touchpoint in the monolith
Module comment (16032–16040): the local chord is `2 -> 2 -> 2`, `(m1,m2) = (5,5)`, `55_6 = 35 = 6^2 - 1`, `(C,w) = (3, 22_3) = (3,8)` — the GST+ SURVIVE/SURVIVE orientation.

| # | Name | Kind | Exact statement | Monolith line |
|---|------|------|-----------------|---------------|
| E70 | `GSTScopedTwoDigitBig1ClearS` | def | `(C d : Nat) : Prop := d ≠ 1 ∧ gstFirstMicroOutputS C d ≠ 1 ∧ gstSecondMicroOutputS C d ≠ 1` | 16044–16047 |
| E71 | `gst_scoped_two_digit_happy_gate_right_chordS` | thm | `(C d) (hC : C < 4) (hd : d < 3) (hhappy : d = 2 ∧ (C = 0 ∨ C = 3)) (hclear : GSTScopedTwoDigitBig1ClearS C d) : C = 3 ∧ d = 2 ∧ gstFirstMicroOutputS C d = 2 ∧ gstSecondMicroOutputS C d = 2 ∧ gstFirstMicroMassS C d = 5 ∧ gstSecondMicroMassS C d = 5 ∧ gstFirstMicroMassS C d + 6*gstSecondMicroMassS C d = 35 ∧ gstHandwrittenUJumpS C d = -6` — **the digit-2 Happy Gate hits the unique right chord with masses (5,5) and 5 + 6·5 = 35 = 6²−1** | 16051–16062 |
| E72 | `gst_scoped_right_chord_is_36_state_35S` | thm | the mixed-radix state selected by the chord is the maximal legal 36-state cell: carry 3 + ternary word 22 | 16076 (partial in digest) |
| E73 | `GSTCanonicalLocalRightChordS` | def | `(T q) : Prop := (… ∧ gstCarryS T q = 3 ∧ gstCarryS T (q+1) = 3 ∧ gstPhysicalMicroPairS T q = (5,5) ∧ … masses sum 35 ∧ UJump = −6) ∨ (…carry 0 → 2, pair (4,2), UJump = −8)` | 15604–15627 |
| E74 | `GSTCanonicalCrossingFailureCertificateS` | def | `(Q s n c z) : Prop := let A := 4^(3^s); let T := Q (s+1) n; let H := z + A*T; GSTSeededBadTraceS 1 H ∧ (∃ q, GSTSeededHappyS 0 T q ∧ GSTCanonicalLocalRightChordS T q) ∧ GSTCanonicalPhysicalTrapS Q s n c z` | 15631–15638 |
| E75 | `gst_canonical_crossing_failure_certificate_surgeryS` | thm | `(Q) (hQ : GSTCanonicalOriginEnergyS Q) (s n c z) (hs : 1 ≤ s) (hn : 1 ≤ n) (hA : 4^(3^s) = 1 + 3^(s+1)*c) : …` (atomic corrected surgery; no old duality/residual-Omega in proof) | 15644–15650 (partial) |

### E.10 Wave-merge surface (monolith ⇄ GST Graph V2)
| # | Name | Exact statement | Monolith line |
|---|------|-----------------|---------------|
| E76 | `gst_step6_terminal_packet_kernel` | `(s n) (hs : 1 ≤ s) (hn : 1 ≤ n) (hchild : GSTNavigationWitness (gstNavigationConstant (s+1) n)) (hBad : GSTOmegaInfiniteBadTrace s 1 n) : ∃ q, GSTU2DEventTransport.HappyCell (GSTGraphV2InfiniteControl.graph 1 (GSTGraphV2CanonicalNWave.nWaveShift s n (n+1)) (s+2+q)).seven.carry …seven.digit ∧ ∀ j, ¬ HappyCell …(nWaveShift … + GSTGraphV2PerfectPowerBlock.canonicalWidth s) (s+2+j)…` — **the certified terminal packet living ON the V2 graph waves: proves a child Happy Gate exists on the nWaveShift graph** | 16797–16817 |
| E77 | `gst_residual_null_second_trit_zero_or_twoS` | `(s n) (hs : 2 ≤ s) (hn : 1 ≤ n) (hn1 : n % 3 = 1) (hBad : GSTOmegaInfiniteBadTrace s 1 n) : (n/3) % 3 = 0 ∨ (n/3) % 3 = 2` | 10979–10983 |
| E78 | `gst_residual_prefix_one_no_bad_of_infinite_support_bridgeS` | `(hbridge : GSTCanonicalResidualInfiniteSupportBridgeS) (s n) (hs) (hn) (hn3 : n % 3 ≠ 0) (hchild) : ¬ GSTOmegaInfiniteBadTrace s 1 n` | 15991–15995 |
| E79 | `gst_residual_prefix_one_u_bad_contradiction_of_bridgeS` | `(hbridge) (s n) … (hBad : GSTOmegaInfiniteBadTrace s 1 n) : False` | 16001–16008 |

### E.11 Names referenced but NOT defined in the digest (must be verified before use)
`hasTernaryTwo`, `hasTwoInFirstK`, `hasTwoInFirstKStruct`, `powMod`,
`powMod_correct`, `hasTwoInFirstK_eq_struct`, `v3`, `pow_v3_dvd`,
`digit_identity`, `lte_identity`, `c`, `gstDigit`, `gstDigitS`, `gstCarry`,
`gstCarryS`, `gstAffineMulCarryS`, `gstNavigationConstant`, `gstOmega`,
`GSTNavigationWitness`, `GSTOmegaInfiniteBadTrace`,
`gstGoodSpace_carry_mod3_zero`, `gstCarry_lt_four`, `carry_bound`,
`carry_propagation`, `bridge_carry_zero`,
`gst_big1_projector_two_layer_forces_plus_surviveS`,
`gst_big1_projector_two_layer_chord_35S`, `gstMicroHighBitS`,
`gstMicroLowBitS`, `gstFirstMicroOutputS`, `gstSecondMicroOutputS`,
`gstFirstMicroMassS`, `gstSecondMicroMassS`, `gstHandwrittenUJumpS`,
`gstPhysicalMicroPairS`, `GSTPhysicalTwoDigitBig1ClearS`,
`GSTCanonicalPhysicalTrapS`, `GSTSeededBadTraceS`, `InfiniteTernarySupportS`,
`ternaryOriginDigitS`, `ternary_origin_eventually_zeroS`,
`gstOmegaPressureEnergyS`, `gstOmegaPressureTransferS`,
`three_pow_succ_gt_selfS`, `gst_three_pow_succ_gt_pressureS`,
`GSTGraphV2InfiniteControl`, `GSTGraphV2CanonicalNWave`,
`GSTGraphV2PerfectPowerBlock`, `GSTU2DEventTransport`.

---

## PART F — CONNECTORS: 6-adic structure ⇄ ternary digits ⇄ powers of 4

**F.1 physicalEnergy IS the 4^K chart.** GEO A7: `physicalEnergy P = 4^P.x4Phase * P.sourceEnergy`. Setting `x4Phase := K`, `sourceEnergy := 1` gives exactly the integer `4^K`. The axiom's `4^K` and `4^(K+1)` are two points of the same physical x4 chart one phase apart (`t → t+1`).

**F.2 The x4 chart is a triadic isometry.** D4 `triadic_shadow_mul_four_pow_iff`:
`TriadicShadowAt k (4^t x) (4^t y) ↔ TriadicShadowAt k x y` — since 4 is a unit
mod 3^k, ALL triadic (digit-carrying) resolution is preserved exactly by the
4^t phase multiplication. B21 `x4_chart_preserves_six_iso` is the non-expansive
six-adic half.

**F.3 The dyadic half is saturated — the axiom is purely triadic.** D8
`dyadic_shadow_mul_four_pow_of_saturated` (k ≤ 2t) + D10
`six_iso_mul_four_pow_iff_truncated_skew_shadows`: at any exponent t, the x4
chart retains FULL triadic depth k and dyadic depth k−2t. For the one-phase
step t = 1 and k ≤ 2, the dyadic shadow carries zero residual condition ⇒ the
entire discriminating content of a digit statement at depth k is its
`TriadicShadowAt k` component. **This is the "distinction proves itself"
point: placed in the six-adic universe, the four-power digit-2 statement
reacts as a purely triadic-shadow statement, transported by a genuine
isometry (F.2).**

**F.4 The digit-2 Happy Gate IS the maximal six-adic (36-state) cell.** E68
`GSTSeededHappyS`: digit 2 with carry ∈ {0,3}. E71/E72: that gate is exactly
the right chord 2→2→2 with masses (5,5), `5 + 6·5 = 35 = 6² − 1`, i.e.
`55₆ = 6² − 1`, the maximal legal 36-state cell — a base-6 (six-adic
resolution-2) object. The monolith's digit-2 witness and the SixAdic
universe's resolution-2 child structure (`sixChildCenter`, Fin 6) meet here.

**F.5 The carry machine is the triadic transport law.** E23
`carry_propagation` + E25/E26/E27 give the exact state machine
`C(p+1) = (C(p) + 4·d_p)/3` (for the values that occur): d_p = 2 sends
C ∈ {1,2,3} → C(p+1) = 3; combined with E49
`gst_shared_information_carry_equationS` (conserved coupling of the
R-chart and 4R-chart carries) this is the monolith form of "how the digit-2
witness moves when the x4 phase advances" — the same phenomenon F.2 describes
congruence-wise.

**F.6 The bridge at depth 2k.** E44 `four_pow_succ_lt_three_pow_doubleS`
(4^(N+1) < 3^(2N), N ≥ 3) and E31/E32 (4^k < 3^(2k)): all nonzero digits of
4^k live below position 2k; E30 `bridge_carry_zero` (C(2k) = 0); E33
`gst_digit_two_position_lt_twice` (digit-2 positions < 2k, quarantined). At
depth 2k the six-adic skew D10 with t = k gives dyadic 2k−2k = 0: the bridge
depth is exactly where the x4 chart's dyadic shift saturates.

**F.7 K ≥ 5 boundary.** E4 `erdos_exception_n8`: 4^4 has no ternary digit 2
at all, so no witness (common or otherwise) exists below K = 5. E51
`gst_pow4_mod3_oneS`: 4^m % 3 = 1, so position 0 is never a digit-2 witness
(p ≥ 1 in every statement).

**F.8 The exponent trit lift = LTE block.** E52–E54 with hA : `4^(3^p) =
1 + 3^(p+1)·c`, c ≡ 1 (mod 3) (see also `lte_identity` used at 6386):
digits of 4^K at position p+1 are shifted by the trits of K — the exact
3-adic LTE tower `v3(4^n − 1) = 1 + v3(n)` governing which K classes have
witnesses at which depths (hence the v3(k)/leading-trit hypotheses of E21).

**F.9 Wave merge surface already exists.** E76
`gst_step6_terminal_packet_kernel` puts Happy-Cells (digit-2 gates) directly
onto `GSTGraphV2InfiniteControl.graph` /
`GSTGraphV2CanonicalNWave.nWaveShift` / `GSTGraphV2PerfectPowerBlock` — the
monolith already feeds GST-Graph-V2 waves. The six-adic files are the V2
graph's resolution overlay. A 3rd wave extending `nWaveShift` with the
SixAdic resolution layer is the natural merge point (see PLAN.md).

**Gaps found (nothing in scope connects these yet):**
- NO theorem in the four SixAdic files mentions `digit3`/`gstDigit`/trits —
  the digit world lives only in the monolith. `digit3` itself never appears
  in the digest (only `gstDigit`/`gstDigitS`, evidently `n / 3^p % 3` — see
  E61/E62 where `T % 3^(K+1) = T % 3^K + 3^K * gstDigitS T K`).
- NO in-scope theorem explains the `K ≠ 7` exclusion of the axiom; K = 7 is
  covered by no special-case lemma in the digest.
- The universal h_creation coverage for all K ≥ 5 is QUARANTINED (E34).
