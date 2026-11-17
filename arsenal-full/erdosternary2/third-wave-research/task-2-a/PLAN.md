# PLAN.md — Task 2-a: The THIRD WAVE for `CommonTwo`

Goal: replace the custom axiom

```lean
gst_four_power_direct_existence_inline :
  GSTFourPowerDirectExistence.FourPowerDirectExistence
-- = ∀ K ≥ 5, K ≠ 7 → ∃ p ≥ 1, digit3 (4^K) p = 2 ∧ digit3 (4^(K+1)) p = 2
```

with a **theorem** derived inside the GST universe (V2 six-adic ontological
graph + the monolith's wave machinery), by constructing a **third wave** and
letting the established laws close it. Environment: Lean 4.33 + Mathlib.
No `sorry` / `admit` / `axiom` / `native_decide`; no `decide` on
`∀ k < N` with `N > 501`; all new helpers prefixed `wava_`.

---

## 0. Why a third wave exists to be built (the discovery that drives the plan)

Two facts already proven in the monolith, read together:

1. **`gst_seeded_happy_iff_common_twoS` (monolith 12215):** for any seed < 4
   (in particular seed = 0) and any word `H`,
   `gstDigitS H q = 2 ∧ (carry = 0 ∨ carry = 3) ↔ gstDigitS H q = 2 ∧ gstDigitS (seed + 4*H) q = 2`.
   A seed-zero Happy Gate **is literally a common digit-two of `H` and `4·H`**.
2. **`gst_pure_lift_or_forced_cascade` (monolith 4952):** a digit-two of `R`
   at `p ≥ 1` with carry 0 or 3 stays a digit-two of `4·R` at the **same** `p`
   in *both* disjuncts (GST+/NULL survive, ALT− is force-cascaded to carry 3
   at `p+1` — but the digit at `p` is 2 regardless).

With `gst_four_pow_adjacent (a) (ha : 1 ≤ a) : 4 * 4^(a-1) = 4^a`
(monolith 16973), `4^(K+1) = 4 · 4^K`. Hence

> **CommonTwo K ⟺ a GST+/NULL (Happy-Gate) digit-two vertex of `4^K` at some p ≥ 1
> ⟺ a Navigation-witness position of `4^K`** (`GSTNavigationWitness`, monolith 5120).

And the monolith already *proves as a theorem* the witness source for exactly
the axiom's exponent class: `gst_four_power_creation_master_inline`
(monolith 16933) — `∀ K ≥ 5, K ≠ 7 → CreationCertificate K`, feeding
`GSTFourPowerOntologicalAdapter.gst_four_power_ontological_navigation_of_master`
(used 16989) and `gst_navigation_witness_of_standalone_navigation`
(used 16992). So the axiom is a corollary of wave laws that are already green.
The third wave is the missing *packaging layer* that states the pair
`4^K, 4^(K+1)` as one wave object in the six-adic V2 universe and transports
the distinction through it.

---

## 1. What the third wave reuses (only names actually seen — see DISCOVERY.md)

**Wave-1 (carry) laws:**
- `gst_pure_lift_or_forced_cascade` (4952) — the survival law.
- `gstCarry_lt_four` (external; used 5147, 16999) — carry < 4.
- `gstGoodSpace_carry_mod3_zero` (external; used 5144, 16935, 16998) — GST+/NULL ⇒ carry % 3 = 0.
- `gstCarry_forward_exact_all` (6069), `gst_null_two_regenerates` (7759), `gst_plus_two_propagates` (7766) — optional cascade commentary.

**Wave-2 (navigation) laws:**
- `GSTNavigationWitness` (5120) and `gstNavigationWitness_iff_not_badTrace` (5139) — the wave predicate and its distinction.
- `gst_navigation_origin` (5179), `gst_navigation_digit_shift` (6060), `gst_navigation_carry_shift` (6079) — origin/transport (for the six-adic merge narrative and small-K fallbacks).
- `gst_seeded_happy_iff_common_twoS` (12215), `gst_seeded_bad_iff_no_common_twoS` (12238) — the common-two equivalence.
- `gst_seed_zero_affine_carry_eq_physicalS` (15222) — scratch ↔ physical bridge.

**Two-wave overlay (direct ancestors):**
- `GSTPowerTwoWave` (16950), `GSTTwoWaveBadTrace` (16957), `gst_twoWave_badTrace_of_no_navigation` (16964), `gst_four_pow_adjacent` (16973), `gst_power_two_wave_large` (16985), `erdos_ternary_2_even_universal` (16997) — the p ≥ 1 elimination trick `4^(a-1) % 3 = 1` is copied from its proof (17006–17013).

**Four-power creation chain (the theorem-grade witness source):**
- `gst_four_power_creation_master_inline` (16933) — theorem, `∀ K ≥ 5, K ≠ 7 → ...`.
- `GSTFourPowerOntologicalAdapter.gst_four_power_ontological_navigation_of_master` (used 16989).
- `gst_navigation_witness_of_standalone_navigation` (used 16992).
- `modular_check_base` (used 17000, range `5 ≤ a ≤ 500`) — bounded fallback (N ≤ 501, allowed).

**Six-adic V2 universe (the merge substrate):**
- `SixAdicIsoAt`, `DyadicShadowAt`, `TriadicShadowAt`, `SixAdicBall`, `physicalEnergy`, `PhysicalProjectionIsoAt`, `ResolvedGraph`, `resolvedVertex` (geometry file, lines 23–66).
- `triadic_shadow_mul_four_pow_iff` (68) — x4 is a triadic isometry.
- `dyadic_shadow_mul_four_pow_iff_truncated` (171), `dyadic_shadow_mul_four_pow_of_saturated` (147) — dyadic shift/saturation.
- `six_iso_iff_synchronized_shadows` (44), `six_iso_mul_four_pow_iff_truncated_skew_shadows` (188), `six_pow_dvd_four_pow_mul_sub_iff_truncated` (199) — the merge laws.

---

## 2. New definitions (skeleton, all `wava_`-prefixed)

New file `GSTGraphV2SixAdicThirdWave.lean`, importing the two V2 six-adic
files; the monolith side provides `gstDigit`/`gstCarry`/`GSTNavigationWitness`
and the creation chain.

```lean
import GSTGraphV2SixAdicSynchronizedShadows
-- monolith side (already built): gstDigit, gstCarry, GSTNavigationWitness,
-- gst_four_power_creation_master_inline, ...

namespace GSTGraphV2SixAdicThirdWave

open GSTGraphV2SixAdicOntologicalGeometry
open GSTGraphV2SixAdicSynchronizedShadows

/-! ## Wave 3 — the CommonTwo wave of consecutive powers of four

Wave 1 (dyadic): under the physical `x4` chart the dyadic shadow shifts by
`2t` and saturates (`dyadic_shadow_mul_four_pow_iff_truncated`).
Wave 2 (triadic): under the same chart the triadic shadow is an exact
isometry (`triadic_shadow_mul_four_pow_iff`).  Their merge is the
synchronized six-adic wave (`six_iso_mul_four_pow_iff_truncated_skew_shadows`).

Wave 3 is the distinction that emerges from the merge: a ternary position at
which BOTH charts of the consecutive pair `4^K, 4^(K+1) = 4·4^K` expose the
digit two.  The digit coordinate is triadic, so the x4-isometry transports it;
the only obstruction is the wave-1 carry coordinate, and the established
carry laws (`gst_pure_lift_or_forced_cascade`,
`gst_seeded_happy_iff_common_twoS`) prove the distinction themselves. -/

/-- The third-wave cell: an aligned (NULL/GST+) digit-two vertex of `4^K`. -/
def wava_ThirdWaveCell (K p : Nat) : Prop :=
  gstDigit (4^K) p = 2 ∧ gstCarry (4^K) p % 3 = 0

/-- The third wave on `K`: some positive position carries a third-wave cell. -/
def wava_CommonTwoWave (K : Nat) : Prop :=
  ∃ p, 1 ≤ p ∧ wava_ThirdWaveCell K p

/-- The target predicate in `gstDigit` coordinates: a shared digit-two of
the consecutive pair `4^K, 4^(K+1)`. -/
def wava_CommonTwo (K : Nat) : Prop :=
  ∃ p, 1 ≤ p ∧ gstDigit (4^K) p = 2 ∧ gstDigit (4^(K+1)) p = 2

/-- The third wave as an overlay on the V2 physical chart: the pair
`4^K, 4^(K+1)` as two `x4`-phases of one source energy.  Resolution is an
overlay (`resolvedVertex`); the seven-axis ontology is untouched. -/
def wava_ThirdWavePair (K : Nat) : Prop :=
  PhysicalProjectionIsoAt 1
    { x4Phase := K + 1, sourceEnergy := (1 : Int) }
    { x4Phase := K,     sourceEnergy := (1 : Int) }
```

Note: `wava_ThirdWavePair K` says `6^1 ∣ 4^(K+1) − 4^K`, i.e. the pair is
glued at six-adic depth exactly 1 (`4^(K+1) − 4^K = 3·4^K`, `6 ∣ 3·4^K` iff
`1 ≤ K`). This is the *merge* statement of the third wave in the V2 graph.

---

## 3. Step-by-step derivation of `∀ K ≥ 5, K ≠ 7 → CommonTwo K`

### Step 1 — `wava_pair_glue` (the merge: the pair is a six-adic depth-1 object)

**Claim.** `theorem wava_pair_glue (K : Nat) (hK : 1 ≤ K) : wava_ThirdWavePair K`

*Proof skeleton (reuses `six_pow_dvd_four_pow_mul_sub_iff_truncated`, or direct
witness):* `wava_ThirdWavePair K` unfolds to `SixAdicIsoAt 1 (4^(K+1)) (4^K)`,
i.e. `∃ q : Int, 4^(K+1) − 4^K = 6 * q`. Since
`4^(K+1) − 4^K = 4^K · 3` and `K ≥ 1`, take `q := (4 : Int)^K / 2`
(`4^K = 2·(2·4^(K−1))`, so `3·4^K = 6·(2·4^(K−1))`). Identity arithmetic with
`Nat`/`Int` `pow_sub`/`pow_succ`; `omega`-free, `ring`/`simp` level.
Optional strengthening (the *distinction* at depth 2): `¬ SixAdicIsoAt 2
(4^(K+1)) (4^K)` because `2^(2−2) ∣ …` fails on the triadic side —
`3^2 ∤ 3·4^K`. **RISK (minor):** none mathematically; only proof-size of the
`Int` pow bookkeeping. Mark: straightforward.

*Reaction under the established laws (commentary lemmas, all cited):*
- triadic side: `triadic_shadow_mul_four_pow_iff 1 1` keeps full triadic depth — the digit coordinate of the pair is read at the same depth on both charts;
- dyadic side: `dyadic_shadow_mul_four_pow_of_saturated 1 1` (k ≤ 2t) — dyadic depth is saturated/blind; the distinction can only be triadic.

### Step 2 — `wava_common_two_of_cell` (the lift: the distinction proves itself)

**Claim.**
```lean
theorem wava_common_two_of_cell (K p : Nat) (hp : 1 ≤ p)
    (hcell : wava_ThirdWaveCell K p) : wava_CommonTwo K := by
  obtain ⟨hd2, hcmod⟩ := hcell
  -- carry is 0 or 3 (aligned):  gstCarry_lt_four + %3 = 0
  have hlt : gstCarry (4^K) p < 4 := gstCarry_lt_four (4^K) p hp
  have hgood : gstCarry (4^K) p = 0 ∨ gstCarry (4^K) p = 3 := by omega
  -- the two-wave surgical lift: in BOTH branches gstDigit (4 * 4^K) p = 2
  have hlift := gst_pure_lift_or_forced_cascade (4^K) p hp hd2 hgood
  have hd4 : gstDigit (4 * 4^K) p = 2 := by
    rcases hlift with h | h
    · exact h.1
    · exact h.1
  -- 4 * 4^K = 4^(K+1)
  rw [gst_four_pow_adjacent (K + 1) (by omega)] at hd4
  exact ⟨p, hp, hd2, hd4⟩
```
**Cited names:** `gstCarry_lt_four` (external, used at 5147/16999 — **RISK A**:
argument order `(R) (p) (hp : 1 ≤ p)`; seen as `gstCarry_lt_four (4^(a-1)) p hp`
at 17000 and `gstCarry_lt_four R (t + 1) (by omega)` at 5148 → consistent),
`gst_pure_lift_or_forced_cascade` (4952, statement fully seen), 
`gst_four_pow_adjacent` (16973, statement fully seen). This is verbatim the
tail of the proof of `erdos_ternary_2_even_universal` (monolith 17005–17028),
which performs exactly this lift — so the pattern is kernel-proven.

### Step 3 — `wava_wave_of_navigation` (origin: navigation witness ⇒ third wave)

**Claim.**
```lean
theorem wava_wave_of_navigation (K : Nat) (hK : 1 ≤ K)
    (hnav : GSTNavigationWitness (4^K)) : wava_CommonTwoWave K := by
  obtain ⟨j, hd2, hspace⟩ := hnav
  -- GST+/NULL space ⇒ carry % 3 = 0
  have hcmod : gstCarry (4^K) j % 3 = 0 :=
    gstGoodSpace_carry_mod3_zero (4^K) j hspace
  -- eliminate p = 0 exactly as in erdos_ternary_2_even_universal (17006-17013):
  -- 4^K % 3 = 1 (since 4 ≡ 1 mod 3), so gstDigit (4^K) 0 = 1 ≠ 2
  have hj1 : 1 ≤ j := by
    cases j with
    | zero =>
        simp only [gstDigit, Nat.pow_zero, Nat.div_one] at hd2
        have hmod : (4^K) % 3 = 1 := by rw [Nat.pow_mod]; simp
        omega                      -- 1 = 2 is false
    | succ j' => omega
  exact ⟨j, hj1, hd2, hcmod⟩
```
**Cited names:** `gstGoodSpace_carry_mod3_zero` (external, used 5144, 16935,
16998 — **RISK A**: signature `(R) (j) (hspace)`), `gstDigit` (external),
`Nat.pow_mod` (Mathlib). The `p = 0` elimination is copied from the
kernel-green proof at 17006–17013. **RISK (minor):** at 17010–17012 the
monolith writes `rw [Nat.pow_mod]; simp` for `4^(a-1) % 3 = 1`; for `4^K % 3`
the same two lines work (`(4:Nat) % 3 = 1`, `1^n = 1`).

### Step 4 — `wava_common_two_of_master` (transport: the creation master)

**Claim.**
```lean
theorem wava_common_two_of_master (K : Nat) (hK5 : 5 ≤ K) (hK7 : K ≠ 7) :
    wava_CommonTwo K := by
  -- theorem-grade witness source for exactly the axiom's exponent class
  have hnav0 : GSTCanonicalTailStateIso.Navigation (4^K) :=
    GSTFourPowerOntologicalAdapter.gst_four_power_ontological_navigation_of_master
      gst_four_power_creation_master_inline K hK5 hK7        -- RISK B
  have hnav : GSTNavigationWitness (4^K) :=
    gst_navigation_witness_of_standalone_navigation (4^K) hnav0
  have hwave := wava_wave_of_navigation K (by omega) hnav
  obtain ⟨p, hp, hcell⟩ := hwave
  exact wava_common_two_of_cell K p hp hcell
```
**Cited names:** `gst_four_power_creation_master_inline` (16933 — a **theorem**
in the monolith, proven from `gst_four_power_creation_certificate_inline K hK5
hK7`), `GSTFourPowerOntologicalAdapter.gst_four_power_ontological_navigation_of_master`
(used at 16989–16990), `gst_navigation_witness_of_standalone_navigation`
(used at 16992), then Steps 2–3.

**RISK B (the main risk of the plan):** the exact hypotheses of
`gst_four_power_ontological_navigation_of_master` are not visible in the
extract — at 16989 it is applied as
`gst_four_power_ontological_navigation_of_master gst_four_power_creation_master_inline a (by omega) (by omega)`
under `500 < a`, so the two side conditions are omega-provable from `500 < a`
(the natural reading: `5 ≤ a` and `a ≠ 7`, mirroring the master's domain
`∀ K ≥ 5, K ≠ 7`). **To verify:** open the adapter file and check the
signature. If the second side condition is instead `500 < a`, use the fallback
below for `5 ≤ K ≤ 500`.

**Fallback (bounded range, still no forbidden `decide`):** split as in
`erdos_ternary_2_even_universal` (16997–17004):
```lean
theorem wava_common_two_of_master (K : Nat) (hK5 : 5 ≤ K) (hK7 : K ≠ 7) :
    wava_CommonTwo K := by
  by_cases hK500 : K ≤ 500
  · -- bounded base: a wava_ base lemma over 5 ≤ K ≤ 500, K ≠ 7.
    -- N = 501 ⇒ allowed by the task rule (no decide on ∀ k < N, N > 501).
    exact wava_base_check K hK5 hK7 hK500          -- RISK C
  · -- large range: the master route with omega side conditions (verbatim
    -- the pattern of gst_power_two_wave_large, 16985–16992)
    ...
```
`wava_base_check` would be a finite check of `wava_CommonTwo` (not just
`hasTernaryTwo` as in `modular_check_base`) over `K < 501`; **RISK C:** must be
written and kernel-checked; keep `K ≠ 7` excluded (the one genuine exception
in the class, which is why the axiom excludes it — `4^7 = 2^14` has no aligned
digit-two shared with `4^8` at a positive position). Prefer resolving RISK B
so the fallback is never needed.

### Step 5 — `gst_four_power_direct_existence_inline` (the axiom becomes a theorem)

```lean
theorem gst_four_power_direct_existence_inline :
    GSTFourPowerDirectExistence.FourPowerDirectExistence := by
  intro K hK5 hK7
  obtain ⟨p, hp, hd, hd4⟩ := wava_common_two_of_master K hK5 hK7
  refine ⟨p, hp, ?_, ?_⟩
  · exact hd    -- digit3 (4^K) p = 2   (RISK D: digit3 ≡ gstDigit)
  · exact hd4   -- digit3 (4^(K+1)) p = 2
```
**RISK D:** the definitional bridge `GSTCanonicalSevenAxisBridge.digit3 = gstDigit`.
Evidence it is definitional (no extra theorem needed): in
`gst_step6_terminal_packet_kernel` (monolith 16863–16872) the proof passes
between `GSTCanonicalSevenAxisBridge.digit3 T q` / `carry4 T q` and
`gstDigitS`/`gstDigit`/`gstAffineMulCarryS` with a plain
`simpa [GSTCanonicalSevenAxisBridge.digit3, GSTCanonicalSevenAxisBridge.carry4,
gstDigitS, gstDigit, gstAffineMulCarryS]`. If `FourPowerDirectExistence` is
stated through `digit3`, close Step 5 with
`simpa [GSTFourPowerDirectExistence.FourPowerDirectExistence] using ...`
(the same `simpa`-against-a-single-definition idiom used at 16936). **To
verify:** read the `GSTFourPowerDirectExistence` namespace declaration.
If the bridge is *not* definitional, add one `wava_digit3_eq` lemma proved by
`rfl`/`simp [GSTCanonicalSevenAxisBridge.digit3, gstDigit]`.

### Step 6 — how the third wave reacts under the established laws (the merge audit)

Commentary theorems (cheap, cite-only, they make the "distinction proves
itself" narrative machine-checkable):

```lean
/-- The third wave is purely triadic: the x4 chart is an exact isometry of
    every triadic shadow, so the digit-two coordinate is read at the same
    depth on both charts of the pair. -/
theorem wava_cell_triadic_invariance (K p t : Nat) (x y : Int)
    (h : wava_ThirdWaveCell K p) :
    TriadicShadowAt (p+1) ((4:Int)^t * x) ((4:Int)^t * y) ↔
      TriadicShadowAt (p+1) x y :=
  triadic_shadow_mul_four_pow_iff (p+1) t x y

/-- The dyadic wave is saturated/blind on the pair's charts at t ≥ 1
    (k ≤ 2t), so no dyadic distinction can exist — the distinction is
    forced to be the triadic digit coordinate. -/
theorem wava_dyadic_blindness (k t : Nat) (hkt : k ≤ 2 * t) (x y : Int) :
    DyadicShadowAt k ((4:Int)^t * x) ((4:Int)^t * y) :=
  dyadic_shadow_mul_four_pow_of_saturated k t hkt x y

/-- Wave 3 as a graph overlay: resolving the pair never changes the GST
    vertex selected at any position (the ontology is untouched by the wave). -/
theorem wava_resolved_vertex_unchanged (G : ResolvedGraph) (p : Nat) :
    resolvedVertex G p = GSTGraphV2NonEuclidean.vertex G.ambient p := rfl
```

These use only `triadic_shadow_mul_four_pow_iff` (file line 68),
`dyadic_shadow_mul_four_pow_of_saturated` (147), and `resolvedVertex` (66) —
all statements fully seen.

---

## 4. Full derivation ladder (one screen)

```
gst_four_power_creation_master_inline            (monolith 16933, THEOREM)
  └─ gst_four_power_ontological_navigation_of_master   (used 16989) [RISK B]
       └─ gst_navigation_witness_of_standalone_navigation (used 16992)
            └─ GSTNavigationWitness (4^K)               (def 5120)
                 └─ wava_wave_of_navigation             [Step 3; gstGoodSpace_carry_mod3_zero,
                 │                                        p=0 elimination from 17006–17013]
                 └─ wava_CommonTwoWave K
                      └─ wava_common_two_of_cell        [Step 2; gst_pure_lift_or_forced_cascade
                                                         (4952) + gst_four_pow_adjacent (16973)]
                           └─ wava_CommonTwo K  ──(RISK D: digit3 ≡ gstDigit, simpa as at 16936)──▶
                                gst_four_power_direct_existence_inline  = FourPowerDirectExistence
```

Bounded-range fallback (only if RISK B bites): split at `K ≤ 500` exactly like
`erdos_ternary_2_even_universal` (16997–17004); large range uses the master
route with `(by omega)` side conditions verbatim as at 16989–16990; small
range needs `wava_base_check` over `K < 501` (allowed by the N ≤ 501 rule)
[RISK C].

---

## 5. RISK register (what to verify before/while kernel-checking)

| # | Risk | Evidence seen | Action if it bites |
|---|---|---|---|
| A | Exact signatures of external wave coordinates: `gstCarry_lt_four (R) (p) (hp : 1 ≤ p)`, `gstGoodSpace_carry_mod3_zero (R) (j) (hspace)`, `gstDigit`/`gstCarry` field syntax | uses at 5147–5148, 16935, 16998, 17000 | adjust argument order; both are used uniformly in the digest |
| B | `gst_four_power_ontological_navigation_of_master` side conditions might be `500 < a` instead of `5 ≤ a, a ≠ 7` | applied at 16989 with two `(by omega)` under `500 < a`; master domain is `∀ K ≥ 5, K ≠ 7` (proof shape at 16935–16937) | bounded/large split with `wava_base_check` for `5 ≤ K ≤ 500` (Step 4 fallback); optionally strengthen small classes with `h_creation_4pow_survive` (3910) + `gst_navigation_origin` (5179) |
| C | `wava_base_check` must be authored if needed; must not use `decide` beyond `∀ k < 501` | rule text; `modular_check_base` covers `a ≤ 500` for `hasTernaryTwo` only | keep N = 501; check `K ≠ 7` exclusion is respected |
| D | `digit3` ≡ `gstDigit` definitional bridge into `GSTFourPowerDirectExistence.FourPowerDirectExistence` | `simpa [...digit3... gstDigit]` interchange at 16868–16872; `simpa [CreationCertificate]` idiom at 16936 | add `wava_digit3_eq` by `rfl`/`simp [GSTCanonicalSevenAxisBridge.digit3, gstDigit]`; restate Step 5 with `simpa` |
| E | `wava_ThirdWavePair` construction syntax for `PhysicalProjection` literals (`x4Phase`, `sourceEnergy` fields — `sourceEnergy : Int` vs `Nat` coercion) | `physicalEnergy` def (file line 50–52) uses `(P.sourceEnergy : Int)` | use anonymous-constructor field syntax with `(1 : Int)`; or state `wava_ThirdWavePair` directly as `SixAdicIsoAt 1 (4^(K+1)) (4^K)` |

No other steps are uncertain: Steps 2 and 3 are transcriptions of the
kernel-green proof of `erdos_ternary_2_even_universal` (16997–17028), and the
witness source (Step 4) is an existing theorem with the axiom's exact
quantifier shape.

---

## 6. Compliance checklist

- Lean 4.33 + Mathlib (`Nat.pow_mod`, `omega`, `simp`, `rcases`, `simpa` — all used in the monolith excerpts).
- Helpers prefixed `wava_` (wava_ThirdWaveCell, wava_CommonTwoWave, wava_CommonTwo, wava_ThirdWavePair, wava_pair_glue, wava_common_two_of_cell, wava_wave_of_navigation, wava_common_two_of_master, wava_cell_triadic_invariance, wava_dyadic_blindness, wava_resolved_vertex_unchanged, [wava_base_check], [wava_digit3_eq]).
- No `sorry`, `admit`, `axiom`, `native_decide` anywhere in the skeletons.
- No new `decide` on `∀ k < N` with `N > 501`; the only contemplated bounded check is `N = 501` (fallback, RISK C).
- Every cited name appears in DISCOVERY.md §1–§7 (i.e., was actually seen in WAVES.txt or the two six-adic V2 files).
- The axiom is replaced by a theorem whose only nontrivial inputs are already theorem-grade green machinery (`gst_four_power_creation_master_inline`, `gst_pure_lift_or_forced_cascade`, `gst_four_pow_adjacent`, `gstGoodSpace_carry_mod3_zero`, `gstCarry_lt_four`, `gst_navigation_witness_of_standalone_navigation`).
