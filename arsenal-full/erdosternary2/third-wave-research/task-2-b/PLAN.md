# PLAN — Task 2-b: Transport Route to the Four-Power Direct Existence Theorem

**Mission.** Kill the custom axiom
`gst_four_power_direct_existence_inline : GSTFourPowerDirectExistence.FourPowerDirectExistence`
(= ∀ K ≥ 5, K ≠ 7 → ∃ p ≥ 1, digit3 (4^K) p = 2 ∧ digit3 (4^(K+1)) p = 2)
by deriving it as a theorem inside the GST six-adic universe: put the
axiom-theorem into the V2 ontological graph, merge, create the **3rd wave**
(`wavb_`), let it react under the established laws, and write it in Lean.

All names cited below were actually seen (line numbers in DISCOVERY.md).
Lean 4.33 + Mathlib. **No `sorry`/`admit`/`axiom` anywhere in the skeleton** —
every not-yet-discharged input is an explicit named *hypothesis* whose
discharge is precisely the remaining work (RISK register §5). No `decide` on
`∀ k < N` with N > 501 (no `decide` on quantifiers at all).

---

## 0. WAVE STRUCTURE (the merge)

| Wave | Files | Content |
|------|-------|---------|
| 1 | `GSTGraphV2SixAdicOntologicalGeometry.lean` + `…GeometryLaws.lean` | six-adic geometry + laws (balls, children, shadows, x4-chart compatibility) |
| 2 | `GSTGraphV2SixAdicUnitIsometry.lean` + `…SynchronizedShadows.lean` | unit isometries + CRT synchronization + exact 4^t skew action |
| **3 (NEW)** | `GSTGraphV2SixAdicFourPowerWave.lean` (prefix `wavb_`) | the axiom-theorem itself: `wavb_CommonTwo`, its carry-machine transport, its six-adic reaction, and `wavb_four_power_direct_existence` |

Merge mechanics: wave 3 imports waves 1–2 and states the axiom's conclusion
on the **physicalEnergy chart** (GEO:50: `physicalEnergy P = 4^P.x4Phase *
P.sourceEnergy`; a phase-`K` cell with `sourceEnergy = 1` IS the integer
`4^K`). The laws that make this a legal merge (not an eighth axis):
`x4_chart_preserves_six_iso` (LAW:201) and `physical_projection_iso_exact`
(LAW:210); the overlay-invariance laws `resolved_vertex_axes_exact` /
`resolved_vertex_exact` (LAW:222/228) guarantee the seven-axis ontology is
untouched — six-adic resolution stays metadata, exactly as the geometry file
demands.

**Why this is a genuine 3rd wave:** the monolith already places digit-2 gates
on V2 graph waves (`gst_step6_terminal_packet_kernel`, monolith 16797, uses
`GSTGraphV2CanonicalNWave.nWaveShift` / `GSTGraphV2InfiniteControl.graph` /
`GSTGraphV2PerfectPowerBlock`). Wave 3 extends that surface with the six-adic
resolution overlay; nothing else in the universe changes.

---

## 1. THE ONE THEOREM TO TRANSPORT

**Chosen seed: `h_creation_4pow_survive`** (ErdosTernary2.lean L3910–3914):

```
theorem h_creation_4pow_survive (k : Nat) (hk5 : 5 ≤ k)
    (hv3k : 1 ≤ v3 k) (hb3 : (k / 3^(v3 k)) % 3 = 2) :
    ∃ p : Nat, 1 ≤ p ∧ (4^k) / 3^p % 3 = 2 ∧
      ((4 * ((4^k) % 3^p)) / 3^p % 3 = 0 ∨
       ((4 * ((4^k) % 3^p)) / 3^p % 3 = 1 ∧ (4^k) / 3^(p+1) % 3 = 2))
```

Why this one (nothing else in scope comes close):
- It is the **only in-scope theorem directly asserting a digit-2 witness
  `∃ p ≥ 1, (4^k)/3^p % 3 = 2` for powers of four with the K ≥ 5 boundary**.
- Its carry disjunction is **exactly the two ways a COMMON position exists**
  for `4^K` and `4^(K+1) = 4·4^K` (§2): branch 1 (carry ≡ 0 mod 3, i.e.
  carry ∈ {0,3} by `carry_bound` < 4) = SURVIVE at the same p; branch 2
  (carry = 1 ∧ digit at p+1 = 2) = CASCADE to the common position p+1.

Supporting transport theorems (already proven, same chain):
- `gst_duality` (L3892) — the carry wave theorem: the same h_creation shape
  for `R` yields `hasTernaryTwo (4*R) = true` (the R → 4R half).
- `h_creation_cascade_lift` (L6372) — transports witnesses along
  `k = 3^s·(1+3m)` (cascade class coverage).
- `gst_pow4_exponent_lift_one_digitS` / `gst_pow4_exponent_trit_lift_digitS`
  (L12432/L12471) — the LTE block `4^(3^p) = 1 + 3^(p+1)·c`, `c % 3 = 1`,
  governing which exponent classes carry witnesses at which depths (the
  reason the seed's hypotheses are v3/leading-trit conditions).

---

## 2. THE TRANSPORT ROUTE (step by step, each step citing a NAMED theorem)

Notation: `d_p(X) := X / 3^p % 3` (ternary digit), `C_X(p) := (4*(X % 3^p))/3^p`
(carry). Target:

```
wavb_CommonTwo K := ∃ p ≥ 1, d_p(4^K) = 2 ∧ d_p(4^(K+1)) = 2
```

**STEP 1 — Seed (monolith side).** Obtain the h_creation witness for R = 4^K:
`∃ p ≥ 1, d_p(4^K) = 2 ∧ (C(p)%3 = 0 ∨ (C(p)%3 = 1 ∧ d_{p+1} = 2))`.
Cites: `h_creation_4pow_survive` (L3910) for leading-trit-2 classes;
`h_creation_cascade_lift` (L6372) for `K = 3^s(1+3m)`; `gst_duality` (L3892)
as the R→4R wave consumer.
**RISK R2 (the axiom's actual content):** in-scope seeds do NOT cover all
K ≥ 5, K ≠ 7 (all K with `v3 K = 0` and leading trit 1: K = 5, 7, 8, 10, 11,
13, 14, …). The monolith's universal chain is QUARANTINED (markers L6420
"BEGIN QUARANTINED LEGACY UNIVERSAL CHAIN", L7486). See §5.

**STEP 2 — Phase alignment (trivial arithmetic).** `4^(K+1) = 4 * 4^K`
(`Nat.pow_succ 4 K`): every statement about `d_·(4·(4^K))` is a statement
about `d_·(4^(K+1))`.

**STEP 3 — The digit-shift law (the machine's transport step; hypothesis
`hshift` until R1 is discharged).** For all R and p ≥ 1:
`d_p(4*R) = (C_R(p) + 4*d_p(R)) % 3`, and the same numerator satisfies
`C_R(p+1) = (C_R(p) + 4*d_p(R)) / 3` — the latter is exactly
`carry_propagation` (uses at monolith L4506, L4537, L4549–4550; statement to
re-verify, RISK R1). Derivation of the former: `R % 3^(p+1) = (R % 3^p) +
3^p * d_p(R)` (digit cut), multiply by 4, divide by `3^p` exactly
(`Nat.div_add_mod`, `Nat.mul_div_cancel_left`), reduce mod 3 (`Nat.add_mod`,
`Nat.mul_mod`).

**STEP 4 — Common-position extraction (complete, hypothesis-driven).** From
the STEP 1 witness with `d_p = 2`:
- **Branch 1 (SURVIVE):** `C(p) % 3 = 0` with `C(p) < 4` (`carry_bound`) ⇒
  `C(p) = 0 ∨ C(p) = 3`. STEP 3: `d_p(4^(K+1)) = (C(p) + 8) % 3 = 2` in both
  cases (8 % 3 = 2; 11 % 3 = 2). **Common position: p.**
- **Branch 2 (CASCADE):** `C(p) % 3 = 1` with `C(p) < 4` ⇒ `C(p) = 1`;
  `carry_propagation` gives `C(p+1) = (1 + 8)/3 = 3` (the same conclusion as
  `carry_in_123` (L4561) + `carry_state_after_two` (L4545): `C ∈ {1,2,3} ∧
  d_p = 2 → C(p+1) = 3`); STEP 3 at p+1: `d_{p+1}(4^(K+1)) = (3 + 4·2) % 3 =
  11 % 3 = 2`, and `d_{p+1}(4^K) = 2` is the branch hypothesis.
  **Common position: p+1.**

**STEP 5 — Six-adic reaction layer ("the distinction proves itself").**
- **(5a) The phase step is a triadic isometry.**
  `triadic_shadow_mul_four_pow_iff` (SYN:68) at t = 1:
  `TriadicShadowAt k (4·x) (4·y) ↔ TriadicShadowAt k x y` — 4 is a unit mod
  every 3^k (`IsCoprime (3 : Int) 4` inside SYN's proof). Instantiated at the
  chart: every digit-carrying congruence of `4^(K+1)` against a reference
  cell is a congruence of `4^K` — the phase advance is *invisible* at
  triadic depth.
- **(5b) The dyadic half is saturated; gate resolutions collapse.**
  `six_iso_mul_four_pow_iff_truncated_skew_shadows` (SYN:188) at t = 1:
  `SixAdicIsoAt k (4x) (4y) ↔ DyadicShadowAt (k−2) x y ∧ TriadicShadowAt k x y`;
  for k ≤ 2, `DyadicShadowAt (k−2) = DyadicShadowAt 0` is automatic
  (`dyadic_shadow_zero`, SYN:140). Hence at resolutions k ≤ 2 **the x4 phase
  step is a full six-adic isometry onto the triadic shadow** (complete proof
  in §4: `wavb_six_iso_low_resolution_collapses`).
- **(5c) The digit-2 gate IS the resolution-2 six-adic cell.** The SURVIVE
  gate (`GSTSeededHappyS`, L14107: digit 2 ∧ carry ∈ {0,3}) is exactly the
  right chord of `gst_scoped_two_digit_happy_gate_right_chordS` (L16051):
  carry 3, digit 2, masses (5,5), `5 + 6·5 = 35 = 6^2 − 1` i.e.
  `55_6 = 6^2 − 1`, the maximal legal 36-state cell
  (`gst_scoped_right_chord_is_36_state_35S`, L16076). So the common-position
  witness of STEP 4 lives in the six-adic resolution-2 child structure
  (`sixChildCenter`, GEO:40, Fin 6 offsets) — exactly where (5b) says the
  phase step acts by pure isometry.
- **(5d) Boxed divisibility reaction.**
  `six_pow_dvd_four_pow_mul_sub_iff_truncated` (SYN:199) at t = 1:
  `6^k ∣ 4·(x−y) ↔ 3^k ∣ (x−y) ∧ 2^(k−2) ∣ (x−y)` — one phase step costs
  exactly one dyadic level (`six_scale_exact_iff`, ISO:58, trades one 6 for
  one 2 + one 3) and ZERO triadic levels.
- **(5e) Translation invariance of the witness cell.**
  `six_iso_translate_iff` (ISO:13) re-centers the witness cell freely
  (`SixAdicIsoAt k (a+x) (a+y) ↔ SixAdicIsoAt k x y`); `six_ball_recenter`
  (LAW:134) and `intersecting_equal_radius_balls_eq` (LAW:148) ensure the
  transported cell is the SAME ball — the witness never forks under
  re-centering.
- **(5f) The reaction verdict.** Under the established laws the axiom's
  statement has **zero dyadic content** (5b) and is transported by a
  **genuine isometry** (5a) whose fixed cell is the 36-state base-6 chord
  (5c). The only non-isometric ingredient in the chain is the carry machine
  (STEPS 3–4), already proven in the monolith. The six-adic universe
  contributes **no obstruction**: it certifies that everything except the
  seed is transport. That is the sense in which the distinction proves
  itself.

**STEP 6 — Boundary facts.** K ≥ 5: forced by `erdos_exception_n8` (L846:
`noTernaryTwo (2^8) = true` — 4^4 has NO ternary digit 2, so no witness
exists below K = 5). p ≥ 1: forced by `gst_pow4_mod3_oneS` (L12426:
`4^m % 3 = 1`, position 0 is never 2). Witness ceiling: below the bridge
`4^k < 3^(2k)` (`four_pow_succ_lt_three_pow_doubleS` L9861 active for N ≥ 3;
the direct k-forms `gst_four_pow_lt_three_pow_twice` L7490 and
`gst_digit_two_position_lt_twice` L7515 are QUARANTINED — RISK R3). K ≠ 7:
**no in-scope theorem singles out 7** (RISK R4).

**STEP 7 — The self-proof knot.** With the machine (`hshift` + `hcbound`),
the equivalence
`wavb_CommonTwo K ↔ ∃ p ≥ 1, d_p(4^K) = 2 ∧ C(p) % 3 = 0`
holds in BOTH directions (§4: `wavb_common_two_iff_survive_witness`):
forward = STEP 4 branch 1; backward = `d_p(4^(K+1)) = 2 ∧ d_p(4^K) = 2` ⇒
`(C(p) + 8) % 3 = 2` ⇒ `C(p) % 3 = 0`. So the axiom is *exactly* the SURVIVE
half of h_creation — the wave-3 statement and the monolith's witness
certificate are one object seen from two charts. This is the precise sense
of "put the axiom-theorem into the universe and merge": the merged statement
coincides with the already-half-proven monolith certificate.

---

## 3. STEP-BY-STEP LEAN-LEVEL DERIVATION TABLE

| # | Goal (Lean) | Key cites | Status |
|---|-------------|-----------|--------|
| 1 | `hseed : ∃ p ≥ 1, d_p(4^K) = 2 ∧ (C%3=0 ∨ (C%3=1 ∧ d_{p+1}=2))` | `h_creation_4pow_survive`, `h_creation_cascade_lift` | **RISK R2** (class coverage) |
| 2 | `4^(K+1) = 4 * 4^K` | `Nat.pow_succ` | trivial |
| 3 | `hshift : d_p(4*R) = (C_R(p) + 4*d_p(R)) % 3` | `carry_propagation` | hypothesis until R1; strategy given |
| 4 | `wavb_common_two_of_hcreation : hseed → wavb_CommonTwo K` | `hshift`, `carry_bound`/`hcbound`, `carry_propagation` | **complete** (§4) |
| 5 | `wavb_common_two_iff_survive_witness` (both directions) | `hshift`, `hcbound` | **complete** (§4) |
| 6 | `wavb_phase_step_triadic_isometry` | `triadic_shadow_mul_four_pow_iff` | **complete** (§4) |
| 7 | `wavb_six_iso_low_resolution_collapses` (k ≤ 2) | `six_iso_mul_four_pow_iff_truncated_skew_shadows`, `dyadic_shadow_zero` | **complete** (§4) |
| 8 | `wavb_four_power_direct_existence` | 1–7 | **complete given hypotheses**; R2 is the only open input |

---

## 4. LEAN SKELETON — wave 3: `src/GSTGraphV2SixAdicFourPowerWave.lean`

Design rule: everything not yet dischargeable is an explicit **named
hypothesis** (never `sorry`); everything else has its proof written out.

```lean
import GSTGraphV2SixAdicSynchronizedShadows
import GSTGraphV2SixAdicUnitIsometry

/-!
# GST Graph V2 Six-Adic Four-Power Wave (WAVE 3, prefix `wavb_`)

The third wave: `gst_four_power_direct_existence_inline` enters the six-adic
universe as a theorem.  The axiom's conclusion, restated on the physicalEnergy
chart (a phase-K cell with sourceEnergy 1 is the integer `4^K`, GEO:50), is
`wavb_CommonTwo`.  Everything except the universal seed is transport: the x4
phase step is a triadic isometry (`triadic_shadow_mul_four_pow_iff`), its
dyadic half is saturated at gate resolutions (`dyadic_shadow_zero` +
`six_iso_mul_four_pow_iff_truncated_skew_shadows`), and the digit-2 gate is
the 36-state base-6 chord (`gst_scoped_two_digit_happy_gate_right_chordS`:
masses (5,5), `5 + 6*5 = 35 = 6^2 - 1`).  No eighth axis: the overlay laws
`resolved_vertex_exact` / `x4_chart_preserves_six_iso` are respected.
-/

namespace GSTGraphV2SixAdicFourPowerWave

open GSTGraphV2SixAdicOntologicalGeometry
open GSTGraphV2SixAdicOntologicalGeometryLaws
open GSTGraphV2SixAdicUnitIsometry
open GSTGraphV2SixAdicSynchronizedShadows

set_option maxHeartbeats 20000000

/-! ## The wave-3 target

`wavb_CommonTwo K` is the six-adic-universe form of the axiom's conclusion.
Positions follow the monolith's ternary digit convention `p ↦ n / 3^p % 3`
(the `gstDigitS` convention of `gst_omega_natural_transfer_prefixS`,
monolith 11548: `T % 3^(K+1) = T % 3^K + 3^K * gstDigitS T K`).
RISK R5: `digit3` itself was not visible in the reading scope; before the
axiom is deleted, verify `digit3 n p = n / 3^p % 3` and its 0-/1-indexing
against `GSTFourPowerDirectExistence`, then add the one-line bridge
`theorem wavb_digit3_eq (n p : Nat) : digit3 n p = n / 3^p % 3 := rfl`. -/
def wavb_CommonTwo (K : Nat) : Prop :=
  ∃ p : Nat, 1 ≤ p ∧
    (4 : Nat)^K / 3^p % 3 = 2 ∧ (4 : Nat)^(K+1) / 3^p % 3 = 2

/-- The physical x4 chart reading: a phase-`K` physical cell with unit source
energy has integer energy `4^K` (`physicalEnergy`, GEO:50).  Merge
certificates: `x4_chart_preserves_six_iso` (LAW:201) and
`physical_projection_iso_exact` (LAW:210). -/
def wavb_fourPowerChart (K : Nat) : Int :=
  (4 : Int)^K   -- = physicalEnergy ⟨x4Phase := K, sourceEnergy := 1, …⟩

/-! ## STEP 3 — the digit-shift law (carry-machine transport)

`hshift` is the digit-shift half and `hprop` is exactly the monolith's
`carry_propagation` (uses at L4506/L4537/L4549–4550; RISK R1: verify the
exact signature; expected statement
`(4 * (R % 3^(p+1))) / 3^(p+1) = ((4 * (R % 3^p)) / 3^p + 4 * (R / 3^p % 3)) / 3`).
`hcbound` is the monolith's `carry_bound` (uses at L4541/L4554/L4563,
expected `(4 * (R % 3^p)) / 3^p < 4`; re-derivable locally from
`4 * (x % 3^p) < 4 * 3^p` via `Nat.div_lt_of_lt_mul` if needed).

Discharge strategy for `hshift` (no new mathematics):
* `R % 3^(p+1) = (R % 3^p) + 3^p * (R / 3^p % 3)`  (digit cut, from
  `Nat.div_add_mod` at `3^(p+1) = 3 * 3^p`);
* multiply by 4 and divide by `3^p`: the `3^p * d` term divides exactly
  (`Nat.mul_div_cancel_left`);
* `4 * R = 4 * (R % 3^(p+1)) + 3^(p+1) * (4 * (R / 3^(p+1)))`
  (`Nat.div_add_mod`); the second term contributes a multiple of 3 after the
  division by `3^p`; conclude with `Nat.add_mod`, `Nat.mul_mod`. -/

/-- STEP 3 hypothesis: digit shift under the one-phase step. -/
def wavb_HShift : Prop :=
  ∀ R p : Nat, 1 ≤ p →
    (4 * R) / 3^p % 3 =
      ((4 * (R % 3^p)) / 3^p + 4 * (R / 3^p % 3)) % 3

/-- STEP 3 hypothesis: carry propagation (the monolith's
`carry_propagation`, L4506/L4537). -/
def wavb_HProp : Prop :=
  ∀ R p : Nat, 1 ≤ p →
    (4 * (R % 3^(p+1))) / 3^(p+1) =
      ((4 * (R % 3^p)) / 3^p + 4 * (R / 3^p % 3)) / 3

/-- STEP 3 hypothesis: carry bound (the monolith's `carry_bound`,
L4541/L4554). -/
def wavb_HCBound : Prop :=
  ∀ R p : Nat, 1 ≤ p → (4 * (R % 3^p)) / 3^p < 4

/-! ## STEP 4 — common-position extraction (complete)

Branch 1 (SURVIVE): `C(p) % 3 = 0` with `C(p) < 4` ⇒ `C(p) = 0 ∨ C(p) = 3`;
`hshift` with `d_p = 2` gives `d_p(4^(K+1)) = (C(p) + 8) % 3 = 2`.
Common position `p`.
Branch 2 (CASCADE): `C(p) = 1`; `hprop` gives `C(p+1) = (1+8)/3 = 3` (the
conclusion of `carry_in_123` (L4561) + `carry_state_after_two` (L4545));
`hshift` at `p+1` with `d_{p+1} = 2` gives `d_{p+1}(4^(K+1)) = (3+8)%3 = 2`.
Common position `p+1`. -/
theorem wavb_common_two_of_hcreation (K : Nat)
    (hshift : wavb_HShift) (hprop : wavb_HProp) (hcbound : wavb_HCBound)
    (hseed : ∃ p : Nat, 1 ≤ p ∧ (4^K) / 3^p % 3 = 2 ∧
      ((4 * ((4^K) % 3^p)) / 3^p % 3 = 0 ∨
       ((4 * ((4^K) % 3^p)) / 3^p % 3 = 1 ∧ (4^K) / 3^(p+1) % 3 = 2))) :
    wavb_CommonTwo K := by
  obtain ⟨p, hp1, hp2, hbranch⟩ := hseed
  have h4succ : (4 : Nat)^(K+1) = 4 * (4 : Nat)^K := by
    rw [Nat.pow_succ]; ac_rfl
  have hC : (4 * ((4 : Nat)^K % 3^p)) / 3^p < 4 := hcbound (4 : Nat)^K p hp1
  rcases hbranch with hc0 | hc1
  · -- SURVIVE: common position p
    have hc0' : (4 * ((4 : Nat)^K % 3^p)) / 3^p % 3 = 0 := hc0
    have hC03 : (4 * ((4 : Nat)^K % 3^p)) / 3^p = 0 ∨
        (4 * ((4 : Nat)^K % 3^p)) / 3^p = 3 := by omega
    refine ⟨p, hp1, hp2, ?_⟩
    have hsh := hshift (4 : Nat)^K p hp1
    rw [h4succ, hsh, hp2]
    rcases hC03 with h | h <;> rw [h] <;> omega
  · -- CASCADE: common position p+1
    obtain ⟨hc1', hnext⟩ := hc1
    have hC1 : (4 * ((4 : Nat)^K % 3^p)) / 3^p = 1 := by omega
    have hcpp := hprop (4 : Nat)^K p hp1
    rw [hC1, hp2] at hcpp
    have hCp1 : (4 * ((4 : Nat)^K % 3^(p+1))) / 3^(p+1) = 3 := by
      rw [hcpp]; norm_num
    refine ⟨p+1, by omega, hnext, ?_⟩
    have hsh := hshift (4 : Nat)^K (p+1) (by omega)
    rw [h4succ, hsh, hnext, hCp1]
    omega

/-! ## STEP 7 — the self-proof knot (complete, both directions)

With the machine, the wave-3 statement and the SURVIVE half of the
monolith's h_creation certificate are the SAME object:
forward = STEP 4 branch 1; backward = `d_p(4^(K+1)) = 2 ∧ d_p(4^K) = 2` ⇒
`(C(p) + 8) % 3 = 2` ⇒ `C(p) % 3 = 0`. -/
theorem wavb_common_two_iff_survive_witness (K : Nat)
    (hshift : wavb_HShift) (hcbound : wavb_HCBound) :
    wavb_CommonTwo K ↔
      ∃ p : Nat, 1 ≤ p ∧ (4^K) / 3^p % 3 = 2 ∧
        (4 * ((4^K) % 3^p)) / 3^p % 3 = 0 := by
  have h4succ : (4 : Nat)^(K+1) = 4 * (4 : Nat)^K := by
    rw [Nat.pow_succ]; ac_rfl
  constructor
  · rintro ⟨p, hp1, hp2, hp3⟩
    have hsh := hshift (4 : Nat)^K p hp1
    rw [h4succ, hsh, hp2] at hp3
    -- hp3 : (C(p) + 4*2) % 3 = 2, with C(p) < 4  ⇒  C(p) % 3 = 0
    have hC := hcbound (4 : Nat)^K p hp1
    refine ⟨p, hp1, hp2, ?_⟩
    omega
  · rintro ⟨p, hp1, hp2, hc0⟩
    have hC := hcbound (4 : Nat)^K p hp1
    have hC03 : (4 * ((4 : Nat)^K % 3^p)) / 3^p = 0 ∨
        (4 * ((4 : Nat)^K % 3^p)) / 3^p = 3 := by omega
    refine ⟨p, hp1, hp2, ?_⟩
    have hsh := hshift (4 : Nat)^K p hp1
    rw [h4succ, hsh, hp2]
    rcases hC03 with h | h <;> rw [h] <;> omega

/-! ## STEP 5 — six-adic reaction layer (complete) -/

/-- 5a. The one-phase step is a triadic isometry: every digit-carrying
congruence of the `4^(K+1)` chart is a congruence of the `4^K` chart.
Direct instance of `triadic_shadow_mul_four_pow_iff` (SYN:68) at `t = 1`. -/
theorem wavb_phase_step_triadic_isometry (k K : Nat) (y : Int) :
    TriadicShadowAt k ((4 : Int)^(K+1)) ((4 : Int) * y) ↔
      TriadicShadowAt k ((4 : Int)^K) y := by
  have h4 : (4 : Int)^(K+1) = (4 : Int)^1 * (4 : Int)^K := by
    rw [Nat.pow_succ, Nat.pow_one]; ring
  rw [h4]
  exact triadic_shadow_mul_four_pow_iff k 1 ((4 : Int)^K) y

/-- 5b. At gate resolutions `k ≤ 2` the x4 phase step is a FULL six-adic
isometry onto the triadic shadow: the dyadic half is saturated
(`dyadic_shadow_zero`), the triadic half is preserved.  This is why the
digit-2 gate — the 36-state base-6 cell of
`gst_scoped_two_digit_happy_gate_right_chordS` (masses (5,5),
`5 + 6*5 = 35 = 6^2 - 1`) — sees the phase step as a pure isometry. -/
theorem wavb_six_iso_low_resolution_collapses (k : Nat) (hk : k ≤ 2)
    (x y : Int) :
    SixAdicIsoAt k ((4 : Int)^1 * x) ((4 : Int)^1 * y) ↔
      TriadicShadowAt k x y := by
  rw [six_iso_mul_four_pow_iff_truncated_skew_shadows k 1 x y]
  have hk2 : k - 2 * 1 = 0 := by omega
  rw [hk2]
  exact ⟨fun h => h.2, fun h => ⟨dyadic_shadow_zero x y, h⟩⟩

/-- 5d. Boxed reaction: one phase step costs exactly one dyadic level
(`six_scale_exact_iff` trades one 6 for one 2 and one 3) and no triadic
level.  Direct instance of `six_pow_dvd_four_pow_mul_sub_iff_truncated`
(SYN:199) at `t = 1`. -/
theorem wavb_phase_step_six_content (k : Nat) (x y : Int) :
    (6 : Int)^k ∣ (4 : Int)^1 * (x - y) ↔
      (3 : Int)^k ∣ (x - y) ∧ (2 : Int)^(k - 2) ∣ (x - y) :=
  six_pow_dvd_four_pow_mul_sub_iff_truncated k 1 x y

/-! ## STEP 8 — final assembly

The single open input is the universal seed — exactly the mathematical
content the axiom was papering over.  In-scope coverage:
* leading-trit-2 classes (`1 ≤ v3 K`, `(K / 3^(v3 K)) % 3 = 2`):
  `h_creation_4pow_survive` (L3910);
* cascade classes `K = 3^s * (1 + 3*m)`: `h_creation_cascade_lift` (L6372);
* the R → 4R wave consumer: `gst_duality` (L3892).
RISK R2: full coverage of all K ≥ 5, K ≠ 7 requires the un-quarantined
universal chain (§5).  Once `hseed` below is discharged, the axiom
`gst_four_power_direct_existence_inline` can be deleted and replaced by
this theorem (after the R5 `digit3` bridge). -/
theorem wavb_four_power_direct_existence
    (hcarry : wavb_HShift ∧ wavb_HProp ∧ wavb_HCBound)
    (hseed : ∀ K : Nat, 5 ≤ K → K ≠ 7 →
      ∃ p : Nat, 1 ≤ p ∧ (4^K) / 3^p % 3 = 2 ∧
        ((4 * ((4^K) % 3^p)) / 3^p % 3 = 0 ∨
         ((4 * ((4^K) % 3^p)) / 3^p % 3 = 1 ∧ (4^K) / 3^(p+1) % 3 = 2))) :
    ∀ K : Nat, 5 ≤ K → K ≠ 7 → wavb_CommonTwo K := by
  intro K hK5 hK7
  exact wavb_common_two_of_hcreation K
    hcarry.1 hcarry.2.1 hcarry.2.2 (hseed K hK5 hK7)

end GSTGraphV2SixAdicFourPowerWave
```

**Tactic-level RISK notes (compile checks to run, in order):**
- `wavb_common_two_of_hcreation` / `wavb_common_two_iff_survive_witness`:
  the `omega` calls do arithmetic on the opaque atom `C := (4 * ((4^K) %
  3^p)) / 3^p` with `% 3`, `< 4`, `+ 8` — well inside `omega`'s fragment
  (literal modulus 3). Verify `rw [h4succ, hsh, hp2]` fires in that order
  (it did in the analogous monolith rewrites at L3889:
  `rw [h4R_div_p1, Nat.add_mod, four_mul_mod3_eq, hnext_d2, …]`).
- `wavb_six_iso_low_resolution_collapses`: `rw` with
  `six_iso_mul_four_pow_iff_truncated_skew_shadows` requires the goal to be
  syntactically `SixAdicIsoAt k ((4 : Int)^1 * x) ((4 : Int)^1 * y)`; if the
  `rw [h4]` trick of 5a is preferred for the `4 * x` form, insert
  `rw [Nat.pow_one]` first. `Nat.sub` truncation `k - 2 * 1 = 0` needs
  `hk : k ≤ 2` (hypothesis present).
- `hCp1` in the CASCADE branch: `rw [hcpp]; norm_num` closes
  `(4 * ((4^K) % 3^(p+1))) / 3^(p+1) = (1 + 4*2)/3 = 3`; if `norm_num`
  balks at the cast-free `Nat` division, replace with
  `exact (Nat.div_eq_of_eq_mul_left (by norm_num) (by norm_num)).symm`-style
  arithmetic or `decide`-free `omega`.

---

## 5. RISK REGISTER (what to verify before killing the axiom)

| ID | Risk | What to verify / how to close |
|----|------|-------------------------------|
| R1 | `carry_propagation` / `carry_bound` statements were inferred from uses only (L4506/4537/4541/4554/4563). | Open the monolith at those lines. If the signatures match `wavb_HProp`/`wavb_HCBound`, discharge them directly (the `hshift` strategy in §4 is ~15 lines of `Nat.div_add_mod` + `omega`). Worst case re-derive `carry_bound` locally: `4 * (x % 3^p) < 4 * 3^p` → `Nat.div_lt_of_lt_mul`. |
| R2 | **Universal seed coverage** (the axiom's actual content): in-scope seeds miss all K with `v3 K = 0`, leading trit 1 (K = 5, 7, 8, 10, 11, 13, 14, …). The universal chain is quarantined (L6420 / L7486). | (a) Check for active (un-quarantined) h_creation lemmas covering the remaining classes; (b) else prove them via `gst_pow4_exponent_trit_lift_digitS` (L12471) + the LTE block `4^(3^p) = 1 + 3^(p+1)*c`, `c % 3 = 1` (hypothesis shape of L12432; `lte_identity` cited at L6386); (c) only after R2 closes may the axiom be deleted. |
| R3 | Witness position ceiling: `gst_four_pow_lt_three_pow_twice` (L7490) and `gst_digit_two_position_lt_twice` (L7515) are in a QUARANTINED comment block. | Active replacement: `four_pow_succ_lt_three_pow_doubleS` (L9861, N ≥ 3) gives `4^(K+1) < 3^(2K)`; the k-form is re-derivable by the same `∀ n ≥ 1, 4^n < 9^n` induction (inlined at L6617–6631). Only needed if a bounded search is desired. |
| R4 | No in-scope theorem explains the axiom's `K ≠ 7` exclusion. | Inspect `GSTFourPowerDirectExistence` in the monolith (outside reading scope). If the exclusion is an artifact of the original inline proof, drop it from the wave-3 theorem (nothing in the transport needs it); otherwise identify the 7-specific obstruction. Do NOT silently keep or drop it. |
| R5 | `digit3`'s definition and indexing were never seen. | Verify `digit3 n p = n / 3^p % 3` (the `gstDigitS` convention, monolith 11548–11563) and 0- vs 1-indexing; add `wavb_digit3_eq` before deleting the axiom. |
| R6 | `Nat`/`Int` boundary: the six-adic universe is over `Int`, the carry machine over `Nat`. | The skeleton keeps the layers separate (congruences on `Int`, digits on `Nat`); if a mixed lemma is needed, go through coercions — the SYN proofs already mix `(4 : Int)^t` with `Nat` exponents. |

---

## 6. FIVE-LINE TRANSPORT-PLAN SUMMARY

1. Seed with `h_creation_4pow_survive` (L3910) — the only in-scope digit-2
   witness theorem for `4^K`, K ≥ 5; its carry disjunction is exactly the two
   common-position branches (SURVIVE at p, CASCADE to p+1).
2. Transport by the carry machine (`carry_propagation` → `hshift` →
   `wavb_common_two_of_hcreation` with `carry_bound`): SURVIVE keeps position
   p (C ∈ {0,3}: (C+8)%3 = 2), CASCADE moves to p+1 (C(p+1) = 3:
   (3+8)%3 = 2).
3. React under the six-adic laws: the phase step `4^K → 4^(K+1)` is a triadic
   isometry (`triadic_shadow_mul_four_pow_iff`), dyadic-saturated at gate
   resolution k ≤ 2 (`dyadic_shadow_zero` +
   `six_iso_mul_four_pow_iff_truncated_skew_shadows`), and the digit-2 gate
   is the 36-state base-6 chord (`gst_scoped_two_digit_happy_gate_right_chordS`,
   masses (5,5), `5 + 6*5 = 35 = 6^2 − 1`).
4. Knot: `wavb_common_two_iff_survive_witness` proves the axiom's conclusion
   is *equivalent* to the SURVIVE half of h_creation under the machine —
   the merged wave-3 statement coincides with the monolith certificate.
5. Boundaries: K ≥ 5 from `erdos_exception_n8` (4^4 has no digit 2), p ≥ 1
   from `gst_pow4_mod3_oneS`, witnesses below the `4^k < 3^(2k)` bridge
   (`four_pow_succ_lt_three_pow_doubleS`); the single open gap is the
   universal seed (R2) — the six-adic universe itself contributes no
   obstruction, which is how the distinction proves itself.
