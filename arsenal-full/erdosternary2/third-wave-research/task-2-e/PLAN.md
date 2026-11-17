# PLAN — Task 2-e: THE REPAIRED UNIVERSAL INDUCTION

Goal: replace the quarantined strong-induction chain by a sound one ending in

```lean
theorem gst_four_power_direct_existence_inline :
    GSTFourPowerDirectExistence.FourPowerDirectExistence
```

with **no** `sorry` / `admit` / `axiom` / `native_decide`, and no `decide` on
`∀ k < N` with `N > 501`. Lean 4.33 + Mathlib. Every helper is prefixed `wave_`.
Only names actually seen in the sources are cited; verbatim signatures are in
`DISCOVERY.md`. Numbered **RISK** items flag every remaining gap.

---

## 0. Design decisions (what changed vs. the quarantined plan)

| Quarantined plan | Repair |
|---|---|
| Step = `ih(k-1) + gst_duality + Φ`, closing the last sub-case with the **generic** oscillation recursion | Step is split by the exponent's low ternary trits; most classes are closed by *verified, witness-free* theorems (row classes, survive tower). Only the residual classes use `ih(K-1)`, closed by `gst_pure_lift_or_forced_cascade` (the sound, local ×4 lift) instead of the false global oscillation |
| Induction on the *h_creation certificate* statement, then a separate conversion `hasTernaryTwo(4^k) → certificate` (the FALSE link) | Induction directly on the *pure/happy* statement `wave_S K` (equivalent to the certificate by the verified `gst_hCreation_exists_iff_pure`), so the false link is never needed |
| Descent engine `h_creation_cascade_lift` ("cascade structure") | **Dropped**: that theorem is vacuous (hypothesis contradicts `cascade_universal`; see DISCOVERY §9). The cube engine `cubic_h_creation_lift` is used where it actually applies |
| Navigation witness supplied by the removed oscillation theorem | The one remaining open lemma (`wave_alt_exit`) is stated *explicitly* as a power-specific exponent-trit statement, never as a generic R-statement — this is the sound replacement for the false theorem |

---

## 1. The induction statement

```lean
/-- The happy-gate / pure-creation statement for one four-power.
    Equal to the h_creation certificate by `gst_hCreation_exists_iff_pure`
    and to `CommonTwo` by the seed-zero happy-gate bridge. -/
def wave_S (K : Nat) : Prop :=
  ∃ p : Nat, 1 ≤ p ∧ gstDigit (4^K) p = 2 ∧
    (gstCarry (4^K) p = 0 ∨ gstCarry (4^K) p = 3)

/-- h_creation-certificate shape, restated in gst coordinates. -/
def wave_Cert (K : Nat) : Prop :=
  ∃ p : Nat, 1 ≤ p ∧ gstDigit (4^K) p = 2 ∧
    (gstCarry (4^K) p % 3 = 0 ∨
      (gstCarry (4^K) p % 3 = 1 ∧ gstDigit (4^K) (p + 1) = 2))
```

**Bridge lemmas (all sound, all from verified pieces):**

```lean
/-- Certificate ⟺ pure/happy. VERIFIED CORE: `gst_hCreation_exists_iff_pure`. -/
theorem wave_S_iff_cert (K : Nat) : wave_S K ↔ wave_Cert K := by
  -- gst_hCreation_exists_iff_pure (4^K) closes this directly:
  -- both sides are "∃ q ≥ 1, digit 2 ∧ carry % 3 = 0" after
  -- gstCarry_lt_four (4^K) q (carry < 4, so %3 = 0 ↔ = 0 ∨ = 3).
  exact gst_hCreation_exists_iff_pure (4^K)

/-- HAPPY GATE ⟹ COMMON TWO (the target direction).
    VERIFIED CORE: `gst_seeded_happy_iff_common_twoS` with seed = 0. -/
theorem wave_commonTwo_of_S (K : Nat) (h : wave_S K) :
    GSTFourPowerDirectExistence.CommonTwo K := by
  -- 4^(K+1) = 0 + 4 * 4^K   (Nat.pow_succ)
  -- gstAffineMulCarryS 4 0 (4^K) q = (0 + 4 * ((4^K) % 3^q)) / 3^q = gstCarry (4^K) q  (definitional)
  -- gstDigitS = gstDigit = digit3  (all three are `R / 3^p % 3`; definitional)
  -- apply gst_seeded_happy_iff_common_twoS 0 (4^K) q (by decide : 0 < 4)
  sorry  -- see RISK 4 (definitional-bridge bookkeeping only; no mathematics)

/-- COMMON TWO ⟹ HAPPY GATE (converse; needed to absorb the row-class cases).
    VERIFIED CORE: the argument of `commonTwo_to_physical_happy_row`
    (digit3_four_mul + directCarry4_lt_four) run backwards. -/
theorem wave_S_of_commonTwo (K : Nat) (h : GSTFourPowerDirectExistence.CommonTwo K) :
    wave_S K := by
  -- from ⟨p, hp, hs, ht⟩ and digit3_four_mul (4^K) p:
  --   digit3 (4 * 4^K) p = (directCarry4 (4^K) p + 4 * 2) % 3
  --   ht : = 2  ⟹  directCarry4 (4^K) p ≡ 0 (mod 3)
  --   directCarry4_lt_four ⟹ carry = 0 ∨ carry = 3
  sorry  -- see RISK 4 (same bookkeeping; the arithmetic is already verified
         -- inside GSTFourPowerDirectHappyBridge.commonTwo_to_physical_happy_row)
```

---

## 2. BASE CASE `5 ≤ K ≤ 500`, `K ≠ 7`

**Reuse the quarantined base verbatim — it is sound.** It calls only ACTIVE,
kernel-checked theorems (`hCreationCheck_univ`, `powMod_eq`, `digit_identity`):

```lean
theorem wave_base (K : Nat) (hK5 : 5 ≤ K) (hK500 : K ≤ 500) (hK7 : K ≠ 7) :
    wave_S K := by
  -- 1. hCreationCheck_univ K (by omega) hK5  ⟹  K = 7 ∨ ∃ p < 50, …(powMod form)
  -- 2. the quarantined conversion (L6443–6470 of the monolith), sound arithmetic:
  --      hpm : ∀ j ≤ 52, powMod 4 K (3^j) = 4^K % 3^j      (powMod_eq, 0 < 3^j)
  --      hp_d2   : (4^K)/3^p % 3 = 2                        (digit_identity + hpm)
  --      hp_carry: carry 0 ∨ (carry 1 ∧ next d2)            (digit_identity + hpm)
  --    ⟹ wave_Cert K
  -- 3. wave_S_iff_cert K
  sorry  -- mechanical transcription of quarantined L6443–6470; no new math
```

### Base-case feasibility verdict

* **Keep `hCreationCheck_univ`.** Its `decide` is on `∀ k < 501` — `N = 501`, exactly
  at the permitted boundary (the rule forbids `N > 501`), every quantified object is
  bounded (`p < 50`, moduli `3^j ≤ 3^52 < 2^82`, `4^k` never appears unbounded —
  `powMod 4 k (3^j)` computes `4^k % 3^j` by iterated small modmul). It is OUTSIDE the
  quarantine and **already compiles** in the monolith: zero new kernel cost, zero OOM
  risk.
* **A fully decide-free base is NOT feasible with the verified row theorems.**
  Coverage arithmetic: row 2 gives 2 of 9 classes (`K%9 ∈ {5,6}` → 18 of 81 mod-81
  classes); row 3 adds 4 mod-27 classes (`{14,18,19,25}` → at most 12 new mod-81
  classes); row 4 adds `RowFourClass` (≤ 14 mod-81 classes). Total ≤ 44 of 81 residue
  classes. The residue (e.g. `K ≡ 3 mod 9` outside row-4, `K ≡ 16 mod 27`, …) has **no**
  fixed-row theorem; the monolith's own `modular_check_base` shows the hard residuals
  `{93, 166, 237, 280, 387, 432, 496}` need row-16 checks (`mod_check_K16`). Producing
  row-5..row-17 overlap theorems is strictly more work and more risk than the existing
  boundary-legal decide.
* Optional *hybrid* (strictly less kernel work, only if reviewers demand it): rows 2–4
  (no decide) + `hCreationCheck_univ` restricted by `rcases` to the uncovered classes
  — same theorem, smaller certificate; NOT proposed for v1.

---

## 3. STEP CASE `K > 500`

Strong induction on `K`; the step never touches the false oscillation. The case split
is by the lowest nonzero ternary trits of `K` (all decidable comparisons on `K % 9`,
`K % 27`, `K % 81`, `v3 K`).

```lean
theorem wave_step (K : Nat) (hK : 501 ≤ K)
    (ih : ∀ k, k < K → 5 ≤ k → k ≠ 7 → wave_S k) : wave_S K := by
```

### 3a. Direct classes — NO induction hypothesis (all verified)

```lean
  -- (R0) K % 9 ∈ {5, 6}:  commonTwo_of_mod9_five_or_six K …  ⟹ CommonTwo K
  --      ⟹ wave_S_of_commonTwo K
  -- (R1) K % 27 ∈ {14, 18, 19, 25}:  commonTwo_of_mod27_row_three K …
  -- (R2) RowFourClass (K % 81):      commonTwo_of_mod81_row_four K …
  -- (S1) 1 ≤ v3 K ∧ (K / 3^(v3 K)) % 3 = 2  (the 2·3^s tower):
  --        h_creation_4pow_survive K hK (by omega) (…)  ⟹ wave_Cert K
  --        ⟹ wave_S_iff_cert K
```

`h_creation_4pow_survive` needs `5 ≤ K` (✓ since `501 ≤ K`) and nothing else.
R0/R1/R2 need nothing but the residue hypothesis. These four cases are *closed
forever* — they are the reason the repair is strictly stronger than the quarantined
plan, which pushed everything through `ih(k-1)`.

### 3b. Cube case `K = 3·K'` with a seeded sub-witness — no new gap

```lean
  -- (C0) K = 3 * K', and ih K' …  yields d_p (4^K') = 2 ∧ (4^K') % 3^p = 1
  --      (the seeded form; holds whenever v3 K' = p - 1):
  --        cubic_h_creation_lift K' p (…) (…) (…)
  --          ⟹ ∃ q ≥ 1, digit 2 at q of (4^K')^3 = 4^(3*K') = 4^K with carry 0
  --          ⟹ wave_S K
```

Sound: `cubic_h_creation_lift` is verified and produces the SURVIVE branch outright.
Coverage note: whenever the sub-witness is the survive witness of `K'` in the
`2·3^(p-1)` tower this reproduces case (S1) one level up — harmless redundancy.

### 3c. Residual classes — `ih(K-1)` + the sound local ×4 lift

For everything not caught by 3a/3b (concretely: `K % 9 ∈ {1,3,4,7,8}` outside the
row-3/row-4 lists, i.e. `K ≡ 1 mod 3` and `K ≡ 3 mod 9` type exponents):

```lean
  -- obtain ⟨p, hp, hd2, hC⟩ : wave_S (K-1) := ih (K-1) (by omega) (by omega) (by omega)
  -- 4^K = 4 * 4^(K-1)   (Nat.pow_succ …)
  -- gst_pure_lift_or_forced_cascade (4^(K-1)) p hp hd2 hC
  rcases … with
    | inl ⟨hd2', hC'⟩ => exact ⟨p, hp, hd2', hC'⟩              -- PURE branch: DONE
    | inr ⟨hd2', hC', hnext3⟩ =>                                 -- FORCED branch:
      -- gstCarry (4^K) p ∈ {1,2}, gstCarry (4^K) (p+1) = 3
      -- if gstDigit (4^K) (p+1) = 2:  ⟨p+1, …, hnext3 as carry 3⟩ — DONE
      -- else: wave_forced_cascade_close (see 3d)
```

Why the pure branch is really pure: by `gstCarry_forward_exact` /
`gstStepCarry_table`,
`gstCarry (4·R) p = gstStepCarry (gstCarry R p) (gstDigit R p)`, and for a happy
digit-two: carry 3 → `gstStepCarry 3 2 = 3` (STABLE — stays happy through ×4);
carry 0 → `gstStepCarry 0 2 = 2` (degrades to ALT-, then `gstStepCarry 2 2 = 3`
resets one row up). So **carry-3 witnesses lift perfectly**, carry-0 witnesses
degrade into the forced cascade — exactly the two branches the verified theorem
returns. The output digit is always 2 (`gstOutputDigit_forward_exact`,
`(3+8)%3 = (0+8)%3 = 2`).

### 3d. The forced-cascade closer — the sound replacement for the false oscillation

```lean
/-- SOUND REPLACEMENT (new, power-specific — never stated for generic R):
    after a forced cascade at row p in 4^K (K ≥ 8, K ≠ 7), some row ≥ p+1 is a
    happy gate of 4^K. -/
theorem wave_forced_cascade_close (K p : Nat) (hK8 : 8 ≤ K) (hK7 : K ≠ 7)
    (hp : 1 ≤ p) (hd2 : gstDigit (4^K) p = 2)
    (hC : gstCarry (4^K) p = 1 ∨ gstCarry (4^K) p = 2)
    (hnext3 : gstCarry (4^K) (p + 1) = 3) :
    wave_S K := by
  -- ingredients, all verified:
  --   find_highest_d2 (2*K) (4^K) …          : highest d2 h, 1 ≤ h < 2*K
  --   highest_d2_carry (4^K) h …              : C(h+1) ∈ {2, 3}
  --   C(h+1) = 2  ⟹ (C(h)+8)/3 = 2 ∧ C(h) < 4 ⟹ C(h) = 0  ⟹ witness at h   [sound, quarantined L6669–6690]
  --   C(h+1) = 3  ∧ C(h) = 3  ⟹ witness at h                                [sound]
  --   remaining sub-case: C(h) ∈ {1, 2} — closed by wave_alt_exit (RISK 1)
  sorry
```

The last sub-case (`C(h+1) = 3`, `C(h) ∈ {1,2}`, all rows above h are 0) is
**precisely** the configuration that made the generic theorem false (R = 7) and that
occurs in the power family exactly at K = 7 (`4^7 = 11201112₁₂₁₃`, d2s at rows 2 and 8,
`C(8) = 1`). It cannot be closed by `bridge_forces_non_one` alone, because the
non-one digit that theorem finds may sit *above* the last d2 (the carry then decays
1 → 0 through zeros with no digit-two left — no witness). The repair isolates it as
one explicit power-specific lemma:

```lean
/-- POWER-SPECIFIC ALT-EXIT (the honest core of the old "oscillation"):
    the highest digit-two of 4^K is itself a happy gate, for every K ≥ 8. -/
theorem wave_alt_exit (K : Nat) (hK8 : 8 ≤ K) (hK7 : K ≠ 7) :
    ∀ h, 1 ≤ h → gstDigit (4^K) h = 2 →
      (∀ j, h < j → gstDigit (4^K) j ≠ 2) →
      (gstCarry (4^K) h = 0 ∨ gstCarry (4^K) h = 3) := by
  sorry  -- RISK 1: the one genuinely open lemma
```

Candidate proof architectures for `wave_alt_exit` (in preference order):

1. **Trit induction.** `K = 3K' + t`. `4^K = (4^K')^3 · 4^t`. Combine
   `cubic_h_creation_lift` (seeded survive form, produces carry-0 witness at row p+1
   of the cube) with the pure-lift table (`gstStepCarry 3 2 = 3`: multiplying by 4
   keeps a carry-3 digit-two happy; `gstStepCarry 2 2 = 3`, `gstStepCarry 1 2 = 3`:
   any ALT- digit-two resets to carry 3 one row up). The highest d2 of `4^K` is then
   controlled by the highest d2 of `(4^K')^3`, inductively. The base of the trit
   induction is `K ≤ 500` (already covered by `wave_base`).
2. **Row-descent.** The highest d2 of `4^K` below row r is determined by
   `K mod 3^(r-1)` (order of 4 mod 3^r is 3^(r-1)); `wave_alt_exit` is then a
   statement about a finite automaton reading the trits of K — provable by strong
   induction on K with a finite invariant, mirroring how
   `noCommonTwo_exponent_trit_law` already constrains counterexamples.

Neither uses any statement about generic `R`.

---

## 4. Assembly

```lean
theorem wave_strong_induction (K : Nat) (hK5 : 5 ≤ K) (hK7 : K ≠ 7) : wave_S K := by
  induction K using Nat.strongRecOn with
  | ind K ih =>
    by_cases hK500 : K ≤ 500
    · exact wave_base K hK5 hK500 hK7
    · -- K ≥ 501 here; K-1 ≥ 500 ≥ 8, so wave_forced_cascade_close / wave_alt_exit
      -- hypotheses (8 ≤ K) hold for the parent and all children
      exact wave_step K (by omega) (fun k hk hk5 hk7 => ih k hk hk5 hk7)

/-- THE TARGET. Kills the axiom `gst_four_power_direct_existence_inline`. -/
theorem gst_four_power_direct_existence_inline :
    GSTFourPowerDirectExistence.FourPowerDirectExistence := by
  intro K hK5 hK7
  exact wave_commonTwo_of_S K (wave_strong_induction K hK5 hK7)
```

(Downstream re-wiring, outside this slice's scope but required for the axiom to be
dead rather than shadowed: `gst_four_power_creation_master_inline` (monolith L16933)
and the compatibility wrapper `gst_four_power_creation_certificate_inline`
(GSTPrefixOneOntologicalEscape.lean L99) must be re-pointed from the axiom to the
new theorem, or the import chain re-sorted so the pipeline's provider route is used.)

---

## 5. RISKS

1. **`wave_alt_exit` is open mathematics, not bookkeeping.** It is exactly the
   power-specific content the removed false generic oscillation pretended to supply;
   empirically it holds for every K ≥ 8 ever tested (the exception set of the whole
   statement is `{0,1,2,3,4,7}` and 7 is precisely an `alt_exit` failure:
   `4^7 = 1 1 2 0 1 1 1 1 2₃`, highest d2 at row 8 with carry 1). To verify:
   build the trit induction of §3d-1 on top of `cubic_h_creation_lift` +
   `gstStepCarry_table` + `gst_pure_lift_or_forced_cascade`, or the automaton
   invariant of §3d-2. Without it the residual classes of §3c cannot close.
   *Mitigation if it resists:* shrink the residual set by proving more row classes
   (rows 5+) so that `ih(K-1)`+pure-branch covers more of §3c, or split
   `wave_forced_cascade_close` so the carry-0-degradation case is handled by
   re-invoking `ih` at a *smaller exponent of the same trit class* rather than at
   K-1.
2. **`h_creation_cascade_lift` is vacuous — do not use it.** Its hypothesis
   (`d_p(4^(3^(s+1)m)) = 2` at `p ≤ s-1`) contradicts `cascade_universal` (digits of
   `4^(3^(s+1)m)` at rows ≤ s+1 are all 0). Any plan text that cites "cascade lift"
   as a descent engine must be re-read as citing `cubic_h_creation_lift` instead.
3. **`cubic_lift_mod81` is too weak for the cube case.** It yields only
   `hasTernaryTwo`, not a certificate/`wave_S`; the C0 case of §3b must go through
   `cubic_h_creation_lift`'s *seeded* hypotheses (`4^m % 3^p = 1`), which hold only
   when `3^(p-1) ∣ m`. Coverage of `K = 3K'` with unseeded `K'` currently falls to
   §3c. Verify: enumerate which `K % 81` the seeded form actually covers.
4. **Definitional-bridge bookkeeping** (`wave_commonTwo_of_S`,
   `wave_S_of_commonTwo`): `digit3` (GSTFourPowerDirectResidue), `gstDigit`,
   `gstDigitS` are all `R / 3^p % 3` but live in different namespaces/files;
   `gstAffineMulCarryS 4 0 H q = gstCarry H q` is definitional only after unfolding
   `gstAffineMulCarryS` and `Nat.zero_add`-normalization. Expect `rfl`/`simp only
   [...]` friction, not mathematical difficulty. `digit3_four_mul` lives in
   GSTFourPowerDirectAdditionCarry (used by `commonTwo_to_physical_happy_row`);
   confirm its exact signature before use.
5. **`RowFourClass` contents unverified in this slice** — the coverage count
   "44/81" assumes 14 classes; read `RowFourClass`'s definition in
   GSTFourPowerDirectResidue81 before relying on coverage arithmetic in the base-case
   argument (this affects only the *verdict text*, not the proof: the decide covers
   everything anyway).
6. **Base decide boundary:** `hCreationCheck_univ` is `∀ k < 501` (legal, N = 501,
   NOT > 501) with all quantities < 3^52. Do NOT strengthen it to `∀ k < 502` or
   beyond, and do NOT re-run it — it is already compiled. If the base is ever
   restructured, the cost bound must be restated: 501 exponents × ≤ 50 rows ×
   modmul on < 2^82 numbers.
7. **Strong-recursion shape:** `Nat.strongRecOn` with the `ih` restricted by
   `5 ≤ k → k ≠ 7` (as in the quarantined `erdos_ternary_2_even_universal`, L6731) —
   make sure `wave_step`'s recursive calls pass the side conditions for `K-1 ≥ 500`
   (automatic when `501 ≤ K`) and for any §3d-1 trit-recursive calls (child exponents
   can drop below 5 only in the trit base, which must be routed to `wave_base` /
   the row classes, never to `wave_alt_exit` at `K < 8`).
8. **Worklog/production wiring:** the axiom remains imported by
   `gst_four_power_creation_certificate_inline` (GSTPrefixOneOntologicalEscape.lean
   L99–104) and `gst_four_power_creation_master_inline` (monolith L16933–16937).
   This slice delivers the proof object; a follow-up edit must swap those two
   `exact`-lines to the new no-axiom theorem (or to the provider pipeline) and
   re-run `#print axioms` on the tail.
