# DISCOVERY — Slice 2-d: Chain Signature Verification

All signatures below are VERBATIM from the source. The seven curated slice files
under `/home/z/agent-work/src/` are byte-identical (diff-verified) to the live
project `/home/z/erdosternary2/`. Line numbers refer to the shared content.

---

## 1. THE AXIOM SITE

**`axiom gst_four_power_direct_existence_inline`** — `GSTPrefixOneOntologicalEscape.lean:93-94`
```lean
axiom gst_four_power_direct_existence_inline :
    GSTFourPowerDirectExistence.FourPowerDirectExistence
```
Exactly ONE consumer (grep over the whole live project):
`gst_four_power_creation_certificate_inline` in the SAME file, line 104.
The monolith's own same-named `gst_four_power_creation_certificate_inline`
(`ErdosTernary2.lean:6434`) is inside a `/- ... -/` comment block (opened at
line 6427, "proof archaeology") — dead code, NOT a consumer.

**Goal statement unfolded** — `GSTFourPowerDirectExistence.lean:26-27` (namespace `GSTFourPowerDirectExistence`):
```lean
def FourPowerDirectExistence : Prop :=
  ∀ K : Nat, 5 ≤ K → K ≠ 7 → CommonTwo K
```
with — `GSTFourPowerDirectExistence.lean:19-22`:
```lean
def CommonTwo (K : Nat) : Prop :=
  ∃ p : Nat, 1 ≤ p ∧
    digit3 (4^K) p = 2 ∧
    digit3 (4^(K+1)) p = 2
```
(`digit3` here is `GSTFourPowerDirectResidue.digit3`.) So the task statement
`∀ K ≥ 5, K ≠ 7 → ∃ p ≥ 1, digit3 (4^K) p = 2 ∧ digit3 (4^(K+1)) p = 2` is
exactly `FourPowerDirectExistence` after unfolding `CommonTwo`. ✓

---

## 2. THE TARGET-SIDE CHAIN (axiom → monolith tail)

**`gst_four_power_creation_certificate_inline`** — `GSTPrefixOneOntologicalEscape.lean:99-104` (root level, imported by `ErdosTernary2.lean:36`):
```lean
theorem gst_four_power_creation_certificate_inline
    (K : Nat) (hK5 : 5 ≤ K) (hK7 : K ≠ 7) :
    GSTFourPowerOntologicalAdapter.CreationCertificate (4^K) := by
  exact
    (GSTFourPowerDirectCreationMaster.directExistence_to_creation_master
      gst_four_power_direct_existence_inline) K hK5 hK7
```
This is the ONLY place the axiom is applied.

**`gst_four_power_creation_master_inline`** — `ErdosTernary2.lean:16933-16937` (monolith tail, THEOREM):
```lean
theorem gst_four_power_creation_master_inline :
    GSTFourPowerOntologicalAdapter.FourPowerCreationMaster := by
  intro K hK5 hK7
  simpa [GSTFourPowerOntologicalAdapter.CreationCertificate] using
    (gst_four_power_creation_certificate_inline K hK5 hK7)
```
NOTE: it is a theorem whose proof transitively uses the axiom via the escape
file. Downstream monolith consumers: `gst_prefix_one_navigation_lift` (16941),
`gst_power_two_wave_large` (16985-16990), `gst_prefix_one_ontological_escape_of_master_inline`
(16914, via `gst_prefix_one_navigation_lift_of_master_inline` 16925), and
eventually `erdos_ternary_2_even_universal` (16997) → `erdos_ternary_2_universal` (17030).

**`gst_four_power_ontological_navigation_of_master`** — `GSTFourPowerOntologicalAdapter.lean:52-56` (namespace `GSTFourPowerOntologicalAdapter`; found here, not in the monolith):
```lean
theorem gst_four_power_ontological_navigation_of_master
    (hMaster : FourPowerCreationMaster)
    (K : Nat) (hK5 : 5 ≤ K) (hK7 : K ≠ 7) :
    Navigation (4^K) :=
  creation_certificate_to_navigation (4^K) (hMaster K hK5 hK7)
```
(`Navigation` = `GSTCanonicalTailStateIso.Navigation`, opened at adapter L8.)
Usage match: monolith 16989-16990 applies it to `gst_four_power_creation_master_inline a (by omega) (by omega)` with `500 < a` — `5 ≤ a`, `a ≠ 7` hold. ✓ Also used in escape L37-38. ✓

**`gst_navigation_witness_of_standalone_navigation`** — `ErdosTernary2.lean:16899-16901` (root level):
```lean
theorem gst_navigation_witness_of_standalone_navigation
    (R : Nat) (h : GSTCanonicalTailStateIso.Navigation R) :
    GSTNavigationWitness R := by
```
Usage match: monolith 16920 (after POE) and 16992 (in `gst_power_two_wave_large`). ✓

**`gst_prefix_one_ontological_escape_of_master`** — `GSTPrefixOneOntologicalEscape.lean:29-32` (namespace `GSTPrefixOneOntologicalEscape`):
```lean
theorem gst_prefix_one_ontological_escape_of_master
    (hMaster : FourPowerCreationMaster)
    (s n : Nat) (hs : 1 ≤ s) (hn : 1 ≤ n) :
    Navigation (canonicalTail s (1 + 3*n)) := by
```
(`FourPowerCreationMaster`/`Navigation`/`canonicalTail` via `open GSTFourPowerOntologicalAdapter`
/ `open GSTPerfectPowerTailNavigation` / `open GSTCanonicalTailStateIso` at escape L14-16.)
Consumed by monolith `gst_prefix_one_ontological_escape_of_master_inline` (16914-16921), which then
applies `gst_navigation_witness_of_standalone_navigation`. ✓

**`directExistence_to_creation_master`** — `GSTFourPowerDirectCreationMaster.lean:50-52` (namespace `GSTFourPowerDirectCreationMaster`):
```lean
theorem directExistence_to_creation_master
    (hDirect : FourPowerDirectExistence) :
    FourPowerCreationMaster := by
```
This is THE bridge from direct existence to the creation master. Also available
pre-composed at pipeline L130-135 and in the transplant probe
(`/home/z/erdosternary2/GSTFourPowerDirectTransplantProbe.lean:43-48`). ✓

**`CreationCertificate`** — `GSTFourPowerOntologicalAdapter.lean:12-16`:
```lean
def CreationCertificate (R : Nat) : Prop :=
  ∃ p : Nat, 1 ≤ p ∧ R / 3^p % 3 = 2 ∧
    ((4 * (R % 3^p)) / 3^p % 3 = 0 ∨
     ((4 * (R % 3^p)) / 3^p % 3 = 1 ∧
      R / 3^(p+1) % 3 = 2))
```
**`FourPowerCreationMaster`** — `GSTFourPowerOntologicalAdapter.lean:20-21`:
```lean
def FourPowerCreationMaster : Prop :=
  ∀ K : Nat, 5 ≤ K → K ≠ 7 → CreationCertificate (4^K)
```

---

## 3. THE NO-AXIOM PROVIDER SIDE (pipeline → direct existence)

All "providers" are currently `Prop` DEFINITIONS (hypotheses), not theorems —
none is proven anywhere in the live project (grep-verified: no theorem
concludes any of them unconditionally).

**`FourPowerHappyGeThreeProvider`** — `GSTFourPowerDirectExistenceProviderPipeline.lean:43-48`:
```lean
def FourPowerHappyGeThreeProvider : Prop :=
  ∀ K : Nat, 8 ≤ K →
    ∃ p : Nat, 3 ≤ p ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^K) p)
        (GSTCanonicalTailStateIso.digit3 (4^K) p)
```

**`FourPowerCommonTwoGeThreeProvider`** — same file `:53-54`:
```lean
def FourPowerCommonTwoGeThreeProvider : Prop :=
  ∀ K : Nat, 8 ≤ K → GSTFourPowerHappyProvider.CommonTwoGeThree K
```

**`FourPowerDirectNoCounterexampleClosure`** — same file `:60-61`:
```lean
def FourPowerDirectNoCounterexampleClosure : Prop :=
  ∀ K : Nat, 5 ≤ K → K ≠ 7 → ¬¬ CommonTwo K
```

**`FourPowerDirectNoBadAffineChannelOne`** — same file `:65-66`:
```lean
def FourPowerDirectNoBadAffineChannelOne : Prop :=
  ∀ K : Nat, 5 ≤ K → K ≠ 7 → ¬ BadChannel 1 (affineOrbit K)
```
(`BadChannel`/`affineOrbit` via `open GSTFourPowerAffineOrbit` / `open GSTFourPowerAffineChannelAutomaton`, pipeline L38-39.)

**Prefix route hypothesis** — `GSTPrefixOneOntologicalEscape.lean:70` (as a theorem hypothesis):
```lean
(hProvider : ∀ K : Nat, 8 ≤ K → GSTFourPowerHappyProvider.PrefixHitGeThree K)
```
with `PrefixHitGeThree` — `GSTFourPowerHappyProvider.lean:29-37`:
```lean
def PrefixHitGeThree (K : Nat) : Prop :=
  ∃ p : Nat, 2 ≤ p ∧
    GSTFourPowerDirectResidue.digit3
        (4^(GSTFourPowerExponentTritObstruction.exponentPrefix K p)) (p+1) =
      GSTFourPowerDirectResidue.digit3
        (4^((GSTFourPowerExponentTritObstruction.exponentPrefix K p)+1)) (p+1) ∧
    GSTFourPowerExponentTritObstruction.exponentTrit K p =
      2 - GSTFourPowerDirectResidue.digit3
        (4^(GSTFourPowerExponentTritObstruction.exponentPrefix K p)) (p+1)
```

**Provider → `FourPowerDirectExistence` bridges** (all THEOREMS, all conditional on a provider):

- `fourPowerDirectExistence_noAxiom_from_provider (hProvider : FourPowerHappyGeThreeProvider) : FourPowerDirectExistence` — pipeline `:80-83`.
  Core engine: **`fourPowerDirectExistence_from_physical_happy_ge_three`** —
  `/home/z/erdosternary2/GSTFourPowerDirectExistenceNoAxiom.lean:69-76` (file NOT in the
  agent-work/src slice; file not in the read list, signature obtained by targeted grep — verbatim):
  ```lean
  theorem fourPowerDirectExistence_from_physical_happy_ge_three
      (happy_ge_three :
        ∀ K : Nat, 8 ≤ K →
          ∃ p : Nat, 3 ≤ p ∧
            GSTCanonicalTailStateIso.HappyCell
              (GSTCanonicalTailStateIso.carry4 (4^K) p)
              (GSTCanonicalTailStateIso.digit3 (4^K) p)) :
      FourPowerDirectExistence := by
  ```
  Proof (NoAxiom L77-85): `K ≥ 8` → `happyCell_to_commonTwo`; `K ∈ {5,6,7}` →
  `commonTwo_five` / `commonTwo_six` / `(hK7 rfl).elim`. This closes the `5 ≤ K ≤ 7` gap.
- `fourPowerDirectExistence_noAxiom_from_commonTwoGeThree (hProvider : FourPowerCommonTwoGeThreeProvider) : FourPowerDirectExistence` — pipeline `:87-92`.
- `fourPowerDirectExistence_noAxiom_from_chat2_closure (hClosed : FourPowerDirectNoCounterexampleClosure) : FourPowerDirectExistence` — pipeline `:96-99`.
- `fourPowerDirectExistence_noAxiom_from_no_bad_affine_channel_one (hNoBad : FourPowerDirectNoBadAffineChannelOne) : FourPowerDirectExistence` — pipeline `:102-105`.

**Row transports inside the engine** — `/home/z/erdosternary2/GSTFourPowerDirectExistenceNoAxiom.lean`:
```lean
theorem happyCell_to_commonTwo
    (K p : Nat) (hp : 1 ≤ p)
    (hHappy :
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^K) p)
        (GSTCanonicalTailStateIso.digit3 (4^K) p)) :
    CommonTwo K := by                -- :33-39
theorem commonTwo_five : CommonTwo 5 := by    -- :57
theorem commonTwo_six : CommonTwo 6 := by    -- :62
```

**Creation-master composition (already committed)** — pipeline `:130-135`:
```lean
theorem fourPowerCreationMaster_noAxiom_from_provider
    (hProvider : FourPowerHappyGeThreeProvider) :
    GSTFourPowerOntologicalAdapter.FourPowerCreationMaster := by
  exact
    GSTFourPowerDirectCreationMaster.directExistence_to_creation_master
      (fourPowerDirectExistence_noAxiom_from_provider hProvider)
```
(analogously `..._from_commonTwoGeThree` :139, `..._from_chat2_closure` :147,
`..._from_no_bad_affine_channel_one` :155; certificate wrappers :163/:172/:180/:189).

---

## 4. THE SEED-ZERO HAPPY GATE

**`gst_seeded_happy_iff_common_twoS`** — `ErdosTernary2.lean:12215-12221`:
```lean
theorem gst_seeded_happy_iff_common_twoS
    (seed H q : Nat)
    (hseed : seed < 4) :
    (gstDigitS H q = 2 ∧
      (gstAffineMulCarryS 4 seed H q = 0 ∨
       gstAffineMulCarryS 4 seed H q = 3)) ↔
    (gstDigitS H q = 2 ∧ gstDigitS (seed + 4*H) q = 2) := by
```
Instance `seed := 0`, `H := 4^K`, `hseed : (0:Nat) < 4`:
`(gstDigitS (4^K) q = 2 ∧ (gstAffineMulCarryS 4 0 (4^K) q = 0 ∨ … = 3)) ↔
 (gstDigitS (4^K) q = 2 ∧ gstDigitS (0 + 4*4^K) q = 2)`, and
`0 + 4*4^K = 4^(K+1)` (`Nat.add_zero`, `Nat.pow_succ`). So the seed-zero Happy
Gate on `4^K` IS `CommonTwo K` restated in the monolith S-language
(`gstDigitS`/`gstAffineMulCarryS`). It is a language converter, NOT a witness
source: no theorem in the read ranges supplies the S-language common-two
witness for all `K ≥ 5, K ≠ 7`.

Language bridges seen (all inline `simpa`, none named standalone):
- monolith 16904-16910: `gstDigit` ↔ `GSTCanonicalTailStateIso.digit3`, `gstCarry` ↔ `GSTCanonicalTailStateIso.carry4` (inside `gst_navigation_witness_of_standalone_navigation`);
- `GSTFourPowerDirectHappyBridge.lean:51-52`: `GSTCanonicalTailStateIso.digit3` ↔ `GSTFourPowerDirectResidue.digit3`;
- monolith 16869-16872: seeded S-language Happy ↔ canonical HappyCell (`gstDigitS`, `gstAffineMulCarryS`, `GSTCanonicalSevenAxisBridge.carry4/digit3` defs unfolded).
- `GSTFourPowerHappyProvider.commonTwoAt_ge_three_to_physical_happy` (:42-48) transports the other way (direct common-two → canonical HappyCell).

---

## 5. FULL VERIFIED CHAIN (one line per link)

```
[MISSING: provider theorem]                       ← sole open mathematical seam
  → fourPowerDirectExistence_noAxiom_from_provider   (pipeline :80)  ✓
      [= fourPowerDirectExistence_from_physical_happy_ge_three (NoAxiom :69),
         K=5: commonTwo_five, K=6: commonTwo_six, K=7: absurd, K≥8: happyCell_to_commonTwo]
  → directExistence_to_creation_master               (DirectCreationMaster :50)  ✓
  → FourPowerCreationMaster  = gst_four_power_creation_master_inline target  ✓
  → gst_four_power_ontological_navigation_of_master  (Adapter :52)  ✓  : Navigation (4^K)
  → gst_navigation_witness_of_standalone_navigation  (monolith :16899)  ✓  : GSTNavigationWitness (4^K)
  → POE (escape :29) / gst_power_two_wave_large (monolith :16985) / erdos_ternary_2_*  ✓
```

Axiom usage path (to be deleted): escape :93 → escape :99-104 → monolith :16933
→ :16941 / :16985 / :16914 → :16997 → :17030.
