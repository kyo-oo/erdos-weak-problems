# PLAN — Slice 2-d: The VERIFIED bridge for `gst_four_power_direct_existence_inline`

Target (verbatim, `GSTPrefixOneOntologicalEscape.lean:93-94`):
```lean
theorem gst_four_power_direct_existence_inline :
    GSTFourPowerDirectExistence.FourPowerDirectExistence
```
(equal to `∀ K ≥ 5, K ≠ 7 → ∃ p ≥ 1, digit3 (4^K) p = 2 ∧ digit3 (4^(K+1)) p = 2`
by `FourPowerDirectExistence`/`CommonTwo` defs, DISCOVERY §1.)

Every name below was seen with the verbatim signature recorded in DISCOVERY.md.
No sorry/admit/axiom; every new helper is prefixed `wavd_`.
Compile site: `/home/z/erdosternary2/` (the agent-work/src slice is missing the
pipeline's imports — RISK 6).

---

## A. The complete have-chain (provider-parameterized; compiles today)

Place in `GSTPrefixOneOntologicalEscape.lean` (the axiom file; it already
imports `GSTFourPowerDirectExistenceProviderPipeline` at its line 7, so all
names below resolve; nothing new needs importing):

```lean
/-- WAVE slice 2-d: direct existence from the checked physical Happy provider. -/
theorem wavd_four_power_direct_existence_of_provider
    (hProvider : GSTFourPowerDirectExistenceProviderPipeline.FourPowerHappyGeThreeProvider) :
    GSTFourPowerDirectExistence.FourPowerDirectExistence :=
  GSTFourPowerDirectExistenceProviderPipeline.fourPowerDirectExistence_noAxiom_from_provider
    hProvider

/-- WAVE slice 2-d: same route through the Chat-2 no-bad-affine-channel gate. -/
theorem wavd_four_power_direct_existence_of_no_bad_channel
    (hNoBad : GSTFourPowerDirectExistenceProviderPipeline.FourPowerDirectNoBadAffineChannelOne) :
    GSTFourPowerDirectExistence.FourPowerDirectExistence :=
  GSTFourPowerDirectExistenceProviderPipeline.fourPowerDirectExistence_noAxiom_from_no_bad_affine_channel_one
    hNoBad

/-- WAVE slice 2-d: the verified creation master derived from a provider —
this is the exact content of monolith `gst_four_power_creation_master_inline`
(ErdosTernary2.lean:16933) without the axiom. -/
theorem wavd_four_power_creation_master_of_provider
    (hProvider : GSTFourPowerDirectExistenceProviderPipeline.FourPowerHappyGeThreeProvider) :
    GSTFourPowerOntologicalAdapter.FourPowerCreationMaster := by
  have hDirect : GSTFourPowerDirectExistence.FourPowerDirectExistence :=
    GSTFourPowerDirectExistenceProviderPipeline.fourPowerDirectExistence_noAxiom_from_provider
      hProvider
  have hMaster : GSTFourPowerOntologicalAdapter.FourPowerCreationMaster :=
    GSTFourPowerDirectCreationMaster.directExistence_to_creation_master hDirect
  exact hMaster
```

Step-by-step composition (each arrow = theorem applied to the listed arguments):

1. `GSTFourPowerDirectExistenceProviderPipeline.fourPowerDirectExistence_noAxiom_from_provider hProvider`
   (pipeline :80-83) — `hProvider : FourPowerHappyGeThreeProvider` → `FourPowerDirectExistence`.
   Engine: `fourPowerDirectExistence_from_physical_happy_ge_three`
   (`GSTFourPowerDirectExistenceNoAxiom.lean:69-76`), which needs NO extra
   hypotheses and closes the `5 ≤ K ≤ 7` band by `commonTwo_five` (:57),
   `commonTwo_six` (:62), `(hK7 rfl).elim` for `K = 7`, and `K ≥ 8` by
   `happyCell_to_commonTwo K p (by omega) hHappy` (:33-39, `hp : 1 ≤ p` from `3 ≤ p`).
2. `GSTFourPowerDirectCreationMaster.directExistence_to_creation_master hDirect`
   (DirectCreationMaster :50-52) — `hDirect : FourPowerDirectExistence` → `FourPowerCreationMaster`.
   (Pre-composed variant already committed: pipeline :130-135
   `fourPowerCreationMaster_noAxiom_from_provider hProvider` — identical result, usable instead.)
3. `GSTFourPowerOntologicalAdapter.gst_four_power_ontological_navigation_of_master hMaster K hK5 hK7`
   (Adapter :52-56) — → `Navigation (4^K)` (i.e. `GSTCanonicalTailStateIso.Navigation`).
4. `gst_navigation_witness_of_standalone_navigation (4^K) hNav` (monolith :16899-16901)
   — → `GSTNavigationWitness (4^K)`. (Monolith-side only; lives in `ErdosTernary2.lean`,
   cannot be referenced from the escape file — the monolith imports the escape
   file, not vice versa. This link is exactly monolith lines 16988-16992.)

Monolith-side tail (for reference; this is what the existing
`gst_power_two_wave_large` proof at :16985-16994 already does):

```lean
-- inside ErdosTernary2.lean, once the master is theorem-backed:
have hnav0 : GSTCanonicalTailStateIso.Navigation (4^a) :=
  GSTFourPowerOntologicalAdapter.gst_four_power_ontological_navigation_of_master
    hMaster a (by omega) (by omega)
have hnav : GSTNavigationWitness (4^a) :=
  gst_navigation_witness_of_standalone_navigation (4^a) hnav0
```

## B. The axiom-site replacement (the actual kill)

Once a sibling slice lands an UNCONDITIONAL provider theorem (RISK 1), replace
escape-file lines 93-94:

```lean
-- DELETE:
-- axiom gst_four_power_direct_existence_inline :
--     GSTFourPowerDirectExistence.FourPowerDirectExistence

-- REPLACE WITH (example for the Chat-2 route; name from the sibling slice):
theorem gst_four_power_direct_existence_inline :
    GSTFourPowerDirectExistence.FourPowerDirectExistence :=
  GSTFourPowerDirectExistenceProviderPipeline.fourPowerDirectExistence_noAxiom_from_no_bad_affine_channel_one
    <sibling-slice provider theorem : FourPowerDirectNoBadAffineChannelOne>
```

With that single edit, lines 99-104 (`gst_four_power_creation_certificate_inline`)
and the entire monolith tail (:16933, :16941, :16985, :16997, :17030) keep their
exact current signatures and become axiom-free. No other edits are needed
anywhere: the axiom has exactly one consumer (grep-verified, DISCOVERY §1).

Interim (provider-parameterized) fallback — only if no unconditional provider
lands — requires threading a hypothesis through:
`gst_four_power_creation_certificate_inline` (escape :99) →
`gst_four_power_creation_master_inline` (monolith :16933) →
`gst_prefix_one_navigation_lift` (:16941) / `gst_power_two_wave_large` (:16985)
→ `erdos_ternary_2_even_universal` (:16997) → `erdos_ternary_2_universal`
(:17030, public zero-arg API). See RISK 2.

## C. Seed-zero happy-gate analysis (mandated statement)

The chain does NOT need a seed-zero happy-gate witness IF a canonical-language
HappyCell provider (`FourPowerHappyGeThreeProvider`) or any Chat-2 gate lands:
`happyCell_to_commonTwo` (`GSTFourPowerDirectExistenceNoAxiom.lean:33-39`)
already transports a canonical `HappyCell (carry4 (4^K) p) (digit3 (4^K) p)`
with `1 ≤ p` directly into `CommonTwo K`.

If instead the witness arrives as a seed-zero Happy Gate for `4^K` (monolith
S-language), the theorem that provides the conversion is EXACTLY
`gst_seeded_happy_iff_common_twoS` (ErdosTernary2.lean:12215-12221), instance
`seed := 0`, `H := 4^K`, `hseed : (0:Nat) < 4` (mp direction):
`(gstDigitS (4^K) q = 2 ∧ (gstAffineMulCarryS 4 0 (4^K) q = 0 ∨ … = 3)) →
 (gstDigitS (4^K) q = 2 ∧ gstDigitS (0 + 4*4^K) q = 2)`, and
`0 + 4*4^K = 4^(K+1)` by `Nat.add_zero`/`Nat.pow_succ`.

What is MISSING on that route:
1. The witness itself — no existing theorem supplies
   `∃ q, gstDigitS (4^K) q = 2 ∧ gstDigitS (4^(K+1)) q = 2` (or any S-language
   seed-zero Happy gate) for all `K ≥ 5, K ≠ 7`. That is exactly the open seam
   the axiom encodes; it must come from a sibling slice.
2. A NAMED S-language → direct-residue transport
   (`gstDigitS`/`gstAffineMulCarryS` → `GSTFourPowerDirectResidue.digit3`/
   `directCarry4`) — only inline `simpa` bridges exist (monolith :16869-16872,
   :16904-16910; HappyBridge :51-52 chains canonical ↔ direct-residue). If the
   witness lands in S-language, a `wavd_` transport lemma must be written; the
   two-step exit is: S-language → canonical (simpa of the defs, as at
   monolith :16869-16872) → `happyCell_to_commonTwo`.

## D. RISKS (numbered)

1. **No unconditional provider exists.** `FourPowerHappyGeThreeProvider`,
   `FourPowerCommonTwoGeThreeProvider`, `FourPowerDirectNoCounterexampleClosure`,
   `FourPowerDirectNoBadAffineChannelOne` (pipeline :43/:53/:60/:65) and the
   prefix route (escape :70) are `Prop` definitions serving as hypotheses;
   grep over the whole live project finds no theorem concluding any of them.
   The bridge of §A is complete and verified, but the axiom can only be KILLED
   by a sibling slice proving one of these (the declared final target is
   `FourPowerDirectNoBadAffineChannelOne`, pipeline :63-66). Until then,
   `wavd_four_power_direct_existence_of_*` remain conditional.
2. **Signature/threading risk if the provider stays hypothetical.**
   `gst_four_power_creation_certificate_inline` (escape :99-104) and monolith
   `gst_four_power_creation_master_inline` (:16933), `gst_prefix_one_navigation_lift`
   (:16941), `erdos_ternary_2_universal` (:17030) are all ZERO-ARGUMENT on the
   master. A provider-parameterized replacement forces adding a hypothesis to
   every one of them (5+ declarations, 2 files), changing the public API of
   `erdos_ternary_2_universal`. Clean kill ⇒ provider must be a theorem.
3. **Namespace discipline.** From the escape file (which has no `open` of the
   relevant namespaces at root level): use fully qualified
   `GSTFourPowerDirectExistenceProviderPipeline.fourPowerDirectExistence_noAxiom_from_provider`,
   `GSTFourPowerDirectCreationMaster.directExistence_to_creation_master`,
   `GSTFourPowerDirectExistence.FourPowerDirectExistence` (the existing escape
   code at :48/:52/:58/:103 already follows exactly this qualification).
   `FourPowerCreationMaster`/`Navigation` unqualified only work inside
   namespaces that `open GSTFourPowerOntologicalAdapter`/`GSTCanonicalTailStateIso`.
4. **Link 4 is monolith-side only.** `gst_navigation_witness_of_standalone_navigation`
   is root-level in `ErdosTernary2.lean`, which imports the escape file; the
   escape file must not try to reference it (import cycle). The escape file's
   natural strongest export is `Navigation (4^K)` (via Adapter :52) — exactly
   what monolith :16988-16992 consumes.
5. **`K ≠ 7` vs `K = 7` handling is inside the engine** — the pipeline wrappers
   take `(hK7 : K ≠ 7)` and the engine kills `K = 7` by `(hK7 rfl).elim`
   (NoAxiom :85). No mismatch with the axiom statement (`K ≠ 7`).
6. **Sandbox gap.** `agent-work/src/` lacks `GSTFourPowerDirectExistenceNoAxiom.lean`,
   `GSTCanonicalTailStateIso.lean`, `GSTFourPowerDirectAdditionCarry.lean`,
   `GSTFourPowerDirectChat2Application.lean` etc., so the pipeline (and hence
   §A) cannot compile there; it compiles in `/home/z/erdosternary2/` (the seven
   curated files are byte-identical to it). Verification build must run there.
7. **`commonTwo_five`/`commonTwo_six` are `norm_num`-on-`digit3` computations**
   (NoAxiom :57-64) — already committed and `#print axioms`-audited in the live
   project; no risk, but they are the only base-case content of the `5 ≤ K ≤ 7`
   band.
8. **Seeded-happy route language mismatch** (§C.2): `gst_seeded_happy_iff_common_twoS`
   speaks `gstDigitS`/`gstAffineMulCarryS`, not `digit3`/`directCarry4`; a
   `wavd_` transport lemma would be new mathematics-adjacent glue (feasible via
   the same `simpa` chains seen at monolith :16869-16872, but currently unwritten).

## E. Verdict

Every implication link is signature-verified against live source (DISCOVERY §5).
The chain closes the axiom **iff** one provider theorem lands; with the Chat-2
gate (`FourPowerDirectNoBadAffineChannelOne`) as the declared final target, the
axiom-site edit of §B is a one-statement, one-file change with zero downstream
signature churn.
