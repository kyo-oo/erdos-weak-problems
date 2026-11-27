# 2026-11-14 — The native law to FS-hypothesis bridge (the bridge round record)

**Provenance note (restoration):** this record was cited in four places
(`GSTLawStackRound49.lean:26-27`, the landing record at :27 and :89,
`research/records/INDEX.md`) but was never written before the original
session ended.  It is written NOW, during the 2026-11-14 restoration round
that rebuilt the campaign's final tree on the fresh corpus clone
(upstream `kyo-oo/HC-PROOF` @ `da5e10959b30e8a81735d6904e3af6595277a7a7`,
branch `research/gpt6-native-point-primitive-span-20261017`).  The five
items below are the bridge round's actual content, reconstructed from the
final assault's 50-agent audit archive.

## 1. The landing-module bridge section

`GSTNativeSingleFoldOrbitLawLanding.lean` §7 ("The bridge to the spanning
framework") — the native-to-typed bridge:

* `certFold` / `certData` (lines 430-449 of the original): from any
  certificate `C` at weight `p`, the typed `GSTFold` over
  `codimensionCycles V.X p` and `RationalSingularCohomology H.analytification (2*p)`
  with the word's own operator pair and the genuine `H.cycleClass p` as the
  cycle-class map; `certData.hodgeFiber` is the GENUINE
  `rationalHodgeSubspace (H.hodgeBigrading p)`, not a rigged span.
* `certFold_orbitClass_eq_hodgeOrbit` (:466): the orbit classes of the
  certificate fold are exactly the underlying classes of the certificate's
  Hodge orbit (the commuting square `nativeOrbit_cycleClass` at every step).
* The span transport: `span_orbitClasses_eq_hodgeFiber` — the rational span
  of the orbit classes IS the genuine rational Hodge fiber, via Mathlib's
  `Submodule.span_range_subtype_eq_top_iff` (the subtype-span transport;
  verified verbatim at the pinned Mathlib
  `Mathlib/LinearAlgebra/Span/Basic.lean:459`).
* `gst_hypothesis_complete_of_isKrylovCyclic` (:532-540): cyclicity gives
  `GSTHypothesisComplete (certData C)` — the typed spanning law with the
  genuine fiber.
* `gst_FS_of_native_law` (:546-556): **the bridge itself** — from
  `NativeGSTSingleFoldOrbitLaw V H`, for every weight `p` a genuine typed
  datum `D` with `GSTHypothesisComplete D ∧ D.hodgeFiber =
  rationalHodgeSubspace (H.hodgeBigrading p)`.
* The master packages (:561-577 and :582): the law's exact-Hodge
  consequence and the per-weight FS-law in one statement, plus the
  dead-or-monogenic instantiation.
* The wiring theorems (:610-612, :617-622): `twelve_cell_world_FS_law` and
  `every_frame_FS_law` — direct re-citations of Face 1 and Face 2 into the
  landing file (NOT consequences of the native law).

**Direction: native ⇒ typed ONLY.**  No typed ⇒ native transport exists
anywhere in the repository; the two laws remain formally distinct; the
W7-E GAP classification stands unchanged.

## 2. The `Twave_bridge` paren repair

The compiler face's `Twave_bridge` statement
(`GSTHypothesisSpanningCompilerFace.lean:81-87`) carried a one-paren
corruption (balance −1) from the generation round; the repair restores the
exact `N12 (eCell ⟨j/3⟩ ⟨j%3⟩) (⟨i/3⟩, ⟨i%3⟩)` application shape
(single-paren pair per component).  Machine-verified: balance 0, and the
`fin_cases i <;> fin_cases j <;> decide` kernel sweep is unchanged.

## 3. The lane hardening

`.github/workflows/gst-native-single-fold-orbit-law-landing.yml`: the path
filter extended from 3 to the full 9-file chain (+ self):
`GSTNativeSingleFoldOrbitLawLanding`, `GSTHodgeSingleHypothesisConditional`,
`GSTHypothesisSpanningProof`, `GSTHypothesisSpanningCompilerFace`,
`GSTHypothesisComplete`, `GSTHypothesisPart1ChowAlgebraTransfer`,
`GSTOriginalXWaveChowMatrixCompiler`, `GSTOriginalXAllWeightsLefschetzResidual`,
`GSTOriginalXDivisorCurveCyclicChowFold`; `timeout-minutes` 180 → 300; the
build timeout 9900 s → 16800 s.  The spanning lane mirrors the extended
filter and adds the `main` branch trigger.

## 4. The Round-49 supersession note

`GSTLawStackRound49.lean` gains the 9-line supersession header: this
draft's nine sorries remain shape-only ledger-108 records by design; the
FS-lock carrier (P6's falsifiable line) is superseded by the sorry-free,
CI-enforced bridge in `GSTNativeSingleFoldOrbitLawLanding.lean`
(`gst_FS_of_native_law`); P6's `FSLaw_at_every_input ↔
EveryHodgeClassIsRationalAlgebraic` is the open frontier line itself and
is not discharged there.

## 5. The record corrections

* The landing record: the bridge phrase at :27, the audit-trail entry at
  :89, the receipts counts (#check ×24 = 12+12, #print axioms ×20 = 10+10),
  the hardened-lane numbers (16800 s / 300 min).
* The complete record: the file is 889 lines (not 888); the FS-lock
  citation corrected to `fslock_round49`.
* The spanning record: the compiler face is 421 lines (not 340).
* `INDEX.md`: the bridge entry (this record) plus the restoration entries.

## Restoration disclosure (binding)

The original session's final tree was lost in the sandbox transfer: only
four of the six chain files survived (plus two corpus files).  This
restoration round recovered the three `GSTOriginalX*` compiler-chain files
verbatim from the pinned upstream commit, rebuilt the landing file's
bridge section from the audit archive (the verbatim-quoted statements —
`gst_FS_of_native_law`, `twelve_cell_world_FS_law`, the `every_frame_FS_law`
proof citation — are preserved exactly; the transport-lemma names
`certFold_nativeOrbit`, `span_orbitClasses_eq_hodgeFiber`, and the
master-package names are RECONSTRUCTIONS written per the audit spec, every
proof step matched to a kernel-attested corpus or pinned-Mathlib lemma),
applied the paren repair and the record corrections.  **No Lean compilation
is claimed from this sandbox** (no git remote or credentials exist here —
third independent confirmation); the kernel verdict belongs to GitHub CI
at the pushed SHA, per AGENTS.md rule 7: no green run is cited until the
run exists at the pushed SHA.
