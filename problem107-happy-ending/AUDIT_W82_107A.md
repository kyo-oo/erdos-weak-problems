# AUDIT — W82-107A `nonempty_cardSet` kernel (adversarial, fresh eyes, lane W82-107B)

TASK ID: W82-107B | AUDITED LANE: W82-107A (`problem107-happy-ending/DM107_Proof_A.lean`,
branch `w82-107a`, kernel commit `9cc7f48`, repair r1 `1fc89c1`) | CI job: `kernel-107dm-a`.
Auditor: KILLER W82-107B (independent lane). English only. Every check below was
re-executed on the actual files at audit time (receipts inline). Adversarial stance:
assume the kernel is broken until the checks say otherwise.

## A1. STATEMENT BYTE-MATCH vs the official spec (DM107_Official.lean)

Spec record (problem107-happy-ending/DM107_Official.lean:57, the verbatim
DeepMind formal-conjectures @ 2207c54d block):

    theorem nonempty_cardSet : ∀ n ≥ 3, (cardSet n).Nonempty

Lane A kernel (DM107_Proof_A.lean:1504):

    theorem nonempty_cardSet : ∀ n ≥ 3, (cardSet n).Nonempty :=

**VERDICT: byte-identical** (modulo the spec block's 4-space record indentation
and the kernel's `:=` proof separator). Diff receipt: the only diff line is the
leading indentation of the spec record. No quantifier reordering, no
`Finset`/`Set` coercion drift, no renamed predicate.

## A2. OFFICIAL `cardSet`/`f` RE-DECLARATION FIDELITY

The kernel cannot import the official statement file (standalone `lake env lean`
target), so it re-declares the definitions. Byte-diff of the re-declared block
against DM107_Official.lean L42–47 (`rg -A2 '^def cardSet'` / `'^noncomputable def f'`
on both files, then diff): **IDENTICAL, both definitions** — same names, same
binder shapes, same bodies, same namespace `Erdos107`, same `noncomputable` on `f`.

## A3. SORRY / AXIOM SCAN

`rg -n "sorry|admit|native_decide|sorryAx|Classical.choice"` over the kernel:
**zero matches** (the only hits are the header's own "Zero sorry, zero
native_decide" declaration). No `axiom` commands, no `unsafe`, no `partial`.
The kernel ends with `#print axioms` on the five headline/corollary theorems
(the CI job greps for the expected `does not depend on any axioms` /
`depends on axioms` lines). `Classical.choose` IS used (in `pointOfX`) — that
is a term, not an axiom declaration; it flows into the `Classical.choice`
axiom dependency of `#print axioms`, which is exactly what the CI grep
acknowledges (`(does not depend on any axioms|depends on axioms)`).

## A4. HIDDEN HYPOTHESES / STRENGTHENED TARGET

`nonempty_cardSet : ∀ n ≥ 3, (cardSet n).Nonempty` — no hypotheses at all;
the statement takes nothing for granted. The load-bearing interior theorem
`erdosSzekeresUpper_mem_cardSet {k : ℕ} (hk : 2 ≤ k)` has exactly the one
hypothesis `2 ≤ k` — weaker than `3 ≤ k`, so the kill covers MORE than the
target scope. `nonempty_cardSet_all (n : ℕ)` (no hypotheses) covers all n ∈ ℕ.
**No hidden strengthening, no weasel scope.**

## A5. DEFINITION-DRIFT DIFF vs FC/Geometry/TwoD.lean (the vendored official)

The kernel does NOT re-declare `NonTrilinear` / `ConvexIndep` / `HasConvexNGon`
/ `IsCcwConvexPolygon` / the `ℝ²` notation. Scan receipt: the only top-level
`def`s in the kernel are its own working definitions (mkPt, slopeLt, slopeGt,
lineSide, halfPlaneLe, IsXMonotone, IsSeqNonTrilinearOn, CupChainEnding,
CapChainStarting, HasCup, HasCap, IsCupSet, IsCapSet, pointOfX, xSortedX,
xSortedSeq, shearPt, shearLinearMap, avoidFinsetReal, forbiddenShearSlopes,
goodShearSlope, erdosSzekeresUpper, erdosSzekeresConjectured) plus the
re-declared official `cardSet`/`f`. The official geometric predicates resolve
against the `import FC.Geometry.TwoD` declarations:
- `NonTrilinear` — FC's `Set.Triplewise` packaging. The kernel adds ONE
  definitional bridge `nonTrilinear_iff : ... ↔ ... := Iff.rfl` (definitionally
  true — no drift possible), used once.
- `ConvexIndep`, `HasConvexNGon` — used with FC's exact shapes
  (`HasConvexNGon k (T : Set ℝ²)` with the `∃ S : Finset ℝ², S.card = n ∧
  ↑S ⊆ P ∧ ConvexIndep S` body). No shadowing instance or local notation found.
- The `convexIndep_triple_of_not_collinear` re-proof inside the kernel is the
  official anchor's proof (DM107_Official.lean L78–99) re-stated because the
  anchor is `private` — byte-diff of the proof script shows the ONLY
  differences are two explanatory comment lines the official anchor carries.
- `ℝ²` resolves to the FC scoped notation (kernel opens `EuclideanGeometry`).

**VERDICT: zero definition drift.**

## A6. UPSTREAM PORT FIDELITY (linrock/math-proofs @ cd3cf0b1)

Vendored upstream copies exist on the lane branch
(problem107-happy-ending/vendor_linrock/: Solution, Statement, Blueprint107,
Erdos107Unified435, InductiveKCupKCap107, XMonotonePerturbation107 — commit
9d6b952). Spot-audit of the port (this auditor read the dependency cone of
`nonempty_cardSet` end to end):
- `erdos_szekeres_cup_cap_theorem_on` (the ES 1935 Pascal-splitting
  pigeonhole induction) — proof script matches the vendored
  XMonotonePerturbation107.lean localization, with `Nat.choose_succ_succ`'s
  argument shuffle by `simpa [Nat.add_assoc, ...]` intact.
- The shear invariance `lineSide_shearPt`, the half-plane separation
  `convexIndep_of_pointwise_strict_sep`, the skipped-chord lemmas and the
  all-triple `convexIndep_of_isCupSet`/`of_isCapSet` match the vendored
  sources section by section.
- Adaptations are the recorded four (module syntax, toolchain, official-defs
  substitution + `nonTrilinear_iff` bridge, cone restriction). The
  deprecated-at-v4.33.0-rc2 alias `Set.image_diff` (= `Set.image_sdiff`,
  Mathlib v4.33.0-rc2 Mathlib/Data/Set/Image.lean:382) is used at one site
  with `set_option linter.deprecated false` — verified present at the pinned
  toolchain by this auditor (independent of lane A's own API audit).

## A7. CI VERDICT (at audit time)

- Run 44966751185 (kernel commit 9cc7f48): `kernel-107dm-a` **failure** —
  root-caused from the job log to the campaign FOUNDATION defect
  (`FC/Combinatorics/SimpleGraph/PathGraph.lean` collided with Mathlib
  v4.33.0-rc2's own `SimpleGraph.pathGraph`; `lake build FC` failed BEFORE the
  kernel was ever compiled — the kernel's own compile step never ran). NOT a
  kernel defect.
- Repair r1 (1fc89c1: merge campaign f2b9949 which deletes the duplicate;
  kernel untouched) — run 44968437049 queued at audit time. **The kernel's
  own CI verdict is PENDING on that run; this audit's structural checks are
  all green.**

## A8. AUDIT VERDICT

**STRUCTURALLY GREEN — no defects found.** Statement byte-match ✓, official
definitions re-declared verbatim with zero drift ✓, zero sorry/axiom
commands ✓, no hidden hypotheses ✓, upstream port faithful with all
adaptations recorded ✓, honest scope discipline (the open core `erdos_107`
not claimed; only the solved variant) ✓. The only open item is the CI verdict
of repair run 44968437049, which was queued (not failed) when this audit
closed; the failure it repairs was the campaign foundation's PathGraph
collision, outside lane A's kernel.

Cross-reference: lane B's kernel (DM107_Proof_B.lean, this lane) reuses lane
A's toolchain-adapted dependency cone §0–§11 verbatim with attribution and
independently re-derives lane A's target as a corollary (`nonempty_cardSet`
there) — a second, independent compilation of the same cone.
