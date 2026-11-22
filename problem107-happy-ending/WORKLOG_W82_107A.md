# WORKLOG — W82-107A: `nonempty_cardSet` (the official solved variant of Erdős #107)

TASK ID: W82-107A | LANE: problem107-happy-ending | BRANCH: w82-107a
Kernel: `problem107-happy-ending/DM107_Proof_A.lean` | CI job: `kernel-107dm-a`
(.github/workflows/kills.yml). GitHub CI is the only Lean verdict (toolchain
leanprover/lean4:v4.33.0-rc2, Mathlib v4.33.0-rc2, `lake build FC` + Arsenal +
`lake env lean problem107-happy-ending/DM107_Proof_A.lean`).

## 1. WHAT WAS KILLED

    theorem Erdos107.nonempty_cardSet : ∀ n ≥ 3, (cardSet n).Nonempty

— the OFFICIAL DeepMind formal-conjectures statement (google-deepmind/
formal-conjectures @ 2207c54d, `FormalConjectures/ErdosProblems/107.lean`),
the official SOLVED variant of Erdős problem #107 (happy ending): for every
n ≥ 3 there is an N such that every N-point set in the plane with no three
collinear contains n points in convex position. Statement signature
byte-identical to the spec in `problem107-happy-ending/DM107_Official.lean`;
`cardSet`/`f` re-declared VERBATIM from that file (the official statement
file is compiled standalone by the kernel-fc CI job and cannot be imported
by an out-of-library kernel, so the definitions are restated verbatim —
identical names, identical bodies, namespace `Erdos107`).

The proof content: for every n ≥ 3 the witness N = erdosSzekeresUpper n =
C(2n−4, n−2) + 1 lies in cardSet n (indeed for every n ∈ ℕ: `nonempty_cardSet_all`
proves `(cardSet n).Nonempty` for ALL n; n < 3 via self-membership, n ≥ 3 via the
Erdős–Szekeres cup–cap witness; `nonempty_cardSet` is its n ≥ 3 corollary).

## 2. WHAT WAS PORTED, FROM WHERE (pin)

Upstream citation (the `formal_proof using lean4` tag on the official DM
statement): **linrock/math-proofs @ cd3cf0b176e95209584bf35555a7c0e501255f6e**,
file `erdos-107/Solution.lean#L59`. Fetched and vendored verbatim under
`problem107-happy-ending/vendor_linrock/` (Apache-2.0; Copyright 2026 The
Formal Conjectures Authors / Linmiao Xu):

| vendored file | upstream path (same commit) |
|---|---|
| `vendor_linrock/Solution.lean` | `erdos-107/Solution.lean` |
| `vendor_linrock/Statement.lean` | `erdos-107/Statement.lean` |
| `vendor_linrock/Blueprint107.lean` | `erdos-107/Proofs/Blueprint107.lean` |
| `vendor_linrock/Erdos107Unified435.lean` | `erdos-107/Proofs/Erdos107Unified435.lean` |
| `vendor_linrock/InductiveKCupKCap107.lean` | `erdos-107/Proofs/InductiveKCupKCapConvexityAndKKSWedgePentagonForcing107.lean` |
| `vendor_linrock/XMonotonePerturbation107.lean` | `erdos-107/Proofs/XMonotonePerturbationBridgeAndWedgePigeonholePentagon107.lean` |

The upstream chain: Solution.lean:59 `nonempty_cardSet` delegates to
`Erdos107.nonempty_cardSet_all` (XMonotonePerturbation107.lean:574), whose
n ≥ 3 branch is `erdosSzekeresUpper_mem_cardSet` (XMono:566) ←
`hasConvexNGon_of_nonTrilinear_and_card_ge` (XMono:482) ←
`hasConvexNGon_of_x_injOn_and_nonTrilinear` (XMono:461) ←
`erdos_szekeres_cup_cap_theorem_on` (XMono:412) + the cup/cap → ConvexIndep
machinery of InductiveKCupKCap107.lean (§1) + the point/lineSide/half-plane
calculus of Erdos107Unified435.lean (§1, §3–§4, §6). My kernel ports exactly
this dependency cone (118 declarations, ~1500 lines); everything outside the
cone (Klein f(4)=5, KKS pentagon forcing, Tóth–Valtr bounds, Dilworth
material, the 8-point construction) is deliberately NOT ported.

Proof scripts inside the cone are copied verbatim except where an adaptation
below required touching a line. Declaration names kept identical to upstream.

## 3. EVERY ADAPTATION (upstream → this kernel)

1. **Module-system syntax stripped**: upstream files are Lean v4.35 module
   files (`module`, `public import`, `@[expose] public section`); this kernel
   is a classic single-file module (`import Mathlib` etc.).
2. **Toolchain re-target**: upstream compiles at leanprover/lean4:v4.35.0-rc2
   (their lake-manifest); this kernel targets the campaign toolchain
   v4.33.0-rc2 / Mathlib v4.33.0-rc2. API audit performed before submission
   (orderEmbOfFin family, Nat.choose_succ_succ(_'), LinearMap.image_convexHull,
   Set.image_diff, Finset.card_image_of_injOn/injective all verified present
   with matching signatures at the v4.33.0-rc2 tag).
3. **Official definitions substituted**: upstream re-defines `NonTrilinear`,
   `ConvexIndep`, `HasConvexNGon` (explicit-∀ shape) and `cardSet`/`f` in its
   own namespace; this kernel uses the VENDORED official definitions from
   `FC.Geometry.TwoD` (`EuclideanGeometry.NonTrilinear` is `Set.Triplewise`-
   packaged, `ConvexIndep`/`HasConvexNGon` byte-identical shapes) and
   re-declares `cardSet`/`f` verbatim from DM107_Official.lean. One new
   DEFINITIONAL bridge lemma was added for the packaging difference:
   `Erdos107.nonTrilinear_iff` (Iff.rfl), used once, in
   `nonTrilinear_image_shearPt` (the only place the port intros through the
   body of a `NonTrilinear` hypothesis; everywhere else the hypothesis is
   only applied, which is definitionally transparent — cf. the certified
   anchor `f_three_eq` in DM107_Official.lean).
4. **Namespace**: everything lives in `namespace Erdos107` (upstream splits
   across Erdos107 / Erdos107.Palomar); the ℝ² notation is the vendored
   `scoped[EuclideanGeometry]` one (upstream declares its own `Plane` abbrev
   + notation — dropped).
5. **Only the cone**: upstream's `nonempty_cardSet_all` case-splits
   `le_or_gt n 3` and uses `self_mem_cardSet_of_le_three` for n ≤ 3; the
   n < 3 branch here additionally routes the 0/1/2 split through the arsenal
   law `ErdosTernary2.lt_three_cases` (see §4) — same mathematical content.
6. **Skipped upstream decls** (outside the cone, names listed for audit):
   parabola/le_of_mem_cardSet machinery, f-monotonicity family,
   cupCapBound arithmetic (recurrence/symmetry/hockey-stick — the `_on`
   theorem is used directly with the (k−2, k−2) diagonal, so `cupCapBound`
   itself is unnecessary), Klein 4/5-point material, lineSide separation
   quartet beyond what cup/cap ConvexIndep needs (lineSide_sep_of_neg_pos,
   the four/five-point convexity criteria), KKS wedge forcing, Dilworth
   material, Tóth–Valtr.
7. **`#print axioms` commands** trimmed to the five ledger lines
   (nonempty_cardSet_all, nonempty_cardSet, erdosSzekeresUpper_mem_cardSet,
   hasConvexNGon_of_nonTrilinear_and_card_ge, dm107a_arsenal_bridge).
8. **Bridge additions (new, not in upstream)**: `erdosSzekeresConjectured`,
   `two_mul_choose_central_le_succ`, `two_pow_le_central_binom`,
   `erdosSzekeresConjectured_le_upper` (ported from upstream
   Erdos107Unified435.lean §4 — kept because the arsenal bridge needs the
   2^(n−2)-type comparison), plus `two_pow_ge_succ` and
   `dm107a_arsenal_bridge` (new; witness sanity, see §4).

## 4. THE ARSENAL BRIDGE (BOSS's law; read-before-cite)

Imports: `import Arsenal.ErdosTernary2.Basic`, `import Arsenal.CardinalWorlds`.
Laws used, each read at its source line before citation:

* `ErdosTernary2.lt_three_cases` — Arsenal/ErdosTernary2/Basic.lean:16
  (n < 3 → n = 0 ∨ n = 1 ∨ n = 2). LOAD-BEARING in `nonempty_cardSet_all`'s
  n < 3 branch, hence in the kill itself (`nonempty_cardSet` is its corollary).
* `two_pow_pos` — Arsenal/CardinalWorlds.lean:420 (0 < 2^j). Used in
  `dm107a_arsenal_bridge`.
* `two_pow_ge2` — Arsenal/CardinalWorlds.lean:431 (2 ≤ 2^j for 1 ≤ j). Used
  in `dm107a_arsenal_bridge`.
* `two_pow_factored` — Arsenal/CardinalWorlds.lean:425 (2^j = 2·2^(j−1) for
  1 ≤ j). Used to prove the in-kernel `two_pow_ge_succ : m + 1 ≤ 2^m`
  (successor step), which feeds the bridge's n ≤ witness bound.

`dm107a_arsenal_bridge n (hn : 3 ≤ n)` certifies the witness arithmetic of
the kill: 0 < 2^(n−2), 2 ≤ 2^(n−2), erdosSzekeresConjectured n ≤
erdosSzekeresUpper n (i.e. 2^(n−2)+1 ≤ C(2n−4, n−2)+1 — the conjectured
open-core threshold is dominated by our witness), and n ≤ erdosSzekeresUpper n
(so the convex n-gon found is a proper part of the witness configuration).
Honesty note (never fake a citation): the binomial law
`two_pow_le_central_binom` (2^k ≤ C(2k,k)) is NOT an arsenal law — it is
ported from upstream Erdos107Unified435.lean:933 (proved there from Mathlib's
Pascal recurrence) and is labeled as such in the kernel.

## 5. DIVERGENCES FROM LINROCK (mathematical content)

None in the cone: every ported theorem has the same statement and the same
proof (modulo §3.1–3.5). The two genuinely new statements
(`two_pow_ge_succ`, `dm107a_arsenal_bridge`) are additions, not alterations,
and are clearly marked. The final theorem statement is byte-identical to the
official spec.

## 6. CI

Job `kernel-107dm-a` in `.github/workflows/kills.yml`, following the
`kernel-fc` pattern: elan v4.33.0-rc2, `lake update`, `lake exe cache get`,
`lake build FC`, `lake build Arsenal.ErdosTernary2.Basic`,
`lake build Arsenal.CardinalWorlds`,
`lake env lean problem107-happy-ending/DM107_Proof_A.lean`, then greps:
no `error:|sorryAx|unknown identifier|unsolved goals|declaration uses
.sorry.`, presence of `DM107A_NONEMPTY_CARDSET_GREEN`, and the
`#print axioms Erdos107.nonempty_cardSet` line present (standard axioms
only — the file-wide sorryAx grep guards the axiom profile).

## 7. STATUS LEDGER

- [x] linrock chain vendored (commit 9d6b952, within first 10 minutes).
- [x] DM107_Proof_A.lean written (complete port, zero sorry).
- [x] CI job kernel-107dm-a wired.
- [ ] CI green (repair loop from Actions logs — see below for the history).

### Repair history
(round 1 = first push; append per round)
