# W83-REPAIR-142B — Repair log for `problem142-rk-asymptotic/DM142_Proof_B.lean`

Repair surgeon: W83-REPAIR-142B. Target: DM142_Proof_B.lean (was 644 lines, now 650),
branch `campaign`, first-ever-compile kernel. Method: every external identifier in the
repaired file was **pin-verified against the exact toolchain sources** — Mathlib @
`51e6992efd06126df61a496bebf8f49482a4e129` (lake-manifest pin for `v4.33.0-rc2`) and
leanprover/lean4 @ `v4.33.0-rc2`, fetched raw from GitHub (the WORKLOG's L72 NAME-ATLAS
doctrine; no lake/lean run, CI remains the only compiler). Audit defects D1–D3 applied
verbatim; D5/D6 resolved with pin-verified names; **one NEW critical defect found beyond
the audit** (Bool.and_eq_true is a Prop-equality at this pin, not an Iff).

## REPAIRS APPLIED

### D1 (CRITICAL) — `apDiff_ne_zero` binder transposition — APPLIED
L198 (now L222): `(hu : ∀ y ∈ u, …)` → `(hu : ∀ y ∈ t, …)`. Exactly the audit's one-token
patch. The three bridge call sites needed **no change**: with the corrected binder their
`intro y hy` yields `hy : y ∈ t`, and their existing `rw [hset] at hy` (hset : t = the FC
set-builder from `Set.IsAPOfLength.eq`) now finds the pattern, rewrites to
`y ∈ {a + n • d | (n : ℕ) (_ : n < ↑k)}`, and `obtain ⟨n, -, hn⟩ := hy` destructs the
∃-chain exactly as FC's own `Nat.isAPOfLengthWith_pair` proof does. Verified against the
vendored `Set.IsAPOfLength.eq` (FC/Combinatorics/AP/Basic.lean:145). `hset` is now unused
inside the helper (harmless — theorem binders are not linted as errors).

### D2 (CRITICAL) — forward references to the scanners — APPLIED
The scanner block (old L322–343: `midFree3`/`k4Free`/`k5Free` + docstrings + header) was
moved above §2 and is now §2 ("The scan checkers"), immediately after
`maxCard_ge_of_witness`. The bridges section is now §3; the leftover machinery
(inRange, subset_Icc_of_inRange, ltHead, chainLt, ltAll_cons, nodup_of_chainLt) got a new
§4 header ("Range, monotone-chain and Nodup machinery"); subsequent headers renumbered
(§5 stone builders, §6 witnesses, §7 arsenal, §8 board) and the one in-file §-reference
("(the Cantor-sibling; §6)" → §7) updated. Def-before-use now holds everywhere
(declaration order re-listed and checked: §0 allT/memL → §2 scanners → §3 bridges →
§4 machinery → §5 stone3/4/5 → §6 witnesses+stones → §7 arsenal → §8 board).

### D3 (CRITICAL) — `False` delivered where `↑k ≤ 1` is the goal — APPLIED
The three bridge conclusions now read `exact (hscan …).elim` (dot-notation `False.elim`,
core Prelude.lean:329), exactly as the audit's patch: k=3 (one line), k=4 and k=5
(two-line applications, closing paren placed after the last `(by omega)`).

### D5 (MEDIUM) — `Set.card_mono`/`Set.card_singleton` on `ENat.card` — RESOLVED (encard route)
Both names were name-risk (no CI-green precedent). **Pin ground truth**: Mathlib
`Data/Set/Card.lean:73` has `@[simp] theorem _root_.ENat.card_coe_set_eq (s : Set α) :
ENat.card s = s.encard := rfl` — i.e. `ENat.card` on a set is *definitionally* `Set.encard`,
which has the full API at this pin. The ending of `apDiff_ne_zero` was rewritten:
```lean
have hc : t.encard = ((k : ℕ) : ENat) := hcard              -- defeq via ENat.card_coe_set_eq (rfl)
have h1 : t.encard ≤ ({a} : Set ℕ).encard := Set.encard_le_encard hsub   -- Set/Card.lean:188
rw [Set.encard_singleton] at h1                             -- Set/Card.lean:121, @[simp]
rw [hc] at h1
have h1' : ((k : ℕ) : ENat) ≤ ((1 : ℕ) : ENat) := h1        -- numeral bridge, no metavars
have h2 : k ≤ 1 := ENat.natCast_le_natCast.1 h1'            -- ENat/Basic.lean:393
omega
```
Justification: `Set.encard_le_encard (h : s ⊆ t) : s.encard ≤ t.encard` and
`Set.encard_singleton (e) : ({e} : Set α).encard = 1` both verified verbatim in the pinned
source (namespace `Set`, lines 188/121). The cast step avoids `exact_mod_cast` entirely:
`ENat.natCast_le_natCast {n m : ℕ} : (n : ℕ∞) ≤ (m : ℕ∞) ↔ n ≤ m` is pin-verified
(Mathlib/Data/ENat/Basic.lean:393, namespace `ENat`); the explicit `h1'` ascription
(`≤ ((1 : ℕ) : ENat)`) removes the numeral-unification edge case (the literal `1 : ℕ∞` is
only defeq, not syntactic, to the cast — with `h1'` there are no metavariables left).
Sibling fix: `coe_lt_coe_k`'s proof `by exact_mod_cast h` → `ENat.natCast_lt_natCast.2 h`
(ENat/Basic.lean:389, pin-verified; variable RHS so a clean syntactic `.2`). The old
`ENat.coe_le_coe`/`coe_lt_coe` names are **deprecated aliases** at this pin
(`@[deprecated (since := "2026-07-17")]`) — deliberately NOT used.

### D6 (LOW-MEDIUM) — `List.length_toFinset` — RESOLVED
`List.length_toFinset` does **not** exist at this pin. Replaced at all three stone
builders with `List.toFinset_card_of_nodup (nodup_of_chainLt W hchain)` — verified twice:
(a) pin source `Mathlib/Data/Finset/Card.lean` (the WORKLOG Session-042 NAME-ATLAS
correction "`List.toFinset_card` ✗ → `List.toFinset_card_of_nodup` (Finset/Card.lean:212)"
is recorded from an actual CI failure round), and (b) CI-green precedent:
`problem271-status/StanleyGrowth.lean:810,910` and `problem404-full/ResidualTail.lean:546`
use exactly this name with the positional Nodup argument and are green kernels.

### NEW DEFECT (CRITICAL, missed by the audit) — `Bool.and_eq_true.1/.2` — FIXED (5 sites)
At the pinned toolchain `Bool.and_eq_true` is **an equality of Props, not an Iff**:
`Mathlib/Init/../Init/SimpLemmas.lean:366`:
`@[simp] theorem Bool.and_eq_true (a b : Bool) : ((a && b) = true) = (a = true ∧ b = true)`.
`Eq` has no `.1`/`.2` field, so the file's five `Bool.and_eq_true.1 h` / `.2 ⟨…⟩`
projections (allT_true_iff ×2, subset_Icc_of_inRange, ltAll_cons, nodup_of_chainLt) were
guaranteed "invalid projection" errors. All five now use the pin-verified Iff
`Bool.and_eq_true_iff {x y : Bool} : (x && y) = true ↔ x = true ∧ y = true`
(lean4 src/Init/Data/Bool.lean:176). The repo's green kernels only ever use
`simp only [Bool.and_eq_true]` (Eq-form, fine) — no green precedent for the projection
form, which is why this never surfaced.

### Receipts — namespaced `#print axioms` — FIXED (8 sites)
All eight `#print axioms` lines now use full names (`#print axioms DM142B.r3_216_ge`,
… `DM142B.ternary_cantor_digit01`), mirroring the green-pattern sibling 142A
(`#print axioms DM142A.r_mono` inside `namespace DM142A` — full names resolve from inside
the namespace). Output will read `'DM142B.r3_216_ge' does not depend on any axioms` (or
`depends on axioms: […]` if simp pulls propext/Quot.sound — both forms match the
commander's post-fix grep alternation; the sorryAx negative grep is unaffected).
`#eval "DM142B_LOWER_GREEN"` byte-unchanged (grep -F exact match).

### D7 (comment-only math slip) — FIXED
"the Cantor 2^5 = 8 in [1, 3^5]" → "the Cantor family's 2^5 = 32" in the
`w1024_not_cantor` docstring (prose only; the theorem was already decide-certified TRUE).

## HUNT RESULTS (mission item 3 — all clean)
Post-repair greps: no `not_mem_empty`, no `mem_biUnion`, no `Set.card_mono` /
`Set.card_singleton`, no `List.length_toFinset`, no `exact_mod_cast`, no `Bool.and_eq_true.`
projection form, no `ErdosTern2.` (correct namespace `ErdosTernary2.` used, verified in
Arsenal source), no `CardinalWorlds.` identifier prefixes (all matches are file-path
citations in comments), zero `sorry`/`admit`/`native_decide` (the only "sorry" hit is the
docstring phrase "zero sorry"). 21 `by decide` lines (19 stones ×3 decides + 2 arsenal)
— the audit's no-OOM decide structure untouched.

## FULL EXTERNAL-NAME VERIFICATION TABLE (all pin-verified)
| Name | Pin location | Form |
|---|---|---|
| `Set.IsAPOfLength.eq/.card`, `maxCard` | FC/Combinatorics/AP/Basic.lean:145/143/223 | vendored |
| `ENat.card_coe_set_eq` (rfl-bridge) | Mathlib Data/Set/Card.lean:73 | used defeq only |
| `Set.encard_le_encard` / `Set.encard_singleton` | Data/Set/Card.lean:188 / :121 | exact |
| `ENat.natCast_le_natCast` / `natCast_lt_natCast` | Data/ENat/Basic.lean:393 / :389 | exact |
| `le_csSup` | Order/ConditionallyCompleteLattice/Basic.lean:198 | root ns |
| `mem_upperBounds`; `BddAbove := (upperBounds s).Nonempty` | Order/Bounds/Basic.lean:35; Bounds/Defs.lean:39 | root ns |
| `Finset.card_mono`, `Finset.mem_coe` | used by FC itself / in-file usage at pin | exact |
| `Finset.mem_Icc` | Order/Interval/Finset/Defs.lean:301 (ns Finset) | `a ≤ x ∧ x ≤ b` order ✓ |
| `List.mem_toFinset` | Data/Finset/Dedup.lean:120 (ns List) | iff ✓ |
| `List.toFinset_card_of_nodup` | Data/Finset/Card.lean + WORKLOG atlas + green precedent | `(h : Nodup)` positional |
| `List.nodup_nil` / `List.nodup_cons` | lean4 src/Init/Data/List/Pairwise.lean:285/291 | iff `.2 ⟨_, _⟩` ✓ |
| `List.mem_cons` | lean4 src/Init/Data/List/Lemmas.lean:354 | iff ✓ |
| `Bool.and_eq_true_iff` | lean4 src/Init/Data/Bool.lean:176 | iff ✓ |
| `nsmul_eq_mul` (via `by simp` in nsmul_nat) | Algebra/Ring/Defs.lean:188 @[simp]; `Nat.cast_id` @[simp] Nat/Cast/Basic.lean:170 | smul-instance-coherent with FC's `•` (both `NSMul.toSMul`, `default_instance high`; AddMonoid extends NSMul — Group/Defs.lean:662) |
| `decide_eq_true`, `of_decide_eq_true` | lean4 Prelude.lean:1022/1030 | core |
| `if_pos` / `if_neg` | lean4 Init/Core.lean:1178/1183 | core |
| `False.elim` (`.elim`), `absurd`, `Nat.lt_trans`, `Nat.mul_zero`, `Nat.add_zero`, `Nat.mod_lt (x) {y} : 0 < y → …`, `Bool.noConfusion` | lean4 core | exact signatures checked |
| `ErdosTernary2.lt_three_cases (n) (h : n < 3)` | Arsenal/ErdosTernary2/Basic.lean:16 (ns ErdosTernary2) | 2 explicit args ✓ |
| `noTernaryTwoStruct` | Arsenal/CardinalWorlds.lean:51 (root ns) | structural twin ✓ |

## PRESERVED
Namespace `DM142B`; all 19 stone theorem statements byte-identical (git diff shows no
removed `theorem r*`/`def w*`/board lines); witness lists untouched (audit's python mirror
remains valid — all 19 stones stay TRUE); `stone3/4/5` builder statements untouched;
decide structure untouched (no-OOM law respected); `maxHeartbeats 16000000` /
`maxRecDepth 262144` unchanged (option verified in use by Arsenal at this toolchain).

## RESIDUAL COMPILE RISKS (honest ledger)
1. **Defeq-only steps** (all default-transparency-safe, but not machine-checked here):
   `hc := hcard` (ENat.card ↔ encard, `rfl`-lemma), `h1' := h1` (numeral cast),
   `obtain` through the set-builder membership (FC's own proofs use the same
   destructuring), the `noQuatTwoS x (x+1)` / `noTernaryTwoStruct x (x+1)` whnf-unfolds
   in §7 (audit-verified: `x + 1` whnfs to `Nat.succ x`).
2. **`by simp` in `nsmul_nat`**: verified the two @[simp] lemmas it needs
   (`nsmul_eq_mul`, `Nat.cast_id`) exist at the pin; simp-closure is not
   machine-checked. Fallback if CI objects: `nsmul_eq_mul i d` as a term (cast defeq).
3. `hscan` argument counts (9/11/14) and the `⟨S, hsub, hfree, rfl⟩` sSup-membership
   shape — audit-verified, unchanged.
4. CI-workflow items NOT in this file's scope (commander's): kills.yml L167–168 grep
   still needs the `DM142B.` prefix (audit D4); the 142B step still relies on the
   107DM-A step for the Arsenal oleans (audit D8).
5. **Sibling warning**: `DM142_Proof_A.lean` carries the same NEW
   `Bool.and_eq_true.1/.2` defect (≥5 sites: lines 88, 93, 253, 429, 449 …) in addition
   to its known D1-analog (L174–176) and D3-analog (L269) — audit/fix before its CI run.
