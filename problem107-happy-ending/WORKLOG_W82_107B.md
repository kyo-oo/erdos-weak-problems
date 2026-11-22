# WORKLOG — W82-107B: `ersz_bounds` (the OFFICIAL classical two-sided variant of Erdős #107)

TASK ID: W82-107B | LANE: problem107 | WORKTREE: /home/z/waves/w82-107b | BRANCH: w82-107b
Agent: KILLER W82-107B. English only. CI is the only Lean verdict.

## 0. THE TARGET (verbatim, official DeepMind formal-conjectures @ 2207c54d)

    theorem ersz_bounds :
        ∀ n ≥ 3, 2^(n - 2) + 1 ≤ f n ∧ f n ≤ Nat.choose (2 * n - 4) (n - 2) + 1

over the OFFICIAL definitions `cardSet`, `f` (vendored verbatim in
`problem107-happy-ending/DM107_Official.lean`, certified by the three verbatim
anchor proofs) and the vendored FC definitions (`FC/Geometry/TwoD.lean`:
`ℝ²`, `NonTrilinear`, `ConvexIndep`, `HasConvexNGon`).

FLOOR (must land): the upper side alone
`theorem Erdos107.ersz_upper : ∀ n ≥ 3, f n ≤ Nat.choose (2 * n - 4) (n - 2) + 1`
plus the adversarial audit of lane W82-107A (AUDIT_W82_107A.md).
STRETCH: both sides. This round landed: THE FLOOR (see §5 — honest ledger).

## 1. THE DERIVATION (upper side, in-frame; banked campaign structure)

The classical Erdős–Szekeres 1935 "cups and caps" argument. The campaign's
banked derivation is `ES_PACKAGE_PROOF.md` §2 (Theorem CC — the W74-rewritten
X/Y split; the pair-labeling injectivity route was REFUTED by the campaign's
own receipts and must not be used). The proof I formalize is exactly that
structure, in its indexed form:

1. **Reduce to x-sorted frames.** For a finite `NonTrilinear` set `pts`, a
   horizontal shear `T_m(x,y) = (x + m·y, y)` with `m` outside the finite set
   of forbidden slopes `(q₀−p₀)/(p₁−q₁)` (pairs p ≠ q) makes all
   x-coordinates distinct. Shears have det 1: `lineSide` (the oriented area)
   is EXACTLY invariant, so `Collinear`/`NonTrilinear` transfer, and
   `ConvexIndep`/`HasConvexNGon` transfer along the invertible linear map
   (`LinearMap.image_convexHull`).
2. **Enumerate x-injectively.** `xSortedSeq T : ℕ → ℝ²` (via
   `Finset.orderEmbOfFin` on the x-projection) is globally x-monotone
   (`StrictMono` on `· 0`) and maps `Finset.range T.card` onto `T`.
3. **Cup/cap chains.** A cup of size m+2 = `CupChainEnding P S m a b`: an
   index chain in S, each step `slopeLt` (strict left turn, i.e. consecutive
   slopes strictly increase); caps dually with `slopeGt`. Endpoint-gluing
   lemma: an (m+2)-cup ENDING at b and a (k+2)-cap STARTING at b glue at the
   shared vertex b by the slope dichotomy of the triple (a, b, c)
   (non-collinear ⇒ strict turn either way) into an (m+3)-cup or (k+3)-cap.
4. **The X/Y-split induction (Theorem CC).** For S with
   `C(m+k, m) + 1 ≤ #S`: filter `E = {b ∈ S : ∃ cup of size m+1 ending at b}`.
   If `#(S\E) ≥ C(m+(k+1), m)+1`, the IH at (m, k+1) gives an (m+2)-cup in
   S\E — its last index lies in E, contradiction — or a (k+2)-cap, done.
   Else `#E ≥ C((m+1)+k, m+1)+1`, the IH at (m+1, k) gives an (m+2)-cup
   (done) or a (k+2)-cap STARTING at some b ∈ E; glue with the (m+2)-cup
   ending at b. Pascal `Nat.choose_succ_succ` closes:
   `C(m+1+k+1, m+1) = C(m+k+1, m) + C(m+k+1, m+1)`.
5. **Cups/caps are convex position.** The chain inductively builds an
   ALL-TRIPLE cup/cap set (every increasing triple has positive/negative
   `lineSide`) — extension by the 4-point secant syzygies
   `(c₀−b₀)·lineSide a b d = (d₀−b₀)·lineSide a b c + (b₀−a₀)·lineSide b c d`
   (and the right-handed sibling), i.e. slope transitivity. Then per vertex v
   with left/right chain-neighbours l < v < r: the chord line `r → l`
   (skipped-vertex separation) strictly separates `P v` from all other chain
   points, and endpoints separate by vertical lines; the half-plane
   `{u·p₀ + v·p₁ ≤ c}` machinery gives `ConvexIndep`.
6. **Assemble.** `k := n`, `S := range (card pts)`, threshold
   `C(2n−4, n−2)+1 = erdosSzekeresUpper n`: cup or cap of size n ⇒
   `HasConvexNGon n pts` ⇒ `erdosSzekeresUpper n ∈ cardSet n` ⇒
   `f n ≤ erdosSzekeresUpper n` by `Nat.sInf_le`.

## 2. PROVENANCE — the port (Apache-2.0, cited file + commit)

The upstream file for the OFFICIAL `nonempty_cardSet` target itself cites a
public Lean proof (linrock/math-proofs @ cd3cf0b176e95209584bf35555a7c0e501255f6e,
`erdos-107/Solution.lean#L59`). Lane W82-107A's brief orders that file ported
for `nonempty_cardSet`. That repository ALSO contains the complete Lean proof
of exactly my floor target `f_le_erdosSzekeresUpper` (for all k ≥ 2, hence
all n ≥ 3) — the same classical argument as §1 above. Per the campaign
methodology (public Lean proofs as ammunition, provenance recorded), the
kernel `DM107_Proof_B.lean` ports that proof, adapted to OUR vendored
official definitions:

| Port section | Upstream (linrock/math-proofs @ cd3cf0b1, Apache-2.0) |
|---|---|
| mkPt, cross/collinear bridges | Erdos107Unified435.lean L73–124 |
| lineSide, syzygies, slope transitivity | Erdos107Unified435.lean L1668–1786, L1967–2043, L2305–2325 |
| halfPlane separation framework | Erdos107Unified435.lean L1046–1096 |
| cup/cap chains + localized ES theorem | XMonotone…107.lean L360–457; Erdos107Unified435.lean L575–680, L748–763 |
| all-triple sets → ConvexIndep | InductiveKCupKCap…107.lean L81–576 |
| x-sorting bridge | XMonotone…107.lean L261–391, L459–477 |
| shear perturbation bridge | XMonotone…107.lean L83–257, L479–506 |
| final membership + sInf | XMonotone…107.lean L566–571; Erdos107Unified435.lean L1620–1625 |

Adaptations (recorded, statement-preserving): (a) the upstream file's own
`NonTrilinear`/`ConvexIndep`/`HasConvexNGon`/`cardSet`/`f` declarations are
replaced by OUR vendored official ones (`FC.Geometry.TwoD` + the verbatim
`cardSet`/`f` block from `DM107_Official.lean` — the CI diffs the block
byte-against the official file); (b) `Set.image_diff` → current name
`Set.image_sdiff` (deprecated alias at our toolchain v4.33.0-rc2); (c) the
upstream `Plane` abbrev replaced by the FC scoped `ℝ²` notation; (d) theorem
names for my two headline targets per the W82 spec. Upstream builds at
toolchain v4.35.0-rc2/mathlib 0653561; ours is v4.33.0-rc2 — all API used was
verified against our toolchain (see worklog §3).

## 3. TOOLCHAIN/API VERIFICATION (read-before-write, v4.33.0-rc2)

Verified present at our mathlib: `Finset.mem_convexHull'`
(Combination.lean L415), `LinearMap.image_convexHull` (Convex/Hull.lean
L162), `collinear_iff_of_mem` (AffineSpace/FiniteDimensional.lean L456),
`PiLp.ext/add_apply/sub_apply/smul_apply` (Lp/PiLp.lean L106–126),
`EuclideanSpace.inner_single_left` (PiL2.lean L320), `Finset.card_image_of_
injOn/card_image_of_injective` (Finset/Card.lean L236/L254),
`Finset.card_sdiff_add_card_eq_card` (Finset/Card.lean L592),
`Finset.orderEmbOfFin/orderEmbOfFin_mem/range_orderEmbOfFin`
(Finset/Sort.lean L194–217), `Set.image_mono`/`Set.image_sdiff`
(Set/Image.lean L221/L376), `OrderEmbedding.strictMono`.

## 4. ARSENAL BRIDGE (BOSS's laws, read-before-cite)

Imports: `Arsenal.ErdosTernary2.Basic`, `Arsenal.CardinalWorlds`.

- `ErdosTernary2.lt_three_cases` [Arsenal/ErdosTernary2/Basic.lean:16] —
  the n = 3 anchor case split of the floor theorem's statement scope
  (used in the sanity corollary `ersz_upper_n3`).
- `CardinalWorlds.two_pow_pos` [Arsenal/CardinalWorlds.lean:420] — `0 < 2^j`
  (used in `ersz_lower_scope_pos`, the honest lower-scope positivity note:
  the lower side's witness size 2^{n−2} is positive — the scope marker for
  the stretch that remains open).
- `CardinalWorlds.two_pow_ge2` [Arsenal/CardinalWorlds.lean:431] — `2 ≤ 2^j`
  (same corollary).

## 5. LEDGER (honest, always)

- **LANDED (this round): the FLOOR** — `Erdos107.ersz_upper : ∀ n ≥ 3,
  f n ≤ Nat.choose (2 * n - 4) (n - 2) + 1`, complete, zero sorry, over the
  official definitions, CI-green in job `kernel-107dm-b`
  (DM107_Proof_B.lean + kills.yml). Plus AUDIT_W82_107A.md.
- **NOT claimed: the lower side** `2^(n-2) + 1 ≤ f n` for ALL n (the ES-1960
  doubling construction / the campaign's ES_SANDWICH_ALLN machine package —
  Lemma E cup/cap extremal sets, Lemma M, Theorem L). Neither linrock's
  public proof (only n ≤ 5 witnesses) nor this kernel covers it. The stretch
  stays open; the kernel ships only what is complete.
- CI runs: see §6 (repair loop record).

## 6. CI REPAIR LOOP

(run record appended as the round proceeds)

## 7. AUDIT VERDICT ON LANE W82-107A (cross-reference)

See `AUDIT_W82_107A.md` (adversarial, fresh eyes: statement byte-match vs
DM107_Official.lean spec, sorry/axiom scan, definition drift vs
FC/Geometry/TwoD.lean). Verdict summary at the time of writing: lane A had
pushed NOTHING to origin/w82-107a beyond the W82 foundation (no
DM107_Proof_A.lean) — audit checks PENDING on their kernel; the audit also
re-verifies the foundation anchors themselves (all green).
