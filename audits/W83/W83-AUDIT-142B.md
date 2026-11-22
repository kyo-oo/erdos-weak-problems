# W83-AUDIT-142B — Adversarial static audit of `problem142-rk-asymptotic/DM142_Proof_B.lean`

Auditor: W83-AUDIT-142B (Lean 4.33 / Mathlib v4.33.0-rc2, no local Lean — CI-only verdict).
Target: branch `campaign` @ 9a29c0e4, 644 lines, FIRST-EVER COMPILE (kernel-142dm-b step
of job `kernel-dm-w82`). Method: full read of the kernel + FC/Combinatorics/AP/Basic.lean +
Arsenal/CardinalWorlds.lean + Arsenal/ErdosTernary2/Basic.lean + kills.yml; independent
python mirror of every witness, count and Bool scan (results embedded below).

## VERDICT

**NOT CI-READY — REJECT (3 critical compile defects + 1 CI-workflow receipt defect).**
The mathematics is SOUND: all 19 stone inequalities are TRUE (independently mirrored in
python: every witness is in range, strictly increasing, and 3/4/5-AP-free under exactly the
kernel's scanner semantics), the sSup-transfer is valid for the official definition, and the
bridge reductions are correct. But the file will not compile: it has **~30+ elaboration
errors** from three independent defects, and even after they are fixed the CI step stays RED
on a receipt-grep mismatch. All repairs are local and mechanical (given below). No OOM bomb:
the decide machinery RESPECTS the L86 no-OOM law.

Most likely FIRST compile error: **L204 type mismatch** (`hy : y ∈ t` fed to
`hu : ∀ y ∈ u, …` inside `apDiff_ne_zero`), immediately followed by **L223
`unknown identifier 'midFree3'`**.

---

## DEFECT LIST (ordered by first occurrence; exact patches)

### D1 — CRITICAL — helper binder transposition in `apDiff_ne_zero` (L198, L204)
`apDiff_ne_zero` (L197–211) declares `(hset : t = u) … (hu : ∀ y ∈ u, ∃ n, y = a + n * d)`
but its own proof uses `hu` on a `y ∈ t` membership:
```lean
    intro y hy                       -- L203: hy : y ∈ t
    obtain ⟨n, hn⟩ := hu y hy        -- L204: needs hy : y ∈ u → TYPE MISMATCH (first error)
```
and the three bridge usages (L229–233 / L261–265 / L293–297) then do `rw [hset] at hy`
(L231/L264/L297) on `hy : y ∈ u` where the rewrite pattern `t` **cannot occur** —
`rw` fails ("did not find instance of pattern"). The author transposed `t`/`u`: the helper
wants `hu` about **t**, and the bridges' `rw [hset] at hy` then correctly converts
`y ∈ t` into membership in the FC set-builder for destructuring.

**Patch (one token, L198):** `u` → `t`
```lean
    (hu : ∀ y ∈ t, ∃ n : ℕ, y = a + n * d) : d ≠ 0 := by
```
After this single change: L204 elaborates (`hy : y ∈ t`); the bridge `rw [hset] at hy`
(L231/264/297) finds the pattern and rewrites to `y ∈ {a + n • d | (n : ℕ) (_ : n < ↑k)}`;
`obtain ⟨n, -, hn⟩ := hy` destructs the ∃-∧ membership exactly as FC's own
`Nat.isAPOfLengthWith_pair` does (`fun ⟨w, ⟨_, _⟩⟩`); `exact ⟨n, by rw [hn, nsmul_nat]⟩`
closes. `hset` becomes unused *inside the helper* (harmless; still used by the bridges).
**Sibling warning:** `DM142_Proof_A.lean` L174–176 has the identical transposition (same
first-compile-pending status; not this audit's target).

### D2 — CRITICAL — forward references to the scanners (L223, L255, L289 vs defs L327/L333/L340)
The §2 bridges use `midFree3` (L223), `k4Free` (L255), `k5Free` (L289) — all defined in §3
(L327, L333, L340). Lean requires declaration-before-use → three `unknown identifier`
errors (L223 is the first), cascading into `stone3/4/5`, all 19 stones, the board and the
`#print axioms` lines.

**Patch:** relocate the scanner block — §3's header through the `k5Free` def
(L322–343, i.e. `/-! ## §3 The scan checkers … -/` … the `k5Free` body ending at L343) —
to immediately after L218 (end of `mem_of_memFinsetCoe`), i.e. before the
`isAPOfLengthFree_three` docstring at L220. (`inRange`/`chainLt` may stay where they are;
only the three scanners must precede §2.)

### D3 — CRITICAL — bridge conclusions deliver `False` where the official def demands `l ≤ 1` (L249, L283–284, L319–320)
The official `Set.IsAPOfLengthFree` (FC Basic.lean:203) is
`∀ t ⊆ s, t.IsAPOfLength l → l ≤ 1`. After `intro t hts ht` the residual goal is
`((3 : ℕ) : ENat) ≤ 1` (resp. 4, 5), but each bridge ends
`exact hscan … : False` — type mismatch (`False` ≠ `↑3 ≤ 1`); `exact` does not insert
`False.elim`.

**Patches (append `.elim`):**
```lean
-- L249
  exact (hscan a (a + 2 * d) (a + d) e0 e2 (by omega) (by omega) (by omega) e1).elim
-- L283–284
  exact (hscan a (a + d) (a + 2 * d) (a + 3 * d) e0 e1 e2 e3
    (by omega) (by omega) (by omega)).elim
-- L319–320
  exact (hscan a (a + d) (a + 2 * d) (a + 3 * d) (a + 4 * d) e0 e1 e2 e3 e4
    (by omega) (by omega) (by omega) (by omega)).elim
```

### D4 — HIGH — CI receipt grep cannot match (kills.yml L167–168, step "Kernel 142DM-B")
The kernel's receipts are `#print axioms r3_216_ge` etc. **inside `namespace DM142B`**
(L633–640), and `#print axioms` prints the fully-resolved name:
`'DM142B.r3_216_ge' does not depend on any axioms`. The required grep
```yaml
grep -E "'(r3_216_ge|r3_7776_ge|r3_46656_ge|dm142b_board)' (does not depend on any axioms|depends on axioms)" kernel142dmb.log
```
is quote-anchored on the short names — the substring `'r3_216_ge' does not depend…` does
NOT occur in `'DM142B.r3_216_ge' does not depend…` (char before `r3_216_ge'` is `.`) →
grep exits 1 → **step RED even after the file compiles.** (The green-pattern sibling 142A
got this right: fully-qualified `#print axioms DM142A.r_mono` + `DM142A.`-prefixed grep.)

**Patch (kills.yml L167 and L168):**
```yaml
          grep -E "'DM142B\.(r3_216_ge|r3_7776_ge|r3_46656_ge|dm142b_board)' (does not depend on any axioms|depends on axioms)" kernel142dmb.log
          ! grep -E "'DM142B\.(r3_216_ge|r3_7776_ge|r3_46656_ge|dm142b_board)'.*sorryAx" kernel142dmb.log
```
(The file's receipt SET is otherwise correct: all four required names are among its eight
`#print axioms`, and `#eval "DM142B_LOWER_GREEN"` matches `grep -F` exactly.)

### D5 — MEDIUM (name risk, no in-repo CI precedent) — ENat.card lemma names (L208–209, also L170–171)
```lean
  have h1 : ENat.card t ≤ ENat.card ({a} : Set ℕ) := Set.card_mono hsub   -- L208
  rw [Set.card_singleton, hcard] at h1                                     -- L209
```
In Mathlib v4.33 the `Set.card_mono` / `Set.card_singleton` names are (best offline
recollection, ncard→encard refactor) the **encard**-typed lemmas — in which case both lines
work (`ENat.card` is defeq-equal to `encard`; `exact` tolerates defeq, `rw`/`kabstract`
matches through the reducible abbrev) — but if they resolve to the Nat.card-typed forms,
L208 is a type mismatch and L209 an rw-pattern failure. Nothing in the repo's CI-green
corpus uses these names on `ENat.card` (only the two never-compiled DM142 kernels do).
Same risk class for `exact_mod_cast` on `((k:ℕ):ENat) ≤ 1` (L210) and
`coe_lt_coe_k` (L170–171) — cast lemma `ENat.coe_le_coe`/`coe_lt_coe` should exist, but the
numeral RHS makes `exact_mod_cast` fragile.
**Patches if CI errors:** L208 `ENat.card_mono hsub` (or `Set.encard_mono hsub`);
L209 `rw [ENat.card_singleton, hcard] at h1` (or `Set.encard_singleton`);
L210 fallback `exact ENat.coe_le_coe.1 h1`; L171 fallback `exact ENat.coe_lt_coe.2 h`.

### D6 — LOW-MEDIUM (name risk) — `List.length_toFinset` (L401, L409, L417)
Current Mathlib name for the old `List.toFinset_card_ofNodup` (rename ~2024); ~85% sure it
is right in v4.33 with the explicit-hypothesis form used here. Fallback:
`List.toFinset_card_ofNodup (nodup_of_chainLt W hchain)`.

### D7 — LOW (comment-only math slip) — L591–592
"the Cantor 2^5 = 8 in [1, 3^5]" — 2^5 = 32, not 8 (and the weight-2 ternary family in
[1,3⁵] has C(5,2)=10 elements). The theorem `w1024_not_cantor` itself is TRUE
(decide-certified; independently mirrored). Fix the prose, not the math.

### D8 — NOTE (fragile CI dependency, not a defect of this file)
The 142B step runs only `lake build FC`; the kernel's `import Arsenal.ErdosTernary2.Basic`
/ `import Arsenal.CardinalWorlds` resolve solely because the earlier 107DM-A step in the
same job built them. If 107DM-A is ever reordered/removed, 142B dies on missing .olean.
Recommend adding `lake build Arsenal.ErdosTernary2.Basic` and
`lake build Arsenal.CardinalWorlds` to the 142B step.

**Verified-clean items (no action):** zero `sorry`/`native_decide`/`admit`; no `==` at
variables (L91-law); no `termination_by` needed (`noQuatTwoS` is structural on its fuel
argument, matching Arsenal's `noTernaryTwoStruct`); `x + 1` does whnf to `Nat.succ x`
(Nat.add recurses on the second arg), so the §6 unfoldings `noQuatTwoS x (x+1)` /
`noTernaryTwoStruct x (x+1)` are definitional; `hscan` argument counts/typing correct
(9/11/14 args); the `⟨S, hsub, hfree, rfl⟩` / `rintro ⟨T, hTsub, -, rfl⟩` shapes mirror
FC's own `maxCard_zero` idioms for the ∃-binders set-builder; `ErdosTern2.lt_three_cases`
signature and `Nat.mod_lt x (by decide : 0 < 3)` compatible.

---

## THE DECIDE-SIZE TABLE (L86 no-OOM audit — every decide, all on CLOSED terms)

59 tactic-`by decide` instances (19 stones × 3 + 2 arsenal) + closed `decide`s inside the
scanner bodies (`Nat.decEq`/`Nat.decLt`/`Nat.decLe` on values ≤ 46656 — GMP single-limb).
**No decide quantifies over `Finset.range N`, `Icc 1 N`, or any range ≥ 500 — the 46656-wide
OOM-bomb pattern is ABSENT.** Every scan runs over a literal witness list via structural
`allT`/`memL`. Budget: `maxHeartbeats 16000000` (≈1.6e10 steps) — worst decide needs ~1e6.

| # | decide goal | closed term size | kernel-reduction cost (est.) | verdict |
|---|---|---|---|---|
| 1–10 | `inRange wX N = true` (10 k=3 stones) | ≤90 elems | ≤180 Nat-compares | trivial |
| 11–19 | `chainLt wX = true` | ≤90 elems | ≤89 compares | trivial |
| 20 | `midFree3 w216 = true` | 6 elems | 36 pairs × ~6 memL = **216** | fine |
| 21 | `midFree3 w1296 = true` | 12 | 144 × 12 = **1,728** | fine |
| 22 | `midFree3 w7776 = true` | 30 | 900 × 30 = **27,000** | fine |
| 23 | `midFree3 w46656 = true` | 90 | 8,100 pairs × ~90 memL = **729,000** | **largest in file — OK** |
| 24 | `midFree3 w1000 = true` | 6 | 216 | fine |
| 25 | `midFree3 w10000 = true` | 24 | 576 × 24 = **13,824** | fine |
| 26 | `midFree3 w2744 = true` | 12 | 1,728 | fine |
| 27 | `midFree3 w38416 = true` | 48 | 2,304 × 48 = **110,592** | fine |
| 28 | `midFree3 w324 = true` | 2 | 8 | fine |
| 29 | `midFree3 w1024 = true` | 10 | 1,000 | fine |
| 30–47 | k=4 stones: `inRange`/`chainLt`/`k4Free` ×6 | ≤12 elems | worst `k4Free w1296`/`w2744`: 12⁴=20,736 quads × 3 decides = **62,208**; `w1024`: 10,000×3=30,000 | fine |
| 48–56 | k=5 stones: ×3 | ≤6 elems | worst `k5Free w216`/`w1000`: 6⁵=7,776 × 4 = **31,104** | fine |
| 57 | `allT (fun x => noQuatTwoS x (x+1)) w1024 = true` | 10 × ≤6 fuel steps | ~60 | fine |
| 58 | `allT (fun x => !(noTernaryTwoStruct x (x+1))) w1024 = true` | 10 × ≤7 | ~70 | fine |
| 59 | (19 ×) `rfl : wX.length = m` | literal list | List.length iota | fine |

Estimated worst elaborator heartbeat consumption: midFree3 w46656 ≈ 1–5M of 16M — safe.
Kernel re-check at declaration time is native-fast. **PASS.**

## WITNESS COUNT TABLE (literal length vs claimed size — python-verified, all 19 stones)

| witness | literal len | claimed | N | in [1,N] | strictly incr (⇒Nodup) | 3-AP-free | 4-AP-free | 5-AP-free |
|---|---|---|---|---|---|---|---|---|
| w216 | 6 | 6 ✓ | 216 | ✓ | ✓ | ✓ | ✓ (k=4 stone) | ✓ (k=5 stone) |
| w1296 | 12 | 12 ✓ | 1296 | ✓ | ✓ | ✓ | ✓ (k=4) | — |
| w7776 | 30 | 30 ✓ | 7776 | ✓ | ✓ | ✓ | — | — |
| w46656 | 90 | 90 ✓ | 46656 | ✓ | ✓ | ✓ | — | — |
| w1000 | 6 | 6 ✓ | 1000 | ✓ | ✓ | ✓ | ✓ (k=4) | ✓ (k=5) |
| w10000 | 24 | 24 ✓ | 10000 | ✓ | ✓ | ✓ | — (honestly excluded) | — |
| w2744 | 12 | 12 ✓ | 2744 | ✓ | ✓ | ✓ | ✓ (k=4) | — |
| w38416 | 48 | 48 ✓ | 38416 | ✓ | ✓ | ✓ | — (honestly excluded) | — |
| w324 | 2 | 2 ✓ | 324 | ✓ | ✓ | ✓ | ✓ (k=4) | ✓ (k=5) |
| w1024 | 10 | 10 ✓ | 1024 | ✓ | ✓ | ✓ | ✓ (k=4) | — |

k=4 ladder reuses w216, w324, w1024, w1000, w1296, w2744 (sizes 6,2,10,6,12,12 — matches
the brief); k=5 reuses w216, w324, w1000 (6,2,6 — matches). **No miscounted literal; no
false theorem.** Extra python checks: w1024 is exactly the base-4 {0,1}-digit weight-2
family (all digits < 2, digit-sum = 2 — C(5,2)=10 ✓) and all 10 elements FAIL the Arsenal
Cantor reader (all have a ternary digit 2) — `w1024_quat_clean` and `w1024_not_cantor` are
TRUE. The banked `receipts142b_audit.txt` (24/24 PASS, negative controls included) agrees
with my independent mirror.

## RECEIPT CHECK (kills.yml, job `kernel-dm-w82`, step "Kernel 142DM-B", L159–169)

- Step builds `lake build FC` then `lake env lean problem142-rk-asymptotic/DM142_Proof_B.lean`.
- `! grep -E 'error:|sorryAx|unknown identifier|unsolved goals|declaration uses .sorry.'` —
  satisfiable only after D1–D3 repairs (before them: "unknown identifier" ×3 + cascades).
- `grep -F "DM142B_LOWER_GREEN"` — file L642 `#eval "DM142B_LOWER_GREEN"` ✓ EXACT MATCH.
- `grep -E "'(r3_216_ge|r3_7776_ge|r3_46656_ge|dm142b_board)' (does not depend on any
  axioms|depends on axioms)"` — the four names ARE among the file's eight `#print axioms`
  (L633–640) ✓, **but the output is namespace-qualified** (`'DM142B.r3_216_ge' …`) → NO
  MATCH → RED. See D4. (Note: since the null-job blackout — run 44967816376 — the entire
  `kernel-dm-w82` job, including this step, has never started; there is no CI history for
  142B or for the sibling 142A.)
- Arsenal imports resolve only via the earlier 107DM-A step (D8).

## MATH-FIDELITY

1. **Official definition.** `r := Set.IsAPOfLengthFree.maxCard` (L80) — verbatim the FC def
   (verified at FC/Combinatorics/AP/Basic.lean:223, `sSup {Finset.card S | (S)
   (_ : S ⊆ Finset.Icc 1 N) (_ : (S : Set ℕ).IsAPOfLengthFree k}`, `noncomputable`,
   k N : ℕ, length coerced to ℕ∞). The kernel's `((k:ℕ):ENat)` coercions match.
2. **The transfer** `maxCard_ge_of_witness` (L181–188) is valid for the official sSup form:
   `le_csSup` with the 4-component membership `⟨S, hsub, hfree, rfl⟩` (mirrors FC's own
   `maxCard_zero` destructuring `rintro n ⟨S, hS, rfl⟩` / 3-component witness) and
   `BddAbove` via `mem_upperBounds` + `Finset.card_mono` — sound; the set IS bounded above
   by `(Finset.Icc 1 N).card` for every member.
3. **The bridges** are mathematically correct one-directional reductions: a 3-AP
   `a, a+d, a+2d` (d≠0) yields the midpoint pair; a 4-AP yields the two-consecutive-midpoint
   quadruple `2(a+d)=a+(a+2d)`, `2(a+2d)=(a+d)+(a+3d)`, `a≠a+3d`; a 5-AP yields the
   three-midpoint quintuple (all endpoints-distinct/equation checks by `omega` — linear,
   safe near powers). The `d ≠ 0` argument (`apDiff_ne_zero`: d=0 ⇒ t ⊆ {a} ⇒
   ENat.card t ≤ 1 < k) is sound. Nodup via strictly-increasing `chainLt` ⇒
   `W.toFinset.card = W.length` ⇒ the stone bound is the literal count.
4. **AP-freeness is NOT hand-waved** — every freeness claim is decide-certified by the
   scanners (and independently python-mirrored). The Behrend-fiber commentary is consistent
   (B = 2m, N = B^d holds for all ten: 6³=216, 6⁴=1296, 6⁵=7776, 6⁶=46656, 10³=1000,
   10⁴=10000, 14³=2744, 14⁴=38416, 18²=324, 4⁵=1024) and no theorem depends on it.
   Example check: w216 = {(0,1,2)-permutations in base 6} — fixed digit-sum 3, digit-square-
   sum 5 — a genuine layer×sphere fiber.
5. **Arsenal citations verified.** `noTernaryTwo` at CardinalWorlds.lean:41 ✓;
   `noTernaryTwoStruct` at :51 ✓ with EXACTLY the recursion shape the kernel's
   `ternary_first_digit` unfolds (`if n = 0 then true else if n % 3 = 2 then false else
   noTernaryTwoStruct (n/3) k`), so the `have h1 := h` definitional unfold typechecks;
   `noTernaryTwo_eq_struct` at :58 with `(hk : n + 1 ≤ k)` ✓ (cited-only, correctly);
   `ErdosTernary2.lt_three_cases` at ErdosTernary2/Basic.lean:16 ✓,
   `(n : Nat) (h : n < 3) : n = 0 ∨ n = 1 ∨ n = 2` — compatible with the call
   `lt_three_cases (x % 3) (Nat.mod_lt x (by decide : 0 < 3))`. Both Arsenal names are
   root-namespace (no wrapper before :41) — the kernel's unqualified references resolve.
   `noQuatTwoS` is a genuine structural twin (fuel-indexed) — kernel-decidable.
6. **Honest scope** is accurately stated (explicit finite lower bounds; the asymptotic
   formula — the official open core — is not claimed; the 24+-element k=4 exclusions are
   conservative, not defects).

## NEXT ACTIONS

1. Apply D1 (move scanner defs L322–343 above §2), D2 (L198 `u`→`t`), D3 (three `.elim`)
   — then re-run the python mirror (unchanged witnesses ⇒ all 19 theorems stay true).
2. Fix kills.yml L167–168 (D4) — otherwise the step is RED on receipts even when green.
3. Pre-empt D5/D6 by switching to `ENat.card_mono`/`ENat.card_singleton` (or keep
   `Set.card_mono` and be ready with the encard fallbacks) and confirm
   `List.length_toFinset`.
4. Add the two `lake build Arsenal.*` lines to the 142B step (D8).
5. Sibling warning: DM142_Proof_A.lean carries D2's transposition (L174–176) and a D3-style
   `False`-into-`↑k ≤ 1` at its L269 (`exact hout hin`) — audit/fix before its next CI run.
6. After green: the receipts to watch are `DM142B_LOWER_GREEN` + the four
   `'DM142B.…' does not depend on any axioms` lines.
