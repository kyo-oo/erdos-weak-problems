# W83-AUDIT-107B — Adversarial Static Audit of `problem107-happy-ending/DM107_Proof_B.lean`

TASK ID: W83-AUDIT-107B | TARGET: DM107_Proof_B.lean (1607 lines, FIRST-EVER CI compile pending)
Auditor method: full read; byte-level diff vs green sibling `DM107_Proof_A.lean`; cross-check against
`FC/Geometry/TwoD.lean`, `FC/Data/Set/Triplewise.lean`, `DM107_Official.lean`, `Arsenal/ErdosTernary2/Basic.lean`,
`Arsenal/CardinalWorlds.lean`, `vendor_linrock/*` (upstream @ cd3cf0b1), `.github/workflows/kills.yml`
(jobs `kernel-dm-w82` L101 and `kernel-107dm-b` L1779). Repo at 9a29c0e, toolchain v4.33.0-rc2 (CI-only; no local Lean).

---

## 1. VERDICT: **GREEN-EXPECT**

**The single structural fact that carries this verdict:** B's entire dependency cone is byte-identical to the
CI-green kernel A. `diff A B` + checksums prove:

- A lines 57–1399 ≡ B lines 75–1417 (md5 `4fe7cf7c801a471df325aa9cf4c97be6` both sides) — this is §0–§11:
  the vendored official `cardSet`/`f`, the `mkPt`/cross-product calculus, `NonTrilinear` bridge (`Iff.rfl`),
  `lineSide` syzygies, half-plane separation, cup/cap chains, the ES-1935 Pascal-splitting induction
  `erdos_szekeres_cup_cap_theorem_on`, `IsCupSet`/`IsCapSet` → `ConvexIndep`, the x-sorting bridge, the
  horizontal-shear reduction, `hasConvexNGon_of_nonTrilinear_and_card_ge`, `erdosSzekeresUpper_mem_cardSet`.
- A lines 1419–1459 ≡ B lines 1468–1518 — `two_mul_choose_central_le_succ`, `two_pow_le_central_binom`,
  `erdosSzekeresConjectured_le_upper`, `two_pow_ge_succ`, and the bodies of `dm107{a,b}_arsenal_bridge`
  (h1–h4 identical).
- A lines 1487–1499 ≡ B lines 1544–1556 — `nonempty_cardSet_all`.

A went GREEN on CI once (per 6da275b S082 SEAL; A has exactly one commit 9cc7f48 = the green bytes) on the
*current* shared-dependency state: `FC/Geometry/TwoD.lean` last touched 3535ca2 and `Arsenal/` last touched
38e1b4e, both strictly before A's green. So the shared cone's green certification transfers to B verbatim.

**B's genuinely new, never-compiled code is only:** §12 floor-kill assembly (L1426–1447), the `h5` extension
of the arsenal bridge (L1528–1530, L1538–1539), `ersz_upper_n3` (L1568–1571), `ersz_lower_scope_pos`
(L1585–1594), and the receipts (L1598–1607). Every identifier there is (i) in-file and proved earlier
(`ersz_upper`, `f_le_erdosSzekeresUpper`, `erdosSzekeresUpper_mem_cardSet`, `erdosSzekeresConjectured_le_upper`,
`two_pow_ge_succ`), (ii) byte-shared with green A (`two_pow_pos`, `two_pow_ge2`, `le_trans`, `omega`), or
(iii) **`Nat.sInf_le`** (L1429) — the one Mathlib name A never used, cross-certified GREEN on the identical
v4.33.0-rc2 CI toolchain by three campaign kernels: `problem708/Erdos708.lean` (in-repo green receipt
`kernel62-green-receipt-43602748433.log`, 9 `sInf_le`/GREEN hits), `problem711/Erdos711.lean`,
`problem961/Erdos961.lean` — all in the exact same shape `Nat.sInf_le hmem : sInf S ≤ m` from
`hmem : m ∈ S` for `S : Set ℕ`; and used identically by vendored upstream
(`vendor_linrock/Erdos107Unified435.lean:1623`, same theorem, same one-liner).

**Most likely first compile error (if any): L1429 `Nat.sInf_le hmem` (type mismatch).** Probability ≈ 0:
the lemma is green-certified on this exact toolchain in ≥3 campaign kernels and in the vendored upstream
twin of this very theorem. No other candidate was found anywhere in the file.

---

## 2. DEFECT LIST

**Compile-killer defects found: NONE.**

Watch items (non-blocking; pre-emptive patches given in campaign idiom):

| # | Line | Class | Note & repair patch (only if it ever fires) |
|---|------|-------|---------------------------------------------|
| W1 | 1429 | unknown-identifier risk (a) | `Nat.sInf_le hmem` — the only B-only Mathlib name. Certified green on v4.33.0-rc2 (Erdos708/711/961 receipts). Fallback patch: `by dsimp only [f]; exact Nat.sInf_le hmem` (forces the `f n = sInf (cardSet n)` δ-unfold before unification). |
| W2 | 1598 | receipt placement | `#eval` sits after `end Erdos107` inside the unclosed `noncomputable section` (auto-closed at EOF). Identical structure in green A (`#eval "DM107A_NONEMPTY_CARDSET_GREEN"`); String-literal `#eval` is unaffected by `noncomputable`. Non-issue. |
| W3 | 87 | heartbeats (g) | `set_option maxHeartbeats 800000` — identical value in green A; B adds only ~90 lines of trivial tactic proofs (omega/decide/dsimp) on top of A's cone. Ample headroom. |

Explicit negative results against the audit DO-list:

- **(a) Unknown identifiers.** Every Mathlib lemma name in B occurs byte-identically in green A
  (`Nat.choose_succ_succ` L561, `Nat.choose_succ_succ'` L1478–1480, `Finset.card_sdiff_add_card_eq_card` L557,
  `Finset.one_lt_card_iff` L543/549, `Finset.card_image_of_injective` L997/1012/1254/1264/1395,
  `Finset.card_image_of_injOn` L1103, `Finset.range_orderEmbOfFin` L1116, `Finset.orderEmbOfFin_mem`
  L1085/1112, `LinearMap.image_convexHull` L1234, `Set.image_diff` L1240 (deprecated alias, linter silenced
  L83 — same as A), `collinear_iff_of_mem` L128/152/272, `collinear_pair` L271/1357–1361,
  `convexHull_subset_affineSpan` L1350, `collinear_insert_iff_of_mem_affineSpan` L1353,
  `Finset.card_eq_three` L1370, `Nat.sub_add_cancel` L1025, `Finset.card_erase_of_mem` L1327,
  `Finset.le_max'`/`Finset.min'_le` L780–816, `Finset.mem_product` L1310) — or is `Nat.sInf_le` (W1).
  Arsenal citations verified at source: `ErdosTernary2.lt_three_cases (n) (h : n < 3)` at Basic.lean:16 ✓;
  `two_pow_pos (j)` at CardinalWorlds.lean:420 ✓; `two_pow_factored (j) (hj : 1 ≤ j)` at :425 ✓;
  `two_pow_ge2 (j) (hj : 1 ≤ j)` at :431 ✓. All call sites match these signatures exactly.
- **(b) Binder mismatches.** None. `two_pow_ge2 (n - 2) (by omega)` supplies both explicit args (L1532, L1590);
  `two_pow_pos (n - 2)` one (L1531, L1589); `lt_three_cases n hn` two (L1551); `ersz_upper n hn` with
  `hn : 3 ≤ n` matches `∀ n ≥ 3` desugaring (L1538, L1593); `Nat.sInf_le hmem` one (L1429).
- **(c) Truncation traps.** `2 * n - 4` / `n - 2` appear only under guards `2 ≤ k` / `3 ≤ n` consumed by
  `omega` in-context (L1025, L1153, L1447, L1498–1503, L1513–1515). n = 3 anchor: `C(2,1)+1 = 3` —
  decide-verified at L1570. Internal k = 2 degenerate witness `C(0,0)+1 = 2` is sound (any 2 points are
  `ConvexIndep` via `convexIndep_of_card_le_two`, L1318). `Nat.sub_add_cancel hk : k - 2 + 2 = k` needs and
  has `hk : 2 ≤ k` (L1025).
- **(d) L91 law (Bool `==` at variables).** ZERO `==` occurrences in the entire file. The only
  definitional-equality gamble is `nonTrilinear_iff ... := Iff.rfl` (L180–183), Prop-level δ: FC's
  `Set.Triplewise` (FC/Data/Set/Triplewise.lean:41–42) literally unfolds to the six-binder ∀-form —
  and it is byte-certified by A's green.
- **(e) L86 NO-OOM.** All 9 `decide` occurrences (L1473, 1501, 1511, 1552–1554, 1569, 1570) are closed tiny
  numerals — the largest is `Nat.choose 2 1 = 2`. Zero quantifier-decides, zero `native_decide`, zero `sorry`,
  zero chunking concerns.
- **(f) omega vs exponentials.** Every `omega` treats `2^k` and `Nat.choose` terms as *atoms* under linear
  side conditions (L1481, 1490, 1505, 1517, 1537, 1571) — legal. The one exponential identity
  `2 ^ (k + 1) = 2 * 2 ^ k` is discharged by `ring` (L1489), not omega. No omega is asked to reason about
  exponential growth.
- **(g) set_options.** 4 linter silencers + maxHeartbeats 800000 — byte-identical to green A (W3).
- **(h) termination_by/decreasing_by.** None in the file. All equation-compiled recursions
  (`erdos_szekeres_cup_cap_theorem_on` L537, `cupChainEnding_mono` L495, `capChainStarting_mono` L501,
  `cupChainEnding_exists_isCupSet` L902, `capChainStarting_exists_isCupSet` L941) live in the byte-identical
  green region; termination was discharged by the equation compiler in A's green run.
- **(i) receipts.** See §3 — complete.
- **Statement/def-shape check (task item 2).** B L100–105 is *verbatim* `DM107_Official.lean` L42–47
  (`cardSet`, noncomputable `f := sInf (cardSet n)`). `NonTrilinear` (TwoD.lean:66–67, `A.Triplewise ...`),
  `ConvexIndep` (TwoD.lean:83–84, `∀ a ∈ S, a ∉ convexHull ℝ (S \ {a})`), `HasConvexNGon` (TwoD.lean:88–89,
  `∃ S : Finset ℝ², S.card = n ∧ ↑S ⊆ P ∧ ConvexIndep S`) — all B usages match these shapes (3-component
  anonymous-constructor witnesses at L996/1011/1253/1263/1371; `intro x hx` against the ConvexIndep ∀ at
  L412/761/833/1319). `ersz_upper`'s `Nat.choose (2 * n - 4) (n - 2) + 1` is the same term as the official
  `(2 * n - 4).choose (n - 2) + 1` and byte-matches upstream Solution.lean:64.
- **A-vs-B idiom delta (task item 3).** The full diff is: header docstring, §12 (new), §13/§14 docstrings,
  bridge `h5` + 5-tuple, `ersz_upper_n3`, §15 `ersz_lower_scope_pos`, receipts. B introduces **no** API or
  idiom that A avoided — the only new external name is `Nat.sInf_le` (W1).

---

## 3. RECEIPT CHECK (kills.yml `kernel-107dm-b`, L1779–1807)

CI requires: negative grep (`error:|sorryAx|unknown identifier|unsolved goals|declaration uses .sorry.`) clean,
plus 5 positive greps. All present with EXACT full names:

| CI grep (kills.yml line) | Required token | Present at |
|---|---|---|
| L1801 `grep -F` | `DM107B_ERSZ_GREEN` | B L1598 `#eval "DM107B_ERSZ_GREEN"` ✓ |
| L1802 | `'Erdos107.ersz_upper' (does not depend on any axioms\|depends on axioms)` | B L1600 `#print axioms Erdos107.ersz_upper` ✓ |
| L1803 | `'Erdos107.f_le_erdosSzekeresUpper'` | B L1601 ✓ |
| L1804 | `'Erdos107.erdosSzekeresUpper_mem_cardSet'` | B L1602 ✓ |
| L1805 | `'Erdos107.ersz_lower_scope_pos'` | B L1607 ✓ |

All four required theorem names exist with exact namespaces (ersz_upper L1445, f_le_erdosSzekeresUpper L1434,
erdosSzekeresUpper_mem_cardSet L1413, ersz_lower_scope_pos L1585). Extra axiom prints (L1603–1606:
`erdos_szekeres_cup_cap_theorem_on`, `hasConvexNGon_of_nonTrilinear_and_card_ge`, `nonempty_cardSet`,
`dm107b_arsenal_bridge`) all name existing declarations — harmless, no error output.

CI wiring verified end-to-end: kills.yml parses as **valid YAML, 19 jobs, no duplicate keys** (the 9a29c0e
null-job-key repair is in place, so this push's jobs will actually start — the L62 `paths:` filter includes
`problem107-happy-ending/**`). The job installs v4.33.0-rc2, runs `lake build FC` +
`lake build Arsenal.ErdosTernary2.Basic` + `lake build Arsenal.CardinalWorlds`, then
`lake env lean problem107-happy-ending/DM107_Proof_B.lean` — the exact pattern of green `kernel-dm-w82` (A).
Expected axiom lines: `depends on axioms: [propext, Classical.choice, Quot.sound]` (`Classical.choose` in
`pointOfX` L1038, `classical` L554) — both grep alternatives are accepted by the CI regex.

---

## 4. MATH-FIDELITY

- **The floor chain is valid and closes ∀ n ≥ 3.** `ersz_upper` (L1445) → `f_le_erdosSzekeresUpper (2 ≤ n)`
  (L1434) → `f_le_erdosSzekeresUpper_of_mem_cardSet` = `Nat.sInf_le` over the definitional
  `f n = sInf (cardSet n)` (L1426–1429) → `erdosSzekeresUpper_mem_cardSet (2 ≤ k)` (L1413): for every
  k ≥ 2, any `NonTrilinear` set of ≥ C(2k−4, k−2)+1 points contains a convex k-gon. n ≥ 3 ⇒ 2 ≤ n by omega.
  (Note the bound is vacuously safe even where `cardSet n` could be empty — `sInf ∅ = 0` — and in fact
  `nonempty_cardSet_all` (L1549) proves it never is.)
- **Base cases.** ES induction m = 0 / k = 0: `C(k,0)+1 = 2 ≤ #S` via `Nat.choose_zero_right` (L542, 548) —
  any two points are a 2-cup and a 2-cap (L543–552). n = 3: `f 3 ≤ C(2,1)+1 = 3` (`ersz_upper_n3`, L1568,
  decide/omega-verified) — exactly the upper side of the official anchor `f_three_eq` (`f 3 = 3`,
  DM107_Official.lean). Internal k = 2 degenerate: witness `C(0,0)+1 = 2`, sound via
  `convexIndep_of_card_le_two`.
- **Pascal-splitting step (L553–580).** `C(m+k+2, m+1) = C(m+k+1, m) + C(m+k+1, m+1)` (L558–561, correct
  succ-succ form via `Nat.choose_succ_succ`), partition `#(S\E) + #E = #S` (L557), branch selection by
  `omega` on atom-linear choose facts (L562, 571) — arithmetically verified by hand. Endpoint gluing
  (L519–532): an (m+2)-cup *ending* at b and a (k+2)-cap *starting* at b, with non-collinearity of the
  triple (a, b, c), split by the slope dichotomy (L196–205) into an (m+3)-cup or (k+3)-cap — correct.
- **Truncation.** No truncated-subtraction anomaly anywhere on the claimed range: n ≥ 3 ⇒ 2n−4 ≥ 2, n−2 ≥ 1;
  all internal uses are omega-guarded (§2c).
- **Statement fidelity.** `∀ n ≥ 3, f n ≤ Nat.choose (2 * n - 4) (n - 2) + 1` is the verbatim upper conjunct
  of the official `ersz_bounds` (DeepMind formal-conjectures @ 2207c54d) and byte-matches the upstream
  `formal_proof` witness (Solution.lean:64).
- **Honest scope — confirmed honest.** The lower side `2^(n−2)+1 ≤ f n` is NOT claimed anywhere in the file.
  `ersz_lower_scope_pos` (L1585) asserts only: `0 < 2^(n−2)` (arsenal), `2 ≤ 2^(n−2)` (arsenal),
  `2^(n−2)+1 ≤ C(2n−4,n−2)+1` (via `two_pow_le_central_binom`: 2^k ≤ C(2k,k), proved in-kernel from Pascal),
  and the proven upper bound. The WORKLOG_W82_107B.md §5 ledger matches the kernel's actual claims — no
  partial-as-complete dressing.

---

## 5. NEXT ACTIONS

1. **Push as-is** and let `kernel-107dm-b` run — this is B's first-ever compile; expectation GREEN.
2. If (against expectation) L1429 fails: apply W1's patch (`by dsimp only [f]; exact Nat.sInf_le hmem`);
   no other repair is anticipated.
3. On green: bank the CI receipt log next to `WORKLOG_W82_107B.md` §6, and record the lane as FLOOR-LANDED
   (upper side only; lower side remains the open stretch, per the honest ledger).

AUDIT CLOSED: no compile-killer found; GREEN-EXPECT with high confidence.
