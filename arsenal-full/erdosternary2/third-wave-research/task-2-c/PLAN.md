# PLAN — Task 2-c: Residue-Tower Closure (the R2 gap)

## PART 1 — THE COVERAGE MAP (mod 81, all classes of K with 5 ≤ K, K ≠ 7)

Row-p coverage depends only on `K mod 3^p` (by `pow4_digit_period`), so everything
reduces to classes mod 81 = 3⁴:

- **Row 2** closes `K % 9 ∈ {5, 6}` (`row_two_overlap_of_mod9_five_or_six`).
  Each mod-9 class lifts to 9 classes mod 81:
  - `≡ 5 (mod 9)`: {5, 14, 23, 32, 41, 50, 59, 68, 77}
  - `≡ 6 (mod 9)`: {6, 15, 24, 33, 42, 51, 60, 69, 78}
  → **18 classes.**
- **Row 3** closes `K % 27 ∈ {14, 18, 19, 25}` (`row_three_overlap_of_mod27_classes`).
  Each mod-27 class lifts to 3 classes mod 81:
  - `14`: {14, 41, 68}; `18`: {18, 45, 72}; `19`: {19, 46, 73}; `25`: {25, 52, 79}
  → 12 classes, of which {14, 41, 68} are already row-2; **9 new: {18, 19, 25, 45, 46, 52, 72, 73, 79}.**
- **Row 4** closes `RowFourClass (K % 81)` = {8, 20, 41, 42, 51, 52, 53, 54, 55, 56, 57, 58, 66, 76}
  (`row_four_overlap_of_mod81_classes`) → 14 classes, of which {41, 42, 51, 52} were already
  row-2/row-3; **10 new: {8, 20, 53, 54, 55, 56, 57, 58, 66, 76}.**

### (a) EXACT closed-class set mod 81 (rows 2+3+4) — 37 of 81 classes

```
 5   6   8  14  15  18  19  20  23  24  25  32  33  41  42  45  46  50  51  52  53
 54  55  56  57  58  59  60  66  68  69  72  73  76  77  78  79
```
(37 classes = 18 row-2 + 9 new row-3 + 10 new row-4; numerically re-verified: these are
exactly the residues r ∈ [0,81) with `digit3 (4^r) q = 2 ∧ digit3 (4^(r+1)) q = 2` for some
q ∈ {2,3,4}.)

### (b) EXACT still-open class set mod 81 — 44 classes (the R2 gap)

```
 0   1   2   3   4   7   9  10  11  12  13  16  17  21  22  26  27  28  29  30  31  34
 35  36  37  38  39  40  43  44  47  48  49  61  62  63  64  65  67  70  71  74  75  80
```
Note: class 7 mod 81 is NOT excluded by `K ≠ 7` — only the single value K = 7 is; e.g.
K = 88, 169, … live in class 7 and must still be covered. Classes 0–4 mod 81 occur for
K ≥ 5 as K = 81·u + r with u ≥ 1.

### Empirical ground truth (Python, big-int; drives all risk assessments below)

- The full exception set with NO common-two row at any p ≥ 1 is exactly **{0,1,2,3,4,7}**
  (checked 0 ≤ K < 5000; every K ≥ 5, K ≠ 7 dies). So `FourPowerDirectExistence` is true.
- Row-5 class set C₅ mod 243 (40 classes): {19, 20, 21, 38, 45, 48, 61, 70, 71, 72, 73,
  76, 77, 78, 85, 86, 87, 90, 91, 114, 115, 116, 117, 122, 123, 124, 133, 134, 138, 145,
  146, 162, 163, 164, 174, 175, 179, 185, 221, 229}.
- Row-6 class set C₆ mod 729: 122 classes (machine-listed; first elements
  8, 20, 21, 22, 23, 24, 30, 51, 55, 56, 73, 74, 79, 80, 106, …).
- Class counts |C_p| for p = 2..7: **2, 4, 14, 40, 122, 364** (→ density → 1/6).
- Cumulative coverage of rows 2..p: 37/81 (45.7%), 133/243 (54.7%), 457/729 (62.7%),
  rows 2..7: 69.1% (survivors mod 2187: 676).
- Survivor counts (residues mod 3^p dodging rows 2..p): **7, 18, 44, 110, 272, 676, 1676**
  for p = 2..8 — growth factor ≈ **2.48 per level** ⇒ survivors → ∞.
- Minimal witness row p(K): median 5, mean 6.6, max 46 (K = 3847) over K ∈ [5,5000];
  empirically `p(K) ≤ K/2 + 8`; **`p(K) ≤ O(log K) is FALSE`** (p(310) = 40).

**Consequence (hard fact): NO fixed finite set of rows closes the theorem.** Rows 2..p
always leave 2.48^p·c surviving residues. The R2 gap is not an enumeration gap; it needs
an unbounded mechanism. The three strategies below are ordered by feasibility.

---

## PART 2 — THREE CLOSURE STRATEGIES

Common conventions: helpers prefixed `wavc_`; Lean 4.33 + Mathlib; no
sorry/admit/axiom; no `decide` on `∀ k < N` with N > 501; every citation below is a name
actually present in the five read files. New file skeleton: import the four modules and
open the four namespaces exactly as `GSTFourPowerDirectExistence.lean` does.

### Strategy (i) — GENERAL ROW-p THEOREM (the pattern, not the lists)

**What generalizes.** `row_four_overlap_of_mod81_residue` is accidentally specialized:
`81 = 3^4` and row 4. The identical proof works for every row p ≥ 1, because
`pow4_digit_period p r (K / 3^p)` is uniform in p. Second, the "class list" itself has a
closed form that none of the current files exploit: writing `u = 4^K % 3^(p+1)` (cheap via
`Nat.pow_mod`), row p is common-two **iff** `u` lies in an explicit pair of intervals
`[2·3^p, (9/4)·3^p) ∪ [(11/4)·3^p, 3·3^p)` — i.e. `digit_p = 2` AND the carry
`⌊4·(u mod 3^p)/3^p⌋ ∈ {0,3}` (numerically verified p = 2..12). Third, the map
`K mod 3^p ↦ 4^K mod 3^(p+1)` is a bijection onto the principal units `1 + 3Z mod 3^(p+1)`
(the order of 4 mod 3^(p+1) is exactly 3^p — this follows from
`pow4_three_power_lte_exact` + `lteCoeff_mod3_one`). Together: **C_p = the preimage of an
explicit interval pair under a bijection** — that is the "classes pattern" the task asks
to state. What it needs: only `Nat` div/mod arithmetic plus the two cited kernels.

```lean
/-- S1. Cost-free digit: compute the row-p digit through a modulus, avoiding huge 4^r. -/
theorem wavc_digit3_mod (R p : Nat) :
    digit3 R p = ((R % 3^(p+1)) / 3^p) % 3 := by
  unfold digit3
  -- key: 3^(p+1) = 3^p * 3 (Nat.pow_succ); split R = 3^(p+1) * (R / 3^(p+1))
  -- + R % 3^(p+1) via Nat.mod_add_div, then Nat.mod_mul / omega bookkeeping
  -- (only lemmas already used in the five files: Nat.pow_succ, Nat.mod_add_div,
  --  Nat.mod_mul, Nat.div_add_mod-style division facts, omega)
  -- PROOF BODY TO BE SUPPLIED (fill per the comments above; no stubs in final code)

/-- S2. GENERAL single-residue class lift (any row p). Direct generalization of
    row_four_overlap_of_mod81_residue (which is p = 4, 81 := 3^4). -/
theorem wavc_row_overlap_of_mod3p_residue
    (p K r : Nat) (hr : K % 3^p = r)
    (h0 : digit3 (4^r) p = 2) (h1 : digit3 (4^(r+1)) p = 2) :
    digit3 (4^K) p = 2 ∧ digit3 (4^(K+1)) p = 2 := by
  have hm := Nat.mod_add_div K (3^p)
  rw [hr] at hm
  have hK  : K = r + 3^p * (K / 3^p) := by omega
  have hK1 : K + 1 = (r + 1) + 3^p * (K / 3^p) := by omega
  constructor
  · rw [hK];  calc digit3 (4^(r + 3^p * (K / 3^p))) p = digit3 (4^r) p :=
        pow4_digit_period p r (K / 3^p)
      _ = 2 := h0
  · rw [hK1]; calc digit3 (4^((r+1) + 3^p * (K / 3^p))) p = digit3 (4^(r+1)) p :=
        pow4_digit_period p (r+1) (K / 3^p)
      _ = 2 := h1

/-- S3. THE PATTERN: interval characterization of a common-two row. -/
theorem wavc_common_two_interval_char (K p : Nat) :
    (digit3 (4^K) p = 2 ∧ digit3 (4^(K+1)) p = 2) ↔
      ((2 * 3^p ≤ 4^K % 3^(p+1) ∧ 4 * (4^K % 3^(p+1)) < 9 * 3^p)
        ∨ 11 * 3^p ≤ 4 * (4^K % 3^(p+1))) := by
  -- let u = 4^K % 3^(p+1); 4^(K+1) = 4 * 4^K;
  -- digit_p(4^K) = (u / 3^p) % 3 (wavc_digit3_mod);
  -- 4u = 4*(u % 3^p) + 4*d*3^p with carry c = (4*(u % 3^p)) / 3^p ≤ 3;
  -- digit_p(4^(K+1)) = (c + d) % 3; both = 2 ↔ d = 2 ∧ c ≡ 0 [3] ↔ interval pair.
  -- PROOF BODY TO BE SUPPLIED (fill per the comments above; no stubs in final code)

/-- S4. Order exactness: 4 has order exactly 3^p mod 3^(p+1). -/
theorem wavc_pow4_order_exact (p : Nat) :
    4^(3^(p-1)) % 3^(p+1) ≠ 1 ∧ 4^(3^p) % 3^(p+1) = 1 := by
  -- 4^(3^p) ≡ 1: pow4_scaled_mod_next p 1
  -- 4^(3^(p-1)) = 1 + 3^p * lteCoeff (p-1), lteCoeff (p-1) % 3 = 1
  --   (pow4_three_power_lte_exact, lteCoeff_mod3_one) ⇒ 3^(p+1) ∤ (4^(3^(p-1)) - 1)
  -- PROOF BODY TO BE SUPPLIED (fill per the comments above; no stubs in final code)

/-- S5. From S4: K mod 3^p ↦ 4^K mod 3^(p+1) is injective on principal units. -/
theorem wavc_pow4_mod_bijection (p : Nat) (a b : Nat) (hb : b < 3^p)
    (h : 4^a % 3^(p+1) = 4^b % 3^(p+1)) : a % 3^p = b % 3^p := by
  -- PROOF BODY TO BE SUPPLIED (fill per the comments above; no stubs in final code)
```
What S1–S5 buy: rows 5 and 6 become cheap (`RowFiveClass` over the 40 listed C₅ classes,
`RowSixClass` over C₆; per-class digit checks evaluate `4^r % 3^(p+1)` with `Nat.pow_mod`
through `wavc_digit3_mod`, instead of `norm_num [digit3]` on 4^728). **RISK flags:**
S2 — none (mechanical). S3/S5 — medium (pure `Nat` div/mod combinatorics; the carry case
split `c ∈ {0,1,2,3}` is `interval_cases`-sized). **FATAL LIMIT (must be stated):**
strategy (i) alone can never finish — survivor counts grow ≈ 2.48^p, so every finite tower
leaves infinitely many K uncovered. It is the cheap-69% half of the proof, not the closure.

### Strategy (ii) — FIXED ROWS + COVERING/COUNTING (induction on K)

**Claim to exploit:** coverage is prefix-hereditary. If `K = m + a·3^p` with
`m = K % 3^p`, then for every row `q ≤ p` we have `K ≡ m (mod 3^q)` and
`K + 1 ≡ m + 1 (mod 3^q)`, hence by `pow4_digit_period` (period `3^q` at row `q`):
rows `q ≤ p` of `4^K` and `4^(K+1)` **coincide with those of `m` and `m+1`**. So a
counterexample K inherits "no common row ≤ p" from its own prefix m < K. Combine with
rows 2..6 (457/729 coverage) and strong induction on K:

```lean
/-- S6. Prefix transfer: low rows of K are the rows of its prefix. -/
theorem wavc_row_prefix_transfer (K p q : Nat) (hq : q ≤ p)
    (m := K % 3^p) :
    digit3 (4^K) q = digit3 (4^m) q ∧
    digit3 (4^(K+1)) q = digit3 (4^(m+1)) q := by
  -- K = m + 3^p * (K / 3^p) (Nat.mod_add_div); q ≤ p ⇒ 3^q ∣ 3^p;
  -- rewrite K = m + 3^q * (3^(p-q) * (K / 3^p)) and apply pow4_digit_period q m _
  -- PROOF BODY TO BE SUPPLIED (fill per the comments above; no stubs in final code)

/-- S7. The attempted induction (skeleton; DO NOT assume it closes — see risk). -/
theorem wavc_cover_by_induction (K : Nat) (hK : 5 ≤ K) (h7 : K ≠ 7) : CommonTwo K := by
  -- strong induction on K (Nat.strongRecOn);
  -- pick p with 3^p ≤ K < 3^(p+1); m := K % 3^p; a := exponentTrit K p ∈ {1, 2};
  -- case m ∈ {0,1,2,3,4,7}: direct finite check of K = m + a·3^p against
  --   row_four_overlap_of_mod81_classes / wavc_row_overlap_of_mod3p_residue and
  --   rows p+1 via row_common_two_iff_prefix_killing_trit;
  -- case m ≥ 5, m ≠ 7: apply IH to m at rows ≤ p (wavc_row_prefix_transfer);
  --   if the covering row of m is ≤ p, transfer to K.  ← THE GAP
  -- PROOF BODY TO BE SUPPLIED (fill per the comments above; no stubs in final code)
```
**RISK: HIGH — this is where R2 actually lives.** The induction step needs "m is covered
at some row ≤ p", i.e. a *height bound* `h(m) ≤ log₃(K)`. Empirically FALSE: K = 310 has
minimal witness row 40 while its top scale is p = 5 (m = 67 is covered at row 9, fine —
but K = 310 itself is only covered at row 40, far above p+1 = 6; nothing at rows ≤ 40
transfers). Counting also blocks a pure mod-class finish: survivors mod 3^p grow ≈ 2.48^p
(7, 18, 44, 110, 272, 676, 1676), so any `∀ K, K % 3^P ∈ closedSet` formulation fails for
every fixed P. Salvage value: S6 is true, cheap, and is the bridge that strategy (iii)
needs. Empirical law worth attempting as a standalone lemma: `p(K) ≤ K/2 + 8` (true on
[5,5000]) — but no proof route is currently visible; treat as a flag, not a plan.

### Strategy (iii) — THE EXPONENT-TRIT LAW ROUTE (forcing / survivor-tree pin)

**The mechanism already on file:** `noCommonTwo_all_exponent_trit_laws` says a
counterexample K must dodge the killing trit `2 − d` at every scale where its prefix pair
agrees; `row_common_two_iff_prefix_killing_trit` (the iff) and
`equal_prefix_pair_has_killing_trit` (the witness builder) make this an equivalence, so
the constraints are EXACTLY the complement of coverage. Define the survivor predicate and
its one-step recursion, then prove the only eventually-zero ternary paths that survive all
scales are {0,1,2,3,4,7}:

```lean
/-- S8. Survivors at depth p: no common-two row in 2..p. Decidable, cheap:
    each test is 4^r % 3^(q+1) via Nat.pow_mod + wavc_digit3_mod. -/
def wavc_survivor (K p : Nat) : Prop :=
  ∀ q, 2 ≤ q → q ≤ p → ¬ (digit3 (4^K) q = 2 ∧ digit3 (4^(K+1)) q = 2)

/-- S9. One-step recursion = killing-trit law in survivor form. -/
theorem wavc_survivor_step (K p : Nat) (hp : 1 ≤ p) :
    wavc_survivor K (p+1) ↔
      wavc_survivor K p ∧
      (digit3 (4^(exponentPrefix K p)) (p+1) ≠
        digit3 (4^((exponentPrefix K p)+1)) (p+1)
       ∨ exponentTrit K p ≠
        2 - digit3 (4^(exponentPrefix K p)) (p+1)) := by
  -- ⇐ direction: contrapose each surviving scale through
  -- row_common_two_iff_prefix_killing_trit; ⇒ direction: instantiate at q = p+1.
  -- PROOF BODY TO BE SUPPLIED (fill per the comments above; no stubs in final code)

/-- S10. Counterexample = eternal survivor (the object to be pinned). -/
theorem wavc_counterexample_survivor_all (K : Nat) (hNo : ¬ CommonTwo K) :
    ∀ p, wavc_survivor K p := by
  intro p q hq _ hrow
  exact hNo ⟨q, by omega, hrow.1, hrow.2⟩

/-- S11. THE PIN (the genuinely open lemma; the finish line of slice 2-c). -/
theorem wavc_survivor_pin (K : Nat) (hK : 5 ≤ K) (h7 : K ≠ 7)
    (h : ∀ p, wavc_survivor K p) : False := by
  -- planned proof shape (three sub-lemmas):
  -- (1) kernel-enumerate the survivor tree to depth 8 (1676 residues mod 3^8:
  --     feasible; each seed check is Nat.pow_mod-sized, NOT decide-on-∀-k<501);
  -- (2) wavc_row_prefix_transfer (S6): eternal survival of K forces its every
  --     prefix to be a survivor — the path of K in the depth-8 tree;
  -- (3) a CONTRACTING invariant on the tree (e.g. via S3's interval form: the
  --     survivor branches at scale p are exactly the principal units outside
  --     [2·3^p, 9·3^p/4) ∪ [11·3^p/4, 3·3^(p+1)), a measure-1/6 hole per level;
  --     an eventually-zero path meets the hole by depth ~K/2).  ← INVENTION NEEDED
  -- PROOF BODY TO BE SUPPLIED (fill per the comments above; no stubs in final code)

/-- S12. Assembled theorem (kills the axiom once S11 lands). -/
theorem wavc_four_power_direct_existence : FourPowerDirectExistence := by
  intro K hK h7
  by_contra hNo
  exact wavc_survivor_pin K hK h7 (wavc_counterexample_survivor_all K hNo)
```
**RISK flags:**
- S8–S10: low (restatements of `noCommonTwo_all_exponent_trit_laws` /
  `row_common_two_iff_prefix_killing_trit`; all names cited exist).
- S11(1): medium — depth-8 enumeration is 1676 residues; keep every digit check behind
  `wavc_digit3_mod` + `Nat.pow_mod`; never `decide` over a 3^8-range ∀.
- S11(3): **HIGH — this is the mathematical core of R2.** The survivor tree branches
  ≈ 2.48 per level (infinitely many 3-adic paths survive), so no naive König/counting
  argument pins it; what must be proved is that every *eventually-zero* path (a natural
  number) hits the killing hole. Best available handle: the interval form S3 + the
  bijection S5 turn the question into "the 3-adic powers 4^K hit the hole intervals",
  where the hole has relative measure 1/6 at every scale (empirical |C_p|/3^p → 1/6:
  2/9, 4/27, 14/81, 40/243, 122/729, 364/2187). A distribution/anti-concentration lemma
  for `4^K mod 3^(p+1)` along eventually-zero exponent paths is the missing invention.
- If S11(3) resists, the honest fallback for the mission: prove S1–S10 + depth-8
  enumeration + `p(K) ≤ K/2 + 8` as a computed certificate up to a large explicit bound,
  and flag the analytic core for a dedicated slice.

---

## PART 3 — Recommended sequencing (best strategy, 5 lines)

1. S2 + S6 + S9 first: one day of mechanical Lean, zero mathematical risk, and they are
   the shared spine of all three strategies.
2. S3 + S5 next: the interval characterization + bijection — the first *closed form* for
   the class pattern; makes rows 5..7 cheap (69.1% coverage) and reformulates R2 as a
   3-adic interval-hitting problem.
3. Then S11(1): the depth-8 survivor enumeration as a kernel-checkable certificate.
4. Then attack S11(3), the contracting invariant — the only genuinely open lemma; the
   trit-law file (`noCommonTwo_all_exponent_trit_laws`) plus S3/S5 are the tools.
5. S12 assembles `FourPowerDirectExistence` and deletes the custom axiom.
