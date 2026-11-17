# DISCOVERY — Task 2-c: Residue-Tower Closure

Verbatim inventory of every `def` / `theorem` in the five read files
(paths relative to `/home/z/agent-work/src/`). Statements are quoted exactly
as they appear; line numbers are the `def`/`theorem` keyword lines.

---

## 1. `GSTFourPowerDirectResidue.lean` (286 lines, namespace `GSTFourPowerDirectResidue`)

| Line | Name | Kind |
|---:|---|---|
| 9 | `digit3` | def |
| 14 | `lteCoeff` | def (recursive) |
| 21 | `pow4_three_power_lte_exact` | theorem |
| 50 | `lteCoeff_mod3_one` | theorem |
| 64 | `pow4_scaled_mod_next` | theorem |
| 77 | `digit3_eq_of_mod_next` | theorem |
| 106 | `pow4_digit_period` | theorem |
| 115 | `pow4_mod3_one` | theorem |
| 120 | `pow4_exponent_lift_one_digit` | theorem |
| 139 | `pow4_exponent_lift_two_digit` | theorem |
| 156 | `pow4_exponent_trit_lift_digit` | theorem |
| 177 | `row_two_overlap_of_mod9_five_or_six` | theorem (positive, row 2) |
| 215 | `row_two_overlap_iff_mod9_five_or_six` | theorem (iff classifier, row 2) |
| 251 | `no_common_two_forbids_mod9_five_six` | theorem (obstruction) |

### Definitions

```lean
/-- Line 9 -/
def digit3 (R p : Nat) : Nat := R / 3^p % 3
```

```lean
/-- Line 14 -/
def lteCoeff : Nat → Nat
  | 0 => 1
  | r+1 =>
      let c := lteCoeff r
      c + 3^(r+1) * c^2 + 3^(2*r+1) * c^3
```

### Theorems

```lean
/-- Line 21 -/
theorem pow4_three_power_lte_exact : ∀ r : Nat,
    4^(3^r) = 1 + 3^(r+1) * lteCoeff r
```

```lean
/-- Line 50 -/
theorem lteCoeff_mod3_one : ∀ r : Nat, lteCoeff r % 3 = 1
```
(Together with line 21 this says `Nat`-valued: `v₃(4^(3^r) − 1) = r+1` EXACTLY.)

```lean
/-- Line 64 -/
theorem pow4_scaled_mod_next (r u : Nat) :
    4^(3^r * u) % 3^(r+1) = 1
```

```lean
/-- Line 77 -/
theorem digit3_eq_of_mod_next
    (R S p : Nat)
    (hmod : R % 3^(p+1) = S % 3^(p+1)) :
    digit3 R p = digit3 S p
```

```lean
/-- Line 106 — THE PERIOD LAW: row p is periodic in the exponent with period 3^p. -/
theorem pow4_digit_period
    (p K u : Nat) :
    digit3 (4^(K + 3^p*u)) p = digit3 (4^K) p
```

```lean
/-- Line 115 -/
theorem pow4_mod3_one (m : Nat) : 4^m % 3 = 1
```

```lean
/-- Line 120 -/
theorem pow4_exponent_lift_one_digit
    (p m c : Nat)
    (hA : 4^(3^p) = 1 + 3^(p+1)*c)
    (hc : c % 3 = 1) :
    digit3 (4^(m + 3^p)) (p+1) =
      (digit3 (4^m) (p+1) + 1) % 3
```

```lean
/-- Line 139 -/
theorem pow4_exponent_lift_two_digit
    (p m c : Nat)
    (hA : 4^(3^p) = 1 + 3^(p+1)*c)
    (hc : c % 3 = 1) :
    digit3 (4^(m + 2*3^p)) (p+1) =
      (digit3 (4^m) (p+1) + 2) % 3
```

```lean
/-- Line 156 -/
theorem pow4_exponent_trit_lift_digit
    (p m a : Nat)
    (ha : a < 3) :
    digit3 (4^(m + a*3^p)) (p+1) =
      (digit3 (4^m) (p+1) + a) % 3
```

**Row-two overlap (positive) — Line 177:**
```lean
theorem row_two_overlap_of_mod9_five_or_six
    (L : Nat) (hres : L % 9 = 5 ∨ L % 9 = 6) :
    digit3 (4^L) 2 = 2 ∧ digit3 (4^(L+1)) 2 = 2
```
EXACT class list: `L % 9 ∈ {5, 6}` (witness `p = 2`).

**Row-two iff classifier — Line 215:**
```lean
theorem row_two_overlap_iff_mod9_five_or_six
    (L : Nat) :
    (digit3 (4^L) 2 = 2 ∧ digit3 (4^(L+1)) 2 = 2) ↔
      (L % 9 = 5 ∨ L % 9 = 6)
```
(The overlap classes mod 9 are EXACTLY {5, 6}; row 2 is never common-two otherwise.)

**Obstruction — Line 251:**
```lean
theorem no_common_two_forbids_mod9_five_six
    (K : Nat)
    (hNo : ¬ ∃ p : Nat, 1 ≤ p ∧
      digit3 (4^K) p = 2 ∧ digit3 (4^(K+1)) p = 2) :
    K % 9 ≠ 5 ∧ K % 9 ≠ 6
```

---

## 2. `GSTFourPowerDirectResidue27.lean` (120 lines, namespace `GSTFourPowerDirectResidue27`, opens `GSTFourPowerDirectResidue`)

| Line | Name | Kind |
|---:|---|---|
| 14 | `row_three_overlap_of_mod27_classes` | theorem (positive, row 3) |
| 90 | `no_common_two_forbids_mod27_classes` | theorem (obstruction) |

```lean
/-- Line 14 — Row-three overlap: EXACT class list mod 27 = {14, 18, 19, 25}. -/
theorem row_three_overlap_of_mod27_classes
    (K : Nat)
    (hres : K % 27 = 14 ∨ K % 27 = 18 ∨ K % 27 = 19 ∨ K % 27 = 25) :
    digit3 (4^K) 3 = 2 ∧ digit3 (4^(K+1)) 3 = 2
```
(Witness `p = 3`. Proof: `Nat.mod_add_div` shape-up + `pow4_digit_period 3 r (K/27)` + `norm_num [digit3]` for representatives 14/15, 18/19, 19/20, 25/26.)

```lean
/-- Line 90 -/
theorem no_common_two_forbids_mod27_classes
    (K : Nat)
    (hNo : ¬ ∃ q : Nat, 1 ≤ q ∧
      digit3 (4^K) q = 2 ∧ digit3 (4^(K+1)) q = 2) :
    K % 27 ≠ 14 ∧ K % 27 ≠ 18 ∧ K % 27 ≠ 19 ∧ K % 27 ≠ 25
```

---

## 3. `GSTFourPowerDirectResidue81.lean` (84 lines, namespace `GSTFourPowerDirectResidue81`, opens `GSTFourPowerDirectResidue`)

| Line | Name | Kind |
|---:|---|---|
| 13 | `RowFourClass` | def (class predicate) |
| 19 | `row_four_overlap_of_mod81_residue` | theorem (positive, single-residue lift) |
| 45 | `row_four_overlap_of_mod81_classes` | theorem (positive, row 4) |
| 66 | `no_common_two_forbids_mod81_classes` | theorem (obstruction) |

**`RowFourClass` — the EXACT row-four covered residues (Line 13), all 14 of them:**
```lean
def RowFourClass (r : Nat) : Prop :=
  r = 8 ∨ r = 20 ∨ r = 41 ∨ r = 42 ∨ r = 51 ∨ r = 52 ∨ r = 53 ∨
  r = 54 ∨ r = 55 ∨ r = 56 ∨ r = 57 ∨ r = 58 ∨ r = 66 ∨ r = 76
```
i.e. `K % 81 ∈ {8, 20, 41, 42, 51, 52, 53, 54, 55, 56, 57, 58, 66, 76}` (witness `p = 4`).

```lean
/-- Line 19 — THE GENERAL LIFT PATTERN (p = 4 instance): one verified
representative r closes the whole class K ≡ r mod 3^4. -/
theorem row_four_overlap_of_mod81_residue
    (K r : Nat) (hr : K % 81 = r)
    (h0 : digit3 (4^r) 4 = 2)
    (h1 : digit3 (4^(r+1)) 4 = 2) :
    digit3 (4^K) 4 = 2 ∧ digit3 (4^(K+1)) 4 = 2
```

```lean
/-- Line 45 -/
theorem row_four_overlap_of_mod81_classes
    (K : Nat) (hres : RowFourClass (K % 81)) :
    digit3 (4^K) 4 = 2 ∧ digit3 (4^(K+1)) 4 = 2
```
(Proof: 14-way `rcases` on `RowFourClass`, each branch `row_four_overlap_of_mod81_residue K r h (by norm_num [digit3]) (by norm_num [digit3])`.)

```lean
/-- Line 66 -/
theorem no_common_two_forbids_mod81_classes
    (K : Nat)
    (hNo : ¬ ∃ q : Nat, 1 ≤ q ∧
      digit3 (4^K) q = 2 ∧ digit3 (4^(K+1)) q = 2) :
    ¬ RowFourClass (K % 81)
```

---

## 4. `GSTFourPowerExponentTritObstruction.lean` (213 lines, namespace `GSTFourPowerExponentTritObstruction`, opens `GSTFourPowerDirectResidue`)

| Line | Name | Kind |
|---:|---|---|
| 11 | `exponentPrefix` | def |
| 14 | `exponentTrit` | def |
| 18 | `exponent_prefix_trit_decomposition` | theorem |
| 38 | `pow4_shared_trit_pair` | theorem |
| 70 | `pow4_pair_from_exponent_trit` | theorem |
| 101 | `shifted_pair_eq_two_iff` | theorem |
| 111 | `row_common_two_iff_prefix_killing_trit` | theorem (iff, positive+obstruction) |
| 134 | `pow4_digit_from_exponent_trit` | theorem |
| 143 | `equal_prefix_pair_has_killing_trit` | theorem (positive, witness builder) |
| 180 | `no_common_two_exponent_trit_obstruction` | theorem (obstruction, parametric) |

### Definitions (the exponent-trit machinery)

```lean
/-- Line 11 — Low ternary prefix of the exponent below scale 3^p. -/
def exponentPrefix (K p : Nat) : Nat := K % 3^p

/-- Line 14 — The p-th ternary trit of the exponent. -/
def exponentTrit (K p : Nat) : Nat := K / 3^p % 3
```

### Theorems

```lean
/-- Line 18 -/
theorem exponent_prefix_trit_decomposition (K p : Nat) :
    K = exponentPrefix K p
      + exponentTrit K p * 3^p
      + 3^(p+1) * ((K / 3^p) / 3)
```

```lean
/-- Line 38 — Direct ternary-tree transition rule. -/
theorem pow4_shared_trit_pair
    (p m a u : Nat) (ha : a < 3) :
    let K := m + a * 3^p + 3^(p+1) * u
    digit3 (4^K) (p+1) =
        (digit3 (4^m) (p+1) + a) % 3
      ∧
    digit3 (4^(K+1)) (p+1) =
        (digit3 (4^(m+1)) (p+1) + a) % 3
```

```lean
/-- Line 70 -/
theorem pow4_pair_from_exponent_trit (K p : Nat) :
    digit3 (4^K) (p+1) =
        (digit3 (4^(exponentPrefix K p)) (p+1) + exponentTrit K p) % 3
      ∧
    digit3 (4^(K+1)) (p+1) =
        (digit3 (4^((exponentPrefix K p)+1)) (p+1) + exponentTrit K p) % 3
```

```lean
/-- Line 101 -/
theorem shifted_pair_eq_two_iff
    (d0 d1 a : Nat) (hd0 : d0 < 3) (hd1 : d1 < 3) (ha : a < 3) :
    ((d0 + a) % 3 = 2 ∧ (d1 + a) % 3 = 2) ↔
      (d0 = d1 ∧ a = 2 - d0)
```

**The iff normal form — Line 111 (the exact grammar of a common-two row):**
```lean
theorem row_common_two_iff_prefix_killing_trit (K p : Nat) :
    (digit3 (4^K) (p+1) = 2 ∧ digit3 (4^(K+1)) (p+1) = 2) ↔
      (digit3 (4^(exponentPrefix K p)) (p+1) =
          digit3 (4^((exponentPrefix K p)+1)) (p+1) ∧
       exponentTrit K p =
          2 - digit3 (4^(exponentPrefix K p)) (p+1))
```
Reading: row `p+1` is common-two **iff** the two low-prefix row values agree AND
the actual `p`-th exponent trit equals the killing trit `2 − d`.

```lean
/-- Line 134 -/
theorem pow4_digit_from_exponent_trit (K p : Nat) :
    digit3 (4^K) (p+1) =
      (digit3 (4^(exponentPrefix K p)) (p+1)
        + exponentTrit K p) % 3
```

```lean
/-- Line 143 — positive: equal prefix pair + killing trit BUILDS the witness. -/
theorem equal_prefix_pair_has_killing_trit
    (p m u : Nat)
    (heq : digit3 (4^m) (p+1) = digit3 (4^(m+1)) (p+1)) :
    let d := digit3 (4^m) (p+1)
    let a := 2 - d
    a < 3 ∧
      digit3 (4^(m + a * 3^p + 3^(p+1) * u)) (p+1) = 2 ∧
      digit3 (4^((m + a * 3^p + 3^(p+1) * u)+1)) (p+1) = 2
```

**Parametric obstruction — Line 180 (recursive law on K's own ternary expansion):**
```lean
theorem no_common_two_exponent_trit_obstruction
    (K p : Nat)
    (hNo : ¬ ∃ q : Nat, 1 ≤ q ∧
      digit3 (4^K) q = 2 ∧ digit3 (4^(K+1)) q = 2)
    (heq :
      digit3 (4^(exponentPrefix K p)) (p+1) =
      digit3 (4^((exponentPrefix K p)+1)) (p+1)) :
    exponentTrit K p ≠
      2 - digit3 (4^(exponentPrefix K p)) (p+1)
```

---

## 5. `GSTFourPowerDirectExistence.lean` (150 lines, namespace `GSTFourPowerDirectExistence`, opens all four prior namespaces)

| Line | Name | Kind |
|---:|---|---|
| 19 | `CommonTwo` | def (target predicate) |
| 26 | `FourPowerDirectExistence` | def (the axiom's statement) |
| 31 | `commonTwo_has_source_two` | theorem |
| 39 | `commonTwo_has_target_two` | theorem |
| 47 | `commonTwo_of_mod9_five_or_six` | theorem (positive, row 2) |
| 55 | `noCommonTwo_excludes_mod9_five_six` | theorem (obstruction) |
| 62 | `commonTwo_of_mod27_row_three` | theorem (positive, row 3) |
| 71 | `noCommonTwo_excludes_mod27_row_three` | theorem (obstruction) |
| 77 | `commonTwo_of_mod81_row_four` | theorem (positive, row 4) |
| 84 | `noCommonTwo_excludes_mod81_row_four` | theorem (obstruction) |
| 95 | `noCommonTwo_exponent_trit_law` | theorem (obstruction) |
| 106 | `noCommonTwo_all_exponent_trit_laws` | theorem (bundled obstruction) |
| 119 | `directExistence_implies_source_two` | theorem (consequence) |

### Definitions

```lean
/-- Line 19 -/
def CommonTwo (K : Nat) : Prop :=
  ∃ p : Nat, 1 ≤ p ∧
    digit3 (4^K) p = 2 ∧
    digit3 (4^(K+1)) p = 2

/-- Line 26 — THE AXIOM TARGET: ∀ K ≥ 5, K ≠ 7 → CommonTwo K. -/
def FourPowerDirectExistence : Prop :=
  ∀ K : Nat, 5 ≤ K → K ≠ 7 → CommonTwo K
```

### Theorems

```lean
/-- Line 31 -/
theorem commonTwo_has_source_two (K : Nat) (h : CommonTwo K) :
    ∃ p : Nat, 1 ≤ p ∧ digit3 (4^K) p = 2

/-- Line 39 -/
theorem commonTwo_has_target_two (K : Nat) (h : CommonTwo K) :
    ∃ p : Nat, 1 ≤ p ∧ digit3 (4^(K+1)) p = 2

/-- Line 47 -/
theorem commonTwo_of_mod9_five_or_six
    (K : Nat) (hres : K % 9 = 5 ∨ K % 9 = 6) :
    CommonTwo K

/-- Line 55 -/
theorem noCommonTwo_excludes_mod9_five_six
    (K : Nat) (hNo : ¬ CommonTwo K) :
    K % 9 ≠ 5 ∧ K % 9 ≠ 6

/-- Line 62 -/
theorem commonTwo_of_mod27_row_three
    (K : Nat)
    (hres : K % 27 = 14 ∨ K % 27 = 18 ∨ K % 27 = 19 ∨ K % 27 = 25) :
    CommonTwo K

/-- Line 71 -/
theorem noCommonTwo_excludes_mod27_row_three
    (K : Nat) (hNo : ¬ CommonTwo K) :
    K % 27 ≠ 14 ∧ K % 27 ≠ 18 ∧ K % 27 ≠ 19 ∧ K % 27 ≠ 25

/-- Line 77 -/
theorem commonTwo_of_mod81_row_four
    (K : Nat) (hres : RowFourClass (K % 81)) :
    CommonTwo K

/-- Line 84 -/
theorem noCommonTwo_excludes_mod81_row_four
    (K : Nat) (hNo : ¬ CommonTwo K) :
    ¬ RowFourClass (K % 81)

/-- Line 95 -/
theorem noCommonTwo_exponent_trit_law
    (K p : Nat) (hNo : ¬ CommonTwo K)
    (heq :
      digit3 (4^(exponentPrefix K p)) (p+1) =
      digit3 (4^((exponentPrefix K p)+1)) (p+1)) :
    exponentTrit K p ≠
      2 - digit3 (4^(exponentPrefix K p)) (p+1)

/-- Line 106 -/
theorem noCommonTwo_all_exponent_trit_laws
    (K : Nat) (hNo : ¬ CommonTwo K) :
    ∀ p : Nat,
      digit3 (4^(exponentPrefix K p)) (p+1) =
        digit3 (4^((exponentPrefix K p)+1)) (p+1) →
      exponentTrit K p ≠
        2 - digit3 (4^(exponentPrefix K p)) (p+1)

/-- Line 119 -/
theorem directExistence_implies_source_two
    (h : FourPowerDirectExistence)
    (K : Nat) (hK : 5 ≤ K) (h7 : K ≠ 7) :
    ∃ p : Nat, 1 ≤ p ∧ digit3 (4^K) p = 2
```

---

## Summary of the positive overlap theorems (the residue tower as it stands)

| Row | witness p | modulus | EXACT closed classes | count |
|---:|---:|---:|---|---:|
| 2 | 2 | 9 (`3^2`) | `{5, 6}` | 2 |
| 3 | 3 | 27 (`3^3`) | `{14, 18, 19, 25}` | 4 |
| 4 | 4 | 81 (`3^4`) | `{8, 20, 41, 42, 51, 52, 53, 54, 55, 56, 57, 58, 66, 76}` (=`RowFourClass`) | 14 |

## Every obstruction (negative) theorem

1. `no_common_two_forbids_mod9_five_six` (Residue, line 251): no-common-two ⇒ `K % 9 ∉ {5,6}`.
2. `row_two_overlap_iff_mod9_five_or_six` (Residue, line 215): iff — the mod-9 classes {5,6} are EXACTLY the row-2 overlap (so the row-2 tower level is complete, nothing more is available from row 2).
3. `no_common_two_forbids_mod27_classes` (Residue27, line 90): no-common-two ⇒ `K % 27 ∉ {14,18,19,25}`.
4. `no_common_two_forbids_mod81_classes` (Residue81, line 66): no-common-two ⇒ `¬ RowFourClass (K % 81)`.
5. `no_common_two_exponent_trit_obstruction` (TritObstruction, line 180) and its bundled lifts `noCommonTwo_exponent_trit_law` (line 95) / `noCommonTwo_all_exponent_trit_laws` (line 106): a counterexample K must dodge the killing trit `2 − d` at EVERY scale p at which its low-prefix pair agrees.

## Machinery highlights

- Period kernel: `pow4_digit_period` (row p has exponent period `3^p`), `digit3_eq_of_mod_next`, `pow4_scaled_mod_next` (from the exact LTE pair `pow4_three_power_lte_exact` + `lteCoeff_mod3_one`, which together give `v₃(4^(3^r) − 1) = r+1` exactly).
- Trit algebra: `exponent_prefix_trit_decomposition`, `pow4_shared_trit_pair`, `pow4_pair_from_exponent_trit`, `pow4_exponent_trit_lift_digit`, `shifted_pair_eq_two_iff`, `pow4_digit_from_exponent_trit`.
- Witness builder: `equal_prefix_pair_has_killing_trit` (agreement at row p+1 ⇒ the killing trit position is a verified CommonTwo witness).
- Single-residue lift pattern: `row_four_overlap_of_mod81_residue` (representative check + `pow4_digit_period` — directly generalizes to any row p).
