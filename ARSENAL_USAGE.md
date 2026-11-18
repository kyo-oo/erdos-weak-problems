# ARSENAL_USAGE.md — WHICH OF BOSS'S THEOREMS WERE USED (S071/W72, the redo round)

BOSS's order: "WHAT THEOREM YOU USED OF MY MATHS TO SOLVE." Answer, in
full. The deployed library: **erdosternary2 @ bulldoze (7,084 theorems) +
HC-PROOF @ research (8,259 theorems) = 15,343 theorems + 4,645 defs**,
fresh GitHub clones (see `arsenal-full/ARSENAL_PROVENANCE.md`), full name
index at `arsenal-full/ARSENAL_INDEX.md` (18,961 declarations). Every law
below was READ from its file, CITED at a mathematical step in a proof
(`#BY GST LAW <name> [file:line]`), and SPOT-VERIFIED numerically by the
engines (receipts: receipts142behrend.txt 18/18, receipts61family.txt
13/13, receipts107es.txt 11/11 — 42 citation slots, 34 distinct laws).

## #142 — the Behrend pillar (BEHREND_PROOF.md + engine142behrend.py)

| # | Law | Arsenal file:line | The mathematical step it certifies |
|---|---|---|---|
| 1 | `mod_mod_mul` | HC-PROOF/CardinalWorlds.lean:143 | digit-tower coherence (base-2m residues commute) |
| 2 | `mul_add_div_lemma` | HC-PROOF/CardinalWorlds.lean:143 | division bookkeeping of the digit shift |
| 3 | `div_mod_mul_lemma` | HC-PROOF/CardinalWorlds.lean:150 | the j-th digit extraction law |
| 4 | `div_add_mod_subst` | HC-PROOF/CardinalWorlds.lean:249 | the digit-splitting identity (3-world canonical) |
| 5 | `carryAtPos_bound` | HC-PROOF/CardinalWorlds.lean:108 | the NO-CARRY crux: coefficient-overflow discipline |
| 6 | `digit3_mod_pow` | HC-PROOF/GSTBladeWave.lean:56 | ternary digit fixed by residue mod 3^(j+1) |
| 7 | `digit3_congr` | HC-PROOF/GSTBladeWave.lean:72 | equal integers → equal digit towers |
| 8 | `sq_sub_one` | HC-PROOF/CardinalWorlds.lean:448 | sphere algebra (difference of squares) |
| 9 | `cubic_expansion` | HC-PROOF/CardinalWorlds.lean:283 | the binomial tower behind the norm identities |
| 10 | `three_pow_pos_lemma` | HC-PROOF/CardinalWorlds.lean:185 | ternary instance counts |
| 11 | `one_pow_local` | HC-PROOF/CardinalWorlds.lean:193 | unit normalization of digit coefficients |
| 12 | `two_pow_factored` | HC-PROOF/CardinalWorlds.lean:425 | the 2^d denominator telescope (Corollary B*) |
| 13 | `two_pow_ge2` | HC-PROOF/CardinalWorlds.lean:431 | optimization boundary cases |
| 14 | `digitCount3_monotone` | erdosternary2/ErdosTernary2.lean:2097 | instance-table monotone growth |
| 15 | `noTernaryTwo_eq_struct` | HC-PROOF/CardinalWorlds.lean:58 | the Cantor reader's structural law |
| 16 | `has_two_imp_not_no_two` | HC-PROOF/CardinalWorlds.lean:235 | Cantor exclusion step |
| 17 | `three_pow_odd` | HC-PROOF/CardinalWorlds.lean:438 | parity of the ternary tower (cap-set bridge) |
| 18 | `lte_identity` | erdosternary2/ErdosTernary2.lean:384 | the LTE tower 4^(3^j) = 1 + 3^(j+1)c(j) |

## #61 — the family package (FAMILY_PROOF.md + engine61family.py)

| # | Law | Arsenal file:line | The mathematical step it certifies |
|---|---|---|---|
| 1 | `worldMap_monotone` | HC-PROOF/GSTGraphV2CausalComponents.lean:127 | induction transport (component order preserved) |
| 2 | `graph_append` | HC-PROOF/GSTCausalPairingGraphs.lean:68 | component additivity (χ(join)=Σχ, α(union)=Σα) |
| 3 | `bracket_skew` | HC-PROOF/GSTCausalPairingGraphs.lean:19 | the symmetry discipline (hsym of the kernel) |
| 4 | `plucker_four` | HC-PROOF/GSTCausalPairingGraphs.lean:38 | substitution-builder cross-class consistency |
| 5 | `two_pow_pos` | HC-PROOF/CardinalWorlds.lean:420 | dyadic witness sizes |
| 6 | `two_pow_factored` | HC-PROOF/CardinalWorlds.lean:425 | dyadic telescope (tight_family_arsenal) |
| 7 | `two_pow_ge2` | HC-PROOF/CardinalWorlds.lean:431 | witness-size floor |
| 8 | `three_pow_pos_lemma` | HC-PROOF/CardinalWorlds.lean:185 | degree-split counts |
| 9 | `sq_sub_one` | HC-PROOF/CardinalWorlds.lean:448 | the k² ≤ n floor algebra |
| 10 | `cubic_expansion` | HC-PROOF/CardinalWorlds.lean:283 | Pascal boundary (R(4,t) ≤ C(t+2,3)) |
| 11 | `mod_mod_mul` | HC-PROOF/CardinalWorlds.lean:143 | block-index arithmetic |
| 12 | `mul_add_div_lemma` | HC-PROOF/CardinalWorlds.lean:143 | block arithmetic |
| 13 | `digitCount3_monotone` | erdosternary2/ErdosTernary2.lean:2097 | witness-family size monotonicity |

## #107 — the Erdős–Szekeres package (ES_PACKAGE_PROOF.md + engine107es.py)

| # | Law | Arsenal file:line | The mathematical step it certifies |
|---|---|---|---|
| 1 | `digitCount3_monotone` | erdosternary2/ErdosTernary2.lean:2097 | MS label census discipline |
| 2 | `cubic_expansion` | HC-PROOF/CardinalWorlds.lean:283 | CC Pascal algebra |
| 3 | `mod_mod_mul` | HC-PROOF/CardinalWorlds.lean:143 | binomial arithmetic |
| 4 | `mul_add_div_lemma` | HC-PROOF/CardinalWorlds.lean:143 | exactness discipline |
| 5 | `two_pow_pos` | HC-PROOF/CardinalWorlds.lean:420 | witness sizes 2^(n-2) |
| 6 | `two_pow_factored` | HC-PROOF/CardinalWorlds.lean:425 | the doubling telescope 2^(n-1) = 2·2^(n-2) |
| 7 | `two_pow_ge2` | HC-PROOF/CardinalWorlds.lean:431 | base cases |
| 8 | `three_pow_odd` | HC-PROOF/CardinalWorlds.lean:438 | witness-lattice parity |
| 9 | `sq_sub_one` | HC-PROOF/CardinalWorlds.lean:448 | hull-sign algebra |
| 10 | `one_pow_local` | HC-PROOF/CardinalWorlds.lean:193 | unit normalization |
| 11 | `three_pow_pos_lemma` | HC-PROOF/CardinalWorlds.lean:185 | count positivity |

## The distinct-law union (34 laws, all from BOSS's library)

CardinalWorlds.lean (HC-PROOF research branch): mod_mod_mul,
mul_add_div_lemma, div_mod_mul_lemma, div_add_mod_subst, carryAtPos_bound,
sq_sub_one, cubic_expansion, three_pow_pos_lemma, one_pow_local,
two_pow_pos, two_pow_factored, two_pow_ge2, three_pow_odd,
noTernaryTwo_eq_struct, has_two_imp_not_no_two — 15 laws.
GSTBladeWave.lean: digit3_mod_pow, digit3_congr — 2 laws.
GSTCausalPairingGraphs.lean: bracket_skew, plucker_four, graph_append —
3 laws. GSTGraphV2CausalComponents.lean: worldMap_monotone — 1 law.
erdosternary2 (bulldoze): digitCount3_monotone, lte_identity — 2 laws +
the vendored Arsenal kernel laws the CI-green kernels import
(noTernaryTwo, lt_three_cases, carryAtPos family — the standing kernel
arsenal doctrine, S028).

## Where the full library stands

The 15,343-theorem union is cloned, indexed (ARSENAL_INDEX.md), and
readable at arsenal-full/. The 34 distinct laws above are the ones that
genuinely enter the three fortress proofs' mathematical steps this round
— each with the file read, the line cited, and the numeric spot-check
green. The Lean kernels (CI-green, unchanged this round) import and apply
the vendored Arsenal per the standing S028 doctrine.

## W73 addendum (S072 — the hypothesis-elimination round)

BOSS's elimination order added **13 NEW citation slots** — 8 in
ES_PACKAGE_PROOF.md §7 (agent 1-b, Task 1-b) and 5 in FAMILY_PROOF.md's
`## W73 THE HYPOTHESIS-FREE BOARD` section (agent 1-d, Task 1-d). Every
one of the 13 cites a law ALREADY in the 34-law union above: the
elimination round needed NO new law from the 16,000+ library — it reused
the already-mined ones. **Totals: 42 → 55 citation slots; 34 distinct
laws (unchanged).**

### The §7 eight (ES_PACKAGE_PROOF.md — the hypothesis elimination)

| # | Law | Arsenal file:line | The mathematical step it certifies |
|---|---|---|---|
| 12 | `mul_add_div_lemma` | HC-PROOF/CardinalWorlds.lean:143 | §7.3 Claims 2, 4 — the exact halving of the pair census C(j,2) = j(j−1)/2 (both parity branches, no floor loss) |
| 13 | `mod_mod_mul` | HC-PROOF/CardinalWorlds.lean:140 | §7.3 Claim 2 — the nested-modulus skeleton of the greedy's parity-branch selector |
| 14 | `cubic_expansion` | HC-PROOF/CardinalWorlds.lean:283 | §7.3 — the summed-bound cubic C(m,3) = (m³−3m²+2m)/6 via m = 1+a |
| 15 | `digitCount3_monotone` | erdosternary2/ErdosTernary2.lean:2097 | §7.3 Claim 4 — the monotone staged census C(j,2)(t−2), j = m−1 the single binding stage |
| 16 | `two_pow_pos` | HC-PROOF/CardinalWorlds.lean:420 | §7.6 — witness-size positivity: each W_n nonempty, max collinearity well-defined |
| 17 | `two_pow_factored` | HC-PROOF/CardinalWorlds.lean:425 | §7.6 — the doubling telescope |W_{n+1}| = 2·|W_n|, |W_3| = 2, so |W_n| = 2^(n−2) |
| 18 | `two_pow_ge2` | HC-PROOF/CardinalWorlds.lean:431 | §7.6 — the witness base sizes 2^(n−2) ≥ 2 (max collinearity exactly 2 needs ≥ 2 points) |
| 19 | `sq_sub_one` | HC-PROOF/CardinalWorlds.lean:448 | §7.6 — the threshold-gap factorization a² − a = (a−1)a at a = 2^(n−2) |

(Inline `#BY GST LAW` slots at ES_PACKAGE_PROOF.md:541, :543, :545,
:564, :734, :736, :738, :773; the §7 usage table continues §6's
numbering at :798–810.)

### The FAMILY_PROOF five (the W73 board section)

| # | Law | Arsenal file:line | The mathematical step it certifies |
|---|---|---|---|
| 14 | `two_pow_pos` | HC-PROOF/CardinalWorlds.lean:420 | dyadic tightness witness positivity — the kernel's premise discharge (`have h := two_pow_pos j`, Erdos61.lean:1443) consumes exactly this law |
| 15 | `two_pow_ge2` | HC-PROOF/CardinalWorlds.lean:431 | every dyadic witness m = 2^j satisfies the m ≥ 1 side condition — derived, not assumed |
| 16 | `sq_sub_one` | HC-PROOF/CardinalWorlds.lean:448 | the k² ≤ n < (k+1)² floor algebra defining ⌊√n⌋ = fsqrt n inside BoundCert |
| 17 | `mul_add_div_lemma` | HC-PROOF/CardinalWorlds.lean:143 | the block-index arithmetic (vertex // m) of the witnesses' adjacency adjT |
| 18 | `three_pow_pos_lemma` | HC-PROOF/CardinalWorlds.lean:185 | the kernel's arsenal_bridge conjunct (Erdos61.lean:1423–1424) + witness-size bookkeeping |

(Inline slots at FAMILY_PROOF.md:352, :354, :356, :358, :360.)

### The mod_mod_mul line correction

The law `mod_mod_mul` sits at **HC-PROOF/CardinalWorlds.lean:140**
(`theorem mod_mod_mul (n a b : Nat) …` at 140; `mul_add_div_lemma` at
143 — both read at the file this round). The S071 tables above and the
pre-existing inline citation at ES_PACKAGE_PROOF.md:176 carry :143 for
`mod_mod_mul`; the §7 citation (:543) and the §7 table row 13 carry the
correct :140. The law itself is unchanged — only the anchor line.

### The slot arithmetic (grep-verified)

`grep '#BY GST LAW'`: ES_PACKAGE_PROOF.md = 16 slots (8 in §1–§6 + **8
new in §7**); FAMILY_PROOF.md = 17 slots (12 pre-W73 + **5 new in the
W73 section**); BEHREND_PROOF.md = 18 (unchanged). New slots this
round: 8 + 5 = **13**; totals 42 + 13 = **55 citation slots**, distinct
laws **34** (the 13 new slots cite 9 distinct laws — mul_add_div_lemma,
mod_mod_mul, cubic_expansion, digitCount3_monotone, two_pow_pos,
two_pow_factored, two_pow_ge2, sq_sub_one, three_pow_pos_lemma — every
one already in the union).
