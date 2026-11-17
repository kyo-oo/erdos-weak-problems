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
