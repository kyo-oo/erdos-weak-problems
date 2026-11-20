# NEW_CLAIMS — W76-142E (ENGINE lane, Erdős #142)

Schema per claim: {"id", "statement", "verification"} (matching
comparator-official/challenges/142/solution.json). All engines deterministic,
all receipts in problem142-ap-free/. Every cited arsenal law was read at its
exact file:line in arsenal-full/ this session and numerically spot-checked
(receipts142table_v2.txt, ARSENAL LAW SPOT-CHECKS).

---

## C142-TABLE-EXT

{"id": "C142-TABLE-EXT",
 "statement": "The certified exact r_3 table (largest 3-AP-free subset of [1,N]) is extended from the banked range N <= 38 to N <= 48: r_3(39) = 14, r_3(40) = 15, r_3(41) = r_3(42) = r_3(43) = r_3(44) = r_3(45) = r_3(46) = r_3(47) = r_3(48) = 16. Every new cell carries BOTH certificates: a SAT witness of size r_3(N) and an UNSAT certificate at r_3(N)+1 (no 3-AP-free subset of [1,N] has more elements). All 10 cells are CERTIFIED-BOTH; none is WITNESS-ONLY. The values agree with the OEIS A003002 b-file (independent external anchor) at every N = 1..48, and the fresh C branch-and-bound independently re-derives the banked column r_3(1..38) (38/38 values, 38/38 witnesses re-validated).",
 "verification": "engine142table_v2.py (Z3 5.4.1 feasibility bisection: SAT@v witness saved + UNSAT@v+1 confirmed twice with independent solver seeds; genuine `unsat` status required, timeouts never accepted; translation symmetry x_0=true imposed, valid WLOG since A - min(A) is AP-free of the same size containing 0) AND bnb142.c (fresh C bitboard branch-and-bound: taking v marks w=2v-p for every chosen p, bound count+popcount(non-excluded>=i); forced-0 and no-force runs must agree) AND checker142lib.py (third, independent pair-midpoint-scan checker re-validating BOTH witnesses) AND the OEIS b-file cross-check. Slowest certificates: N=48 UNSAT 1.204s/0.917s (two seeds) and BnB 0.020s (2,919,777 nodes); engine wall 21.5s. Negative controls: planted-AP detection; keeping only the d=1 AP clauses makes 17 feasible in [0,48) and the returned witness fails the full 3-AP check (clause load-bearing); formula sha + verdict reproducible. Receipts: problem142-ap-free/receipts142table_v2.txt; data: problem142-ap-free/tables_rk_v2.json (k=3 N=1..48 with per-cell status, both certificates' runtimes, witnesses 0- and 1-based; banked k=4,5,6 tables carried verbatim)."}

## C142-MODELSTEP-CERT

{"id": "C142-MODELSTEP-CERT",
 "statement": "THE NO-WRAP LAW (the model step L-NW of the density-increment architecture): for every prime p and every cyclic AP P(a,d,L) = {a + i*d mod p : i in [0,L)} in Z_p with |P| = L <= floor(sqrt(p)), every internal 3-AP of P (a triple {x,y,z} subset P with x != z and x + z == 2y mod p) is GENUINE in rescaled coordinates phi(t) = (t-a)*d^{-1} mod p: phi(x) + phi(z) = 2*phi(y) as integers. Certified at p in {101, 1009, 3203, 9973}. Certified companions: (i) the structural form — the internal 3-APs of P are exactly the integer 3-APs of the index interval [0,L-1] (per-(L,d) counts are d-invariant and equal the integer-AP count for every L <= sqrt(p) at every prime); (ii) the exact threshold — the law's clean range is precisely L <= (p+1)/2 (verified: ZERO rescaled wraps at every L <= (p+1)/2 scanned, and exactly 2 wrapping triples per parametrization (a,d) at L = (p+3)/2, both wrap directions); (iii) the density bookkeeping — rescaling preserves cardinalities, densities and relative lengths (nested rescales multiply exactly), and the 3-AP count transfers exactly between the cyclic and rescaled-integer worlds.",
 "verification": "TWO independent methods per prime. (a) wrapscan142.c — exhaustive point-level brute wrap-scan over ALL (d, L <= sqrt(p)) parametrizations (a=0) plus random a-samples: 1,198,788 parametrizations, 841,996,456 internal 3-APs scanned, ZERO rescaled-coordinate wraps; original-coordinate wraps counted separately (allowed). (b) engine142modelstep.py — algebraic rescaled-coordinates check: phi-recovery phi(x_i) == i EXHAUSTIVE over all d and all points (1,962,788 checks, gmpy2 inverses) + forward identity (27,843,402 checks; numpy-exhaustive over all d plus an independent pure-python re-check) + the no-wrap bound 2(L-1) < p per L + the exact-threshold negative controls + density bookkeeping on 24 planted progressions (bijection, density preservation, nested double-rescale, 3-AP count transfer by two independent counting codes at both levels). Wall: 4.5s for the largest prime. Receipts: problem142-ap-free/receipts142modelstep.txt; raw scans: experiments_v2/wrapscan_*.jsonl."}

## C142-SECONDMOMENT-CK (supporting the K-lane's L-EP law)

{"id": "C142-SECONDMOMENT-CK",
 "statement": "THE SECOND-MOMENT CHECKPOINTS (empirical forms of the ENERGY-POPULARITY law L-EP): for explicit dense sets A subset [1,N] with |A| = delta*N exactly, at N in {10^3, 10^4} and delta in {0.3, 0.5, 0.7}, three deterministic families (interval, seeded random, evenly-spread Beatty): (SM-0) two independent counting codes (naive loops vs bitset big-int shifts; pair spectra cross-checked a third way by FFT convolution) agree exactly on the 3-AP count T3, the triple-difference spectrum f3(d) and the pair-difference spectrum r(d); (SM-1) the cubic expansion identity holds EXACTLY in integers: N^3 T3 = m^3 T0 + m^2 S1 + m S2 + S3 with T0 = sum_d (N-2d), g = N*1_A - m (the cubic_expansion law: 1_A = delta + f splits the triple count into the random baseline delta^3 T0 plus the linear/pairwise/cubic deviation terms); (SM-2) the Cauchy-Schwarz second-moment bound S3^2 <= S4*S5 holds exactly (|C| <= sqrt(E2')*sqrt(V2), the difference-axis second moment); (SM-3) the spectral second moment sum_d f3(d)^2 >= T3^2/D holds; (SM-4) popular differences: sum_d r(d) = C(m,2), max_d r(d) >= ceil(C(m,2)/(N-1)) and max_d f3(d) >= ceil(T3/D) (pigeonhole over the difference axis), and the observed constants c_obs = max r(d)/N (range 0.105..0.699) and c3_obs = max f3(d)/N (range 0.045..0.699) all exceed the c(delta) = delta^2/2 claim level. Observed baseline ratios T3/(delta^3 T0): random family 0.96..1.00 (the random model), interval family 1.43..3.34, Beatty 0.96..1.99 — the structured deviations that the L-EP law bounds.",
 "verification": "engine142secondmoment.py: 18/18 cells fully green, wall 67s. Negative controls: a Stanley AP-free set (T3 = 0 by both codes, certified AP-free by the component-1 third checker), a hand-computed case (N=8, T3=4), and the exact-cancellation check (for the AP-free set with T3 = 0 vs delta^3 T0 = 5.76, the cubic identity still holds EXACTLY — the deviation terms cancel). Receipts: problem142-ap-free/receipts142secondmoment.txt; data: problem142-ap-free/tables_secondmoment_v2.json."}

---

## Arsenal laws cited by this lane (all verified at exact file:line, spot-checked numerically)

#BY GST LAW cubic_expansion [CardinalWorlds.lean:283]
#BY GST LAW digit3_mod_pow [GSTBladeWave.lean:56]
#BY GST LAW digit3_congr [GSTBladeWave.lean:72]
#BY GST LAW mod_mod_mul [CardinalWorlds.lean:140]
#BY GST LAW div_mod_mul_lemma [CardinalWorlds.lean:150]
#BY GST LAW div_add_mod_subst [CardinalWorlds.lean:249]
#BY GST LAW carryAtPos_bound [CardinalWorlds.lean:108]
#BY GST LAW sum_le_sum_of_forall [erdosternary2/bulldoze/problem261-continuum-tower/Erdos261Tower.lean:116]
#BY GST LAW tower_cauchy [erdosternary2/bulldoze/problem261-continuum-tower/Erdos261Tower.lean:810]
