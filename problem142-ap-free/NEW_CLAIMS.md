# W76 NEW CLAIMS — problem 142 (the 142E engine-lane claims + the 142K killer-lane claims, merged)

## SECTION 1 — the W76-142E lane claims


## C142-SUBLINEAR-COMPLETE
"THEOREM SUBLINEAR (W76, in-package, complete, unconditional): for every eps in (0, 1/8], every 3-AP-free S subset [1,N] with N >= N0(eps) = 480*(1024/eps)^(ceil(13300/eps^2)+2) satisfies |S| <= eps*N. Hence r_3(N)/N -> 0. Assembly: the transfer law (Lemma T) + L-BP (Bertrand in-package: sieve n<=1024 + the binomial magnitude chain at n=512/1024/2048) + L-EP (the energy-popularity law: the triple-deviation identity, Parseval confinement, large-coefficient extraction — all on BOSS'S OWN character laws hc_fourier_character_norm/exponential/unitary + hc_circle_L2_basis + exact_three_geometric_sum + the gst energy-split family + tower_cauchy) + L-ARC REPAIRED (the arc increment: the W75 constant chain was BROKEN — error 0.196*delta^2*p exceeded main 0.125*delta^2*p; the repair M=ceil(128/delta), Re >= kappa*p/2, error <= (pi/32)*delta^2*p < delta^2*p/8, and the repaired chain has NO delta <= 1/2 ceiling — probe-certified delta in [0.52, 0.70] at p in {1009, 2003}, 14/14) + L-NW (the no-wrap model step: 841,996,456 internal 3-APs scanned at p in {101,1009,3203,9973}, ZERO wraps, two methods) + the UNION FIRING LAW (delta* = 0.81: the certified table fires for containers L in [3,48] — ceil(0.81L) > r_3(L) everywhere, max ratio 0.8; the interval-capacity mesh fires for L >= 49 — cap <= 0.659). Engine: 264/264 checks GREEN (EP-CK 196-lane battery + FIRING-TABLE-UNION + BP-CK + PB-CK + PB-CK-MESH + MESH-INT + I-CK-HI + I-CK-HI-LTERM + DF-CK + LAW-SPEC 23/23)."

## C142-LAW-EP
"NEW LAW L-EP (ENERGY-POPULARITY): (i) the triple-deviation identity T = delta^3 p^2 + (1/p) sum_{r != 0} fhat(r)^2 fhat(-2r) — derived on BOSS'S OWN phase system (hc_fourier_exponential/unitary compose the phases; hc_fourier_character_norm + exact_three_geometric_sum annihilate the balanced sums; gst_infinite_paradox_energy_split + cubic_expansion carry the expansion); (ii) the energy confinement sum |fhat|^2 = p^2 delta(1-delta) (hc_circle_L2_basis + tower_cauchy); (iii) the large-coefficient extraction M* >= delta^2 p/2 for cyclically-AP-free A with p >= 2/delta^2. Nine arsenal theorems combined. Engine: EP-CK exact identities at p in {101, 1009, 4999, 10007}, two counting codes, exact complex arithmetic."

## C142-LAW-ARC-REPAIRED
"NEW LAW L-ARC (THE ARC-INCREMENT, REPAIRED): if max_{r != 0} |fhat(r)| >= delta^2 p / 2 then a cyclic AP P with |P| >= p*delta/256 and |A cap P| >= (delta + delta^2/1024)|P| exists — for ALL delta in (0,1), NO CEILING (the W75 version's constants were broken: error term 2*pi/M*sum|f| with M=ceil(32/delta) exceeds the main term; the repair: M = ceil(128/delta), phase selection Re >= kappa*p/2 among {r,-r,2r,-2r}, error <= (pi/32)*delta^2*p < delta^2*p/8). Engine: I-CK (banked) + I-CK-HI (delta in [0.52,0.70], p in {1009,2003}, 14/14 green: coefficient >= delta^2/2, gains +0.30..+0.48)."

## C142-LAW-NW
"NEW LAW L-NW (NO-WRAP MODEL STEP): for a cyclic AP P = {x0 + i*d} in Z_p with d != 0 and 2L-2 < p, the internal 3-APs are genuine iff the index relation i+k=2j — the density-increment flow rescales containers with zero wrap error. Engine: 841,996,456 internal 3-APs scanned at p in {101, 1009, 3203, 9973} by two independent methods (point-level wrap-scan + algebraic rescaled-coordinates), ZERO disagreements, sharp threshold negative controls (clean at (p+1)/2, exactly 2 wraps at (p+3)/2)."

## C142-LAW-BP
"NEW LAW L-BP (THE PRIME-WINDOW LAW, Bertrand in-package): for every L >= 1 a prime q with 2L < q <= 4L exists. Derivation: the binomial-coefficient argument (divisibility cell + size cell + the contradiction magnitude chain 4^n/(2n+1) > (2n)^(sqrt(2n)+pi(2n/3)) at n = 512/1024/2048 — margins 10^4 to 10^96) + the finite sieve (every window (n,2n], n <= 1024, contains a prime). Engine: BP-CK green."

## C142-LAW-TERM-UNION
"NEW LAW L-TERM + THE UNION FIRING LAW: (a) L-TERM (terminal inconsistency): a cyclically-AP-free A in Z_p with p >= 2/delta^2 has delta <= (9-sqrt(17))/8 = 0.6096 (the extraction's demand delta^2/(2(1-delta)) exceeds the universal max 2*delta*(1-delta) above it — pure algebra on L-EP + Parseval); (b) THE UNION FIRING LAW (the flow's termination): at relative density > 0.81 on ANY container, either the certified table fires (L in [3,48]: ceil(0.81L) > r_3(L), max ratio 0.8 at L=5) or the interval-capacity mesh fires (L >= 49: cap <= 0.618 + 2/49 = 0.659). Engine: FIRING-TABLE-UNION + MESH-INT + I-CK-HI-LTERM green; PB-CK/PB-CK-MESH exhaustive p in {5..17}."


## SECTION 2 — the W76-142K lane claims (the sublinear close)
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
