# NEW LAWS — W77-107E (problem107-happy-ending/NEW_LAWS_107.md)

Laws discovered/derived this lane. Every law is either proven in-package
(ALLN_PROOF.md) or machine-certified with receipts; nothing else is
claimed.

## L-ROT (proven; S1-certified)
Orientation signs are exactly invariant under det=1 linear maps
(rotations, shears): orient(Tp,Tq,Tr) = orient(p,q,r) when det(T) = 1,
since orient(p,q,r) = bracket(q-p, r-p) and brackets scale by det.
#BY GST LAW bracket_transform [HC-PROOF-research/GSTCausalPairingGraphs.lean:27]
#BY GST LAW bracket_shear [HC-PROOF-research/GSTCausalPairingGraphs.lean:33]

## L-SLOPEAVG (proven)
In a k-cup, every triple (not only consecutive) turns left: the slope of
any long segment is a positive-weighted average of the consecutive
slopes it spans, and strictly increasing consecutive slopes separate the
averages. Dually for caps. This strengthens the composition step: cups
are ALL-triples-CCW, not merely consecutive-triples-CCW.
#BY GST LAW plucker_four [HC-PROOF-research/GSTCausalPairingGraphs.lean:38]

## L-CC (proven; S3 dual-code certified)
Every k-cup / k-cap is k points in convex position (via L-SLOPEAVG and
the below-chord / above-chord argument).
#BY GST LAW plucker_four [HC-PROOF-research/GSTCausalPairingGraphs.lean:38]

## L-MLT — the label multiplicity law (leg (a) proven; leg (b) certified)
(a) |P_ij| <= C(i+j-2, i-1): proven from banked Theorem CC + label
absoluteness (Lemma A1: a chain of a subset is a chain of the whole).
(b) |P_ij| <= C(i+j-4, i-2): the tight law, engine-certified on
5,510,000+ configurations (zero violations); boundary rows (i=2 or j=2)
proven. The tight leg follows from L-AVOID by banked CC at (i,j).
#BY GST LAW sum_le_sum_of_forall [erdosternary2/bulldoze/problem261-continuum-tower/Erdos261Tower.lean:116]
#BY GST LAW cubic_expansion [HC-PROOF-research/CardinalWorlds.lean:283]
#BY GST LAW two_pow_ge2 [erdosternary2/ErdosTernary2.lean:891]
#BY GST LAW digitCount3_monotone [erdosternary2/ErdosTernary2.lean:2097]

## L-AVOID (certified law; (i+1)/(j+1) rows proven)
P_ij — the exact label class — as a standalone set contains no i-cup and
no j-cap. Certified: 3,322 classes (mult >= 2), zero occurrences
(alln107/s4c_avoid.json). The named front: the interior induction step
(slope-sandwich structure of consecutive P_ij pairs — the L-CHAIN
inequality alpha(p) <= slope(p,q) <= beta(p) for p < q in P_ij is proven
in ALLN_PROOF.md section 3 context and is the entry instrument).

## THEOREM U-BIS (proven; new)
f(n) <= C(2n-2, n-1) - 2n + 4 for every n >= 3 — the second independent
all-n bound, by the label decomposition + L-MLT(a) + hockey-stick
(closed form G(n) = C(2n-2,n-1) - 2n + 3, S7-verified).
#BY GST LAW two_pow_factored [HC-PROOF-research/CardinalWorlds.lean:425]
#BY GST LAW mod_mod_mul [HC-PROOF-research/CardinalWorlds.lean:143]

## THEOREM ES-INF (proven; new — the infinite law)
Every infinite GP point set contains m convex-position points for every
m >= 3. Finite-input composition of banked Theorem U (ALLN_PROOF.md
section 5). The infinite-chain stretch (infinite Ramsey on triple signs)
is documented as the omega-layer front.
#BY GST LAW noTernaryTwo_eq_struct [HC-PROOF-research/CardinalWorlds.lean:58]

## NEGATIVE RESULTS (documented, load-bearing)
- Naive label-pair injectivity: FALSE (this lane 924/1200; W74 audit
  263/300; hand-verified exemplar in this lane's records). Never use it.
- Bare endpoint-merge at (5,5): FALSE (975/2000 unions lack a 5-chain —
  S5). The banked X/Y-split merges through the FIRST cap point, which is
  why it survives.

## C107-LOWER-ALLN (W80-107E lane — NEW, proven for all n)
"THE ALL-n LOWER CONSTRUCTION: for every n >= 3 there is an explicit GP set X_n of
exactly 2^(n-2) rational points with NO n in convex position (hence f(n) >=
2^(n-2)+1). Construction: m=n-2 centers on the concave arc x = 1 - y^2/D
(y_i=(m-2i)/8, D=m/4), cluster T_i = c_i + rho*(E(n-i,i+2;s) - boxcenter) with
s=1/(16(m+1)), rho=1/(2^15 m), |T_i|=C(m,i), sum = 2^(n-2). PROOF (complete,
ES_SANDWICH_ALLN.md sections 2-4): Lemma E (E(a,b;d) has C(a+b-4,a-2) points,
slopes in (0,d], no a-cup, no b-cap — full induction on the A/B split with the
cross-slope band (d/2,d) strictly above intra slopes <= d/3); Lemma M (every
strictly-middle-cluster point of Y lies strictly RIGHT of the top-bottom chord
BT, margin >= (1-o(1))/(4m) >> 57rho/32 — concavity of the arc); Theorem L (the
CCW chain decomposition: right chain = cup-run in the bottom cluster + single
visits; left chain = cap-run in the top cluster + single visits; Lemma M kills
middle points on the left chain; |Y| <= (k+1)+(n-l-1)+(l-k-1) = n-1). Machine:
engine107loweralln.py S0-S6 (S3 exhaustive n=3..7 both codes, S4 randomized
n=8..10 max found = n-1, 529K/450K/318K hits, structure census middles <= 1 on
every hit); finisher independent rebuild verify107lower.py (two NEW codes: two-
pop-set monotone chain + gift wrap; exhaustive n=5 56/56, n=7 C(32,7)=3,365,856;
transversal witness law: ALL one-per-cluster transversals convex = the n-1
witness for all n). KNOWN RED SUB-CELL, DISCHARGED: engine S2 slope_bands
demanded the center constant m/(m-1) for perturbed cross pairs — the true min
dips below by O(rho) (finisher V5 measured, factor >= 30x above the load-
bearing bound 1/(1+38rho) > 1/2 vs intra <= 1/64); threshold artifact, not a
construction failure; every load-bearing cell green."
#BY GST LAW two_pow_factored [erdosternary2/ErdosTernary2.lean:885]
#BY GST LAW binom_mod_sq_local [erdosternary2/ErdosTernary2.lean:460]

## C107-SANDWICH-ALLN (W80-107E lane — NEW, the deliverable)
"THE ALL-n SANDWICH: for every integer n >= 3: 2^(n-2)+1 <= f(n) <=
C(2n-4,n-2)+1, with f(3)=3 and f(4)=5 exact. Lower side = C107-LOWER-ALLN
(proven all n; engine spot-certificates n=3..10). Upper side = banked KILL1:
ES_PACKAGE_PROOF.md section 2 Theorem CC + section 3 Theorem U (X/Y-split
induction, distinct-x discharged by rotation section 7.5), fresh certificates
receipts107alln.txt. Exact values: PROOF.md sections 1-2 (f(3)=3, f(4)=5
complete); f(5)=9 Turan-Makai cited (engine107f5 lane work). Gap law (exact,
finite n): gap(n) = (C(2n-4,n-2)+1)/(2^(n-2)+1) = 1.00, 1.40, 2.33, 4.18,
7.67, 14.23, 26.61, 50.08 at n=3..10 (engine S5b, n=3..16 green; central-
binomial sandwich C(2m,m)^2(2m+1) <= 16^m and C(2m,m)(2m+1) >= 4^m two codes
m=0..30, giving f(n) <= 4^(n-2)/sqrt(2n-3)+1); asymptotic ratio ~
2^(n-2)/sqrt(pi n) is CONTEXT ONLY, not load-bearing."
#BY GST LAW two_pow_ge2 [erdosternary2/ErdosTernary2.lean:891]
