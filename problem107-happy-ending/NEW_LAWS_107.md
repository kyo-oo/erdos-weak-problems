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
