# NEW CLAIMS — problem107-happy-ending (W77-107E + W75/W77-107K, union)

Schema-compatible with comparator-official/challenges/107/solution.json.
The commander integrates; this lane does not edit solution.json.

```json
[
  {
    "id": "C107-ALLN-CERT",
    "statement": "For every (a,b) in {(3,3),(3,4),(4,3),(3,5),(5,3),(3,6),(6,3),(4,4)}: every distinct-x general-position set of C(a+b-4,a-2)+1 points contains an a-cup or b-cap. Machine-certified exhaustively (integer grids): 11426+84404+84404+27252+27252+290+290+624 configurations, zero violations; plus random certificates at (4,5),(5,4),(5,5),(6,6) (3000/3000/3000/300 green).",
    "status": "certified-complete",
    "receipts": "receipts107alln.txt S6; alln107/s6_forcing.json"
  },
  {
    "id": "C107-UBIS",
    "statement": "For every n >= 3: every set of C(2n-2,n-1) - 2n + 4 points in general position in the plane contains n points in convex position. Complete in-package proof (label decomposition + L-MLT(a) + hockey-stick + L-CC + L-ROT).",
    "status": "proven-complete",
    "receipts": "ALLN_PROOF.md section 4; receipts107alln.txt S7"
  },
  {
    "id": "C107-ESINF",
    "statement": "Every infinite set of points in the plane in general position contains m points in convex position for every m >= 3.",
    "status": "proven-complete",
    "receipts": "ALLN_PROOF.md section 5 (finite-input composition of banked Theorem U)"
  },
  {
    "id": "C107-MLT",
    "statement": "Label multiplicity law: in a distinct-x GP set, |{p : cup(p)=i, cap(p)=j}| <= C(i+j-2,i-1) [proven], and <= C(i+j-4,i-2) [engine-certified: 5,510,000+ configurations, zero violations; boundary rows proven].",
    "status": "proven-leg-plus-certified-tight-leg",
    "receipts": "ALLN_PROOF.md section 3; alln107/s4b_n4.json, s4b_n5.json, s4b_n6.json, alln107/s4b_multiplicity.json"
  },
  {
    "id": "C107-AVOID",
    "statement": "Avoidance law: the label class P_ij, as a standalone point set, contains no i-cup and no j-cap ((i+1)/(j+1) avoidance proven; i/j avoidance certified on 3,322 classes, zero occurrences).",
    "status": "certified-law-proven-boundary",
    "receipts": "ALLN_PROOF.md section 3; alln107/s4c_avoid.json"
  },
{
    "id": "C107-LOWER-ALLN",
    "statement": "For every n >= 3 there is an explicit GP set X_n of exactly 2^(n-2) rational points with no n in convex position; hence f(n) >= 2^(n-2)+1 for all n >= 3.",
    "status": "proven-all-n (Lemma E induction + Lemma M margin + Theorem L chain count); engine-certified n=3..10 (exhaustive n<=7, randomized 8..10); finisher two-code independent verification n=5,7",
    "receipts": "ES_SANDWICH_ALLN.md sections 1-4; engine107loweralln_receipts.txt; verify107lower_receipts.txt"
  },
  {
    "id": "C107-SANDWICH-ALLN",
    "statement": "For every n >= 3: 2^(n-2)+1 <= f(n) <= C(2n-4,n-2)+1; f(3)=3 and f(4)=5 exact. Lower = C107-LOWER-ALLN (proven all n); upper = banked Theorem CC/U (ES_PACKAGE_PROOF.md).",
    "status": "assembled-theorem (both sides proven all n)",
    "receipts": "ES_SANDWICH_ALLN.md (the proof record); ES_PACKAGE_PROOF.md sections 2-3; receipts107alln.txt; PROOF.md sections 1-2"
  }
]
```

## C107-OT8 (W75/W77-107K lane)
"THE n=8 ORDER-TYPE ENUMERATION: the realization-diversified cell-insertion enumeration: 242 n=7 parents (certified 135 mirror-identified, anchor match) x 616 type-preserving realizations x all arrangement cells (slab method, per-parent cell counts EXACTLY matching the line-arrangement formula on all 242 parents) = 99,742 insertions -> 6402 reflection-distinguished types, 225 self-mirror, 3315/3315 mirror-identified closed in W77-107K (ot8_v2.pkl with exact realizations). ROOT-CAUSE DISCOVERY (mathematical, in-package): the cell set of the pair-line arrangement is NOT an order-type invariant — within one order type's realization space, cells appear/disappear across 3-line-concurrency walls, so single-realization insertion provably misses children (1 mirror-closure failure exhibited and diagnosed; the realization-diversification recovers 13 identified types). The n=9 full certificate (158,817 anchor) is the compute-planned next lane (15x10-minute chunked runs, the anchor count is the certificate)."

## C107-SIXPOINT-REFUTATION (W75-107K lane)
"THE ADVERSARIAL CATCH: the naive 'triangle + 3 interior => convex 5' lemma is FALSE — exact-rational counterexample: concentric triangles A(0,10) B(-9,-8) C(9,-8) with u(0,10/3) v(-3,-8/3) w(3,-8/3): all 6 five-subsets have hull size 3 or 4. The f(5) <= 9 case tree must route through the outer quadrilateral/triangle vertices (the true Makai structure) — the engine caught the false lemma before it shipped (the campaign's no-wrong-construction doctrine)."

## W81 (W81-107A lane)

- C107-E5-EXACT — THEOREM f(5) = 9 exactly. The F8 reduction (146 convex-5-free 8-types, exhaustive two-code over the complete bank) + heredity + the saturated F8 storm (zero convex-5-free children) + the census battery (250,922 hull<=4 types, zero convex-5-free) + the validation ladder (SET EQUALITY n=4..8). See F5_CERTIFICATE.md.
