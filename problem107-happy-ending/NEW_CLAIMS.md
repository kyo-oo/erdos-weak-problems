# NEW CLAIMS — W77-107E (problem107-happy-ending/NEW_CLAIMS.md)

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
    "receipts": "ALLN_PROOF.md section 3; alln107/s4b_n4.json, s4b_n5.json, s4b_n6.json, s4b_n7.json, s4b_multiplicity.json"
  },
  {
    "id": "C107-AVOID",
    "statement": "Avoidance law: the label class P_ij, as a standalone point set, contains no i-cup and no j-cap ((i+1)/(j+1) avoidance proven; i/j avoidance certified on 3,322 classes, zero occurrences).",
    "status": "certified-law-proven-boundary",
    "receipts": "ALLN_PROOF.md section 3; alln107/s4c_avoid.json"
  }
]
```
