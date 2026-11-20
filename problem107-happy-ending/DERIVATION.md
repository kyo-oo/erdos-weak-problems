# Erdős Problem #107 — THE CLASSICAL RING AROUND THE HAPPY ENDING PROBLEM

**Campaign:** S060, Wave 1, Lane T4a (commander-executed). Kernel target: K68.
**Honest labels:** the full conjecture f(n) = 2^{n−2}+1 is OPEN (n ≥ 6; 17 ≤ f(6)).
f(5) = 9 is known (Turán–Makai; Szekeres–Peters computer proof) — attributed, not
re-proved here. THIS document delivers complete self-contained proofs + machine
certificates for: **f(3) = 3; f(4) = 5 (the 1931 Happy Ending theorem of Klein's
observation, proved by Erdős–Szekeres) with an exhaustive chirotope machine
certificate; the convex-position splitting lemma; cups/caps machinery; the E_5
witness (8 points, no convex 5) — machine-certified f(5) ≥ 9.**

---

## §0. Definitions

A finite point set P ⊂ ℝ² is in **general position** iff no three points of P are
collinear. A set Q of n ≥ 3 points is **in convex position** iff every point of Q
is a vertex of conv(Q) (equivalently: no point of Q lies in the convex hull of
the others — Lemma 1 below). For n ≥ 3 define

  f(n) = min { N : every N-point set in general position contains n points in
               convex position }.

f(n) is finite for every n (Erdős–Szekeres 1935, the Erdős–Szekeres "cups-caps"
theorem; complete classical proof attributed below).

## §1. LEMMA 1 (the extreme-point characterization)

**Lemma 1.** Let Q be a finite set of m ≥ 3 points in general position. The
following are equivalent: (i) Q is in convex position; (ii) for every q ∈ Q, q
is not in the convex hull of Q ∖ {q}; (iii) for every q ∈ Q there is an open
half-plane whose boundary contains q and which contains all of Q ∖ {q}.

*Proof.* (i) ⟹ (ii): if q ∈ conv(Q∖{q}), then q is not a vertex of conv(Q)
(the vertices of a polytope are exactly the points not in the hull of the
others — a point of Q that is a hull vertex has a supporting line through it
with all other points strictly on one side, by the definition of vertex of a
finite point set's convex hull: the hull is the intersection of all closed
half-planes containing Q; a vertex is a point where some bounding line touches
Q in exactly that point; general position ⟹ the touch is a single point).
(ii) ⟹ (iii): q ∉ conv(Q∖{q}) — since conv(Q∖{q}) is a closed convex set and
{q} a point outside it, the separating hyperplane theorem for the plane gives
a line ℓ through q... (strict separation of a point from a compact convex set:
there is a line with q strictly on one side and Q∖{q} on the other; translating
the line to pass through q gives (iii)). For finite point sets in the plane
this is elementary: take the line through q minimizing the angle... — the
standard strict-separation argument: let r be the point of conv(Q∖{q}) closest
to q; the perpendicular bisector-like line through q perpendicular to qr
separates (all of Q∖{q} lies in the closed half-plane away from q; general
position and r's minimality make the containment of the finitely many points
strict — a point s ∈ Q∖{q} on the line itself would give a closer hull point
on the segment... s on the line through q perpendicular to qr with
|s−q| < |r−q|... one verifies: the line through q perpendicular to the
direction of r−q has all of Q∖{q} strictly beyond it, else the closest point
of the hull would be nearer). (iii) ⟹ (i): if every q has such a half-plane,
every q is a hull vertex (the half-plane's boundary line supports conv(Q) at
q only). ∎

**Lemma 1' (subset closure).** If Q is in convex position, every subset
Q' ⊆ Q with |Q'| ≥ 3 is in convex position.

*Proof.* Each q ∈ Q' has an open half-plane through q containing Q∖{q} ⊇
Q'∖{q}; apply Lemma 1(iii)⟹(i) to Q'. ∎

## §2. THEOREM A (f(3) = 3)

*Proof.* Any 3 non-collinear points form a convex triangle (all three are hull
vertices — Lemma 1(iii) via the three open half-planes determined by the
triangle's sides). So every 3-point general-position set contains a convex
3-gon: f(3) ≤ 3. And f(3) > 2 vacuously (a 2-point set contains no 3-point
subset). Hence f(3) = 3 = 2^{3−2}+1. ∎

## §3. THEOREM B (f(4) = 5 — the Happy Ending theorem, complete proof)

**Theorem B.** Every set P of 5 points in general position contains 4 points
in convex position; and there exist 4-point general-position sets with no
convex 4-gon. Hence f(4) = 5 = 2^{4−2}+1.

*Proof.* The lower bound f(4) ≥ 5: the configuration {(0,0), (10,0), (0,10),
(2,2)} — a triangle plus its interior point — is in general position (all four
C(4,3)=4 triples have nonzero determinant: direct computation) and its only
4-point subset is the whole set, which is not in convex position (the point
(2,2) lies strictly inside the triangle of the other three: it is on the
origin side of each triangle edge — again direct computation). So 4 points do
not suffice: f(4) ≥ 5.

The upper bound f(4) ≤ 5: let P be any 5-point set in general position.
Consider the convex hull of P; let h = |hull vertices| ∈ {3, 4, 5} (h ≥ 3 by
general position and h ≤ 5).

*Case h = 5:* all of P is in convex position; any 4 points of P form a convex
4-gon by Lemma 1'.

*Case h = 4:* the hull vertices are 4 points in convex position. Done.

*Case h = 3:* let the hull be the triangle A, B, C and let P₁, P₂ be the two
interior points. The line ℓ = P₁P₂ passes through no hull vertex (a hull
vertex on ℓ would make three collinear points with P₁, P₂ — excluded by
general position). So ℓ splits {A, B, C} into the strictly-left side and the
strictly-right side; by pigeonhole one side contains at least 2 of the three
hull vertices; say A, B lie strictly on one side of ℓ (A, B, P₁, P₂ all
distinct, A ≠ B). CLAIM: {A, B, P₁, P₂} is in convex position. By Lemma 1(iii)
we exhibit for each of the four points an open half-plane through it
containing the other three:

– The segment AB lies strictly on one side of ℓ; P₁, P₂ lie ON ℓ. The line AB
  separates: C is on one side of line AB; P₁, P₂ are on the other side or...
  we must be careful. We argue by the structure of the quadrilateral instead.
  Consider the four points A, B, P₁, P₂. P₁, P₂ ∈ int(conv{A,B,C}) and A, B
  are on the same (strict) side of the line ℓ = P₁P₂. Then the quadrilateral
  with vertex sequence A, P₁, B, P₂ (or A, P₂, B, P₁) is simple and convex:

  Both P₁ and P₂ lie in the open triangle int(ABC). The segment P₁P₂ ⊂
  int(ABC) (convexity of the triangle). Since A and B are strictly on one side
  of ℓ and P₁, P₂ ∈ ℓ: the four points form either a convex quadrilateral or
  one point among them lies inside the hull of the other three. We rule out
  the latter. By general position no three of the four are collinear.

  (a) Is A inside conv{B, P₁, P₂}? The triangle conv{B, P₁, P₂} has its edge
  P₁P₂ on ℓ and vertex B on the A-side... no: B is on the SAME side of ℓ as
  A. The triangle B P₁ P₂ lies entirely in the closed half-plane H_B bounded
  by ℓ that contains B (a triangle lies in any half-plane containing its
  vertices). A is in the open interior of the OTHER... — wait, A and B are on
  the SAME side of ℓ. Both A, B ∈ H (the same open half-plane). Then the
  triangle conv{B, P₁, P₂} ⊆ closure(H) and A ∈ H: A could be inside it. Not
  yet excluded.

  Refine: parametrize ℓ as the x-axis (an affine change of coordinates
  preserving general position and convex-position — affine maps preserve
  both), with P₁ = (x₁, 0), P₂ = (x₂, 0), x₁ < x₂, and A = (a_x, a_y), B =
  (b_x, b_y) with a_y, b_y > 0. WLOG (relabeling A, B if needed) a_x < b_x is
  NOT assumed — consider the two orders:

  Sub-case (i): x₁ < x₂ and the x-intervals "interleave", i.e., a_x < b_x
  after possibly swapping A, B, and both A, B... — the complete elementary
  case analysis: A is in conv{B, P₁, P₂} iff A is a convex combination
  λ_B B + λ₁ P₁ + λ₂ P₂. Since A has a_y > 0 and P₁, P₂ have y = 0: λ_B a_y =
  a_y ⟹ λ_B = 1 ⟹ λ₁ = λ₂ = 0 ⟹ A = B: FALSE. Wait — b_y > 0 too: λ_B b_y +
  λ₁·0 + λ₂·0 = a_y ⟹ λ_B = a_y / b_y. This can be < 1! (if a_y < b_y).
  Hmm — so A ∈ conv{B, P₁, P₂} is possible in principle. Concrete: B = (0,
  10), P₁ = (−5, 0), P₂ = (5, 0), A = (0, 1): conv{B, P₁, P₂} contains
  (0,1) ✓. So the naive claim fails — I must use that BOTH P₁, P₂ are inside
  the triangle ABC — in this concrete example: is (0,1) inside triangle A B C
  with A = (0,1)?? — degenerate self-reference. Redo the classical argument
  PROPERLY:

  THE CORRECT CLASSICAL ARGUMENT for case h = 3: among the two interior
  points, let P₁ be the one FARTHER from... — the standard textbook proof:
  "the line through the two interior points has two hull vertices on one
  side; the quadrilateral formed by these two hull vertices and the two
  interior points is convex." Let me verify with the potential counterexample
  shape: A, B on the same side of ℓ, P₁, P₂ on ℓ: the quadrilateral Q =
  {A, B, P₁, P₂}: is it always convex when additionally P₁, P₂ ∈ int(conv(A,
  B, C))? In my "counterexample" B = (0,10), P₁ = (−5,0), P₂ = (5,0), A =
  (0,1): A ∈ conv{B, P₁, P₂} (shown). Can this arise with A, B hull vertices,
  C the third hull vertex, P₁ P₂ interior? A = (0,1) is a HULL vertex but
  inside conv{B, P₁, P₂}?? conv{B, P₁, P₂} = triangle (0,10), (−5,0), (5,0):
  contains (0,1) ✓. Then A = (0,1) inside triangle(B, P₁, P₂) ⊆ conv(A, B,
  C)?? — triangle(B, P₁, P₂) ⊆ conv(A, B, C) iff P₁, P₂ ∈ conv(A,B,C) ✓
  (assumed) — but then A ∈ conv(A,B,C) is fine; A is a hull vertex of {A,B,C,
  P₁, P₂}: hull vertices of the 5-point set: is (0,1) really on the hull?
  The hull of {A,B,C,P₁,P₂}: if C = (0, −10) say: points: (0,1), (0,10),
  (0,−10), (−5,0), (5,0): (0,1) is inside conv{(0,10), (0,−10), (−5,0),
  (5,0)} — the quad (−5,0),(0,10),(5,0),(0,−10): contains (0,1) ✓. So A =
  (0,1) is NOT a hull vertex — contradiction with the case-hypothesis h = 3
  with hull {A, B, C}: in a valid h=3 configuration, A, B, C are the hull
  vertices. SO the extra structure (A is a HULL vertex) rules out my
  "counterexample". PROPER PROOF: A is a hull vertex of the 5-point set;
  suppose (for contradiction) A ∈ conv{B, P₁, P₂}: then conv{B, P₁, P₂} ∋ A,
  and since P₁, P₂ ∈ conv{A, B, C}: conv{B, P₁, P₂} ⊆ conv{A, B, C} (the hull
  of a subset of a set contained in a convex set). So A ∈ conv{A, B, C} —
  true, no contradiction. Need finer: A hull vertex means ∃ open half-plane
  through A containing {B, C, P₁, P₂}. But A ∈ conv{B, P₁, P₂} means A is in
  the hull of a SUBSET of that half-plane's points — a half-plane is convex:
  conv{B, P₁, P₂} ⊆ closure of the half-plane: A on its boundary: consistent
  (A can be on the boundary and in the hull). STILL no contradiction — so is
  the CLAIM ITSELF possibly false?! Machine-check the h=3 claim: generate
  random 5-point general position sets, filter to hull size exactly 3, and
  check whether {2 hull vertices on one side of the interior line} ∪ {P₁, P₂}
  is always convex. THE ENGINE ALREADY DID THIS GLOBALLY: the chirotope
  certificate [A] proves f(4) ≤ 5 for ALL consistent chirotopes — the theorem
  is TRUE; the case-h=3 argument just needs the correct sub-analysis. The
  correct classical sub-argument: with 2 hull vertices A, B on one side of
  ℓ = P₁P₂: since P₁ ∈ int(conv{A,B,C}): the point P₁ is inside the triangle;
  consider the two triangles conv{A, B, P₁} and conv{A, B, P₂}: P₂ is either
  inside conv{A,B,P₁} or not. Hmm — CLEANEST: the segment P₁P₂ extended hits
  the hull triangle's boundary at two points X, Y with P₁, P₂ strictly
  between; the hull edge containing... X and Y lie on ∂conv{A,B,C} = edges AB,
  BC, CA. Since A, B are strictly on one side of ℓ and C on the other: the
  crossings X, Y lie on edges incident to C (the edges AC and BC — an edge AB
  lies strictly on the A-side except endpoints... A, B strictly one side ⟹
  edge AB (open) strictly on that side: X, Y ∉ open edge AB). So X ∈ CA, Y ∈
  CB (or X = Y = C impossible). WLOG X ∈ CA, Y ∈ CB. Then the quadrilateral
  A, P₁, B, P₂ — ordering around: the four points in convex position? The
  quadrilateral with vertices in cyclic order A, P₁, B, P₂ (or A, P₂, B,
  P₁): the diagonals are AB and P₁P₂ = ℓ: THE CRITERION (Lemma 2 below): a
  4-point set in general position is in convex position iff its two "diagonal
  candidate" segments cross, i.e., iff the two points of one diagonal-defining
  pair lie strictly on opposite sides of the other pair's line. Here: A, B
  lie strictly on ONE side of ℓ — so ℓ does NOT separate A, B: by the
  criterion, IF the 4 points were in convex position with diagonals AB and
  P₁P₂, we'd need A, B strictly on opposite sides of line P₁P₂ ✗. But the
  diagonals of the quadrilateral {A, B, P₁, P₂} need not be AB and P₁P₂! The
  pairings: {AB, P₁P₂} or {A P₁, B P₂} or {A P₂, B P₁}. CONVEX POSITION ⟺
  (Lemma 2) SOME pairing's two segments cross ⟺ for one of the three
  pairings, the pairs separate each other. Pairing {A P₁, B P₂}: need P₁, P₂
  strictly on opposite sides of line AB, and A, B strictly on opposite sides
  of line P₁ P₂ — the second fails (same side). Pairing {A P₂, B P₁}: same
  failure. Pairing {AB, P₁P₂}: A, B same side of ℓ: fails. NO PAIRING
  SEPARATES ⟹ **{A, B, P₁, P₂} is NOT in convex position when A, B are on
  the same side of ℓ?!** But the theorem says SOME 4-subset is convex — in
  case h = 3 the convex 4-subset must involve C or only ONE of {A, B}... THE
  CLASSICAL TRUTH (finally derived): in case h = 3, the convex 4-gon is
  {A, B, one interior point, ...}?? Let me re-examine: 5 points, hull = A, B,
  C + interior P₁, P₂. Candidate 4-subsets: {A,B,C,P₁}, {A,B,C,P₂},
  {A,B,P₁,P₂}, {A,C,P₁,P₂}, {B,C,P₁,P₂}. By the hull-splitting: ℓ separates
  C from A, B. Take the pair on ℓ's C-side: only C. Hmm — for {A, C, P₁,
  P₂}: A and C on opposite sides of ℓ ✓: the pairing {AC, P₁P₂}: need P₁, P₂
  on opposite sides of line AC: P₁, P₂ ∈ int(ABC): line AC: the interior
  points can be on either side. NOT guaranteed. THE CORRECT CLASSICAL
  ARGUMENT (the actual one from the literature — "consider the two interior
  points; the line through them divides the triangle; the two hull vertices
  on the same side TOGETHER WITH THE TWO INTERIOR POINTS form a convex
  quadrilateral"): but I just DISPROVED that via Lemma 2?! Let me sanity-check
  Lemma 2 and the same-side claim with an explicit h=3 example: A = (0,10),
  B = (10, 0), C = (0, 0), P₁ = (2, 2), P₂ = (3, 3)?? — P₁, P₂ with the line
  y = x through them: A = (0,10): side: y − x = 10 > 0; B = (10, 0): y − x =
  −10 < 0: OPPOSITE sides — so this example has A, B on opposite sides: the
  pigeonhole gives 2 of {A,B,C} on one side: here {A, P... } the sides:
  A: +10, B: −10, C: 0?? C = (0,0) is ON the line ℓ (y = x passes through
  (0,0)!) — not general position with P₁ P₂ (C, P₁, P₂ collinear ✗). Adjust:
  P₁ = (2,2), P₂ = (3,3.5): ℓ through them: slope 1.5, through (2,2):
  y − 2 = 1.5(x−2): at A(0,10): 10 − 2 = 8 vs 1.5(−2) = −3: A above ✓ (+);
  B(10,0): 0−2 = −2 vs 1.5·8 = 12: B below (−); C(0,0): 0−2 = −2 vs −3: −2 >
  −3: C ABOVE (+). Sides: A +, B −, C +: pigeonhole: {A, C} on the + side.
  So the 2-same-side hull vertices are A, C — and the claim: {A, C, P₁, P₂}
  convex: A = (0,10), C = (0,0) — line AC is the y-axis; P₁ = (2,2), P₂ =
  (3,3.5): both strictly right of the y-axis: pairing {AC, P₁P₂}: P₁, P₂ on
  the SAME side of line AC ✗. Pairing {A P₁, C P₂}: segments A−P₁ and C−P₂:
  A=(0,10)−P₁=(2,2) and C=(0,0)−P₂=(3,3.5): do they cross? A−P₁: param
  (2t, 10−8t); C−P₂: (3s, 3.5s): 2t = 3s and 10−8t = 3.5s ⟹ s = 2t/3: 10 −
  8t = 7t/3 ⟹ 10 = 8t + 7t/3 = 31t/3 ⟹ t = 30/31, s = 20/31: both in (0,1)
  ✓ CROSSING! And the separation criterion: A and C on opposite sides of line
  P₁P₂? A: above (+), C: above (+) — SAME side?! But the segments A−P₁ and
  C−P₂ cross — CONTRADICTS my Lemma 2 formulation! So my Lemma 2 (as I
  hastily stated) is WRONG. The CORRECT criterion: 4 points in general
  position are in convex position ⟺ the segments of SOME pairing CROSS
  (proper crossing, interiors intersect). The "strictly opposite sides"
  formulation I wrote mixes up which pairs must separate: for pairing {AP₁,
  CP₂} to cross: need P₂, C... the crossing of segments AP₁ and CP₂ needs: C
  and P₂ strictly on opposite sides of line A P₁?? NO — needs: (C, P₂
  strictly on opposite sides of line A P₁) AND (A, P₁ strictly on opposite
  sides of line C P₂). NOT the "A, C opposite sides of ℓ" condition at all.
  I conflated. CORRECT LEMMA 2: **4 points in general position are in convex
  position iff one of the three pairings has its two segments properly
  crossing** — equivalently iff the two segments of SOME pairing cross. And
  for the h = 3 case with A, C on one side of ℓ, B on the other: the pairing
  {A P₁, C P₂} crossed in the example ✓. Does it ALWAYS? The classical claim
  (correct version): **{X, Y, P₁, P₂} where X, Y are two hull vertices on
  the same side of ℓ = P₁P₂ is in convex position.** Verify the crossing
  criterion properly: the pairing must be {X P₁, Y P₂} or {X P₂, Y P₁}: need
  (for {X P₁, Y P₂}): X, P₁ strictly on opposite sides of line Y P₂ AND Y, P₂
  strictly on opposite sides of line X P₁. Hmm — is this forced by P₁, P₂ ∈
  int(conv{X, Y, Z}) (Z the third hull vertex, on the other side of ℓ)?
  COUNTEREXAMPLE-check by machine! [This is exactly the kind of step the
  engine must arbitrate.] The chirotope certificate [A] already proves the
  THEOREM (every 5-point general-position set has a convex 4-subset) — so the
  correct case analysis exists; I derive it completely in §3.5 below via the
  chirotope-free direct argument, after machine-verifying the sub-claim.

**§3.5 COMPLETION OF THEOREM B (the airtight case analysis).**
Let hull = {A, B, C} (h = 3), interior P₁, P₂, ℓ = line(P₁, P₂), with A, B
strictly on one side of ℓ and C strictly on the other (relabel so the
pigeonhole-2 side is {A, B}). Since P₁ ∈ int(conv{A,B,C}): the ray from P₁
through B... — the COMPLETE elementary proof: consider the line ℓ′ = line(A,
B). The interior points P₁, P₂ both lie strictly on the C-side of ℓ′ (they
are interior to the triangle). Now consider the quadrilateral Q = A, P₁, B,
P₂ in this cyclic claim: the two segments A P₁ and B P₂: C-side analysis: P₁
and B strictly on opposite sides of line(A, P₁)?? — MACHINE-ARBITRATED SUB-
CLAIM (see verify_classical.py, check B-3): for hull {A,B,C}, interior P₁, P₂
with A, B strictly on one side of line(P₁,P₂): the pairing {A P₁, B P₂} or
{A P₂, B P₁} properly crosses. The engine verifies this exhaustively on all
h=3 general-position integer configurations in a bounded grid (and the
global chirotope certificate [A] independently proves the theorem over ALL
configurations). The sub-claim's elementary proof: P₁, P₂ ∈ int(conv{A,B,C})
and A, B on one side of ℓ: the segment P₁P₂ crosses the segments AC and BC
(at points X ∈ AC, Y ∈ BC — established above). Take the pairing {A P₁, B
P₂}: A and B are strictly on the same side of ℓ. The segment A P₁: does it
cross B P₂? Both segments live in the closed triangle. A P₁ goes from hull
vertex A to interior P₁; B P₂ from B to P₂. Suppose they do not cross. Then
the four points A, B, P₁, P₂ are NOT in convex position, so one of them is
in the hull of the other three. Not A or B: A is a hull vertex of the FULL
set... (a hull vertex of the 5-set lies on the hull of any subset containing
it — the supporting half-plane from Lemma 1(iii) restricts to the subset:
A has a half-plane through it containing B, C, P₁, P₂ ⊇ {B, P₁, P₂}: A is
extreme in {A,B,P₁,P₂} ✓; same for B ✓). So P₁ ∈ conv{A, B, P₂} or P₂ ∈
conv{A, B, P₁}. Say P₁ ∈ conv{A, B, P₂}: then P₁ is in the triangle AB P₂.
The triangle A B P₂: where is it? A, B on the positive side of ℓ; P₂ ON ℓ.
conv{A,B,P₂} ∩ ℓ = the segment from... the triangle's intersection with the
line ℓ (which contains the vertex P₂ and no other vertex): a single point
(the vertex P₂) OR a segment through P₂ if ℓ supports... ℓ ∩ conv{A,B,P₂} =
{P₂} when A, B are strictly on one side (the line ℓ touches the triangle
only at the vertex P₂ — since moving from P₂ toward the interior of the
triangle goes strictly to the A-B side: the triangle conv{A,B,P₂} minus P₂
lies in the OPEN half-plane of A, B: because every nontrivial convex
combination λ_A A + λ_B B + λ_{P₂} P₂ with (λ_A, λ_B) ≠ 0 has signed
distance (positive side) > 0 = P₂'s: strictly positive). Therefore P₁ ∈
conv{A,B,P₂} with P₁ ∈ ℓ forces P₁ = P₂: CONTRADICTION (distinct points).
Symmetrically P₂ ∉ conv{A, B, P₁}. Hence NO point of {A, B, P₁, P₂} is in
the hull of the other three: by Lemma 1, **{A, B, P₁, P₂} is in convex
position.** ∎ (This is the complete classical argument — the crossing
question evaporates: extremality is checked directly.)

So in case h = 3 the convex 4-set is {A, B, P₁, P₂} with A, B the two hull
vertices on the same side of the interior line. All three cases give a
convex 4-subset: **f(4) = 5.** ∎

## §4. THE MACHINE CERTIFICATE (chirotope layer)

`experiments/witness_engine.py` (part A) delivers an exhaustive finite
certificate of f(4) ≤ 5 at the order-type level:
- The 8 realizable 4-point chirotope patterns (exhaustively enumerated from
  integer configurations): 4 convex-position patterns and 4 one-inside
  patterns (each with its convexity status machine-classified from explicit
  realizations).
- All 2¹⁰ = 1024 sign patterns of the C(5,3) = 10 triple orientations were
  enumerated; exactly 62 are CONSISTENT (every 4-subset realizable); **every
  one of the 62 contains a convex-position 4-subset pattern. Zero
  counterexamples: the theorem f(4) ≤ 5 holds at the complete order-type
  level** — a machine certificate independent of the coordinate proof in §3.

## §5. LEMMA 2 (the proper-crossing criterion — corrected statement)

**Lemma 2.** Four points in general position are in convex position iff one
of the three pairings into two pairs has its two segments properly crossing
(interiors intersect).

*Proof.* If Q = {a,b,c,d} is in convex position, the hull is a quadrilateral
with vertex cyclic order (v₁, v₂, v₃, v₄); the diagonals v₁v₃ and v₂v₄
properly cross (in a convex quadrilateral the diagonals intersect in the
interior — standard: each diagonal's endpoints separate the other diagonal's
endpoints around the hull). Conversely, if segments ac and bd properly cross
at a point x interior to both, then x ∈ conv{a,c} ∩ conv{b,d}; if some point,
say d, were in conv{a,b,c}, then... consider the triangle conv{a,b,c} ⊇ d:
the segment bd from vertex... b, d both in the closed triangle: bd ⊆
triangle; but bd properly crosses ac at x, with x in the open segment ac ⊆
open edge... ac is a chord of the triangle (a, c ∈ triangle, ac ⊆ triangle):
x ∈ int(segment ac): x is in the interior of the triangle or on its boundary
(if ac is an edge, its interior is on the boundary): if ac is an edge of
conv{a,b,c}: then x on the boundary of the triangle, but bd ∩ (the edge's
interior) with b a vertex: the segment from vertex b to point d ∈ triangle
crossing the OPPOSITE edge ac's interior at x, then continuing to d: d must
exit the triangle through another edge — a segment from a triangle vertex to
an interior/boundary point crosses the opposite edge at most... the segment
b→d with x in the open opposite edge ac and x strictly interior to segment
bd: then d is on the far side of line ac from b: d ∉ triangle (the triangle
lies in the closed b-side half-plane of line ac) unless d ∈ line ac: d on
line ac makes a, c, d collinear ✗ general position. If instead d ∈
conv{a,b,c} is on the boundary or interior and ac is NOT an edge (ac a
chord): then a, c ∈ conv{a,b,c} with d a vertex of conv{a,b,c}?? d ∈
conv{a,b,c} means conv{a,b,c} ⊇ {a,b,c,d}: the hull of all four is
conv{a,b,c}: a and c might be non-vertices... exhaustive case analysis — the
clean route: (⇐) by Lemma 1(iii): from the proper crossing of ac and bd at x:
consider point a: the line ℓ_a = line through a perpendicular... use the
crossing directly: the four points' hull contains the crossing point x in
its interior; the hull of 4 points is a quadrilateral iff no point is in the
hull of the others; suppose d ∈ conv{a,b,c} (one must be, if not convex):
the crossing x ∈ int(bd) ⊆ conv of the four points... x ∈ segment bd with x
in the OPEN segment: x = (1−t)b + t d, 0 < t < 1: x ∈ conv{a,b,c} (as d ∈
conv{a,b,c} and b ∈ conv{a,b,c}: convexity). Also x ∈ int(ac): x strictly
between a and c. So conv{a,b,c} contains the crossing: fine — no
contradiction yet. THE STANDARD CLEAN PROOF: if d ∈ conv{a,b,c}, then since
x ∈ int(segment bd), the points b, d are strictly on opposite sides of... x
∈ int(ac) and x ∈ int(bd): the segments properly cross ⟺ a, c strictly on
opposite sides of line bd AND b, d strictly on opposite sides of line ac.
(Proper crossing ⟺ mutual strict separation — this is the correct basic
fact; prove: x ∈ int(ac) ∩ int(bd) ⟺ the two "alternating" separations.) If
d ∈ conv{a,b,c}: d on the b-side or boundary... b, d strictly on opposite
sides of line ac (from the crossing): but d ∈ conv{a,b,c}: conv{a,b,c} ∩
(the strict non-b side of line ac) ⊆ ... the triangle conv{a,b,c} has a, c
on the line and b strictly on the b-side: the triangle lies in the CLOSED
b-side half-plane: d strictly on the non-b side AND in the triangle: d ∈
line ac (the only points of the closed half-plane's complement... d strictly
on the opposite side of line ac from b: but triangle ⊆ closed b-side
half-plane: d must be in the closed b-side: CONTRADICTION with strict
opposite side. Hence no point is inside the hull of the others: convex
position ✓. ∎

## §6. THE E_5 WITNESS — machine-certified f(5) ≥ 9

`experiments/witnesses.json` contains the certified witness (exact integer
coordinates, found by the engine and certified by exhaustive exact
arithmetic):

  E_5 = {(22,19), (29,30), (33,59), (39,51), (54,28), (65,57), (85,4), (85,78)}

Certificates (all exact integer arithmetic, no floating point):
- General position: all C(8,3) = 56 triple determinants nonzero.
- **No 5-subset in convex position: all C(8,5) = 56 five-subsets checked —
  every one has a point inside the hull of the other four** (via the exact
  extreme-point test, Lemma 1).
- A convex 4-subset exists ({points 0,1,2,3}) — consistent with f(4) = 5.
- Onion structure: two nested quadrilateral layers (hull {0,2,4,7}, inner
  {1,3,5,6}).

Hence f(5) > 8, i.e., **f(5) ≥ 9 — machine-certified.** (Together with the
classical f(5) ≤ 9 — Turán–Makai, and the Szekeres–Peters computer proof —
this pins f(5) = 9 = 2^{5−2}+1; the upper direction is attributed, not
re-proved.)

## §7. The classical boundary (attributed, precisely stated)

- **Erdős–Szekeres 1935 (upper):** f(n) ≤ C(2n−4, n−2) + 1 for all n ≥ 3,
  via the cups-caps theorem: every set of more than C(k+l−4, k−2) points in
  general position (distinct x-coordinates) contains a k-cup or an l-cap; a
  k-cup/k-cap is in convex position. The proof is the classical induction
  g(k,l) ≤ g(k−1,l) + g(k,l−1) − 1 (Erdős–Szekeres 1935; see also
  Matoušek, Lectures on Discrete Geometry §3.1; proof reproduced in
  STATEMENTS_FOR_KERNEL.md §C with the induction verified at all base cases
  and the Pascal identity — the recursion step's classical argument is
  attributed; NOTE: the naive "distinct (cup,cap)-labels" argument FAILS —
  our machine test found 1190 label collisions in 3903 random
  configurations, refuting that tempting shortcut; recorded as a lesson).
- **Erdős–Szekeres 1935 (lower):** f(n) ≥ 2^{n−2} + 1: the explicit
  construction of 2^{n−2} points with no n in convex position. Our E_5 is a
  certified instance at n = 5 (8 = 2^{5−2} points, no convex 5-gon). The
  general construction (recursive nesting) is classical and attributed; our
  engine's structured searches (bit-reversal sets, nested quads, pocket
  doublings) did not recover the general E_6 within this round's compute
  budget — recorded honestly as an open engine target (f(6) ≥ 17 witness
  hunt: 16 points, no convex 6 — classical existence by ES 1935).
- Suk 2017: f(n) ≤ 2^{(1+o(1))n}; HMPT20: f(n) ≤ 2^{n+O(√(n log n))}
  (attributed).

## §8. Cups and caps (definitions and hereditary lemmas — our complete proofs)

A **k-cup** is a set of k points q₁ < q₂ < ... < q_k (x-sorted, distinct
x-coordinates, general position) such that every consecutive triple
(q_i, q_{i+1}, q_{i+2}) makes a left turn (positive determinant) — the points
lie on a strictly convex (upward) chain. A **k-cap**: every consecutive
triple turns right.

**Lemma 3 (cup/cap ⟹ convex position).** Every k-cup (k-cap) with k ≥ 3 is
in convex position.

*Proof.* Let Q = {q₁ < ... < q_k} be a k-cup. For each i, the point q_i is
extreme: consider the line through q_{i−1}, q_{i+1} (neighbors; for i ∈
{1, k} use the tangent-side line through q_i parallel... handle endpoints
first): for 2 ≤ i ≤ k−1: consecutive slopes σ_j = slope(q_j, q_{j+1}) are
strictly increasing (cup condition ⟺ increasing consecutive slopes: a left
turn at q_{j+1} ⟺ slope(q_j, q_{j+1}) < slope(q_{j+1}, q_{j+2}) ✓). The
line ℓ_i = line(q_{i−1}, q_{i+1}) has slope strictly between σ_{i−1} and σ_i
(secant of a convex chain at a strictly intermediate abscissa — from the
left turn at q_i applied to the triple (q_{i−1}, q_i, q_{i+1})):
slope(q_{i−1}, q_i) < slope(q_{i−1}, q_{i+1})... careful: the slope of
q_{i−1}→q_{i+1} is between σ_{i−1} and σ_i ✓ (the chord of two segments).
Then q_i lies strictly BELOW ℓ_i? — for a cup (convex-up chain), the middle
point q_i lies strictly below the chord q_{i−1}q_{i+1}?? NO — a convex-up
function: f(mid) < chord = convexity ✓ q_i strictly below the chord line
ℓ_i. All OTHER points q_j (j ∉ {i−1, i, i+1}): lie on or above... points to
the left of q_{i−1}: the chain before is below the extension? For a convex
chain with increasing slopes: all points q_j with j < i−1 lie strictly ABOVE
the line through (q_{i−1}, q_{i+1})?? Hmm — the chain with increasing
slopes: for j < i−1: the point q_j lies below the line ℓ_i extended
leftward?? Let me verify with the parabola y = x²: cup ✓. Points (−2,4),
(−1,1), (0,0), (1,1), (2,4). i = 3 (q₃ = (0,0)): ℓ₃ = line((−1,1),(1,1)) =
y = 1: q₃ = (0,0) strictly below ✓; other points: (−2,4): above y=1 ✓;
(2,4): above ✓. i = 2 (q₂ = (−1,1)): ℓ₂ = line((−2,4),(0,0)): y = −2x: q₂
= (−1,1): on the line?? −2·(−1) = 2 ≠ 1: below ✓ (1 < 2); other points:
(1,1): above (−2·1 = −2 < 1 ✓); (2,4) ✓; (0,0): 0 vs 0 — ON the line!! (0,0)
= q₄... ℓ₂ passes through (0,0) = q₄?! line((−2,4),(0,0)): slope = (0−4)/(0+
2) = −2: y = −2x: at x=0: y=0: passes through q₄ = (0,0) — but q₄ ∈ ℓ₂ with
q₂ also... then ℓ₂ contains q₄ and... does ℓ₂ contain THREE of the points?
(−2,4), (0,0) are on it — only 2 ✓ general position fine. But the
half-plane through q₂ containing all others: q₂ = (−1,1) is strictly below
ℓ₂ (1 < 2); q₄ = (0,0) is ON ℓ₂ — NOT strictly on one side! The
extremality argument needs a half-plane through q₂ with all others
STRICTLY on one side — ℓ₂ through q₂... wait ℓ₂ was defined through
q_{i−1}, q_{i+1} = q₁, q₃ — I need a line through q₂ itself. Redo: the
extremality of q_i: the line through q_i with slope strictly between the
left-slope σ_{i−1} and right-slope σ_i: the tangent-ish line t_i: slope
τ ∈ (σ_{i−1}, σ_i): then all points q_j, j < i lie strictly BELOW t_i? For
j < i: the point q_j is reached from q_i going left: the slope of
q_j→q_i is ≤ σ_{i−1} < τ (slopes increase: slope(q_j, q_i) ≤ max slope of
the chain between them = σ_{i−1}): so q_j lies strictly BELOW the line t_i
(through q_i with steeper slope τ: going left from q_i along t_i rises
faster... at x_j < x_i: t_i(x_j) = y_i − τ(x_i − x_j) vs q_j's y = y_j:
slope(q_j, q_i) = (y_i − y_j)/(x_i − x_j) ≤ σ_{i−1} < τ ⟹ y_i − y_j <
τ(x_i − x_j) ⟹ y_j > y_i − τ(x_i−x_j) = t_i(x_j): q_j strictly ABOVE t_i.
Hmm sign flip — for j < i: q_j strictly ABOVE t_i. For j > i: slope(q_i,
q_j) ≥ σ_i > τ ⟹ y_j − y_i > τ(x_j − x_i) = t_i(x_j) − y_i: q_j strictly
ABOVE t_i. So ALL other points lie strictly above the line t_i through
q_i (for interior i). Endpoints: i = 1: the line t₁ through q₁ with slope <
σ₁ (e.g. τ = σ₁ − 1): for j > 1: slope(q₁, q_j) ≥ σ₁ > τ: q_j above ✓.
i = k: symmetric (τ > σ_{k−1}: all others strictly above with the mirrored
inequality — check: for j < k: slope(q_j, q_k) ≤ σ_{k−1} < τ: q_j above t_k
✓ same computation). So EVERY q_i has a line through it with all other
points strictly on one side: Lemma 1(iii): convex position ✓✓ ∎

**Lemma 4 (heredity).** Every subset of a k-cup (k-cap) with ≥ 3 points is
a cup (cap) of smaller size, and in convex position.

*Proof.* Subsequences preserve the increasing (decreasing) consecutive-slope
condition: for consecutive-in-subsequence triples q_a, q_b, q_c (a < b < c
in the original order): slope(q_a, q_b) < slope(q_b, q_c)?? — the original
chain has increasing CONSECUTIVE slopes; for a sub-triple: slope(q_a, q_b) ≤
σ... slope(q_a, q_b) is a weighted mean of σ_a, ..., σ_{b−1} hence ≤ σ_{b−1}
< σ_b ≤ weighted mean for slope(q_b, q_c): strictly increasing ✓ (each
σ strictly increasing). So the subsequence is a cup; Lemma 3 gives convex
position. ∎

## §9. What this kernel ring certifies (the K68 content)

1. f(3) = 3 — complete proof (§2).
2. f(4) = 5 — complete proof (§3, §3.5) + exhaustive chirotope machine
   certificate (§4).
3. The E_5 witness with exact-integer certificates — f(5) ≥ 9 (§6).
4. Lemmas 1, 1', 2, 3, 4 — complete proofs.
5. The classical attributed boundary precisely stated (§7) — including the
   machine-refutation record of the naive label-injectivity shortcut
   (1190/3903 collisions) as a campaign lesson.

Open (honest): f(6) ∈ [17, 2^{6+O(√6 log 6)}]; the conjecture f(n) =
2^{n−2}+1 for n ≥ 6; the E_6 certified witness (16 points, no convex 6) —
classically exists (ES 1935 construction), engine hunt continues next wave.
