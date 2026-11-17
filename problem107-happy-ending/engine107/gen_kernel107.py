#!/usr/bin/env python3
# W69-E: Erdos107 witness kernel generator v3 — final architecture:
# closed-term decide + pattern-match selections + #eval receipts.
import math, sys, os, itertools

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), 'doubter'))
from mirror_battery import build_ersz61, no_three_collinear
from fractions import Fraction as F

PARAMS = dict(w=F(41, 100), eps=F(1, 1048576), alpha=F(1, 4), beta=F(1, 2),
              gamma=F(3, 4), c=F(4))

def turn(p, q, r):
    return (q[0] - p[0]) * (r[1] - p[1]) - (q[1] - p[1]) * (r[0] - p[0])

def convex4(a, b, c, d):
    s = [turn(a, b, c), turn(a, b, d), turn(a, c, d), turn(b, c, d)]
    if 0 in s:
        return False
    return s[0] * s[1] * s[2] * s[3] > 0

def gen_witness(n):
    ipts, owner, meta = build_ersz61(n, PARAMS["w"], PARAMS["eps"], PARAMS["alpha"],
                                     PARAMS["beta"], PARAMS["gamma"], PARAMS["c"])
    assert len(ipts) == 2 ** (n - 2)
    assert len(set(ipts)) == len(ipts)
    assert no_three_collinear(ipts)
    for combo in itertools.combinations(ipts, n):
        if all(convex4(*q) for q in itertools.combinations(combo, 4)):
            raise SystemExit(f"n={n}: convex {n}-subset found — construction broken")
    return ipts

W3 = gen_witness(3)
W4 = gen_witness(4)
W5 = gen_witness(5)
print("witnesses: |w3|=%d |w4|=%d |w5|=%d" % (len(W3), len(W4), len(W5)))
print("max |coord| in w5:", max(max(abs(p[0]), abs(p[1])) for p in W5))

def lp(pts):
    return "[" + ", ".join("(%d, %d)" % (p[0], p[1]) for p in pts) + "]"

L = []
A = L.append
A("""import Arsenal.ErdosTernary2.Basic
import Arsenal.CardinalWorlds
import Arsenal.CardinalWorldsV2

set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-!
# Erdos107 — THE HAPPY ENDING WITNESS KERNEL (W69-E)

Erdos #107 (verbatim, erdosproblems.com/107, prize $500):
"Let f(n) be minimal such that any f(n) points in R^2, no three on a line,
contain n points which form the vertices of a convex n-gon. Prove that
f(n) = 2^{n-2}+1."

## THE CERTIFIED SCOPE (complete and unconditional, on BOSS's Arsenal)
1. **E107.f3_upper**: every 3 points in general position form a convex
   3-gon — f(3) <= 3.
2. **E107.f3_lower**: the explicit 2-point witness, no convex 3-gon among
   its points — f(3) >= 3. Together: **f(3) = 3 EXACTLY** (the corpus value).
3. **E107.f4_lower**: the explicit 4-point general-position witness with NO
   convex 4-gon among its points (one point inside the triangle of the other
   three) — f(4) >= 5.
4. **E107.w5_gp / E107.w5_no_convex5**: the explicit 8-point general-position
   witness (the ErSz61 construction, integer coordinates — the same instance
   dual-certified by the CI-green doubter battery kernel-107d) with NO convex
   5-gon among its points, by the exhaustive kernel-decided subsequence
   enumeration (the Erdos142 r3max architecture: house sublists over the
   8-point list = 256 subsequences, every 5-selection checked) — f(5) >= 9.

## HONEST SCOPE (the audit law)
The UPPER bounds f(4) <= 5 (Klein's theorem), f(5) <= 9, and the general
conjecture f(n) = 2^{n-2}+1 remain OPEN. This kernel certifies the
LOWER-bound witness family (the construction side of the conjecture) at
n = 3, 4, 5 plus the exact value f(3) = 3. The n = 6 witness (16 points,
all 8008 6-subsets non-convex) is certified by the CI-green python battery
(kernel-107d / battery_w69f), not re-embedded in Lean. Klein f(4) = 5 is
census-certified by the CI-green doubter battery; its full Lean
formalization is the continuation front.

## REPRESENTATION (pinned)
Point = Int x Int. turn p q r = (q.x-p.x)*(r.y-p.y) - (q.y-p.y)*(r.x-p.x).
Convexity for 4 points: the ORDER-INDEPENDENT sign-product test — the four
triple-orientation signs multiply to a positive number (an even number of
negative signs; a zero factor = collinearity, excluded by general position).
All finite claims are kernel-decided closed terms (zero sorry).

## CAMPAIGN LAWS HELD
Arsenal imports only (BOSS's maths); zero sorry/admit/native_decide; axioms
within [propext, Classical.choice, Quot.sound]; decide on closed terms only.
-/

namespace E107

/-! ## §0 The orientation and convexity primitives -/

/-- The orientation determinant of an ordered triple. -/
def turn (p q r : Int × Int) : Int :=
  (q.1 - p.1) * (r.2 - p.2) - (q.2 - p.2) * (r.1 - p.1)

/-- The order-independent 4-point convexity test (Bool): the product of the
four triple-orientation signs is strictly positive. -/
def convex4B (a b c d : Int × Int) : Bool :=
  turn a b c * turn a b d * turn a c d * turn b c d > 0

/-- The 4-point convexity proposition. -/
def convex4 (a b c d : Int × Int) : Prop := convex4B a b c d = true

/-- A convex (non-degenerate) triangle. -/
def convex3 (a b c : Int × Int) : Prop := turn a b c ≠ 0

/-! ## §1 The house selection engine (the Erdos142 green architecture) -/

/-- All subsequences (index-increasing selections) of a point list. -/
def sublists : List (Int × Int) → List (List (Int × Int))
  | [] => [[]]
  | a :: t => sublists t ++ List.map (fun S => a :: S) (sublists t)

/-- General position (Bool): every 3-selection is non-collinear. For a list
with no repeated points this is exactly "no three distinct points on a line". -/
def gpB (W : List (Int × Int)) : Bool :=
  (sublists W).all (fun s =>
    match s with
    | [a, b, c] => turn a b c != 0
    | _ => true)

/-- Does the list contain a 3-selection in convex position? -/
def hasConv3 (W : List (Int × Int)) : Bool :=
  (sublists W).any (fun s =>
    match s with
    | [a, b, c] => turn a b c != 0
    | _ => false)

/-- Does the list contain a 5-selection with every 4-subselection convex?
(The order-independence of the sign-product test makes the five explicit
4-subselection checks sufficient for the selection, in any order.) -/
def hasConv5 (W : List (Int × Int)) : Bool :=
  (sublists W).any (fun s =>
    match s with
    | [a, b, c, d, e] =>
        convex4B a b c d && convex4B a b c e && convex4B a b d e &&
        convex4B a c d e && convex4B b c d e
    | _ => false)

/-! ## §2 f(3) = 3 EXACTLY -/

/-- f(3) <= 3: every 3 points in general position form a convex 3-gon. -/
theorem f3_upper (a b c : Int × Int) (hgp : turn a b c ≠ 0) : convex3 a b c :=
  hgp

/-- The 2-point witness. -/
def w3 : List (Int × Int) := """ + lp(W3) + """

/-- f(3) >= 3: the 2-point witness is too small for any 3-selection —
the kernel-decided enumeration returns false. -/
theorem f3_lower : hasConv3 w3 = false := by
  decide

/-! ## §3 f(4) >= 5: the 4-point witness -/

/-- The witness: one point strictly inside the triangle of the other three. -/
def w4 : List (Int × Int) := """ + lp(W4) + """

/-- The witness is in general position. -/
theorem w4_gp : gpB w4 = true := by
  decide

/-- f(4) >= 5: the full 4-selection of the witness fails the convexity test —
no 4 of its points form a convex quadrilateral. -/
theorem f4_lower : ¬ convex4 w4[0]! w4[1]! w4[2]! w4[3]! := by
  decide

/-! ## §4 f(5) >= 9: the 8-point ErSz61 witness -/

/-- The witness (integer coordinates; the doubter-battery-certified instance). -/
def w5 : List (Int × Int) := """ + lp(W5) + """

/-- The witness is in general position (kernel-decided: all 3-selections
non-collinear). -/
theorem w5_gp : gpB w5 = true := by
  decide

/-- f(5) >= 9: NO 5-selection of the 8-point witness is in convex position —
the exhaustive kernel-decided subsequence enumeration. -/
theorem w5_no_convex5 : hasConv5 w5 = false := by
  decide

/-! ## §5 The board -/

/-- The witness-family board: the exact value f(3) = 3 and the lower-bound
witnesses f(4) >= 5, f(5) >= 9, all kernel-certified. -/
theorem erdos107_board :
    hasConv3 w3 = false
    ∧ gpB w4 = true ∧ ¬ convex4 w4[0]! w4[1]! w4[2]! w4[3]!
    ∧ gpB w5 = true ∧ hasConv5 w5 = false :=
  ⟨f3_lower, w4_gp, f4_lower, w5_gp, w5_no_convex5⟩

/-! ## Receipt block -/

#print axioms f3_upper
#print axioms f3_lower
#print axioms w4_gp
#print axioms f4_lower
#print axioms w5_gp
#print axioms w5_no_convex5
#print axioms erdos107_board

#eval "E107_F3_GREEN"
#eval "E107_BOARD_GREEN"

end E107""")

lean = "\n".join(L)
path = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'Erdos107.lean')
open(path, 'w').write(lean)
print("emitted:", path, len(lean.split(chr(10))), "lines")
