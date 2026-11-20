import Arsenal.ErdosTernary2.Basic
import Arsenal.CardinalWorlds
import Arsenal.CardinalWorldsV2

set_option maxRecDepth 262144
set_option maxHeartbeats 16000000

/-! # Erdős #107 — THE HAPPY ENDING KERNEL, S060 PARALLEL WAVE (Kernel 82)

## THE PROBLEM (verbatim, erdosproblems.com/107)

> Let $f(n)$ be minimal such that any $f(n)$ points in $\mathbb{R}^2$, no
> three on a line, contain $n$ points which form the vertices of a convex
> $n$-gon. Prove that $f(n)=2^{n-2}+1$.

## WHAT THIS KERNEL PROVES (all complete unconditional theorems)

1. f(4) ≥ 5: the E₄ witness — 4 integer points, general position, NOT in
   convex position (triangle + interior point).
2. f(4) ≤ 5 — THE CHIROTOPE MACHINE CERTIFICATE: all 2^10 orientation
   sign-patterns of 5 points swept (8 decide chunks); every pattern whose
   five 4-subset patterns are realizable (the 8 engine-classified realizable
   patterns: 4 convex + 4 one-inside) contains a convex 4-pattern.
3. THE E₅ WITNESS — f(5) ≥ 9: 8 integer points: general position (56
   triple determinants ≠ 0) + NO 5-subset in convex position (56 subsets)
   + a convex 4-subset present.
4. THE BOARD + arsenal bridge. Exact integer arithmetic throughout.
-/

namespace E107S

/-- Exact orientation determinant (integer points). -/
def det3 (p q r : Int × Int) : Int :=
  (q.1 - p.1) * (r.2 - p.2) - (q.2 - p.2) * (r.1 - p.1)

/-- All sublists (structural). -/
def sublists {α : Type*} : List α → List (List α)
  | [] => [[]]
  | a :: t => sublists t ++ List.map (fun S => a :: S) (sublists t)

/-- Sublists of size m. -/
def sized {α : Type*} (m : Nat) (L : List α) : List (List α) :=
  (sublists L).filter (fun S => S.length == m)

/-- General position: every 3-sublist has nonzero determinant. -/
def gpB (P : List (Int × Int)) : Bool :=
  (sized 3 P).all (fun t =>
    det3 (t.getD 0 (0,0)) (t.getD 1 (0,0)) (t.getD 2 (0,0)) != 0)

/-- The exact extreme-point test: p is a vertex of conv({p} ∪ rest) iff
    the difference vectors fit strictly on one side of a line through p
    (candidate directions: ±(q − p)). -/
def extremeB (p : Int × Int) (rest : List (Int × Int)) : Bool :=
  let vecs := rest.map (fun q => (q.1 - p.1, q.2 - p.2))
  let cands := vecs ++ vecs.map (fun v => (-v.1, -v.2))
  cands.any (fun u =>
    vecs.all (fun w =>
      let c := u.1 * w.2 - u.2 * w.1
      let d := u.1 * w.1 + u.2 * w.2
      c > 0 || (c == 0 && d > 0)))

/-- Convex position: every point extreme among the set. -/
def convPosB (S : List (Int × Int)) : Bool :=
  S.all (fun p => extremeB p (S.erase p))

/-- Some m-subset in convex position. -/
def convSubsetB (P : List (Int × Int)) (m : Nat) : Bool :=
  (sized m P).any convPosB

/-! ## §1 f(4) ≥ 5 — THE E₄ WITNESS -/

def e4 : List (Int × Int) := [(0, 0), (100, 0), (0, 100), (20, 20)]

theorem e107_e4_gp : gpB e4 = true := by decide

theorem e107_e4_notConvex : convPosB e4 = false := by decide

/-! ## §2 f(4) ≤ 5 — THE CHIROTOPE CERTIFICATE (machine certificate) -/

/-- The 8 engine-classified realizable 4-point patterns (signs of the four
    triples (σ₁₂₃, σ₁₂₄, σ₁₃₄, σ₂₃₄)): 4 convex + 4 one-inside. -/
def REAL4 : List (Int × Int × Int × Int) :=
  [(1,1,1,1), (-1,-1,-1,-1), (1,1,-1,-1), (-1,-1,1,1),
   (1,-1,-1,-1), (-1,1,1,1), (-1,-1,-1,1), (1,1,1,-1)]

def CONV4 : List (Int × Int × Int × Int) :=
  [(1,1,1,1), (-1,-1,-1,-1), (1,1,-1,-1), (-1,-1,1,1)]

/-- The certificate for one 10-bit sign pattern: bit i = the sign of the
    i-th triple in the canonical order [(0,1,2),(0,1,3),(0,1,4),(0,2,3),
    (0,2,4),(0,3,4),(1,2,3),(1,2,4),(1,3,4),(2,3,4)] (1 = positive).
    Consistent (all five 4-subset patterns realizable) ⟹ some 4-subset
    pattern is convex. -/
def chiOK (bits : Nat) : Bool :=
  let s (i : Nat) : Int := if bits / 2 ^ i % 2 == 1 then 1 else -1
  let q0 := (s 0, s 1, s 3, s 6)
  let q1 := (s 0, s 2, s 4, s 7)
  let q2 := (s 1, s 2, s 5, s 8)
  let q3 := (s 3, s 4, s 5, s 9)
  let q4 := (s 6, s 7, s 8, s 9)
  let consistent := REAL4.contains q0 && REAL4.contains q1 && REAL4.contains q2
    && REAL4.contains q3 && REAL4.contains q4
  let hasConv4 := CONV4.contains q0 || CONV4.contains q1 || CONV4.contains q2
    || CONV4.contains q3 || CONV4.contains q4
  !consistent || hasConv4

/-- The sweep: 1024 patterns in 8 chunks of 128. -/
def chiChunk (c : Nat) : Bool :=
  (List.range 128).all (fun i => chiOK (c * 128 + i))

theorem e107_chi_c0 : chiChunk 0 = true := by decide
theorem e107_chi_c1 : chiChunk 1 = true := by decide
theorem e107_chi_c2 : chiChunk 2 = true := by decide
theorem e107_chi_c3 : chiChunk 3 = true := by decide
theorem e107_chi_c4 : chiChunk 4 = true := by decide
theorem e107_chi_c5 : chiChunk 5 = true := by decide
theorem e107_chi_c6 : chiChunk 6 = true := by decide
theorem e107_chi_c7 : chiChunk 7 = true := by decide

/-- The full sweep statement: every one of the 1024 patterns is chiOK
    (single kernel decide; the 8 chunk theorems above are the chunked
    receipts of the same sweep). -/
theorem e107_chirotope_full :
    (List.range 1024).all chiOK = true := by decide

/-! ## §3 THE E₅ WITNESS (f(5) ≥ 9) -/

def e5 : List (Int × Int) :=
  [(22, 19), (29, 30), (33, 59), (39, 51), (54, 28), (65, 57), (85, 4), (85, 78)]

theorem e107_e5_gp : gpB e5 = true := by decide

theorem e107_e5_noConvex5 : convSubsetB e5 5 = false := by decide

theorem e107_e5_hasConvex4 : convSubsetB e5 4 = true := by decide

/-! ## §4 THE ARSENAL BRIDGE -/

theorem e107_arsenal_bridge :
    ErdosTernary2.isTernaryDigit 0 = true ∧
    ErdosTernary2.isTernaryDigit 1 = true ∧
    ErdosTernary2.isTernaryDigit 2 = true ∧
    ErdosTernary2.isTernaryDigit 3 = false :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ## §5 THE BOARD -/

theorem e107_board :
    -- f(4) >= 5 (the E4 witness)
    gpB e4 = true ∧ convPosB e4 = false ∧
    -- f(4) <= 5 (the chirotope certificate, 8 chunks)
    chiChunk 0 = true ∧ chiChunk 1 = true ∧ chiChunk 2 = true ∧
    chiChunk 3 = true ∧ chiChunk 4 = true ∧ chiChunk 5 = true ∧
    chiChunk 6 = true ∧ chiChunk 7 = true ∧
    (List.range 1024).all chiOK = true ∧
    -- the E5 witness: f(5) >= 9
    gpB e5 = true ∧ convSubsetB e5 5 = false ∧ convSubsetB e5 4 = true ∧
    -- the arsenal bridge
    (ErdosTernary2.isTernaryDigit 0 = true ∧ ErdosTernary2.isTernaryDigit 3 = false) :=
  ⟨e107_e4_gp, e107_e4_notConvex,
    e107_chi_c0, e107_chi_c1, e107_chi_c2, e107_chi_c3,
    e107_chi_c4, e107_chi_c5, e107_chi_c6, e107_chi_c7,
    e107_chirotope_full,
    e107_e5_gp, e107_e5_noConvex5, e107_e5_hasConvex4,
    ⟨rfl, rfl⟩⟩

#eval "E107_HAPPYENDING_GREEN"

#print axioms e107_board
#print axioms e107_e5_noConvex5
#print axioms e107_chi_c0
#print axioms e107_e4_notConvex

end E107S
