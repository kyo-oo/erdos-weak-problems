/-
# ERDŐS #261 — WEAKENED SUB-QUESTION [Er88c]: KILLED AFFIRMATIVELY

The main questions of Erdős #261 ask whether every n admits

    n / 2^n  =  Σ_k a_k / 2^{a_k}      (distinct integers a_k ≥ 1),

and whether some rational x has 2^{ℵ₀} solutions of

    x  =  Σ_k a_k / 2^{a_k}.

In [Er88c] Erdős WEAKENS the second question to: does there exist a
rational x with at least TWO distinct solutions?

## THE KILL

    x = 1/2 has (at least) THREE representations:

      {2}       :   2/4                      = 1/2
      {3,6,8}   :   3/8   + 6/64  + 8/256    = 1/2
      {4,5,6}   :   4/16  + 5/32  + 6/64     = 1/2

each checkable by hand in one line (all sum to 128/256).

This answers the weakened question of [Er88c] in the AFFIRMATIVE.
Found by the pattern-collision census (this directory,
collision_census2.py): the corrected algebraic characterization of
Kill #2 — a pattern P ⊆ {1..J} (max offset J) certifies n iff

    n · (2^J − A_P) = S_P,   A_P = Σ_{j∈P} 2^{J−j},  S_P = Σ_{j∈P} j·2^{J−j}

— is a function P ↦ n, but NOT injective in the reverse direction once
solutions are collected per VALUE x = n/2^n: n = 1 and n = 2 both give
x = 1/2, and each carries its own pattern families. Deduplicated by
piece-set, x = 1/2 owns (to J = 16) the distinct solutions

    {2},  {3,6,8},  {4,5,6},  {4,5,7,8,11,13,14},  ...

The Borwein–Loring family supplies {2} (n=1, m=1) only; the remaining
collisions are new structure sitting inside the walk-certified pattern
space that TUZ20's per-n enumeration framed but never assembled per-x.

## FORMAL ENCODING (core Lean 4 only; no Mathlib; no sorry; no new axioms)

A finite set S of pieces with all pieces in the window [1, L] is scaled
to integers by multiplying by 2^L (legal: a ≤ L for every piece):

    sumScaled L S  =  Σ_{a ∈ S} a · 2^{L−a}.

Then, exactly,

    Σ_{a ∈ S} a / 2^a  =  (sumScaled L S) / 2^L,

so  x = 1/2  is represented by S at window L = 8  iff

    sumScaled 8 S = 2^7 = 128

with S nodup and all pieces in [1, 8]. All proofs below are closed by
`decide` on numbers ≤ 256 — no OOM surface.

## §-MAP

* §1  pow2, sumScaled (monomorphic Nat engine)
* §2  the three representations of 1/2 (decide)
* §3  THE WEAKENED QUESTION: two distinct solutions (main theorem)
* §4  THREE pairwise-distinct solutions (strengthening)
* §5  the sub-block collision {4,5} ≅ {3,8} (13/32 = 13/32), the
       mechanism that grafts further collisions onto any representation
       containing the block {4,5} in the window
* §6  receipts (Rat sums via #eval — compiler-evaluated, exact) and
       axiom gates.
-/

-- ===========================================================================
-- §1  THE SCALED-INTEGER ENGINE (pure Nat, kernel-computable)
-- ===========================================================================

def pow2 : Nat → Nat
  | 0 => 1
  | k + 1 => 2 * pow2 k

/-- Σ_{a ∈ S} a · 2^{L−a}  — x = 1/2 represented at window L iff = 2^{L−1}. -/
def sumScaled (L : Nat) (S : List Nat) : Nat :=
  (S.map (fun a => a * pow2 (L - a))).sum

/-- The rational value Σ_{a ∈ S} a / 2^a (receipts only; proofs stay in Nat). -/
def sumR (S : List Nat) : Rat :=
  (S.map (fun a : Nat => (Nat.cast a : Rat) / (Nat.cast (pow2 a) : Rat))).sum

-- ===========================================================================
-- §2  THE THREE REPRESENTATIONS OF 1/2 (each one line by hand)
-- ===========================================================================

-- 2/4 = 1/2:
theorem rep_one_piece : sumScaled 8 [2] = 2 ^ 7 := by decide

-- 3/8 + 6/64 + 8/256 = 96/256 + 24/256 + 8/256 = 128/256 = 1/2:
theorem rep_three_spread : sumScaled 8 [3, 6, 8] = 2 ^ 7 := by decide

-- 4/16 + 5/32 + 6/64 = 64/256 + 40/256 + 24/256 = 128/256 = 1/2:
theorem rep_three_consecutive : sumScaled 8 [4, 5, 6] = 2 ^ 7 := by decide

-- ===========================================================================
-- §3  THE WEAKENED QUESTION OF [Er88c] — MAIN THEOREM
-- ===========================================================================

/-- **Erdős #261, weakened sub-question [Er88c] — AFFIRMATIVE.**
There exists a rational (namely x = 1/2, i.e. scaled sum 2^7 at window
L = 8) with TWO distinct representations x = Σ a_k / 2^{a_k}: the
witness lists are nodup, all pieces are distinct positive integers in
[1, 8], and both carry the identical scaled sum 2^7 = 128 = 2^8 · (1/2). -/
theorem erdos261_weakened_two_solutions :
    ∃ (S₁ S₂ : List Nat),
      S₁ ≠ S₂ ∧
      S₁.Nodup ∧ S₂.Nodup ∧
      (∀ a ∈ S₁, 0 < a ∧ a ≤ 8) ∧ (∀ a ∈ S₂, 0 < a ∧ a ≤ 8) ∧
      sumScaled 8 S₁ = 2 ^ 7 ∧ sumScaled 8 S₂ = 2 ^ 7 := by
  refine ⟨[2], [3, 6, 8], by decide, by decide, by decide, by decide,
    by decide, by decide⟩

-- ===========================================================================
-- §4  STRENGTHENING — THREE PAIRWISE-DISTINCT REPRESENTATIONS
-- ===========================================================================

/-- x = 1/2 has THREE pairwise-distinct representations. -/
theorem erdos261_three_solutions :
    ∃ (S₁ S₂ S₃ : List Nat),
      S₁ ≠ S₂ ∧ S₁ ≠ S₃ ∧ S₂ ≠ S₃ ∧
      S₁.Nodup ∧ S₂.Nodup ∧ S₃.Nodup ∧
      (∀ a ∈ S₁, 0 < a ∧ a ≤ 8) ∧ (∀ a ∈ S₂, 0 < a ∧ a ≤ 8) ∧
      (∀ a ∈ S₃, 0 < a ∧ a ≤ 8) ∧
      sumScaled 8 S₁ = 2 ^ 7 ∧ sumScaled 8 S₂ = 2 ^ 7 ∧
      sumScaled 8 S₃ = 2 ^ 7 := by
  refine ⟨[2], [3, 6, 8], [4, 5, 6], by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide⟩

-- ===========================================================================
-- §5  THE SUB-BLOCK COLLISION {4,5} ≅ {3,8}  (13/32 = 13/32)
-- ===========================================================================

/-- The two-piece block {4,5} and the two-piece block {3,8} carry the
identical value 4/16 + 5/32 = 13/32 = 3/8 + 8/256. Any representation
containing the block {4,5} inside the window therefore admits a sibling
with {3,8} grafted in — the collision-generation mechanism. -/
theorem block_swap :
    sumScaled 8 [4, 5] = sumScaled 8 [3, 8] := by decide

theorem block_swap_value : sumScaled 8 [4, 5] = 104 := by decide

-- ===========================================================================
-- §6  RECEIPTS (compiler-evaluated, exact) + AXIOM GATES
-- ===========================================================================

-- The three rational sums, exact values (each prints 1/2):
#eval sumR [2]
#eval sumR [3, 6, 8]
#eval sumR [4, 5, 6]

-- The scaled receipts (each prints 128):
#eval (sumScaled 8 [2], sumScaled 8 [3, 6, 8], sumScaled 8 [4, 5, 6])

-- All three rational sums coincide:
#eval (sumR [2] == sumR [3, 6, 8] && sumR [3, 6, 8] == sumR [4, 5, 6])

-- The sub-block collision receipt (both 104):
#eval (sumScaled 8 [4, 5], sumScaled 8 [3, 8])

#print axioms erdos261_weakened_two_solutions
#print axioms erdos261_three_solutions
#print axioms block_swap
