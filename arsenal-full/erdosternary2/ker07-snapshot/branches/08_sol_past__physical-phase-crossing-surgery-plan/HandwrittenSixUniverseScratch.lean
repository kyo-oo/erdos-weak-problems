/- ======================================================================
/- CHRONOLOGICAL LABEL -- #0908 / 1132
/-    Path         : branches/sol_physical-phase-crossing-surgery-plan/HandwrittenSixUniverseScratch.lean
/-    Ref          : origin/sol/physical-phase-crossing-surgery-plan
/-    First-commit : 2026-08-17 08:15:36 +0530  (d02bd96)
/-    Last-commit  : 2026-08-17 08:15:36 +0530  (d02bd96)
/-    Total commits: 1
/- ======================================================================
/- GIT HISTORY (chronological, oldest first)
/- ======================================================================
/- [01/1] 2026-08-17 08:15:36 +0530  d02bd96  (ker07-dev)
/-        Add exact 6^k universe prefix arithmetic
/- ====================================================================== -/

import Mathlib

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

/-!
# Finite arithmetic of the handwritten 6^k / 7 / 13 layer

No GST forcing theorem is asserted here.  These lemmas simply make the finite
state-count arithmetic exact before it is coupled to the V2 graph.
-/

/-- Number of bridge states through natural depth i, including depth zero. -/
def gstSixUniversePrefixS (i : Nat) : Nat :=
  ∑ k in Finset.range (i+1), 6^k

/-- Exact six-ary geometric recurrence. -/
theorem gst_six_universe_prefix_succS (i : Nat) :
    gstSixUniversePrefixS (i+1) =
      gstSixUniversePrefixS i + 6^(i+1) := by
  unfold gstSixUniversePrefixS
  rw [show i+1+1 = (i+1)+1 by omega, Finset.sum_range_succ]

/-- Closed integer form of the finite 6^k universe.
The denominator 5=6-1 is represented without division. -/
theorem gst_six_universe_prefix_closedS (i : Nat) :
    5 * gstSixUniversePrefixS i = 6^(i+1) - 1 := by
  induction i with
  | zero =>
      norm_num [gstSixUniversePrefixS]
  | succ i ih =>
      rw [gst_six_universe_prefix_succS, Nat.mul_add, ih]
      have hp : 0 < 6^(i+1) := Nat.pow_pos (by decide)
      rw [show 6^((i+1)+1) = 6^(i+1) * 6 by rw [Nat.pow_succ]]
      omega

/-- The first nontrivial cumulative bridge universe has seven states. -/
theorem gst_six_universe_prefix_oneS :
    gstSixUniversePrefixS 1 = 7 := by
  decide

/-- The first aligned two-layer modulus factors as (6-1)(6+1). -/
theorem gst_six_square_boundary_factorS :
    6^2 - 1 = 5 * 7 := by
  decide

/-- The exact EQ2 event factor 13 is 6 plus the first cumulative universe 7. -/
theorem gst_event_factor_thirteen_from_six_sevenS :
    13 = 6 + gstSixUniversePrefixS 1 := by
  decide

/-- Boss's scalar kernel 7/(x-6) is exactly normalized at the global event
factor x=13.  Kept as integer division because 13-6 divides 7 exactly. -/
theorem gst_handwritten_kernel_normalizes_at_thirteenS :
    7 / (13 - 6) = 1 := by
  decide

/-- The first known nested canonical binary quotient factorization. -/
theorem gst_first_binary_quotient_factorizationS :
    455 = 5 * 7 * 13 := by
  decide
