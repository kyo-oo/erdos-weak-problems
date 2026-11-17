/- ======================================================================
/- CHRONOLOGICAL LABEL -- #1132 / 1132
/-    Path         : branches/sol_5c579-final-bigN-right-chord-atomic/CanonicalOriginTritForcingScratch.lean
/-    Ref          : origin/sol/5c579-final-bigN-right-chord-atomic
/-    First-commit : 2026-08-18 01:39:21 +0530  (678313b)
/-    Last-commit  : 2026-08-18 01:39:21 +0530  (678313b)
/-    Total commits: 1
/- ======================================================================
/- GIT HISTORY (chronological, oldest first)
/- ======================================================================
/- [01/1] 2026-08-18 01:39:21 +0530  678313b  (ker07-dev)
/-        surgery: force ordinary origin trits from canonical parent badness
/- ====================================================================== -/

import CanonicalPhaseCrossingSurgeryScratch
import CanonicalOriginCutIntersectionScratch
import PrefixOneTerminalZScratch
import ResidualNullBranchReductionScratch

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

/-!
# Canonical origin-trit forcing at a physical prefix-one cut

This file turns complete physical phase-one badness into a literal restriction
on the ordinary ternary origin `n`.

At parent origin `b = 1 + 3*n`, row `q` of the forced-one tail is row `q+1`
of `Q_s(b)`.  The canonical origin-cut theorem decomposes that physical vertex
into

  * the finite origin prefix `a = b mod 3^(q+1)`, and
  * the next ordinary origin trit `digit_3(n,q)`.

Therefore, if the finite-prefix carry is in a good GST space, complete parent
badness forbids exactly the origin trit that would shift the exposed physical
digit to BIG2.  In particular, a good BIG2 finite-prefix state forces the
actual q-th origin trit to be nonzero.

No old duality, residual-Omega termination, global mirror, terminal NULL, or
global BIG1 projector is used.
-/

/-- The residual origin trit after the forced leading one is literally the
q-th ternary trit of `n`. -/
theorem gst_prefix_one_residual_origin_trit_exactS
    (n q : Nat) :
    ((1 + 3*n) / 3^(q+1)) % 3 = gstDigitS n q := by
  have hshift := gst_prefixed_one_digit_shiftS n q
  simpa [gstDigitS] using hshift

/-- Complete badness of the genuine canonical prefix-one parent forbids the
next ordinary-origin trit from completing a good finite prefix to physical
BIG2 at cut q+1. -/
theorem gst_prefix_one_bad_forbids_origin_trit_shift_at_cutS
    (s n q : Nat) (hs : 1 ≤ s)
    (hbad : GSTSeededBadTraceS 1
      (GSTHardPrefixOneTailS
        gstNavigationConstant gstCanonicalPrefixOffsetS s n))
    (hcarry :
      gstCarryS
          (gstNavigationConstant s ((1 + 3*n) % 3^(q+1))) (q+1) = 0 ∨
      gstCarryS
          (gstNavigationConstant s ((1 + 3*n) % 3^(q+1))) (q+1) = 3) :
    (gstDigitS
        (gstNavigationConstant s ((1 + 3*n) % 3^(q+1))) (q+1) +
      gstDigitS n q) % 3 ≠ 2 := by
  intro hshiftedTwo

  let b : Nat := 1 + 3*n
  let k : Nat := q + 1
  let a : Nat := b % 3^k
  let m : Nat := b / 3^k
  let H : Nat :=
    GSTHardPrefixOneTailS
      gstNavigationConstant gstCanonicalPrefixOffsetS s n

  have hdecomp : a + 3^k*m = b := by
    dsimp [a, m]
    exact Nat.mod_add_div b (3^k)

  have hmtrit : m % 3 = gstDigitS n q := by
    dsimp [m, b, k]
    exact gst_prefix_one_residual_origin_trit_exactS n q

  have hcutDigit :=
    gst_canonical_origin_cut_digitS s a k m hs
  have hfullDigitFormula :
      gstDigitS (gstNavigationConstant s b) k =
        (gstDigitS (gstNavigationConstant s a) k + m % 3) % 3 := by
    rw [← hdecomp]
    exact hcutDigit

  have hfullCarryFormula :=
    gst_canonical_origin_cut_carryS s a k m hs
  have hfullCarryEq :
      gstCarryS (gstNavigationConstant s b) k =
        gstCarryS (gstNavigationConstant s a) k := by
    rw [← hdecomp]
    exact hfullCarryFormula

  have hcarryA :
      gstCarryS (gstNavigationConstant s a) k = 0 ∨
        gstCarryS (gstNavigationConstant s a) k = 3 := by
    simpa [a, b, k] using hcarry

  have hfullDigit :
      gstDigitS (gstNavigationConstant s b) k = 2 := by
    rw [hfullDigitFormula, hmtrit]
    simpa [a, b, k] using hshiftedTwo

  have hfullCarry :
      gstCarryS (gstNavigationConstant s b) k = 0 ∨
        gstCarryS (gstNavigationConstant s b) k = 3 := by
    rw [hfullCarryEq]
    exact hcarryA

  have hparent :
      gstNavigationConstant s b = 1 + 3*H := by
    dsimp [b, H]
    exact gst_hard_tail_parent_navigationS
      gstNavigationConstant gst_navigation_constant_origin_energyS
      gstCanonicalPrefixOffsetS gst_navigation_constant_unit_prefixS
      s n hs

  have hDigitShift :
      gstDigitS (gstNavigationConstant s b) k = gstDigitS H q := by
    dsimp [k]
    rw [hparent]
    exact gst_prefixed_one_digit_shiftS H q

  have hCarryShift :
      gstCarryS (gstNavigationConstant s b) k =
        gstAffineMulCarryS 4 1 H q := by
    dsimp [k]
    rw [hparent]
    exact gst_prefixed_one_carry_shiftS H q

  have htailDigit : gstDigitS H q = 2 :=
    hDigitShift.symm.trans hfullDigit

  have htailCarry :
      gstAffineMulCarryS 4 1 H q = 0 ∨
        gstAffineMulCarryS 4 1 H q = 3 := by
    rcases hfullCarry with h0 | h3
    · exact Or.inl (hCarryShift.symm.trans h0)
    · exact Or.inr (hCarryShift.symm.trans h3)

  have hbadAt := hbad q
  exact hbadAt ⟨htailDigit, htailCarry⟩

/-- Genuine forcing consequence.  If the finite canonical origin prefix is
already a good BIG2 physical state at cut q+1, then a completely bad parent
forces the actual q-th ternary origin trit of n to be nonzero. -/
theorem gst_prefix_one_bad_good_big2_prefix_forces_origin_nonzeroS
    (s n q : Nat) (hs : 1 ≤ s)
    (hbad : GSTSeededBadTraceS 1
      (GSTHardPrefixOneTailS
        gstNavigationConstant gstCanonicalPrefixOffsetS s n))
    (hcarry :
      gstCarryS
          (gstNavigationConstant s ((1 + 3*n) % 3^(q+1))) (q+1) = 0 ∨
      gstCarryS
          (gstNavigationConstant s ((1 + 3*n) % 3^(q+1))) (q+1) = 3)
    (hprefixBig2 :
      gstDigitS
        (gstNavigationConstant s ((1 + 3*n) % 3^(q+1))) (q+1) = 2) :
    gstDigitS n q ≠ 0 := by
  intro hnzero
  have hforbid :=
    gst_prefix_one_bad_forbids_origin_trit_shift_at_cutS
      s n q hs hbad hcarry
  apply hforbid
  rw [hprefixBig2, hnzero]
  decide
