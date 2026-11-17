/- ======================================================================
/- CHRONOLOGICAL LABEL -- #0049 / 1132
/-    Path         : workbench/SolOriginDescent.lean
/-    Ref          : main
/-    First-commit : 2026-08-14 21:44:31 +0530  (83dd56f)
/-    Last-commit  : 2026-08-14 21:44:31 +0530  (83dd56f)
/-    Total commits: 1
/- ======================================================================
/- GIT HISTORY (chronological, oldest first)
/- ======================================================================
/- [01/1] 2026-08-14 21:44:31 +0530  83dd56f  (ker07-dev)
/-        Import Sol inline surgery handoff and GST graph workspace
/- ====================================================================== -/

import SolOmegaSurgery

/-!
  Property-level natural-origin descent for the canonical Navigation constants.
  These lemmas intentionally do not use `gst_prefix_one_navigation_lift`.
-/

set_option maxRecDepth 10000000
set_option maxHeartbeats 100000000

/-- A complete bad trace is the exact negation-side language used by the
    natural-origin descent. -/
def GSTCompleteBadTrace (R : Nat) : Prop :=
  ∀ j, GSTBadPair (gstCarry R j) (gstDigit R j)

/-- Complete badness rules out Navigation. -/
theorem gst_no_navigation_of_complete_bad
    (R : Nat) (hbad : GSTCompleteBadTrace R) :
    ¬ GSTNavigationWitness R := by
  intro hnav
  exact (gstNavigationWitness_iff_not_badTrace R).1 hnav hbad

/-- No Navigation yields the complete bad language. -/
theorem gst_complete_bad_of_no_navigation
    (R : Nat) (hno : ¬ GSTNavigationWitness R) :
    GSTCompleteBadTrace R := by
  intro j
  exact gstBadTrace_of_no_navigation_witness R hno j

/-- Property-level `0`-digit descent.  If the canonical state with exponent
    parameter `3*m` is completely bad, then the strictly smaller canonical
    child at level `s+1` and parameter `m` is completely bad. -/
theorem gst_origin_digit0_bad_descends
    (s m : Nat) (hs : 1 ≤ s)
    (hbad : GSTCompleteBadTrace
      (gstNavigationConstant s (3*m))) :
    GSTCompleteBadTrace
      (gstNavigationConstant (s+1) m) := by
  apply gst_complete_bad_of_no_navigation
  intro hchild
  have hparent : GSTNavigationWitness
      (gstNavigationConstant s (3*m)) :=
    gst_navigation_constant_mul3_witness s m hs hchild
  exact gst_no_navigation_of_complete_bad _ hbad hparent

/-- The `2` origin digit is terminal: canonical complete badness is impossible
    because the origin theorem supplies a Navigation witness immediately. -/
theorem gst_origin_digit2_bad_impossible
    (s b : Nat) (hs : 1 ≤ s) (hb : 1 ≤ b)
    (hb2 : b % 3 = 2)
    (hbad : GSTCompleteBadTrace
      (gstNavigationConstant s b)) : False := by
  have hnav : GSTNavigationWitness
      (gstNavigationConstant s b) :=
    gst_navigation_constant_b2_witness s b hs hb hb2
  exact gst_no_navigation_of_complete_bad _ hbad hnav

/-- Terminal exponent parameter `1` is also incompatible with complete badness
    from level two onward. -/
theorem gst_origin_one_bad_impossible
    (s : Nat) (hs : 2 ≤ s)
    (hbad : GSTCompleteBadTrace
      (gstNavigationConstant s 1)) : False := by
  have hnav : GSTNavigationWitness
      (gstNavigationConstant s 1) :=
    gst_navigation_constant_one_witness_all s hs
  exact gst_no_navigation_of_complete_bad _ hbad hnav

/-- Strong-induction measure for a nonzero multiple-of-three origin. -/
theorem gst_origin_digit0_parameter_decreases
    (m : Nat) (hm : 1 ≤ m) :
    m < 3*m := by
  omega

#check gst_origin_digit0_bad_descends
#check gst_origin_digit2_bad_impossible
#check gst_origin_one_bad_impossible
