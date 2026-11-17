/- ======================================================================
/- CHRONOLOGICAL LABEL -- #0968 / 1132
/-    Path         : branches/sol_physical-phase-crossing-surgery-plan/HandwrittenSignedKernelFluxScratch.lean
/-    Ref          : origin/sol/physical-phase-crossing-surgery-plan
/-    First-commit : 2026-08-17 10:16:24 +0530  (dad764d)
/-    Last-commit  : 2026-08-17 10:16:24 +0530  (dad764d)
/-    Total commits: 1
/- ======================================================================
/- GIT HISTORY (chronological, oldest first)
/- ======================================================================
/- [01/1] 2026-08-17 10:16:24 +0530  dad764d  (ker07-dev)
/-        Add signed handwritten event-kernel flux identities
/- ====================================================================== -/

import Mathlib

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

/-!
# Signed handwritten 7/(x-6) kernel on the microscopic x2 event coordinate

This file uses the exact x2/base3 bridge

  a + 2*d = e + 3*a'

with a,a' binary and d,e ternary.  Its event symbol is J=d+3e.  The physical
six-state event image is {0,1,3,5,7,8}; J=6 is the missing central value.

On the active BIG2 events Boss's kernel 7/(J-6) has the exact signed values

  CREATE  J=7 : +7
  DESTROY J=5 : -7
  SURVIVE J=8 : +7/2.

To keep the arithmetic integral we encode twice this kernel.  The resulting
quantity is a discrete horizontal flux plus a SURVIVE residual, so its sum
telescopes on every finite physical row.
-/

def gstMicroTwoIndicatorS (d : Nat) : Int := if d = 2 then 1 else 0

def gstMicroEventOutputS (a d : Nat) : Nat := (a + 2*d) % 3

def gstMicroEventCarryS (a d : Nat) : Nat := (a + 2*d) / 3

def gstMicroEventSymbolS (a d : Nat) : Nat :=
  d + 3*gstMicroEventOutputS a d

/-- Active means BIG2 is present on at least one side of the microscopic cell. -/
def gstMicroBig2ActiveS (a d : Nat) : Prop :=
  d = 2 ∨ gstMicroEventOutputS a d = 2

/-- Signed CREATE/DESTROY flux. -/
def gstMicroBig2FluxS (a d : Nat) : Int :=
  7 * (gstMicroTwoIndicatorS (gstMicroEventOutputS a d) -
       gstMicroTwoIndicatorS d)

/-- Twice Boss's signed kernel on the active sector, written without division.
The first term is the boundary flux; the second is the SURVIVE residual. -/
def gstMicroKernelTwiceS (a d : Nat) : Int :=
  14 * (gstMicroTwoIndicatorS (gstMicroEventOutputS a d) -
        gstMicroTwoIndicatorS d) +
  7 * gstMicroTwoIndicatorS d *
      gstMicroTwoIndicatorS (gstMicroEventOutputS a d)

/-- Exact six-state event-symbol table. -/
theorem gst_micro_event_symbol_tableS :
    gstMicroEventSymbolS 0 0 = 0 ∧
    gstMicroEventSymbolS 0 1 = 7 ∧
    gstMicroEventSymbolS 0 2 = 5 ∧
    gstMicroEventSymbolS 1 0 = 3 ∧
    gstMicroEventSymbolS 1 1 = 1 ∧
    gstMicroEventSymbolS 1 2 = 8 := by
  decide

/-- Six is not a physical microscopic event symbol. -/
theorem gst_micro_event_symbol_ne_sixS
    (a d : Nat) (ha : a < 2) (hd : d < 3) :
    gstMicroEventSymbolS a d ≠ 6 := by
  have hac : a = 0 ∨ a = 1 := by omega
  have hdc : d = 0 ∨ d = 1 ∨ d = 2 := by omega
  rcases hac with h0 | h1 <;>
    rcases hdc with d0 | d1 | d2 <;>
    subst a <;> subst d <;> decide

/-- CREATE/DESTROY/SURVIVE receive the signed kernel values 14,-14,7. -/
theorem gst_micro_kernel_twice_active_tableS :
    gstMicroKernelTwiceS 0 1 = 14 ∧
    gstMicroKernelTwiceS 0 2 = -14 ∧
    gstMicroKernelTwiceS 1 2 = 7 := by
  decide

/-- Cross-multiplied exact form of 2*7/(J-6) on every active BIG2 cell.

  (J-6) * K2 = 14.
-/
theorem gst_micro_kernel_resolvent_exactS
    (a d : Nat) (ha : a < 2) (hd : d < 3)
    (hactive : gstMicroBig2ActiveS a d) :
    ((gstMicroEventSymbolS a d : Int) - 6) *
      gstMicroKernelTwiceS a d = 14 := by
  have hac : a = 0 ∨ a = 1 := by omega
  have hdc : d = 0 ∨ d = 1 ∨ d = 2 := by omega
  rcases hac with h0 | h1 <;>
    rcases hdc with d0 | d1 | d2 <;>
    subst a <;> subst d <;>
    simp [gstMicroBig2ActiveS, gstMicroEventOutputS] at hactive <;>
    norm_num [gstMicroEventSymbolS, gstMicroEventOutputS,
      gstMicroKernelTwiceS, gstMicroTwoIndicatorS]

/-- The signed CREATE/DESTROY part is exactly a difference of BIG2 boundary
indicators.  This is the one-cell divergence law. -/
theorem gst_micro_big2_flux_exactS (a d : Nat) :
    gstMicroBig2FluxS a d =
      7 * (gstMicroTwoIndicatorS (gstMicroEventOutputS a d) -
           gstMicroTwoIndicatorS d) := by
  rfl

/-- Abstract finite-row telescope.  This theorem is deliberately stated for
an arbitrary sequence of ternary digits; when instantiated with consecutive
physical x2 columns, `b (r+1)` is the output BIG2 indicator of column r.
-/
theorem gst_micro_big2_flux_telescopesS
    (b : Nat → Int) (L : Nat) :
    (∑ r in Finset.range L, 7 * (b (r+1) - b r)) =
      7 * (b L - b 0) := by
  induction L with
  | zero => simp
  | succ L ih =>
      rw [Finset.sum_range_succ, ih]
      ring

/-- Kernel decomposition: signed boundary flux plus the SURVIVE residual. -/
theorem gst_micro_kernel_twice_decomposeS (a d : Nat) :
    gstMicroKernelTwiceS a d =
      2 * gstMicroBig2FluxS a d +
      7 * gstMicroTwoIndicatorS d *
          gstMicroTwoIndicatorS (gstMicroEventOutputS a d) := by
  unfold gstMicroKernelTwiceS gstMicroBig2FluxS
  ring
