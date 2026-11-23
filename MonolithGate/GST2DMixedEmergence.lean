import Mathlib

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace GST2DMixedEmergence

/-- One literal x2/base-3 microscopic output. -/
def microOutput (a d : Nat) : Nat := (a + 2*d) % 3

def highBit (C : Nat) : Nat := C / 2
def lowBit (C : Nat) : Nat := C % 2

def midDigit (C d : Nat) : Nat := microOutput (highBit C) d

def finalMicroDigit (C d : Nat) : Nat :=
  microOutput (lowBit C) (midDigit C d)

/-- Exact x4/base-3 cell output digit. -/
def outDigit (C d : Nat) : Nat := (C + 4*d) % 3

/-- Exact x4/base-3 next carry. -/
def nextCarry (C d : Nat) : Nat := (C + 4*d) / 3

/-- Handwritten U charge chart. -/
def uCharge (C : Nat) : Int :=
  if C = 0 then 5 else if C = 3 then 21 else 15

/-- Handwritten U jump. -/
def uJump (C d : Nat) : Int :=
  3 * uCharge (nextCarry C d) - uCharge C - 24*(d : Int)

/-- Indicator of information digit BIG2. -/
def twoI (d : Nat) : Int := if d = 2 then 1 else 0

/-- One literal microscopic signed seven-kernel edge. -/
def microSevenKernel (a d : Nat) : Int :=
  14 * (twoI (microOutput a d) - twoI d) +
    7 * (twoI d * twoI (microOutput a d))

/-- The two microscopic x2 layers whose composition is one x4 GST cell. -/
def sevenKernel (C d : Nat) : Int :=
  microSevenKernel (highBit C) d +
    microSevenKernel (lowBit C) (midDigit C d)

/-- Number of microscopic BIG2→BIG2 SURVIVE edges inside the x4 cell.  It is
`0`, `1`, or `2`; unlike a coarse x4 indicator it retains the hidden BIG1
midpoint of the NULL chord `2→1→2`. -/
def surviveI (C d : Nat) : Int :=
  twoI d * twoI (midDigit C d) +
    twoI (midDigit C d) * twoI (finalMicroDigit C d)

/-- Vertical carry potential selected by the exact twelve-cell system. -/
def carryPotential (C : Nat) : Int :=
  if C = 0 then -5 else if C = 1 then -7 else if C = 2 then 1 else 3

/-- Horizontal information potential.  It vanishes on BIG0 and BIG2 and is
`-56` exactly on BIG1. -/
def infoPotential (d : Nat) : Int :=
  112 * twoI d - 56*(d : Int)

/-- Primitive `8:7` mixture of the handwritten seven-kernel and U operator. -/
def mixedDensity (C d : Nat) : Int :=
  8 * sevenKernel C d + 7 * uJump C d

/-- Two literal x2 layers reproduce the x4 output trit. -/
theorem finalMicroDigit_eq_outDigit
    (C d : Nat) (hC : C < 4) (hd : d < 3) :
    finalMicroDigit C d = outDigit C d := by
  have hCc : C = 0 ∨ C = 1 ∨ C = 2 ∨ C = 3 := by omega
  have hdc : d = 0 ∨ d = 1 ∨ d = 2 := by omega
  rcases hCc with h0 | h1 | h2 | h3 <;>
    rcases hdc with d0 | d1 | d2 <;>
    subst C <;> subst d <;>
    norm_num [finalMicroDigit, midDigit, microOutput, highBit, lowBit, outDigit]

/-- The microscopic seven-kernel telescopes horizontally: only the endpoint
BIG2 charge and the two genuine microscopic SURVIVE incidences remain. -/
theorem sevenKernel_micro_telescope
    (C d : Nat) (hC : C < 4) (hd : d < 3) :
    sevenKernel C d =
      14 * (twoI (outDigit C d) - twoI d) + 7 * surviveI C d := by
  have hCc : C = 0 ∨ C = 1 ∨ C = 2 ∨ C = 3 := by omega
  have hdc : d = 0 ∨ d = 1 ∨ d = 2 := by omega
  rcases hCc with h0 | h1 | h2 | h3 <;>
    rcases hdc with d0 | d1 | d2 <;>
    subst C <;> subst d <;>
    norm_num [sevenKernel, microSevenKernel, surviveI, twoI,
      finalMicroDigit, midDigit, microOutput, highBit, lowBit, outDigit]

/-- The mixed horizontal potential is exactly the BIG1 detector on physical
ternary digits. -/
theorem infoPotential_physical_table
    (d : Nat) (hd : d < 3) :
    (d = 0 ∧ infoPotential d = 0) ∨
    (d = 1 ∧ infoPotential d = -56) ∨
    (d = 2 ∧ infoPotential d = 0) := by
  have hdc : d = 0 ∨ d = 1 ∨ d = 2 := by omega
  rcases hdc with rfl | rfl | rfl <;>
    norm_num [infoPotential, twoI]

/-- The U operator by itself is already a two-direction divergence: horizontal
information transport plus the ternary carry-potential derivative. -/
theorem uJump_divergence
    (C d : Nat) (hC : C < 4) (hd : d < 3) :
    uJump C d =
      8 * ((d : Int) - (outDigit C d : Int)) +
      carryPotential C - 3 * carryPotential (nextCarry C d) := by
  have hCc : C = 0 ∨ C = 1 ∨ C = 2 ∨ C = 3 := by omega
  have hdc : d = 0 ∨ d = 1 ∨ d = 2 := by omega
  rcases hCc with h0 | h1 | h2 | h3 <;>
    rcases hdc with d0 | d1 | d2 <;>
    subst C <;> subst d <;>
    norm_num [uJump, uCharge, outDigit, nextCarry, carryPotential]

/-- **Mixed 2D GST emergence equation.**

The primitive mixture `8·sevenKernel + 7·U` is forced by the requirement that
the horizontal potential identify BIG0 and BIG2.  What remains is exactly:

* a horizontal BIG1-only boundary derivative;
* a vertical ternary carry derivative; and
* positive microscopic SURVIVE incidence in the interior.

Thus the two-dimensional object is an algebraic consequence of the two raw
handwritten operators, not an imposed geometry. -/
theorem mixed_cell_emergence
    (C d : Nat) (hC : C < 4) (hd : d < 3) :
    mixedDensity C d =
      infoPotential (outDigit C d) - infoPotential d +
      7 * carryPotential C - 21 * carryPotential (nextCarry C d) +
      56 * surviveI C d := by
  have hCc : C = 0 ∨ C = 1 ∨ C = 2 ∨ C = 3 := by omega
  have hdc : d = 0 ∨ d = 1 ∨ d = 2 := by omega
  rcases hCc with h0 | h1 | h2 | h3 <;>
    rcases hdc with d0 | d1 | d2 <;>
    subst C <;> subst d <;>
    norm_num [mixedDensity, sevenKernel, microSevenKernel, surviveI, twoI,
      uJump, uCharge, finalMicroDigit, midDigit, microOutput, highBit, lowBit,
      outDigit, nextCarry, carryPotential, infoPotential]

/-- The two x4 Happy realizations separate naturally in the emergent equation:
NULL is the hidden BIG1 chord `2→1→2`; GST+ is the all-SURVIVE chord
`2→2→2`. -/
theorem happy_chord_dichotomy
    (C : Nat) (hC : C = 0 ∨ C = 3) :
    (C = 0 ∧ midDigit C 2 = 1 ∧ finalMicroDigit C 2 = 2 ∧ surviveI C 2 = 0) ∨
    (C = 3 ∧ midDigit C 2 = 2 ∧ finalMicroDigit C 2 = 2 ∧ surviveI C 2 = 2) := by
  rcases hC with rfl | rfl
  · left
    norm_num [midDigit, finalMicroDigit, surviveI, microOutput,
      highBit, lowBit, twoI]
  · right
    norm_num [midDigit, finalMicroDigit, surviveI, microOutput,
      highBit, lowBit, twoI]

/-- Ordinary horizontal discrete derivative. -/
theorem horizontal_diff_telescope (f : Nat → Int) (N : Nat) :
    Finset.sum (Finset.range N) (fun t => f (t+1) - f t) =
      f N - f 0 := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      ring

/-- One horizontal row of physical x4 cells. -/
theorem mixed_row_emergence
    (C Cnext d : Nat → Nat) (N : Nat)
    (hcell : ∀ t, t < N →
      C t < 4 ∧ d t < 3 ∧
      outDigit (C t) (d t) = d (t+1) ∧
      nextCarry (C t) (d t) = Cnext t) :
    Finset.sum (Finset.range N) (fun t => mixedDensity (C t) (d t)) =
      infoPotential (d N) - infoPotential (d 0) +
      7 * (Finset.sum (Finset.range N) (fun t => carryPotential (C t)) -
        3 * Finset.sum (Finset.range N) (fun t => carryPotential (Cnext t))) +
      56 * Finset.sum (Finset.range N) (fun t => surviveI (C t) (d t)) := by
  have hlocal :
      Finset.sum (Finset.range N) (fun t => mixedDensity (C t) (d t)) =
        Finset.sum (Finset.range N) (fun t =>
          (infoPotential (d (t+1)) - infoPotential (d t)) +
          (7 * carryPotential (C t) - 21 * carryPotential (Cnext t)) +
          56 * surviveI (C t) (d t)) := by
    apply Finset.sum_congr rfl
    intro t ht
    rcases hcell t (Finset.mem_range.mp ht) with ⟨hC, hd, hout, hnext⟩
    rw [mixed_cell_emergence (C t) (d t) hC hd, hout, hnext]
    ring
  rw [hlocal, Finset.sum_add_distrib, Finset.sum_add_distrib]
  have htel := horizontal_diff_telescope (fun t => infoPotential (d t)) N
  rw [htel]
  rw [Finset.sum_sub_distrib]
  rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  ring

/-- **Full 2D divergence theorem.** Every finite rectangle cut from the live
Nat×Nat grid has only left/right BIG1 boundary charge, bottom/top carry flux,
and positive microscopic SURVIVE incidence. The live top boundary remains
explicit; no terminal state or support horizon occurs. -/
theorem mixed_rectangle_emergence
    (C d : Nat → Nat → Nat) (N K : Nat)
    (hcell : ∀ t p, t < N → p < K →
      C t p < 4 ∧ d t p < 3 ∧
      outDigit (C t p) (d t p) = d (t+1) p ∧
      nextCarry (C t p) (d t p) = C t (p+1)) :
    Finset.sum (Finset.range K) (fun p =>
      (3 : Int)^p * Finset.sum (Finset.range N) (fun t =>
        mixedDensity (C t p) (d t p))) =
      Finset.sum (Finset.range K) (fun p =>
        (3 : Int)^p * (infoPotential (d N p) - infoPotential (d 0 p))) +
      7 * (Finset.sum (Finset.range N) (fun t => carryPotential (C t 0)) -
        (3 : Int)^K * Finset.sum (Finset.range N) (fun t => carryPotential (C t K))) +
      56 * Finset.sum (Finset.range K) (fun p =>
        (3 : Int)^p * Finset.sum (Finset.range N) (fun t =>
          surviveI (C t p) (d t p))) := by
  induction K with
  | zero => simp
  | succ K ih =>
      have hprefix : ∀ t p, t < N → p < K →
          C t p < 4 ∧ d t p < 3 ∧
          outDigit (C t p) (d t p) = d (t+1) p ∧
          nextCarry (C t p) (d t p) = C t (p+1) := by
        intro t p ht hp
        exact hcell t p ht (by omega)
      have ih' := ih hprefix
      have hrow := mixed_row_emergence
        (fun t => C t K) (fun t => C t (K+1)) (fun t => d t K) N
        (by
          intro t ht
          exact hcell t K ht (by omega))
      rw [Finset.sum_range_succ, ih', hrow]
      simp only [Finset.sum_range_succ]
      rw [pow_succ]
      ring

#check mixed_cell_emergence
#check happy_chord_dichotomy
#check mixed_rectangle_emergence
#print axioms mixed_cell_emergence
#print axioms mixed_rectangle_emergence

end GST2DMixedEmergence