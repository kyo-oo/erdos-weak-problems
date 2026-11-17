import Mathlib
import waves.GSTWaveCohomology

/-!
# WAVE I V2 — STRONGER COHOMOLOGICAL TRANSPORT

This layer upgrades the HC Wave-I laws without changing the underlying
GST wave.  It promotes one-way/local statements to exact equivalences
and finite-step transport laws.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000000

namespace GSTWaveCohomologyV2

open GST2DMixedEmergence
open GSTCanonicalSevenAxisBridge
open GSTWaveCohomology

/-- Source-freeness is exactly equivalent to pure coboundary exactness. -/
theorem sourcefree_iff_exact (c : WaveCell) :
    sourceFree c ↔
      waveTwoForm c = horizontalCoboundary c + verticalCoboundary c := by
  constructor
  · exact sourcefree_exact c
  · intro h
    unfold sourceFree
    have hd := wave_cell_decomposition c
    linarith

/-- Exact support of the Wave-I matter current. -/
theorem wave_source_support_exact (c : WaveCell) :
    waveSource c ≠ 0 ↔
      (c.carry = 1 ∧ c.digit = 1) ∨
      (c.carry = 2 ∧ c.digit = 2) ∨
      (c.carry = 3 ∧ c.digit = 2) := by
  rcases c with ⟨C, d, hC, hd⟩
  have hCc : C = 0 ∨ C = 1 ∨ C = 2 ∨ C = 3 := by omega
  have hdc : d = 0 ∨ d = 1 ∨ d = 2 := by omega
  rcases hCc with rfl | rfl | rfl | rfl <;>
    rcases hdc with rfl | rfl | rfl <;>
    norm_num [waveSource, surviveI, twoI, midDigit, finalMicroDigit,
      microOutput, highBit, lowBit]

/-- Exact source-free classification: the harmonic locus is the complement
of the three matter cells. -/
theorem sourcefree_iff_not_matter (c : WaveCell) :
    sourceFree c ↔
      ¬ ((c.carry = 1 ∧ c.digit = 1) ∨
         (c.carry = 2 ∧ c.digit = 2) ∨
         (c.carry = 3 ∧ c.digit = 2)) := by
  unfold sourceFree
  rw [← not_ne_iff]
  exact not_congr (wave_source_support_exact c)

/-- **ROW-CLASS COCYCLE.**  A row class over M+N cells splits exactly into
its first M cells and the N-cell class of the M-times re-encoded world. -/
theorem rowClass_add (R p M N : Nat) :
    rowClass R p (M + N) =
      rowClass R p M + rowClass (4^M * R) p N := by
  unfold rowClass
  rw [Finset.sum_range_add]
  congr 1
  apply Finset.sum_congr rfl
  intro t ht
  unfold rowClassAt
  rw [show (4:Nat)^(M+t) * R = 4^t * (4^M * R) by
    rw [Nat.pow_add]
    ring]

/-- Arbitrary finite re-encoding is associative at the class level. -/
theorem rowClass_three_way (R p A B C : Nat) :
    rowClass R p (A+B+C) =
      rowClass R p A
      + rowClass (4^A * R) p B
      + rowClass (4^(A+B) * R) p C := by
  rw [show A+B+C = (A+B)+C by omega, rowClass_add, rowClass_add]

/-- Wave transport by N cells is an exact cocycle, not merely a one-step
shift. -/
theorem wave_class_transport_finite (R p N M : Nat) :
    rowClass R p (N+M) - rowClass R p N =
      rowClass (4^N * R) p M := by
  rw [rowClass_add]
  ring

/-- A translated row window starting after A horizontal re-encodings. -/
def shiftedRowWindowIntegral (R p A N : Nat) : ℤ :=
  rowWindowIntegral (4^A * R) p N

/-- **TRANSLATED ROW GAUSS LAW.**  The row decomposition holds from every
horizontal GST phase, not only from the original column. -/
theorem shifted_window_integral_decomposition (R p A N : Nat) :
    shiftedRowWindowIntegral R p A N
      = infoPotential (digit3 (4^(A+N) * R) p)
          - infoPotential (digit3 (4^A * R) p)
        + 7 * (∑ t ∈ Finset.range N,
            carryPotential (carry4 (4^(A+t) * R) p)
            - 3 * ∑ t ∈ Finset.range N,
              carryPotential (carry4 (4^(A+t) * R) (p+1)))
        + 56 * ∑ t ∈ Finset.range N,
            surviveI (carry4 (4^(A+t) * R) p)
              (digit3 (4^(A+t) * R) p) := by
  unfold shiftedRowWindowIntegral
  simpa [Nat.pow_add, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
    (window_integral_decomposition (4^A * R) p N)

/-- A translated rectangle after A horizontal re-encodings. -/
def shiftedRectangleIntegral (R A N K : Nat) : ℤ :=
  ∑ p ∈ Finset.range K, (3:Int)^p * ∑ t ∈ Finset.range N,
    mixedDensity (carry4 (4^(A+t) * R) p)
      (digit3 (4^(A+t) * R) p)

/-- **TRANSLATED 2D GAUSS LAW.**  Every finite rectangle cut from any
horizontal phase has the same exact boundary/source decomposition. -/
theorem shifted_rectangle_gauss_law (R A N K : Nat) :
    shiftedRectangleIntegral R A N K
      = ∑ p ∈ Finset.range K, (3:Int)^p *
          (infoPotential (digit3 (4^(A+N) * R) p)
            - infoPotential (digit3 (4^A * R) p))
        + 7 * (∑ t ∈ Finset.range N,
            carryPotential (carry4 (4^(A+t) * R) 0)
          - (3:Int)^K * ∑ t ∈ Finset.range N,
            carryPotential (carry4 (4^(A+t) * R) K))
        + 56 * ∑ p ∈ Finset.range K, (3:Int)^p * ∑ t ∈ Finset.range N,
            surviveI (carry4 (4^(A+t) * R) p)
              (digit3 (4^(A+t) * R) p) := by
  unfold shiftedRectangleIntegral
  simpa [Nat.pow_add, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
    (rectangle_gauss_law (4^A * R) N K)

/-- Capstone for the strengthened Wave-I layer. -/
theorem wave_I_v2_crown :
    (∀ c : WaveCell,
      sourceFree c ↔
        waveTwoForm c = horizontalCoboundary c + verticalCoboundary c)
    ∧ (∀ R p M N,
      rowClass R p (M+N) =
        rowClass R p M + rowClass (4^M * R) p N)
    ∧ (∀ R p A N,
      shiftedRowWindowIntegral R p A N
        = infoPotential (digit3 (4^(A+N) * R) p)
            - infoPotential (digit3 (4^A * R) p)
          + 7 * (∑ t ∈ Finset.range N,
              carryPotential (carry4 (4^(A+t) * R) p)
              - 3 * ∑ t ∈ Finset.range N,
                carryPotential (carry4 (4^(A+t) * R) (p+1)))
          + 56 * ∑ t ∈ Finset.range N,
              surviveI (carry4 (4^(A+t) * R) p)
                (digit3 (4^(A+t) * R) p)) := by
  refine ⟨sourcefree_iff_exact, rowClass_add, ?_⟩
  intro R p A N
  exact shifted_window_integral_decomposition R p A N

#check sourcefree_iff_exact
#check wave_source_support_exact
#check sourcefree_iff_not_matter
#check rowClass_add
#check wave_class_transport_finite
#check shifted_window_integral_decomposition
#check shifted_rectangle_gauss_law
#check wave_I_v2_crown

#print axioms sourcefree_iff_exact
#print axioms wave_source_support_exact
#print axioms rowClass_add
#print axioms shifted_window_integral_decomposition
#print axioms shifted_rectangle_gauss_law
#print axioms wave_I_v2_crown

end GSTWaveCohomologyV2
