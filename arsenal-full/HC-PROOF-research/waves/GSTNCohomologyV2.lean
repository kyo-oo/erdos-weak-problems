import Mathlib
import waves.GSTNCohomology
import waves.GSTWaveCohomologyV2

/-!
# WAVE II V2 — UNCONDITIONAL RANK AND UNIVERSAL INTERFERENCE

This upgrade removes redundant hypotheses from the N-cohomology rank law,
promotes the interference decomposition to arbitrary test amplitudes, and
extracts exact Ω-cut witnesses and digit-two mode classification.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000000

namespace GSTNCohomologyV2

open GST2DMixedEmergence
open GSTCanonicalSevenAxisBridge
open GSTWaveCohomology
open GSTWaveCohomologyV2
open GSTNCohomology

/-- A tower window is empty exactly at depth zero. -/
theorem towerWindow_nil_iff (R p N : Nat) :
    towerWindow R p N = [] ↔ N = 0 := by
  constructor
  · intro h
    have hlen := towerWindow_length R p N
    rw [h] at hlen
    simp at hlen
    exact hlen.symm
  · intro h
    subst N
    simp [towerWindow]

/-- Positive depth is exactly nonemptiness, not merely sufficient for it. -/
theorem towerWindow_nonempty_iff (R p N : Nat) :
    towerWindow R p N ≠ [] ↔ 0 < N := by
  constructor
  · intro hne
    have hN : N ≠ 0 := by
      intro hz
      apply hne
      exact (towerWindow_nil_iff R p N).2 hz
    omega
  · intro hpos hnil
    have hz := (towerWindow_nil_iff R p N).1 hnil
    omega

/-- The canonical N-cohomology basis exists without any ignition or
nonemptiness hypothesis. -/
def canonicalNCohoBasis (R : Nat) (s : NShape) (N : Nat) :
    Fin s.holes → nCohoClasses R s N :=
  fun _ => (fun j => towerWindow R (s.channel j) N, 0)

/-- **UNCONDITIONAL RANK LAW.**  Every N-shape has one canonical readout
coordinate per hole at every depth, including depth zero. -/
theorem ncoho_rank_unconditional (R : Nat) (s : NShape) (N : Nat) :
    ∀ i : Fin s.holes,
      (canonicalNCohoBasis R s N i).1 i =
        towerWindow R (s.channel i) N := by
  intro i
  rfl

/-- The original rank theorem is now an immediate specialization; its old
nonempty-window hypothesis carries no mathematical load. -/
theorem ncoho_rank_absorbed (R : Nat) (s : NShape) (N : Nat) :
    ∃ (basis : Fin s.holes → nCohoClasses R s N),
      ∀ i : Fin s.holes, (basis i).1 i =
        towerWindow R (s.channel i) N := by
  exact ⟨canonicalNCohoBasis R s N, ncoho_rank_unconditional R s N⟩

/-- Pair Wave I with an arbitrary integer amplitude field on the vertical
channel. -/
def weightedInterference (R lo hi : Nat) (A : Nat → ℤ) : ℤ :=
  ∑ p ∈ Finset.Icc lo hi, waveTwoForm (cellOf R p) * A p

def weightedHorizontal (R lo hi : Nat) (A : Nat → ℤ) : ℤ :=
  ∑ p ∈ Finset.Icc lo hi, horizontalCoboundary (cellOf R p) * A p

def weightedVertical (R lo hi : Nat) (A : Nat → ℤ) : ℤ :=
  ∑ p ∈ Finset.Icc lo hi, verticalCoboundary (cellOf R p) * A p

def weightedSource (R lo hi : Nat) (A : Nat → ℤ) : ℤ :=
  ∑ p ∈ Finset.Icc lo hi, waveSource (cellOf R p) * A p

/-- **UNIVERSAL INTERFERENCE LAW.**  Wave-I decomposition pairs exactly
with every integer amplitude field, not only Wave II. -/
theorem weighted_interference_decomposition
    (R lo hi : Nat) (A : Nat → ℤ) :
    weightedInterference R lo hi A =
      weightedHorizontal R lo hi A +
      weightedVertical R lo hi A +
      weightedSource R lo hi A := by
  have hsplit : ∀ p ∈ Finset.Icc lo hi,
      waveTwoForm (cellOf R p) * A p =
        horizontalCoboundary (cellOf R p) * A p
        + (verticalCoboundary (cellOf R p) * A p
          + waveSource (cellOf R p) * A p) := by
    intro p hp
    rw [wave_cell_decomposition]
    ring
  unfold weightedInterference weightedHorizontal weightedVertical weightedSource
  rw [Finset.sum_congr rfl hsplit]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  ring

/-- Wave II's original interference is the canonical-amplitude specialization
of the universal pairing. -/
theorem interference_is_weighted (R lo hi : Nat) :
    interference R lo hi =
      weightedInterference R lo hi (waveIIAmplitude R) := by
  rfl

/-- The original reaction law is absorbed by the universal law. -/
theorem interference_decomposition_absorbed (R lo hi : Nat) :
    interference R lo hi =
      horizontalPairing R lo hi +
      verticalPairing R lo hi +
      sourcePairing R lo hi := by
  simpa [interference_is_weighted, weightedInterference,
    weightedHorizontal, weightedVertical, weightedSource,
    horizontalPairing, verticalPairing, sourcePairing] using
      weighted_interference_decomposition R lo hi (waveIIAmplitude R)

/-- **EXACT Ω-CUT SIGNATURE.**  Every Ω class-two exponent carries a
specified Happy witness at its own cut row, not merely an existential row. -/
theorem shape_signature_exact_cut (R : Nat)
    (hclass : GSTGraphV2OmegaWaveLaw.omegaClassTwo R) :
    ∃ a core : Nat,
      1 ≤ a ∧ core % 3 = 2 ∧ R = 3^a * core ∧
      GSTU2DEventTransport.HappyCell
        (carry4 (4^R) (a+1)) (digit3 (4^R) (a+1)) := by
  rcases hclass with ⟨a, core, ha, hcore, hR⟩
  refine ⟨a, core, ha, hcore, hR, ?_⟩
  rw [hR]
  exact GSTGraphV2OmegaWaveLaw.omega_cut_happy_gate a core ha hcore

/-- On a digit-two row, Wave I's mode belongs to an exact three-value
spectrum. -/
theorem digit_two_mode_classification (R p : Nat)
    (hbig2 : digit3 R p = 2) :
    (twoWaveFrame R p).1 = -56 ∨
    (twoWaveFrame R p).1 = -112 ∨
    (twoWaveFrame R p).1 = 70 := by
  have hC4 : carry4 R p < 4 := (cellOf R p).hcarry
  have hcases :
      carry4 R p = 0 ∨ carry4 R p = 1 ∨
      carry4 R p = 2 ∨ carry4 R p = 3 := by omega
  unfold twoWaveFrame
  simp only [waveTwoForm, cellOf]
  rw [hbig2]
  rcases hcases with h0 | h1 | h2 | h3
  · left
    rw [h0]
    decide
  · right; left
    rw [h1]
    decide
  · left
    rw [h2]
    decide
  · right; right
    rw [h3]
    decide

/-- The old nonvanishing refinement follows from the exact mode spectrum. -/
theorem two_wave_frame_refines_absorbed (R p : Nat)
    (hbig2 : digit3 R p = 2) :
    (twoWaveFrame R p).1 ≠ 0 := by
  rcases digit_two_mode_classification R p hbig2 with h | h | h <;>
    rw [h] <;> decide

theorem wave_II_v2_crown :
    (∀ R p N, towerWindow R p N ≠ [] ↔ 0 < N)
    ∧ (∀ R s N i,
      (canonicalNCohoBasis R s N i).1 i =
        towerWindow R (s.channel i) N)
    ∧ (∀ R lo hi A,
      weightedInterference R lo hi A =
        weightedHorizontal R lo hi A +
        weightedVertical R lo hi A +
        weightedSource R lo hi A) := by
  refine ⟨towerWindow_nonempty_iff, ?_, weighted_interference_decomposition⟩
  intro R s N i
  exact ncoho_rank_unconditional R s N i

#check towerWindow_nil_iff
#check towerWindow_nonempty_iff
#check ncoho_rank_unconditional
#check ncoho_rank_absorbed
#check weighted_interference_decomposition
#check shape_signature_exact_cut
#check digit_two_mode_classification
#check two_wave_frame_refines_absorbed
#check wave_II_v2_crown

#print axioms ncoho_rank_unconditional
#print axioms weighted_interference_decomposition
#print axioms shape_signature_exact_cut
#print axioms digit_two_mode_classification
#print axioms wave_II_v2_crown

end GSTNCohomologyV2
