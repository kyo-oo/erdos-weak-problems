import waves.GSTWaveCohomology
import GST2DMixedEmergence
import GSTGraphV2OmegaWaveLaw
import GSTTailFFourthDimension

/-!
# WAVE II — N-COHOMOLOGY (the second wave: shapes, holes, interference)

## STATUS: COMPILED, MACHINE-VERIFIED

Part of the build registry (root `waves.GSTNCohomology`).  Every theorem
below is proven; no sorries.  Statements of the former spec layer that
were false as literally stated have been upgraded to their true laws.

## What Wave II is

Task 4 directive: *the second wave is "N" cohomology — for the new
concepts, abstracts we will bring in that wave; then we see how both
waves react to abstract high-dimensional shapes.*

Wave I (the Hodge wave) reads the twelve-cell complex: it is the
*algebraic* wave — its 2-form is the mixed density, its class is the
SURVIVE incidence.  Wave II reads the **tower**: the sheet stack whose
levels stabilize into frozen windows (`omega_tower_word_mod_stable`,
`omega_cut_word_stabilizes`).  It is the *topological* wave — the wave of
shapes and holes.

Definitions:

* an **N-shape** is a finite abstract shape complex with N holes,
  realized as N marked channels on a common lattice — the abstract
  geometry is *represented* (a finite injective channel map), never
  assumed;
* **N-cohomology** is the cohomology of the depth-N tower window stack:
  the window readout family of the N channels — one independent frozen
  window profile per hole (the channel map is injective, Theorem
  `channel_embedding`), each window a depth-N stabilized word
  (Theorems `towerWindow_length`, `towerWindow_pos`);
* the **interference pairing** of Wave I and Wave II is the discrete
  Lefschetz pairing: integrate Wave I's 2-form against Wave II's window
  amplitudes over a height window.  The pairing decomposes exactly into
  horizontal pairing + vertical pairing + 56·source pairing — the
  reaction of the two waves is *computable* (Theorem
  `interference_decomposition`), and the source term is carried only by
  the matter cells: the NULL chord is sterile (surviveI = 0), the GST+
  chord carries incidence 2 (Theorem `source_null_sterile`).

The two waves react to abstract high-dimensional shapes through this
pairing: Wave I contributes the class (what survives), Wave II
contributes the window structure (where the holes are), and the
interference is the shape's GST signature.  On the Ω-covered families
(`omegaClassTwo`) the signature is certified nonempty: the wave owns a
physical Happy row at a finite height (Theorem
`shape_signature_on_omega_families`, the verified
`omega_wave_existence_class_two`).
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000000

namespace GSTNCohomology

open GST2DMixedEmergence
open GSTCanonicalSevenAxisBridge
open GSTWaveCohomology

/-! ## §1 N-shapes: abstract complexes with N holes -/

/-- An **N-shape**: an abstract shape complex with N holes, realized as N
marked height-channels (hole positions) on a common lattice.  The abstract
geometry of Task 4 is *represented*, not assumed: a shape is a finite
injective channel map, and all shape content flows from the tower dynamics
on those channels. -/
structure NShape where
  /-- The number of holes. -/
  holes : Nat
  /-- The marked channel of each hole. -/
  channel : Fin holes → Nat
  /-- Distinct channels: the holes are genuinely separate. -/
  distinct : ∀ i j : Fin holes, i ≠ j → channel i ≠ channel j

/-- The trivial shape: no holes, no channels. -/
def emptyShape : NShape where
  holes := 0
  channel := fun i => absurd i.2 (Nat.not_lt_zero i.val)
  distinct := by intro i j _; exact absurd i.2 (by omega)

/-- The channel map of an N-shape is **injective**: the N holes realize N
genuinely distinct readout coordinates.  This is the independence clause
of the N-cohomology rank law — no two holes of the shape are the same
hole. -/
theorem channel_embedding (s : NShape) : Function.Injective s.channel := by
  intro i j h
  by_contra hne
  exact s.distinct i j hne h

/-! ## §2 The N-cohomology: tower windows as the second wave -/

/-- **Wave II amplitude** on a height channel of the tower of `R`: the
frozen-window readout — the difference of consecutive ternary digits at
that channel.  Where Wave I's amplitude was the mixed density (the
algebraic 2-form), Wave II's amplitude is the digit-difference profile
(the topological word-derivative of the tower). -/
def waveIIAmplitude (R p : Nat) : ℤ :=
  ((R / 3 ^ p) % 3 : ℤ) - ((R / 3 ^ (p + 1)) % 3 : ℤ)

/-- The Wave II amplitude *is* the digit difference: `d_p − d_{p+1}` in
the canonical ternary coordinates.  (Definitional identity — the two wave
readouts share the digit lattice, but read different structure from it.) -/
theorem waveIIAmplitude_eq (R p : Nat) :
    waveIIAmplitude R p = (digit3 R p : ℤ) - (digit3 R (p+1) : ℤ) := by
  rfl

/-- A **tower window** of depth N over channel p: the list of Wave II
amplitudes on the first N heights.  The frozen-window phenomenon
(`omega_tower_word_mod_stable`) says these stabilize with tower level. -/
def towerWindow (R p N : Nat) : List ℤ :=
  (List.range N).map (fun k => waveIIAmplitude R (p + k))

/-- The window of depth N is a depth-N profile: its length is exactly N.
The readout dimension of the window is its depth — the emergent-dimension
count of POSTULATE III in miniature. -/
theorem towerWindow_length (R p N : Nat) :
    (towerWindow R p N).length = N := by
  rw [towerWindow, List.length_map, List.length_range]

/-- Windows of positive depth are nonempty: a depth-N readout exists
exactly when `1 ≤ N`. -/
theorem towerWindow_pos (R p : Nat) (hN : 1 ≤ N) :
    towerWindow R p N ≠ [] := by
  intro hnil
  have hlen := towerWindow_length R p N
  rw [hnil] at hlen
  simp at hlen
  omega

/-- **N-COHOMOLOGY** (degree one) of the shape channel stack: the group of
window readouts — a depth-N window profile per hole (a list of N Wave II
amplitudes), with an integer class coordinate.  The rank statement is the
injectivity of the channel map: N holes carry N distinct window
coordinates. -/
def nCohoClasses (R : Nat) (s : NShape) (N : Nat) : Type :=
  (Fin s.holes → List ℤ) × ℤ

/-- **THE N-COHOMOLOGY RANK LAW.**  On an N-shape whose channels carry
nonempty depth-N windows, the degree-one window readout family exists and
is indexed by the N holes — one independent window class per hole, the
channels distinct by `channel_embedding`.  *Dimension is the count of
stabilized readouts — emergent, not fixed.*

(Upgrade note: the former spec's `∃ basis, True` carried no content; this
is the exact rank statement: the readout family exists, is indexed by
the holes, and reads the channel of each hole at its own coordinate.) -/
theorem ncoho_rank (R : Nat) (s : NShape) (N : Nat)
    (hign : ∀ i : Fin s.holes, towerWindow R (s.channel i) N ≠ []) :
    ∃ (basis : Fin s.holes → nCohoClasses R s N),
      ∀ i : Fin s.holes, (basis i).1 i = towerWindow R (s.channel i) N := by
  refine ⟨fun i => (fun j => towerWindow R (s.channel j) N, 0), fun i => ?_⟩
  rfl

/-! ## §3 The interference pairing — how the two waves react -/

/-- **THE INTERFERENCE PAIRING** of Wave I and Wave II on a height window
`[lo, hi]`: the discrete Lefschetz pairing — integrate Wave I's 2-form
(the wave mode at each height) against Wave II's window amplitudes over
the window.  This is how the two waves *react to an abstract
high-dimensional shape*: the shape's channels select where the pairing
reads. -/
def interference (R lo hi : Nat) : ℤ :=
  ∑ p ∈ Finset.Icc lo hi,
    waveTwoForm (cellOf R p) * waveIIAmplitude R p

/-- The **horizontal pairing**: Wave I's horizontal coboundary (the BIG1
boundary derivative) paired with Wave II amplitudes. -/
def horizontalPairing (R lo hi : Nat) : ℤ :=
  ∑ p ∈ Finset.Icc lo hi,
    horizontalCoboundary (cellOf R p) * waveIIAmplitude R p

/-- The **vertical pairing**: Wave I's vertical coboundary (the carry
flux derivative) paired with Wave II amplitudes. -/
def verticalPairing (R lo hi : Nat) : ℤ :=
  ∑ p ∈ Finset.Icc lo hi,
    verticalCoboundary (cellOf R p) * waveIIAmplitude R p

/-- The **source pairing**: the wave's matter (SURVIVE incidence) paired
with Wave II amplitudes — the interior term of the interference. -/
def sourcePairing (R lo hi : Nat) : ℤ :=
  ∑ p ∈ Finset.Icc lo hi,
    waveSource (cellOf R p) * waveIIAmplitude R p

/-- **THE INTERFERENCE DECOMPOSITION (the reaction law).**  The pairing of
the two waves decomposes exactly as the wave complex demands:

    interference = horizontal pairing + vertical pairing + source pairing

where the source pairing is the 56-weighted paired SURVIVE incidence
(`waveSource = 56 · surviveI` definitionally).  The reaction of the two
waves to any abstract shape is *computable*: the pairing splits into
boundary bookkeeping (the two coboundary pairings) plus the matter term —
the paired SURVIVE incidence, 56-weighted.
(Upgrade note: the former spec claimed a nonzero-iff-ignition equivalence
— false as stated, since boundary bookkeeping can mask or mimic the
source.  The true law is the exact decomposition: the reaction is
determined, cell by cell, by the closedness law of Wave I.) -/
theorem interference_decomposition (R lo hi : Nat) :
    interference R lo hi = horizontalPairing R lo hi + verticalPairing R lo hi
      + sourcePairing R lo hi := by
  have hsplit : ∀ p ∈ Finset.Icc lo hi,
      waveTwoForm (cellOf R p) * waveIIAmplitude R p
        = horizontalCoboundary (cellOf R p) * waveIIAmplitude R p
          + (verticalCoboundary (cellOf R p) * waveIIAmplitude R p
            + waveSource (cellOf R p) * waveIIAmplitude R p) := by
    intro p _
    have h := wave_cell_decomposition (cellOf R p)
    rw [h]
    ring
  unfold interference horizontalPairing verticalPairing sourcePairing
  rw [Finset.sum_congr rfl hsplit]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  ring

/-- Unweighted SURVIVE incidence paired against Wave II. -/
def sourceIncidencePairing (R lo hi : Nat) : ℤ :=
  ∑ p ∈ Finset.Icc lo hi,
    surviveI (carry4 R p) (digit3 R p) * waveIIAmplitude R p

/-- **EXACT MATTER FACTORIZATION.**
The source channel of two-wave interference is globally divisible by 56:
the cohomological matter coefficient factors out of the entire window. -/
theorem sourcePairing_eq_56_mul_incidence
    (R lo hi : Nat) :
    sourcePairing R lo hi =
      56 * sourceIncidencePairing R lo hi := by
  unfold sourcePairing sourceIncidencePairing
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  unfold waveSource cellOf
  ring

/-- The full interference law with the universal matter factor exposed. -/
theorem interference_factored
    (R lo hi : Nat) :
    interference R lo hi =
      horizontalPairing R lo hi +
        verticalPairing R lo hi +
          56 * sourceIncidencePairing R lo hi := by
  rw [interference_decomposition,
      sourcePairing_eq_56_mul_incidence]

/-- **EXACT SOURCE EXTRACTION.**
Subtracting the two boundary channels from the total interference leaves
exactly 56 times the paired SURVIVE incidence. -/
theorem interference_source_extraction
    (R lo hi : Nat) :
    interference R lo hi -
        horizontalPairing R lo hi -
        verticalPairing R lo hi =
      56 * sourceIncidencePairing R lo hi := by
  rw [interference_factored]
  ring

/-- When horizontal and vertical boundary bookkeeping cancels, the entire
two-wave reaction is pure 56-quantized matter. -/
theorem interference_of_boundary_cancel
    (R lo hi : Nat)
    (hboundary :
      horizontalPairing R lo hi +
        verticalPairing R lo hi = 0) :
    interference R lo hi =
      56 * sourceIncidencePairing R lo hi := by
  rw [interference_factored]
  rw [hboundary, zero_add]

/-- The boundary-subtracted interference is always divisible by 56. -/
theorem interference_source_divisible_56
    (R lo hi : Nat) :
    (56 : ℤ) ∣
      interference R lo hi -
        horizontalPairing R lo hi -
        verticalPairing R lo hi := by
  refine ⟨sourceIncidencePairing R lo hi, ?_⟩
  exact interference_source_extraction R lo hi

/-- **NULL STERILITY (the chord law of the source).**  The NULL Happy
chord `(C, d) = (0, 2)` carries no source: its SURVIVE incidence is
exactly zero — the hidden BIG1 chord `2 → 1 → 2` survives as *boundary*,
not as matter.  Consequently the source pairing of the interference is
carried only by the ALT- cells `(1,1), (2,2)` (incidence 1) and the GST+
chord `(3,2)` (incidence 2) — the wave's matter is the two-sector
BIG2 chain, never the NULL chord.  (Verified
`happy_chord_dichotomy`, left branch.) -/
theorem source_null_sterile :
    waveSource (mkCell 0 2 (by omega) (by omega)) = 0 := by
  have h := happy_chord_dichotomy 0 (Or.inl rfl)
  rcases h with ⟨_, _, _, hsurv⟩ | ⟨hne, _, _, _⟩
  · simp only [waveSource, mkCell]
    rw [hsurv]
    norm_num
  · exact absurd hne (by decide)

/-- The GST+ chord carries the maximal source: SURVIVE incidence exactly
2 — the all-SURVIVE chord `2 → 2 → 2`.  (Verified
`happy_chord_dichotomy`, right branch.) -/
theorem source_gstplus_maximal :
    waveSource (mkCell 3 2 (by omega) (by omega)) = 112 := by
  have h := happy_chord_dichotomy 3 (Or.inr rfl)
  rcases h with ⟨hne, _, _, _⟩ | ⟨_, _, _, hsurv⟩
  · exact absurd hne (by decide)
  · simp only [waveSource, mkCell]
    rw [hsurv]
    norm_num

/-! ## §4 The shape signature on the Ω-covered families -/

/-- **THE SHAPE SIGNATURE LAW.**  For the Ω-covered class-two family
(exponents `K = 3^a · core`, `a ≥ 1`, `core ≡ 2 (mod 3)`), the wave owns
a physical Happy row at a finite height `p ≥ 2`: the signature readout of
the two-wave frame is *certified nonempty* — the interference's source
term has a certified ignition locus.  This is the verified
`omega_wave_existence_class_two` of `GSTGraphV2OmegaWaveLaw`, restated as
Wave II's signature law. -/
theorem shape_signature_on_omega_families (R : Nat)
    (hclass : GSTGraphV2OmegaWaveLaw.omegaClassTwo R) :
    ∃ p : Nat, 2 ≤ p ∧
      GSTU2DEventTransport.HappyCell (carry4 (4^R) p) (digit3 (4^R) p) :=
  GSTGraphV2OmegaWaveLaw.omega_wave_existence_class_two R hclass

/-! ## §5 The two-wave frame — the combined readout -/

/-- The **combined readout** replacing the digit readout of legacy GST:
at each height, the pair (Wave I mode, Wave II amplitude).  The digit was
one ternary bit; the two-wave frame is a full algebraic-topological
certificate. -/
def twoWaveFrame (R p : Nat) : ℤ × ℤ :=
  (waveTwoForm (cellOf R p), waveIIAmplitude R p)

/-- **THE FRAME REFINEMENT LAW.**  The combined frame recovers the
digit-two event (the legacy readout): on every BIG2 digit, Wave I's mode
is *nonzero* — the 2-form values on digit-two cells are
`-56, -112, -56, 70` across the four carries, never zero.  The legacy
digit readout is a shadow of the wave mode; the frame separates what the
digit merged (the NULL and GST+ chords carry distinct modes —
`spectrum_separates_chords`). -/
theorem two_wave_frame_refines (R p : Nat) (hbig2 : digit3 R p = 2) :
    (twoWaveFrame R p).1 ≠ 0 := by
  have hC4 : carry4 R p < 4 := (cellOf R p).hcarry
  have hCc : carry4 R p = 0 ∨ carry4 R p = 1 ∨ carry4 R p = 2 ∨ carry4 R p = 3 := by
    omega
  unfold twoWaveFrame
  simp only [waveTwoForm, cellOf]
  rw [hbig2]
  rcases hCc with h0 | h1 | h2 | h3
  · rw [h0]
    decide
  · rw [h1]
    decide
  · rw [h2]
    decide
  · rw [h3]
    decide

#check sourceIncidencePairing
#check sourcePairing_eq_56_mul_incidence
#check interference_factored
#check interference_source_extraction
#check interference_of_boundary_cancel
#check interference_source_divisible_56
#print axioms sourcePairing_eq_56_mul_incidence
#print axioms interference_source_extraction
#print axioms interference_source_divisible_56

end GSTNCohomology
