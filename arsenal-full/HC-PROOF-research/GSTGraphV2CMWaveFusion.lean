import GSTGraphV2InformationRecovery
import waves.GSTNCohomologyV3
import GSTGraphV2CMInfiniteCurvatureBridge
import waves.GSTWaveCohomologyV2

/-!
# GST coupled Wave I + Wave II + CM phase on the original seven-axis graph

The seven axes are dimensionless information observations. The historical
twelve physical carry/trit cells have two 5-cycles and two fixed states.
Their complement mirror (C,d) -> (3-C,2-d) exchanges the two five-cycles
and the two fixed states. With a sign constant along each five-cycle but
opposite on its mirrored partner, that mirror induces a *rational*
complex-structure operator J^2=-I on all rational Wave I signals.

The same J COMMUTES with the original information fold U^5=I.

Wave I's ORIGINAL matter/SURVIVE source is a diagonal operator M. It
does NOT commute with J: the wave source breaks the CM parity and hence
creates nonzero structural curvature [J,M]. The combined fold T=U+J+M
is a canonical, exact operator on this symbolic wave cochain space.

This is a wave-level rational CM-compatible representation; a geometric
CM correspondence on the original smooth projective X requires a
separate map respecting the actual cycle class and intersection forms.

Wave II's N-hole shapes are not replaced: their independent hole
coordinates are used below to index arbitrarily many separate
twelve-cell information sectors, with genuine channel selectors.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace GSTGraphV2CMWaveFusion

open GSTGraphV2InformationRecovery
open GST2DMixedEmergence
open GSTWaveCohomology
open GSTNCohomology
open GSTNCohomologyV3

/-- Mirror the original twelve-state information cell, without adding
a spatial dimension. This exchanges the two pentagons of the old vortex. -/
def mirrorCell (s : Cell) : Cell :=
  (⟨3 - s.1.val, by have h := s.1.isLt; omega⟩,
   ⟨2 - s.2.val, by have h := s.2.isLt; omega⟩)

theorem mirror_twice (s : Cell) : mirrorCell (mirrorCell s) = s := by
  rcases s with ⟨c, d⟩
  fin_cases c <;> fin_cases d <;> decide

/-- The mirror and the exact radix fold commute on all twelve cells. -/
theorem mirror_shuffle (s : Cell) :
    mirrorCell (shuffle s) = shuffle (mirrorCell s) := by
  rcases s with ⟨c, d⟩
  fin_cases c <;> fin_cases d <;> decide

/-- One of the two physical 5-cycles together with its zero fixed
state; the complementary six states are the mirrored partner. -/
def positiveCMChannel (s : Cell) : Prop :=
  s.1.val + 4 * s.2.val ∈ ({0, 1, 3, 4, 5, 9} : Finset ℕ)

/-- A rational CM phase, constant under F and reversed by mirror. -/
def cmSign (s : Cell) : ℚ :=
  match s.1.val + 4 * s.2.val with
  | 0 | 1 | 3 | 4 | 5 | 9 => 1
  | _ => -1

theorem cmSign_shuffle (s : Cell) : cmSign (shuffle s) = cmSign s := by
  rcases s with ⟨c, d⟩
  fin_cases c <;> fin_cases d <;>
    norm_num [cmSign, shuffle]

theorem cmSign_mirror_product (s : Cell) :
    cmSign s * cmSign (mirrorCell s) = -1 := by
  rcases s with ⟨c, d⟩
  fin_cases c <;> fin_cases d <;>
    norm_num [cmSign, mirrorCell]

/-- Rationalized Wave I cochains: twelve independent signal coordinates. -/
abbrev WaveSignal := Cell → ℚ

/-- The exact, non-erasing information fold acts by pullback on signals. -/
def U (u : WaveSignal) : WaveSignal :=
  fun s => u (shuffle s)

/-- A complex-structure action created by pairing the two existing
five-cycles and the two existing fixed states. -/
def J (u : WaveSignal) : WaveSignal :=
  fun s => cmSign s * u (mirrorCell s)

/-- Exact finite-order wave information transport U^5=identity. -/
theorem U_five (u : WaveSignal) :
    U (U (U (U (U u)))) = u := by
  funext s
  exact congrArg u (shuffle_five s)

/-- The phase-exchange operator is a true rational complex structure,
without assuming any CM geometry on a projective variety. -/
theorem J_square (u : WaveSignal) : J (J u) = -u := by
  funext s
  change cmSign s * (cmSign (mirrorCell s) *
    u (mirrorCell (mirrorCell s))) = -u s
  rw [mirror_twice, ← mul_assoc, cmSign_mirror_product]
  simp

/-- The information shuffle preserves the CM phase pairing exactly. -/
theorem J_commutes_U (u : WaveSignal) : J (U u) = U (J u) := by
  funext s
  change cmSign s * u (shuffle (mirrorCell s)) =
    cmSign (shuffle s) * u (mirrorCell (shuffle s))
  rw [← mirror_shuffle, cmSign_shuffle]

/-- Each finite information cell really is a native Wave-I cell. -/
def waveCellOf (s : Cell) : GSTWaveCohomology.WaveCell where
  carry := s.1.val
  digit := s.2.val
  hcarry := s.1.isLt
  hdigit := s.2.isLt

/-- Wave I's original exact SURVIVE current, normalized by its fixed
factor 56. This is NOT a chosen artificial parity-breaking field. -/
def sourceMultiplicity (s : Cell) : ℚ :=
  (GST2DMixedEmergence.surviveI s.1.val s.2.val : ℚ)

theorem sourceMultiplicity_is_WaveI (s : Cell) :
    (56 : ℚ) * sourceMultiplicity s =
      (GSTWaveCohomology.waveSource (waveCellOf s) : ℚ) := by
  simp [sourceMultiplicity, GSTWaveCohomology.waveSource,
    waveCellOf, mul_assoc]

/-- Multiply by the actual Wave-I matter source, one cell at a time. -/
def M (u : WaveSignal) : WaveSignal :=
  fun s => sourceMultiplicity s * u s

/-- One mixed source combining an axial information state and a
rotating state; both are original GST information cells. -/
def seed : WaveSignal :=
  fun s => if s = ((0 : Fin 4), (0 : Fin 3)) ∨
              s = ((0 : Fin 4), (1 : Fin 3)) then 1 else 0

/-- Exact wave-source test at the GST+ fixed cell. -/
theorem source_on_positive_fixed :
    sourceMultiplicity ((3 : Fin 4), (2 : Fin 3)) = 2 := by
  norm_num [sourceMultiplicity, surviveI, midDigit,
    finalMicroDigit, microOutput, highBit, lowBit, twoI]

theorem source_on_null_fixed :
    sourceMultiplicity ((0 : Fin 4), (0 : Fin 3)) = 0 := by
  norm_num [sourceMultiplicity, surviveI, midDigit,
    finalMicroDigit, microOutput, highBit, lowBit, twoI]

/-- Native Wave-I source breaks the otherwise commuting (U,J)
information symmetry. This provides an ACTUAL wave-level CM curvature
rather than merely assuming a noncommuting operator exists. -/
theorem wave_source_CM_curvature_nonzero :
    (J (M seed)) ((3 : Fin 4), (2 : Fin 3)) -
       (M (J seed)) ((3 : Fin 4), (2 : Fin 3)) = 2 := by
  norm_num [J, M, seed, cmSign, mirrorCell,
    sourceMultiplicity, surviveI, midDigit,
    finalMicroDigit, microOutput, highBit, lowBit, twoI]

/-- The single fully coupled information–CM–wave fold. -/
def T (u : WaveSignal) : WaveSignal :=
  fun s => U u s + J u s + M u s

/-- Finite algebraic Krylov iteration of the ACTUAL combined fold. -/
def orbit : ℕ → WaveSignal
  | 0 => seed
  | n+1 => T (orbit n)

/-- The exact 12x12 Krylov matrix, to be checked using an independent
integer certificate. This is the matrix used in the Wolfram audit. -/
def orbitMatrix : Matrix Cell (Fin 12) ℚ :=
  fun s k => orbit k.val s

/-- Wave II provides arbitrarily many independently addressed holes;
each hole has its own full Wave-I/CM signal, without a fixed dimension
limit in the ambient ontology. -/
abbrev HoleWaveSignals (s : NShape) := Fin s.holes → WaveSignal

def holeU (s : NShape) (u : HoleWaveSignals s) :
    HoleWaveSignals s := fun i => U (u i)

def holeJ (s : NShape) (u : HoleWaveSignals s) :
    HoleWaveSignals s := fun i => J (u i)

def holeT (s : NShape) (u : HoleWaveSignals s) :
    HoleWaveSignals s := fun i => T (u i)

/-- Original information periodicity is preserved at EVERY wave-II
hole simultaneously, with no imposed bound on hole count. -/
theorem holeU_five (s : NShape) (u : HoleWaveSignals s) :
    holeU s (holeU s (holeU s (holeU s (holeU s u)))) = u := by
  funext i
  exact U_five (u i)

/-- Independent N-hole channel selector; no two holes are identified. -/
def channel (s : NShape) (i : Fin s.holes) (u : WaveSignal) :
    HoleWaveSignals s := fun j => if i = j then u else 0

theorem channel_value (s : NShape) (i : Fin s.holes)
    (u : WaveSignal) :
    channel s i u i = u := by
  simp [channel]

#check GSTNCohomologyV3.independentHoleBasis_reconstruct
#check GSTNCohomologyV2.weighted_interference_decomposition
#check GSTGraphV2InformationRecovery.canonical_vertex_information_step
#check GSTGraphV2CMInfiniteCurvatureBridge.informationCMCurvature_five_sum_zero
#check J_square
#check J_commutes_U
#check wave_source_CM_curvature_nonzero
#check orbitMatrix
#print axioms J_square
#print axioms wave_source_CM_curvature_nonzero

end GSTGraphV2CMWaveFusion
