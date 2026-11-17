import GSTGraphV2CanonicalEscape
import GSTGraphV2CanonicalSheetTranslation
import GSTGraphV2CanonicalPhaseWaveProbe

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTGraphV2CanonicalNWave

open GSTCanonicalSevenAxisBridge
open GSTGraphV2InfiniteControl
open GSTGraphV2PerfectPowerBlock
open GSTGraphV2CanonicalEscape
open GSTGraphV2HandwrittenExponentialCascade
open GSTU2DEventTransport

/-- Horizontal phase accumulated after stripping an arbitrary number of
origin trits. -/
def nWaveShift (s n K : Nat) : Nat :=
  uPhaseShift (s+1) n K

/-- Residual canonical energy after the same arbitrary strip. -/
def nWaveEnergy (s n K : Nat) : Nat :=
  uTailEnergy (s+1) n K

/-- Exact all-K Graph-V2 wave identification. -/
theorem canonical_n_wave_physical
    (s n K x p : Nat) :
    (graph (canonicalEnergy s n) x p).seven.carry =
        (graph (nWaveEnergy s n K) (nWaveShift s n K + x) p).seven.carry ∧
    (graph (canonicalEnergy s n) x p).seven.digit =
        (graph (nWaveEnergy s n K) (nWaveShift s n K + x) p).seven.digit := by
  simpa [nWaveEnergy, nWaveShift] using
    canonical_graph_u_cut_recoordinate_exact s n K x p

/-- Happy observables transport through every layer of the n-wave. -/
theorem canonical_n_wave_happy_iff
    (s n K x p : Nat) :
    HappyCell
        (graph (canonicalEnergy s n) x p).seven.carry
        (graph (canonicalEnergy s n) x p).seven.digit ↔
      HappyCell
        (graph (nWaveEnergy s n K) (nWaveShift s n K + x) p).seven.carry
        (graph (nWaveEnergy s n K) (nWaveShift s n K + x) p).seven.digit := by
  have h := canonical_n_wave_physical s n K x p
  rw [h.1, h.2]

/-- An all-depth bad boundary is transported, without truncation, through
every finite n-wave layer. -/
theorem canonical_n_wave_bad_trace_iff
    (s n K x b : Nat) :
    (∀ j, ¬ HappyCell
        (graph (canonicalEnergy s n) x (b+j)).seven.carry
        (graph (canonicalEnergy s n) x (b+j)).seven.digit) ↔
      (∀ j, ¬ HappyCell
        (graph (nWaveEnergy s n K) (nWaveShift s n K + x) (b+j)).seven.carry
        (graph (nWaveEnergy s n K) (nWaveShift s n K + x) (b+j)).seven.digit) := by
  constructor <;> intro h j hj
  · exact h j ((canonical_n_wave_happy_iff s n K x (b+j)).mpr hj)
  · exact h j ((canonical_n_wave_happy_iff s n K x (b+j)).mp hj)

/-- Exact transport of the complete collision packet through an arbitrary
number of canonical phase-wave layers.  The accumulated horizontal phase is
retained explicitly and the observed strip keeps its literal width; no false
reset to horizontal origin zero is performed. -/
theorem canonical_n_wave_strip_packet_iff
    (s n K x b q : Nat) :
    (HappyCell
        (graph (canonicalEnergy s n) x (b+q)).seven.carry
        (graph (canonicalEnergy s n) x (b+q)).seven.digit ∧
      ∀ j, ¬ HappyCell
        (graph (canonicalEnergy s n) (x + canonicalWidth s) (b+j)).seven.carry
        (graph (canonicalEnergy s n) (x + canonicalWidth s) (b+j)).seven.digit) ↔
    (HappyCell
        (graph (nWaveEnergy s n K) (nWaveShift s n K + x) (b+q)).seven.carry
        (graph (nWaveEnergy s n K) (nWaveShift s n K + x) (b+q)).seven.digit ∧
      ∀ j, ¬ HappyCell
        (graph (nWaveEnergy s n K)
          (nWaveShift s n K + (x + canonicalWidth s)) (b+j)).seven.carry
        (graph (nWaveEnergy s n K)
          (nWaveShift s n K + (x + canonicalWidth s)) (b+j)).seven.digit) := by
  constructor
  · rintro ⟨hChild, hRightBad⟩
    exact ⟨
      (canonical_n_wave_happy_iff s n K x (b+q)).mp hChild,
      (canonical_n_wave_bad_trace_iff
        s n K (x + canonicalWidth s) b).mp hRightBad⟩
  · rintro ⟨hChild, hRightBad⟩
    exact ⟨
      (canonical_n_wave_happy_iff s n K x (b+q)).mpr hChild,
      (canonical_n_wave_bad_trace_iff
        s n K (x + canonicalWidth s) b).mpr hRightBad⟩

/-- At a cutoff exhausting the origin, the arbitrary n-wave is literally a
translated unit-energy Graph-V2 sheet. -/
theorem canonical_n_wave_terminal_energy
    (s n K : Nat) (hK : n / 3^K = 0) :
    nWaveEnergy s n K = 1 := by
  simp [nWaveEnergy, uTailEnergy, uTailExponent, originSuffix, hK]

/-- Once the finite origin has been exhausted, the complete collision packet
is a literal shifted strip of the unit-energy graph.  Both the Happy gate and
the all-depth bad boundary survive the specialization exactly. -/
theorem canonical_n_wave_terminal_strip_packet_iff
    (s n K x b q : Nat) (hK : n / 3^K = 0) :
    (HappyCell
        (graph (canonicalEnergy s n) x (b+q)).seven.carry
        (graph (canonicalEnergy s n) x (b+q)).seven.digit ∧
      ∀ j, ¬ HappyCell
        (graph (canonicalEnergy s n) (x + canonicalWidth s) (b+j)).seven.carry
        (graph (canonicalEnergy s n) (x + canonicalWidth s) (b+j)).seven.digit) ↔
    (HappyCell
        (graph 1 (nWaveShift s n K + x) (b+q)).seven.carry
        (graph 1 (nWaveShift s n K + x) (b+q)).seven.digit ∧
      ∀ j, ¬ HappyCell
        (graph 1 (nWaveShift s n K + (x + canonicalWidth s)) (b+j)).seven.carry
        (graph 1 (nWaveShift s n K + (x + canonicalWidth s)) (b+j)).seven.digit) := by
  have h := canonical_n_wave_strip_packet_iff s n K x b q
  rw [canonical_n_wave_terminal_energy s n K hK] at h
  exact h

#check canonical_n_wave_physical
#check canonical_n_wave_happy_iff
#check canonical_n_wave_bad_trace_iff
#check canonical_n_wave_strip_packet_iff
#check canonical_n_wave_terminal_energy
#check canonical_n_wave_terminal_strip_packet_iff
#print axioms canonical_n_wave_bad_trace_iff
#print axioms canonical_n_wave_strip_packet_iff
#print axioms canonical_n_wave_terminal_strip_packet_iff

-- Kernel trigger after sheet-translation closure.
end GSTGraphV2CanonicalNWave
