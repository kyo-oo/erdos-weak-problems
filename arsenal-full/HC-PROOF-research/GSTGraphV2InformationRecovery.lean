import GSTCanonicalSevenAxisBridge
import Mathlib

/-!
# GST seven-axis arithmetic: exact information recovery and five-cycle law

The original x4/base3 carry/trit edge has twelve physically admissible
local states, not merely three trit values.  **Both** output trit and
regenerated carry are required to retain the complete local information.

This module proves:
* the radix-transform has a concrete inverse on all 12 physical cells;
* it is a permutation of order FIVE (two 5-cycles and two fixed points);
* the source is recovered exactly, with no lossy projection;
* pointwise extension to infinite streams is still exactly reversible,
  with the same 5-period law at every information depth;
* the original GST seven-axis arithmetic vertex is connected to this
  finite local law using the existing canonical-cell theorems.

The finite rank/period describes **information state transformation**.
It does not assign five geometric dimensions, a metric, or a spatial
geometry to a General Space.
-/

namespace GSTGraphV2InformationRecovery

open GSTCanonicalSevenAxisBridge
open GST2DMixedEmergence

/-- The true 12-state physical cell, retaining the carry and trit together. -/
abbrev Cell := Fin 4 × Fin 3

/-- The GST x4/base3 transformation, with the regenerated carry and trit. -/
def shuffle (s : Cell) : Cell :=
  (⟨(s.1.val + 4 * s.2.val) / 3, by
      have hC := s.1.isLt
      have hd := s.2.isLt
      omega⟩,
   ⟨(s.1.val + 4 * s.2.val) % 3, Nat.mod_lt _ (by omega)⟩)

/-- Exact inverse radix decomposition: the output was NOT an erasure. -/
def unshuffle (s : Cell) : Cell :=
  (⟨(s.2.val + 3 * s.1.val) % 4, Nat.mod_lt _ (by omega)⟩,
   ⟨(s.2.val + 3 * s.1.val) / 4, by
      have hC := s.1.isLt
      have hd := s.2.isLt
      omega⟩)

/-- Recover every carry and trit from the output, without a lost bit. -/
theorem unshuffle_shuffle (s : Cell) : unshuffle (shuffle s) = s := by
  rcases s with ⟨c,d⟩
  fin_cases c <;> fin_cases d <;> decide

/-- Every admissible output comes from exactly one admissible input. -/
theorem shuffle_unshuffle (s : Cell) : shuffle (unshuffle s) = s := by
  rcases s with ⟨c,d⟩
  fin_cases c <;> fin_cases d <;> decide

/-- The original 12-state transformation is an equivalence, not merely
a map preserving an arbitrary externally postulated information label. -/
def shuffleEquiv : Cell ≃ Cell where
  toFun := shuffle
  invFun := unshuffle
  left_inv := unshuffle_shuffle
  right_inv := shuffle_unshuffle

/-- Each five-fold local x4/base3 information transformation returns exactly
to its first carry and trit. -/
theorem shuffle_five (s : Cell) :
    shuffle (shuffle (shuffle (shuffle (shuffle s)))) = s := by
  rcases s with ⟨c,d⟩
  fin_cases c <;> fin_cases d <;> decide

/-- Zero is a fixed information state. -/
theorem null_zero_fixed :
    shuffle ((0 : Fin 4), (0 : Fin 3)) = ((0 : Fin 4), (0 : Fin 3)) := by
  decide

/-- The maximal carry and maximal trit are also a fixed information state. -/
theorem max_information_fixed :
    shuffle ((3 : Fin 4), (2 : Fin 3)) = ((3 : Fin 4), (2 : Fin 3)) := by
  decide

/-- The five-cycle law is nontrivial: it is not a one-step identity. -/
theorem shuffle_nontrivial :
    shuffle ((0 : Fin 4), (1 : Fin 3)) ≠ ((0 : Fin 4), (1 : Fin 3)) := by
  decide

/-- A genuinely infinite-depth information history: there is NO last
position or finite truncation in the carrier. -/
abbrev InfiniteInformation := Nat → Cell

/-- A simultaneous GST fold of every information cell. -/
def streamFold (u : InfiniteInformation) : InfiniteInformation :=
  fun n => shuffle (u n)

/-- An inverse fold exists simultaneously at every depth. -/
def streamReturn (u : InfiniteInformation) : InfiniteInformation :=
  fun n => unshuffle (u n)

/-- Infinite-depth information reconstruction. -/
theorem streamReturn_streamFold (u : InfiniteInformation) :
    streamReturn (streamFold u) = u := by
  funext n
  exact unshuffle_shuffle (u n)

/-- The reverse orientation is equally lossless. -/
theorem streamFold_streamReturn (u : InfiniteInformation) :
    streamFold (streamReturn u) = u := by
  funext n
  exact shuffle_unshuffle (u n)

/-- No finite depth was selected: five repeated folds return the
**entire** infinite information stream, not merely an observation window. -/
theorem streamFold_five (u : InfiniteInformation) :
    streamFold (streamFold (streamFold (streamFold (streamFold u)))) = u := by
  funext n
  exact shuffle_five (u n)

/-- The finite state calculation uses the exact legacy seven-axis
GST digit/carry law, not a replaced arithmetic simulator. -/
theorem shuffle_legacy_coordinates (c : Fin 4) (d : Fin 3) :
    (shuffle (c,d)).1.val = nextCarry c.val d.val ∧
    (shuffle (c,d)).2.val = outDigit c.val d.val := by
  constructor <;> rfl

/-- Each original energy/time/depth cell transforms by this exact
information-preserving local permutation. The next carry is a VERTICAL
observation; the outgoing digit is a HORIZONTAL observation. -/
theorem canonical_vertex_information_step (E t p : Nat) :
    ∃ (c : Fin 4) (d : Fin 3),
      c.val = (vertex E t p).carry ∧
      d.val = (vertex E t p).digit ∧
      (shuffle (c,d)).1.val = (vertex E t (p+1)).carry ∧
      (shuffle (c,d)).2.val = (vertex E (t+1) p).digit := by
  have hc := vertex_carry_lt_four E t p
  have hd := vertex_digit_lt_three E t p
  refine ⟨⟨(vertex E t p).carry, hc⟩, ⟨(vertex E t p).digit, hd⟩,
    rfl, rfl, ?_, ?_⟩
  · exact (canonical_cell_exact E t p).2
  · exact (canonical_cell_exact E t p).1

#check shuffleEquiv
#check unshuffle_shuffle
#check shuffle_five
#check streamReturn_streamFold
#check streamFold_five
#check canonical_vertex_information_step
#print axioms shuffle_five
#print axioms streamFold_five

end GSTGraphV2InformationRecovery
