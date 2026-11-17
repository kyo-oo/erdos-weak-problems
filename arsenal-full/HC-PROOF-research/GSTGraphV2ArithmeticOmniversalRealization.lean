import GSTGraphV2OmniversalCore
import GSTGraphV2InfiniteControl
import GST2DMixedEmergence

/-!
# GST GRAPH V2 — ARITHMETIC REALIZATION OF THE OMNIVERSAL EVENT CORE

The new omniversal graph does not discard the original x4/base3 mathematics.
Instead the historical number-theoretic lattice becomes one exact realization
of the carrier-agnostic three-sector event ontology.

A node remembers energy, horizontal time, and vertical information depth.
Horizontal and vertical successor events are genuine primitive events.  The
legacy seven-axis vertex, carry, digit, event code, and charge observables are
then read from that node exactly as before.
-/

namespace GSTGraphV2ArithmeticOmniversalRealization

open GSTGraphV2OmniversalCore
open GSTCanonicalSevenAxisBridge
open GST2DMixedEmergence

/-- Exact translation of the historical three physical spaces into the new
carrier-independent three-sector ontology. -/
def legacySector : GSTCanonicalSevenAxisBridge.Space →
    GSTGraphV2OmniversalCore.Sector
  | .null => .null
  | .altMinus => .altMinus
  | .gstPlus => .gstPlus

/-- One coordinate address in the historical infinite arithmetic realization. -/
structure ArithmeticNode where
  energy : Nat
  time : Nat
  depth : Nat
  deriving Repr, DecidableEq

/-- Primitive arithmetic causal events.  They are merely one realization of
`OmniversalGraph.Event`; the omniversal core itself knows nothing about Nat. -/
inductive ArithmeticEvent : ArithmeticNode → ArithmeticNode → Prop
  | horizontal (E t p : Nat) :
      ArithmeticEvent
        ⟨E, t, p⟩
        ⟨E, t + 1, p⟩
  | vertical (E t p : Nat) :
      ArithmeticEvent
        ⟨E, t, p⟩
        ⟨E, t, p + 1⟩

/-- The complete legacy arithmetic lattice as one omniversal realization. -/
def arithmeticOmniversalGraph : OmniversalGraph where
  Node := ArithmeticNode
  sector n := legacySector
    (GSTCanonicalSevenAxisBridge.vertex n.energy n.time n.depth).space
  Event := ArithmeticEvent

/-- Recover the exact historical seven-axis state from an omniversal arithmetic
node. -/
def sevenAxisState (n : ArithmeticNode) : GSTCanonicalSevenAxisBridge.Vertex :=
  GSTCanonicalSevenAxisBridge.vertex n.energy n.time n.depth

/-- Recover the already-established enriched infinite-control cell. -/
def enrichedCell (n : ArithmeticNode) : GSTGraphV2InfiniteControl.InfiniteCell :=
  GSTGraphV2InfiniteControl.graph n.energy n.time n.depth

@[simp]
theorem sector_exact (E t p : Nat) :
    arithmeticOmniversalGraph.sector ⟨E,t,p⟩ =
      legacySector (GSTCanonicalSevenAxisBridge.vertex E t p).space := rfl

@[simp]
theorem sevenAxisState_exact (E t p : Nat) :
    sevenAxisState ⟨E,t,p⟩ =
      GSTCanonicalSevenAxisBridge.vertex E t p := rfl

@[simp]
theorem enrichedCell_exact (E t p : Nat) :
    enrichedCell ⟨E,t,p⟩ =
      GSTGraphV2InfiniteControl.graph E t p := rfl

/-- Every historical horizontal x4 update is literally an omniversal event. -/
theorem horizontal_is_event (E t p : Nat) :
    arithmeticOmniversalGraph.Event
      (⟨E,t,p⟩ : ArithmeticNode)
      ⟨E,t+1,p⟩ :=
  ArithmeticEvent.horizontal E t p

/-- Every historical vertical base3 information update is literally an
omniversal event. -/
theorem vertical_is_event (E t p : Nat) :
    arithmeticOmniversalGraph.Event
      (⟨E,t,p⟩ : ArithmeticNode)
      ⟨E,t,p+1⟩ :=
  ArithmeticEvent.vertical E t p

/-- The arithmetic content of a horizontal omniversal event is still the exact
legacy output-digit law. -/
theorem horizontal_digit_exact (E t p : Nat) :
    outDigit
        (sevenAxisState ⟨E,t,p⟩).carry
        (sevenAxisState ⟨E,t,p⟩).digit =
      (sevenAxisState ⟨E,t+1,p⟩).digit := by
  exact (GSTCanonicalSevenAxisBridge.canonical_cell_exact E t p).1

/-- The arithmetic content of a vertical omniversal event is still the exact
legacy carry-regeneration law. -/
theorem vertical_carry_exact (E t p : Nat) :
    nextCarry
        (sevenAxisState ⟨E,t,p⟩).carry
        (sevenAxisState ⟨E,t,p⟩).digit =
      (sevenAxisState ⟨E,t,p+1⟩).carry := by
  exact (GSTCanonicalSevenAxisBridge.canonical_cell_exact E t p).2

/-- Every primitive arithmetic event enters the generic causal closure. -/
theorem arithmetic_event_reachable
    {x y : ArithmeticNode}
    (e : arithmeticOmniversalGraph.Event x y) :
    OmniversalGraph.Reachable arithmeticOmniversalGraph x y :=
  OmniversalGraph.reachable_of_event arithmeticOmniversalGraph e

/-- Legacy arithmetic realization crown: both exact native update directions
are embedded in the new event ontology without changing their mathematics. -/
theorem arithmetic_realization_crown :
    (∀ E t p,
      arithmeticOmniversalGraph.Event
        (⟨E,t,p⟩ : ArithmeticNode) ⟨E,t+1,p⟩)
    ∧ (∀ E t p,
      arithmeticOmniversalGraph.Event
        (⟨E,t,p⟩ : ArithmeticNode) ⟨E,t,p+1⟩)
    ∧ (∀ E t p,
      outDigit
          (sevenAxisState ⟨E,t,p⟩).carry
          (sevenAxisState ⟨E,t,p⟩).digit =
        (sevenAxisState ⟨E,t+1,p⟩).digit)
    ∧ (∀ E t p,
      nextCarry
          (sevenAxisState ⟨E,t,p⟩).carry
          (sevenAxisState ⟨E,t,p⟩).digit =
        (sevenAxisState ⟨E,t,p+1⟩).carry) := by
  exact ⟨horizontal_is_event, vertical_is_event,
    horizontal_digit_exact, vertical_carry_exact⟩

#check legacySector
#check ArithmeticNode
#check ArithmeticEvent
#check arithmeticOmniversalGraph
#check sevenAxisState
#check enrichedCell
#check horizontal_digit_exact
#check vertical_carry_exact
#check arithmetic_event_reachable
#check arithmetic_realization_crown

end GSTGraphV2ArithmeticOmniversalRealization
