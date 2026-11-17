import GSTCanonicalSevenAxisBridge
import GSTU2DAtomicBridge

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace GSTGraphV2InfiniteControl

open GSTCanonicalSevenAxisBridge
open GST2DMixedEmergence
open GSTU2DEventTransport
open GSTU2DExactCrossingCharge
open GSTGraphV2CoupledUFlux

/-!
# Main infinite GST V2 control graph

This module does not replace the canonical graph by a finite rectangle.  The
primary object is a function on every horizontal x4 coordinate and every
vertical ternary information coordinate.  Finite rectangles are observations
of that one infinite object.

The seven arithmetic state axes and the three physical GST spaces are retained
inside `Vertex`; the already-green U, mixed-emergence, event and crossing
charges are attached as additional observables of the same vertex.
-/

/-- One enriched cell of the main infinite GST V2 graph. -/
structure InfiniteCell where
  seven : GSTCanonicalSevenAxisBridge.Vertex
  eventCode : Nat
  uCharge : Int
  mixedCharge : Int
  crossingCharge : Int
  survive : Int
  deriving Repr

/-- Enrich one canonical seven-axis vertex with all green charge observables. -/
def cell (E t p : Nat) : InfiniteCell :=
  let v := GSTCanonicalSevenAxisBridge.vertex E t p
  {
    seven := v
    eventCode := GSTCanonicalSevenAxisBridge.event v.carry v.digit
    uCharge := gstUChargeExact v.carry
    mixedCharge := mixedDensity v.carry v.digit
    crossingCharge := crossDensity v.carry v.digit
    survive := surviveI v.carry v.digit
  }

/-- The main graph is genuinely all-depth in both arithmetic directions. -/
def graph (E : Nat) : Nat → Nat → InfiniteCell :=
  fun t p => cell E t p

/-- Every cell of the enriched graph obeys the exact x4/base3 lattice law. -/
theorem graph_cell_exact (E t p : Nat) :
    outDigit (graph E t p).seven.carry (graph E t p).seven.digit =
        (graph E (t+1) p).seven.digit ∧
      nextCarry (graph E t p).seven.carry (graph E t p).seven.digit =
        (graph E t (p+1)).seven.carry := by
  simpa [graph, cell] using
    GSTCanonicalSevenAxisBridge.canonical_cell_exact E t p

/-- Every graph carry is one of the four physical GST carry states. -/
theorem graph_carry_lt_four (E t p : Nat) :
    (graph E t p).seven.carry < 4 := by
  simpa [graph, cell] using
    GSTCanonicalSevenAxisBridge.vertex_carry_lt_four E t p

/-- Every graph information coordinate is one ternary digit. -/
theorem graph_digit_lt_three (E t p : Nat) :
    (graph E t p).seven.digit < 3 := by
  simpa [graph, cell] using
    GSTCanonicalSevenAxisBridge.vertex_digit_lt_three E t p

/-- Happy is event eight on the main infinite graph. -/
theorem graph_happy_iff_event_eight (E t p : Nat) :
    HappyCell (graph E t p).seven.carry (graph E t p).seven.digit ↔
      (graph E t p).eventCode = 8 := by
  simpa [graph, cell] using
    GSTCanonicalSevenAxisBridge.canonical_happy_iff_event_eight E t p

/-- Happy is equivalently positive exact crossing charge on the same cell. -/
theorem graph_happy_iff_crossing_positive (E t p : Nat) :
    HappyCell (graph E t p).seven.carry (graph E t p).seven.digit ↔
      0 < (graph E t p).crossingCharge := by
  dsimp [graph, cell]
  exact GSTU2DExactCrossingCharge.happy_iff_crossDensity_positive _ _
    (GSTCanonicalSevenAxisBridge.vertex_carry_lt_four E t p)
    (GSTCanonicalSevenAxisBridge.vertex_digit_lt_three E t p)

/-- The event-balance equation is available at every cell of the main graph. -/
theorem graph_event_balance_exact (E t p : Nat) :
    (graph E t p).eventCode +
        9 * nextCarry (graph E t p).seven.carry (graph E t p).seven.digit =
      13 * (graph E t p).seven.digit + 3 * (graph E t p).seven.carry := by
  simpa [graph, cell] using
    GSTCanonicalSevenAxisBridge.event_balance_exact
      (GSTCanonicalSevenAxisBridge.vertex E t p).carry
      (GSTCanonicalSevenAxisBridge.vertex E t p).digit

/-- Exact crossing-charge conservation on every observed rectangle of the one
infinite graph.  `K` is not a support horizon: the upper carry boundary remains
explicit and the theorem holds for every `K : Nat`. -/
theorem graph_cross_rectangle_exact (E N K : Nat) :
    Finset.sum (Finset.range K) (fun p =>
      (((3^p : Nat) : Int)) *
        reverseCrossCode
          (fun t => (graph E t p).seven.carry)
          (fun t => (graph E t p).seven.digit) N) =
      Finset.sum (Finset.range K) (fun p =>
        (((3^p : Nat) : Int)) *
          (digitPotential (graph E N p).seven.digit -
            (((4^N : Nat) : Int)) * digitPotential (graph E 0 p).seven.digit +
            84 * reverseSurviveCode
              (fun t => (graph E t p).seven.carry)
              (fun t => (graph E t p).seven.digit) N)) +
      reverseCarryCode (fun t => (graph E t 0).seven.carry) N -
        (((3^K : Nat) : Int)) *
          reverseCarryCode (fun t => (graph E t K).seven.carry) N := by
  apply GSTU2DExactCrossingCharge.reverseCrossRectangle_exact
  intro t p _ht _hp
  exact ⟨graph_carry_lt_four E t p,
    graph_digit_lt_three E t p,
    (graph_cell_exact E t p).1,
    (graph_cell_exact E t p).2⟩

/-! ## Exact full-energy prefix-slice projection

These lemmas are the critical production socket.  They keep the low canonical
prefix instead of replacing a full energy by the exposed tail.  A slice of
`P + 3^b * tail` at vertical coordinate `b+q` therefore reads the tail
information digit together with the correct seeded x4 carry.
-/

/-- Seeded x4 carry used by a full-energy prefix slice. -/
def seededCarry (seed tail q : Nat) : Nat :=
  (seed + 4 * (tail % 3^q)) / 3^q

/-- The shifted quotient of an exact prefix/tail decomposition is the tail
quotient. -/
theorem prefix_slice_quotient_exact
    (b P tail q : Nat)
    (hP : P < 3^b) :
    (P + 3^b * tail) / 3^(b+q) = tail / 3^q := by
  have hp : 0 < 3^b := Nat.pow_pos (by decide)
  rw [pow_add, ← Nat.div_div_eq_div_mul]
  rw [Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt hP, Nat.zero_add]

/-- The information digit on the full-energy slice is literally the tail digit. -/
theorem prefix_slice_digit_exact
    (b P tail q : Nat)
    (hP : P < 3^b) :
    digit3 (P + 3^b * tail) (b+q) = digit3 tail q := by
  unfold digit3
  rw [prefix_slice_quotient_exact b P tail q hP]

/-- The low prefix of an exact decomposition is recovered modulo its ternary
place. -/
private theorem prefix_mod_exact
    (b P tail : Nat)
    (hP : P < 3^b) :
    (P + 3^b * tail) % 3^b = P := by
  simpa [Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt hP]

/-- The full remainder at the deeper slice retains the low prefix and only the
visible tail remainder. -/
private theorem prefix_deep_mod_exact
    (b P tail q : Nat)
    (hP : P < 3^b) :
    (P + 3^b * tail) % (3^b * 3^q) =
      P + 3^b * (tail % 3^q) := by
  rw [Nat.mod_mul]
  rw [prefix_mod_exact b P tail hP]
  have hp : 0 < 3^b := Nat.pow_pos (by decide)
  have hdiv : (P + 3^b * tail) / 3^b = tail := by
    rw [Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt hP, Nat.zero_add]
  rw [hdiv]

/-- Exact seeded carry projection.  The seed is not assumed: it is generated
by the canonical low prefix as `floor(4*P / 3^b)`. -/
theorem prefix_slice_carry_exact
    (b P tail q : Nat)
    (hP : P < 3^b) :
    carry4 (P + 3^b * tail) (b+q) =
      seededCarry ((4 * P) / 3^b) tail q := by
  unfold carry4 seededCarry
  rw [pow_add]
  rw [prefix_deep_mod_exact b P tail q hP]
  rw [← Nat.div_div_eq_div_mul]
  have hp : 0 < 3^b := Nat.pow_pos (by decide)
  have hshape :
      4 * (P + 3^b * (tail % 3^q)) =
        4 * P + 3^b * (4 * (tail % 3^q)) := by ring
  rw [hshape, Nat.add_mul_div_left _ _ hp]

/-- Seed-zero specialization: a prefix whose fourfold copy remains below the
slice modulus exposes the ordinary child carry. -/
theorem prefix_slice_seed_zero
    (b P tail q : Nat)
    (hP : P < 3^b)
    (hseed : 4 * P < 3^b) :
    carry4 (P + 3^b * tail) (b+q) = seededCarry 0 tail q := by
  rw [prefix_slice_carry_exact b P tail q hP]
  have hz : (4 * P) / 3^b = 0 := Nat.div_eq_of_lt hseed
  rw [hz]

/-- Seed-one specialization: when the fourfold low prefix lies in the first
nonzero ternary slice, the same full-energy graph exposes a seed-one parent. -/
theorem prefix_slice_seed_one
    (b P tail q : Nat)
    (hP : P < 3^b)
    (hlo : 3^b ≤ 4 * P)
    (hhi : 4 * P < 2 * 3^b) :
    carry4 (P + 3^b * tail) (b+q) = seededCarry 1 tail q := by
  rw [prefix_slice_carry_exact b P tail q hP]
  have hp : 0 < 3^b := Nat.pow_pos (by decide)
  have hlo' : 1 ≤ (4 * P) / 3^b := by
    exact (Nat.le_div_iff_mul_le hp).2 (by simpa using hlo)
  have hhi' : (4 * P) / 3^b < 2 := by
    exact (Nat.div_lt_iff_lt_mul hp).2 (by simpa using hhi)
  have hone : (4 * P) / 3^b = 1 := by omega
  rw [hone]

/-- Literal graph form of the prefix-slice socket.  Any exact decomposition of
the horizontal full energy gives both the tail trit and the prefix-generated
seeded carry at the corresponding vertical slice. -/
theorem graph_prefix_slice_exact
    (E t b P tail q : Nat)
    (hE : 4^t * E = P + 3^b * tail)
    (hP : P < 3^b) :
    (graph E t (b+q)).seven.digit = digit3 tail q ∧
      (graph E t (b+q)).seven.carry =
        seededCarry ((4 * P) / 3^b) tail q := by
  constructor
  · change digit3 (4^t * E) (b+q) = digit3 tail q
    rw [hE]
    exact prefix_slice_digit_exact b P tail q hP
  · change carry4 (4^t * E) (b+q) =
      seededCarry ((4 * P) / 3^b) tail q
    rw [hE]
    exact prefix_slice_carry_exact b P tail q hP

/-- On a literal full-energy slice, Happy/event-eight is exactly the seeded
Happy predicate of the exposed tail.  This is the production adapter used by
Atomic Surgery V2; no tail-only horizontal surrogate is introduced. -/
theorem graph_prefix_slice_happy_iff
    (E t b P tail q : Nat)
    (hE : 4^t * E = P + 3^b * tail)
    (hP : P < 3^b) :
    HappyCell
        (graph E t (b+q)).seven.carry
        (graph E t (b+q)).seven.digit ↔
      digit3 tail q = 2 ∧
        (seededCarry ((4 * P) / 3^b) tail q = 0 ∨
         seededCarry ((4 * P) / 3^b) tail q = 3) := by
  have hslice := graph_prefix_slice_exact E t b P tail q hE hP
  unfold HappyCell
  rw [hslice.1, hslice.2]

end GSTGraphV2InfiniteControl
