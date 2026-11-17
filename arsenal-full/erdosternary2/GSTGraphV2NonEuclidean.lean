import GSTGraphV2InfiniteControl
import GSTGraphV2HandwrittenExponentialCascade

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace GSTGraphV2NonEuclidean

open GSTCanonicalSevenAxisBridge
open GSTGraphV2InfiniteControl

/-!
# True GST Graph V2

The ambient GST object is not a Euclidean two-dimensional lattice.  Its
primitive state is the original seven non-dimensional axes

  `(x, x', y, y', z, z', n -> n')`

and exactly three spaces `NULL / ALT- / GST+`.

The familiar x4/base3 arithmetic sheet is only a realization/projection of
this ambient graph.  Horizontal x4 phase and ternary observation depth are
external chart parameters; they are not replacement GST axes.
-/

/-- The three and only three GST spaces. -/
inductive Space
  | null
  | altMinus
  | gstPlus
  deriving Repr, DecidableEq

/-- Exact space realization of the y-axis carry. -/
def spaceOfCarry (C : Nat) : Space :=
  if C = 0 then .null else if C = 3 then .gstPlus else .altMinus

/-- The seven non-dimensional GST axes.

`nAxis = (n,n')` is one transformation axis, not two independent dimensions. -/
structure SevenAxes where
  x : Nat
  xPrime : Nat
  y : Nat
  yPrime : Space
  z : Nat
  zPrime : Nat
  nAxis : Nat × Nat
  deriving Repr

/-- V2 conserved/derived information attached to a seven-axis vertex.
These are overlays, never replacement dimensions. -/
structure Overlay where
  sharedCarrier : Nat
  affineQuotient : Nat
  highRemainder : Nat
  phase : Nat
  paradoxEnergy : Nat
  deriving Repr

/-- A fully decorated vertex of the ambient non-Euclidean GST Graph V2. -/
structure Vertex where
  axes : SevenAxes
  overlay : Overlay
  deriving Repr

/-- Exact seven-axis realization of an arithmetic energy `R` at forward
position `p` with finite forward horizon `N`. -/
def axes (R N p : Nat) : SevenAxes :=
  {
    x := p
    xPrime := p + 1
    y := carry4 R p
    yPrime := spaceOfCarry (carry4 R p)
    z := digit3 R p
    zPrime := N - p
    nAxis := (R / 3^p, R / 3^(p+1))
  }

/-- One ambient GST Graph V2.  The arithmetic energy/horizon choose a chart;
the overlay map supplies the conserved information carried by that chart. -/
structure Graph where
  energy : Nat
  horizon : Nat
  overlayAt : Nat → Overlay

/-- Vertex evaluation in the ambient graph. -/
def vertex (G : Graph) (p : Nat) : Vertex :=
  {
    axes := axes G.energy G.horizon p
    overlay := G.overlayAt p
  }

/-- The genuine forward relation is the x -> x' relation. -/
def ForwardEdge (u v : SevenAxes) : Prop :=
  v.x = u.xPrime

/-- A GST witness is digit two realized in one of the two good spaces. -/
def WitnessAt (a : SevenAxes) : Prop :=
  a.z = 2 ∧ (a.yPrime = .null ∨ a.yPrime = .gstPlus)

/-- A chart with a neutral overlay, useful when only the seven-axis geometry is
being observed. -/
def bareGraph (R N : Nat) : Graph :=
  {
    energy := R
    horizon := N
    overlayAt := fun _ =>
      { sharedCarrier := 0, affineQuotient := 0, highRemainder := 0,
        phase := 0, paradoxEnergy := R }
  }

/-- The existing x4/base3 sheet embedded into the ambient graph.  `t` is an
external x4 chart parameter; the actual GST axes are still those in `axes`. -/
def physicalProjection (E N t p : Nat) : SevenAxes :=
  axes (4^t * E) N p

/-- Projection packet retaining both the ambient seven-axis state and the old
arithmetic-sheet cell.  This makes the subgraph relationship explicit. -/
structure PhysicalProjection where
  sourceEnergy : Nat
  x4Phase : Nat
  ternaryDepth : Nat
  horizon : Nat
  ambient : SevenAxes
  sheetCell : GSTGraphV2InfiniteControl.InfiniteCell
  deriving Repr

/-- Embed one old arithmetic-sheet cell into the true ambient GST graph. -/
def projectPhysicalCell (E N t p : Nat) : PhysicalProjection :=
  {
    sourceEnergy := E
    x4Phase := t
    ternaryDepth := p
    horizon := N
    ambient := physicalProjection E N t p
    sheetCell := GSTGraphV2InfiniteControl.graph E t p
  }

/-- A finite forward path in the true graph. -/
structure ForwardPath where
  energy : Nat
  horizon : Nat
  start : Nat
  length : Nat
  node : Nat → SevenAxes

/-- Canonical finite forward observation of the seven-axis graph. -/
def forwardPath (R N start L : Nat) : ForwardPath :=
  {
    energy := R
    horizon := N
    start := start
    length := L
    node := fun i => axes R N (start + i)
  }

#check Space
#check SevenAxes
#check Overlay
#check Vertex
#check Graph
#check axes
#check vertex
#check ForwardEdge
#check WitnessAt
#check physicalProjection
#check PhysicalProjection
#check projectPhysicalCell
#check ForwardPath
#check forwardPath

end GSTGraphV2NonEuclidean
