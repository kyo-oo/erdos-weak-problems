import GSTGraphV2HandwrittenAnchoredCocycle
import GSTU2DCanonicalPhaseDensity
import GSTU2DPureDivergence83

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace GSTGraphV2Production

open GSTCanonicalSevenAxisBridge
open GST2DMixedEmergence
open GSTU2DEventTransport
open GSTGraphV2CoupledUFlux
open GSTGraphV2CoupledUPhysicalBridge
open GSTGraphV2InfiniteControl
open GSTGraphV2UnifiedPowerRectangle
open GSTGraphV2HandwrittenOmegaUBlock
open GSTGraphV2HandwrittenExponentialCascade
open GSTGraphV2HandwrittenAnchoredCocycle
open GSTGraphV2PerfectPowerBlock
open GSTU2DCanonicalPhaseDensity
open GSTU2DPureDivergence83

/-!
# GST Graph V2 — production object

This file constructs the one graph object that all later production mathematics
must use. It deliberately introduces no closing theorem and no alternative
surrogate graph.

The underlying sheet remains the already-defined all-depth arithmetic graph
`GSTGraphV2InfiniteControl.graph E t p`. This module only assembles all of its
currently-green coordinates into one explicit production state:

* the canonical seven arithmetic axes and physical GST space;
* event, U, mixed, crossing and SURVIVE observables;
* the exact local U jump;
* the Equation-I navigation/nullspace residue;
* canonical phase density and the independent 8x3 density;
* explicit horizontal-x4 and vertical-ternary graph edges;
* finite horizontal rectangle state on the same infinite lattice;
* exact natural-origin prefix/suffix/phase coordinates on the same lattice;
* both the neutral higher-level U tail and its re-phased realization;
* the generalized residual `(s,k,m)` frame used by the production seam;
* the exact generalized residual gate row `s+k+1+j`;
* the canonical production-cut frame at `p = s+2+q`.

No finite rectangle replaces the infinite graph. Rectangles and origin frames
below are observations/re-coordinatizations of the same absolute energy.
-/

structure Cell where
  sourceEnergy : Nat
  horizontal : Nat
  vertical : Nat
  absoluteEnergy : Nat
  seven : GSTCanonicalSevenAxisBridge.Vertex
  eventCode : Nat
  uCharge : Int
  uJump : Int
  mixedCharge : Int
  crossingCharge : Int
  survive : Int
  navigationNullspace : Nat
  phaseDensity : Int
  density83 : Int
  deriving Repr

def cell (E t p : Nat) : Cell :=
  let g := GSTGraphV2InfiniteControl.graph E t p
  let R := 4^t * E
  {
    sourceEnergy := E
    horizontal := t
    vertical := p
    absoluteEnergy := R
    seven := g.seven
    eventCode := g.eventCode
    uCharge := g.uCharge
    uJump := GSTGraphV2CoupledUFlux.gstUJumpExact g.seven.carry g.seven.digit
    mixedCharge := g.mixedCharge
    crossingCharge := g.crossingCharge
    survive := g.survive
    navigationNullspace :=
      GSTGraphV2HandwrittenExponentialCascade.navigationNullspace R p
    phaseDensity := GSTU2DCanonicalPhaseDensity.phaseDensity
      g.seven.carry g.seven.digit
    density83 := GSTU2DPureDivergence83.density83
      g.seven.carry g.seven.digit
  }

abbrev Sheet := Nat → Nat → Cell

def graph (E : Nat) : Sheet := fun t p => cell E t p

inductive Direction
  | horizontalX4
  | verticalTernary
  deriving Repr, DecidableEq

structure Edge where
  direction : Direction
  source : Cell
  target : Cell
  deriving Repr

def horizontalEdge (E t p : Nat) : Edge :=
  {
    direction := .horizontalX4
    source := cell E t p
    target := cell E (t+1) p
  }

def verticalEdge (E t p : Nat) : Edge :=
  {
    direction := .verticalTernary
    source := cell E t p
    target := cell E t (p+1)
  }

structure Lattice where
  sourceEnergy : Nat
  vertex : Nat → Nat → Cell
  horizontal : Nat → Nat → Edge
  vertical : Nat → Nat → Edge

def lattice (E : Nat) : Lattice :=
  {
    sourceEnergy := E
    vertex := graph E
    horizontal := fun t p => horizontalEdge E t p
    vertical := fun t p => verticalEdge E t p
  }

structure Neighborhood where
  center : Cell
  horizontalNext : Cell
  verticalNext : Cell
  deriving Repr

def neighborhood (E t p : Nat) : Neighborhood :=
  {
    center := cell E t p
    horizontalNext := cell E (t+1) p
    verticalNext := cell E t (p+1)
  }

structure Rectangle where
  sourceEnergy : Nat
  width : Nat
  vertical : Nat
  left : Cell
  right : Cell
  carryWord : Nat
  physical : GSTGraphV2CoupledUPhysicalBridge.PhysicalState
  uPotential : Int
  deriving Repr

def rectangle (E N p : Nat) : Rectangle :=
  {
    sourceEnergy := E
    width := N
    vertical := p
    left := cell E 0 p
    right := cell E N p
    carryWord := GSTGraphV2UnifiedPowerRectangle.carryWord E p 0 N
    physical := GSTGraphV2UnifiedPowerRectangle.unifiedState E N p
    uPotential := GSTGraphV2HandwrittenAnchoredCocycle.graphUPotential E 0 N p
  }

structure OriginCoordinates where
  level : Nat
  origin : Nat
  depth : Nat
  originPrefixValue : Nat
  originSuffixValue : Nat
  phaseShift : Nat
  tailExponent : Nat
  tailEnergy : Nat
  deriving Repr

def originCoordinates (t n K : Nat) : OriginCoordinates :=
  {
    level := t
    origin := n
    depth := K
    originPrefixValue := GSTGraphV2HandwrittenExponentialCascade.originPrefix n K
    originSuffixValue := GSTGraphV2HandwrittenExponentialCascade.originSuffix n K
    phaseShift := GSTGraphV2HandwrittenExponentialCascade.uPhaseShift t n K
    tailExponent := GSTGraphV2HandwrittenExponentialCascade.uTailExponent t n K
    tailEnergy := GSTGraphV2HandwrittenExponentialCascade.uTailEnergy t n K
  }

structure OriginFrame where
  coordinates : OriginCoordinates
  horizontalOffset : Nat
  vertical : Nat
  fullEnergy : Nat
  full : Cell
  neutralTail : Cell
  phasedTail : Cell
  deriving Repr

def originFrame (t n K x p : Nat) : OriginFrame :=
  let o := originCoordinates t n K
  {
    coordinates := o
    horizontalOffset := x
    vertical := p
    fullEnergy := 4^(3^t * n)
    full := cell (4^(3^t * n)) x p
    neutralTail := cell o.tailEnergy 0 p
    phasedTail := cell o.tailEnergy (o.phaseShift + x) p
  }

def canonicalEnergy (s n : Nat) : Nat :=
  GSTGraphV2PerfectPowerBlock.canonicalEnergy s n

def canonicalWidth (s : Nat) : Nat :=
  GSTGraphV2PerfectPowerBlock.canonicalWidth s

def canonicalGraph (s n : Nat) : Sheet := graph (canonicalEnergy s n)

def canonicalLattice (s n : Nat) : Lattice := lattice (canonicalEnergy s n)

def canonicalRectangle (s n p : Nat) : Rectangle :=
  rectangle (canonicalEnergy s n) (canonicalWidth s) p

def residualEnergy (s k m : Nat) : Nat :=
  GSTGraphV2HandwrittenOmegaUBlock.residualEnergy s k m

def residualGraph (s k m : Nat) : Sheet := graph (residualEnergy s k m)

def residualLattice (s k m : Nat) : Lattice := lattice (residualEnergy s k m)

def residualRectangle (s k m p : Nat) : Rectangle :=
  rectangle (residualEnergy s k m)
    (GSTGraphV2HandwrittenOmegaUBlock.residualWidth s) p

structure ResidualFrame where
  s : Nat
  k : Nat
  origin : Nat
  vertical : Nat
  childExponent : Nat
  parentExponent : Nat
  childEnergy : Nat
  parentWidth : Nat
  originTrit : Nat
  originTail : Nat
  nextTailEnergy : Nat
  block : Rectangle
  deriving Repr

def residualFrame (s k m p : Nat) : ResidualFrame :=
  {
    s := s
    k := k
    origin := m
    vertical := p
    childExponent := GSTGraphV2HandwrittenOmegaUBlock.residualChildExponent s k m
    parentExponent := GSTGraphV2HandwrittenOmegaUBlock.residualParentExponent s k m
    childEnergy := residualEnergy s k m
    parentWidth := GSTGraphV2HandwrittenOmegaUBlock.residualWidth s
    originTrit := GSTGraphV2HandwrittenOmegaUBlock.originTrit m
    originTail := GSTGraphV2HandwrittenOmegaUBlock.originTail m
    nextTailEnergy := 4^(3^(s+k+1) * GSTGraphV2HandwrittenOmegaUBlock.originTail m)
    block := residualRectangle s k m p
  }

/-- Absolute Graph V2 row corresponding to relative child Navigation depth j
in the generalized residual child `Q_(s+k)(m)`. -/
def residualGateRow (s k j : Nat) : Nat := s + k + 1 + j

/-- Generalized residual frame pinned to the exact physical row of a relative
child gate. This is data only; it does not assert that a gate exists. -/
structure ResidualGateFrame where
  s : Nat
  k : Nat
  origin : Nat
  gateDepth : Nat
  row : Nat
  residual : ResidualFrame
  originFrame : OriginFrame
  deriving Repr

def residualGateFrame (s k m j : Nat) : ResidualGateFrame :=
  let p := residualGateRow s k j
  {
    s := s
    k := k
    origin := m
    gateDepth := j
    row := p
    residual := residualFrame s k m p
    originFrame := originFrame (s+k) m (j+1) 0 p
  }

def canonicalCutRow (s q : Nat) : Nat := s + 2 + q

structure CanonicalCutFrame where
  s : Nat
  origin : Nat
  gateDepth : Nat
  row : Nat
  energy : Nat
  width : Nat
  block : Rectangle
  uFrame : OriginFrame
  deriving Repr

def canonicalCutFrame (s n q : Nat) : CanonicalCutFrame :=
  let p := canonicalCutRow s q
  {
    s := s
    origin := n
    gateDepth := q
    row := p
    energy := canonicalEnergy s n
    width := canonicalWidth s
    block := canonicalRectangle s n p
    uFrame := originFrame (s+1) n (q+1) 0 p
  }

#check Cell
#check graph
#check Direction
#check Edge
#check horizontalEdge
#check verticalEdge
#check Lattice
#check lattice
#check Neighborhood
#check neighborhood
#check Rectangle
#check rectangle
#check OriginCoordinates
#check originCoordinates
#check OriginFrame
#check originFrame
#check canonicalGraph
#check canonicalLattice
#check canonicalRectangle
#check residualGraph
#check residualLattice
#check residualRectangle
#check ResidualFrame
#check residualFrame
#check residualGateRow
#check ResidualGateFrame
#check residualGateFrame
#check CanonicalCutFrame
#check canonicalCutFrame

end GSTGraphV2Production
