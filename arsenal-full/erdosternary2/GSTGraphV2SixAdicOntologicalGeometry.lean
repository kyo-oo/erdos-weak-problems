import GSTGraphV2NonEuclidean

/-!
# GST Graph V2 Six-Adic Ontological Geometry

This file adds a six-adic resolution layer to the existing GST Graph V2
non-Euclidean ontology.  It does not add an eighth ontological axis: the
seven-axis vertex ontology is left intact, while six-adic congruence supplies
a resolution relation on integer-valued energy charts.

The base six is used as a synchronized dyadic/triadic resolution scale.  The
core relation is deliberately stated as exact divisibility rather than by a
real-valued metric, so the layer can be used without introducing analytic
completions into the finite GST graph.
-/

namespace GSTGraphV2SixAdicOntologicalGeometry

open GSTGraphV2NonEuclidean

/-- Two integer charts are indistinguishable at six-adic resolution `k` when
    their difference is divisible by `6^k`. -/
def SixAdicIsoAt (k : Nat) (x y : Int) : Prop :=
  ∃ q : Int, x - y = (6 : Int) ^ k * q

/-- The dyadic shadow of a six-adic resolution class. -/
def DyadicShadowAt (k : Nat) (x y : Int) : Prop :=
  ∃ q : Int, x - y = (2 : Int) ^ k * q

/-- The triadic shadow of a six-adic resolution class. -/
def TriadicShadowAt (k : Nat) (x y : Int) : Prop :=
  ∃ q : Int, x - y = (3 : Int) ^ k * q

/-- Closed six-adic congruence ball of resolution `k` around `c`. -/
def SixAdicBall (k : Nat) (c : Int) : Set Int :=
  {x | SixAdicIsoAt k x c}

/-- The six canonical centers refining a ball of resolution `k` to resolution
    `k+1`.  Their offsets are the six residues modulo `6`. -/
def sixChildCenter (k : Nat) (c : Int) (j : Fin 6) : Int :=
  c + (j.val : Int) * (6 : Int) ^ k

/-- Six-adic indistinguishability of two GST graphs through their energy
    coordinates.  The existing seven-axis ontology remains unchanged. -/
def GraphIsoAt (k : Nat)
    (G H : GSTGraphV2NonEuclidean.Graph) : Prop :=
  SixAdicIsoAt k (G.energy : Int) (H.energy : Int)

/-- Integer energy represented by a physical `x4/base3` projection. -/
def physicalEnergy
    (P : GSTGraphV2NonEuclidean.PhysicalProjection) : Int :=
  (4 : Int) ^ P.x4Phase * (P.sourceEnergy : Int)

/-- Six-adic indistinguishability in the physical projection chart. -/
def PhysicalProjectionIsoAt (k : Nat)
    (P Q : GSTGraphV2NonEuclidean.PhysicalProjection) : Prop :=
  SixAdicIsoAt k (physicalEnergy P) (physicalEnergy Q)

/-- A GST graph equipped with a six-adic observational resolution. -/
structure ResolvedGraph where
  ambient : GSTGraphV2NonEuclidean.Graph
  resolution : Nat

/-- Resolution is an overlay: resolving a graph never changes the underlying
    GST vertex selected at position `p`. -/
def resolvedVertex (G : ResolvedGraph) (p : Nat) :
    GSTGraphV2NonEuclidean.Vertex :=
  GSTGraphV2NonEuclidean.vertex G.ambient p

end GSTGraphV2SixAdicOntologicalGeometry
