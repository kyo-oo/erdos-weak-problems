import GSTClassicalHodgeProjectiveSelfCorrespondences
import GSTClassicalHodgeProjectivePointTransport
import GSTClassicalHodgePointwiseNativeCosmicClosure

/-!
# GST CLASSICAL HODGE — FINITE CLOSED POINT CORRESPONDENCES

The earlier projective operator algebra uses graphs of actual endomorphisms of
X.  That is unnecessarily restrictive for a general smooth projective variety:
classical algebraic operators naturally live on correspondences in X × X.

This module installs the first genuinely correspondence-valued point transport.
A `FiniteClosedCorrespondence` consists of

* an actual scheme `C`;
* a closed immersion `C -> X ×_{Spec C} X`;
* finite left fibers on underlying scheme points.

For a codimension-p source point x we enumerate the finite left fiber, project
each correspondence point through the right projection, retain exactly the
targets of ambient codimension p, and apply the residue-degree multiplicity of
the RIGHT projection when realizing the target cycle.

The direction of that residue degree is essential.  For the graph Γ_f of an
actual endomorphism f, the left projection is the identity while the right
projection is f.  Weighting by the left residue degree would therefore erase
the genuine degree carried by f and would fail to recover the already-proved
native pushforward.  Weighting by the right projection is the graph-compatible
pushforward convention.

At this layer the finite left fiber is treated with reduced/set-theoretic
multiplicity one.  A later scheme-theoretic pullback refinement may replace
that unit left-fiber multiplicity by local intersection/length multiplicity;
the right-pushforward residue degree remains the required factor.

This is the point-generator correspondence shadow required by the sharpened
cosmic externalization theorem.  It is strictly broader than a graph of one
endomorphism: one source point may have several right-hand images.

No Hodge-surjectivity statement and no arbitrary coordinate operator is built
into the correspondence.  The separate `RealizesCosmicOnPoints` predicate is
the exact geometric equation still required to identify a chosen
correspondence with one limitless GST matrix unit.
-/

set_option maxHeartbeats 70000000
set_option maxRecDepth 1000000

noncomputable section

open CategoryTheory
open AlgebraicGeometry

namespace GSTClassicalHodgeFiniteClosedCorrespondence

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2G
open GSTNativeCodimensionCyclePresentation
open GSTClassicalHodgeProjectivePointTransport
open GSTClassicalHodgeProjectiveSelfCorrespondences
open GSTClassicalHodgePointwiseNativeCosmicClosure
open GSTClassicalHodgeCanonicalCosmicRealizationEquivalence
open GSTClassicalHodgeFiberedCosmology

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- A genuine closed self-correspondence whose projection to the first factor
has finite fibers on scheme points. -/
structure FiniteClosedCorrespondence
    (V : SmoothProjectiveComplexScheme) where
  carrier : Scheme
  intoProduct : carrier ⟶ selfProduct V
  closedImmersion : IsClosedImmersion intoProduct
  leftFiber_finite : ∀ x : V.X,
    ({z : carrier | (intoProduct ≫ fst V) z = x} : Set carrier).Finite

namespace FiniteClosedCorrespondence

/-- Left projection of the correspondence. -/
abbrev left (K : FiniteClosedCorrespondence V) : K.carrier ⟶ V.X :=
  K.intoProduct ≫ fst V

/-- Right projection of the correspondence. -/
abbrev right (K : FiniteClosedCorrespondence V) : K.carrier ⟶ V.X :=
  K.intoProduct ≫ snd V

/-- Set-theoretic left fiber over one genuine point. -/
def leftFiber
    (K : FiniteClosedCorrespondence V) (x : V.X) : Set K.carrier :=
  {z | K.left z = x}

/-- The left fiber is finite by the correspondence hypothesis. -/
theorem leftFiber_finite'
    (K : FiniteClosedCorrespondence V) (x : V.X) :
    (K.leftFiber x).Finite := by
  simpa [leftFiber, left] using K.leftFiber_finite x

/-- Finite enumerator of the correspondence fiber. -/
noncomputable def leftFiberFinset
    (K : FiniteClosedCorrespondence V) (x : V.X) : Finset K.carrier :=
  (K.leftFiber_finite x).toFinset

@[simp]
theorem mem_leftFiberFinset
    (K : FiniteClosedCorrespondence V) (x : V.X) (z : K.carrier) :
    z ∈ K.leftFiberFinset x ↔ K.left z = x := by
  classical
  simp [leftFiberFinset, leftFiber]

/-- One point of a finite correspondence fiber contributes its right-hand
image with the residue-degree multiplicity of the RIGHT projection whenever
the target remains in the requested codimension stratum.

For graph correspondences this is exactly the residue-degree factor of the
underlying endomorphism, so the construction is compatible with genuine
native point pushforward. -/
noncomputable def targetAtomPresentation
    (K : FiniteClosedCorrespondence V)
    (p : Nat)
    (z : K.carrier) :
    FiniteCodimensionPresentation V.X p := by
  classical
  by_cases hz : Order.coheight (K.right z) = p
  · exact Finsupp.single
      (⟨K.right z, hz⟩ : CodimensionPoint V.X p)
      (pointResidueWeight K.right z)
  · exact 0

/-- Exact target presentation of one source point under a finite closed
correspondence. -/
noncomputable def transition
    (K : FiniteClosedCorrespondence V)
    (p : Nat)
    (x : CodimensionPoint V.X p) :
    FiniteCodimensionPresentation V.X p :=
  (K.leftFiberFinset x.1).sum (K.targetAtomPresentation p)

/-- Real native codimension-p target cycle obtained from the correspondence
fiber over one source point. -/
noncomputable def nativePointImage
    (K : FiniteClosedCorrespondence V)
    (p : Nat)
    (x : CodimensionPoint V.X p) :
    codimensionCycles V.X p :=
  realizeFiniteCodimensionPresentation V.X p (K.transition p x)

/-- Exact formula for a target atom when its right image has the requested
codimension. -/
theorem targetAtomPresentation_eq_single
    (K : FiniteClosedCorrespondence V)
    (p : Nat)
    (z : K.carrier)
    (hz : Order.coheight (K.right z) = p) :
    K.targetAtomPresentation p z =
      Finsupp.single
        (⟨K.right z, hz⟩ : CodimensionPoint V.X p)
        (pointResidueWeight K.right z) := by
  classical
  simp only [targetAtomPresentation]
  split
  · rfl
  · exact absurd hz (by assumption)

/-- Wrong target codimension contributes zero and therefore cannot contaminate
the native codimension-p cycle space. -/
theorem targetAtomPresentation_eq_zero
    (K : FiniteClosedCorrespondence V)
    (p : Nat)
    (z : K.carrier)
    (hz : Order.coheight (K.right z) ≠ p) :
    K.targetAtomPresentation p z = 0 := by
  classical
  simp only [targetAtomPresentation]
  split
  · exact absurd (by assumption) hz
  · rfl

/-- Every correspondence point over x with correct target codimension appears
as an explicit summand in the point transition. -/
theorem transition_eq_fiber_sum
    (K : FiniteClosedCorrespondence V)
    (p : Nat)
    (x : CodimensionPoint V.X p) :
    K.transition p x =
      ∑ z ∈ K.leftFiberFinset x.1, K.targetAtomPresentation p z :=
  rfl

/-- The pointwise Betti realization equation identifying a genuine finite
closed correspondence with one limitless cosmic matrix unit. -/
def RealizesCosmicOnPoints
    (K : FiniteClosedCorrespondence V)
    (i j : ClassicalHodgeBasisIndex V H p) : Prop :=
  ∀ x : CodimensionPoint V.X p,
    H.cycleClass p (K.nativePointImage p x) =
      canonicalCosmicAmbient i j
        (H.cycleClass p (codimensionPointCycle V.X p x))

/-- A finite closed correspondence satisfying the exact pointwise cosmic law
immediately supplies the minimal native point-lift interface. -/
theorem cosmicNativePointLifts
    (K : FiniteClosedCorrespondence V)
    (i j : ClassicalHodgeBasisIndex V H p)
    (hK : K.RealizesCosmicOnPoints (H := H) i j) :
    CosmicNativePointLifts (V := V) (H := H) i j := by
  intro x
  exact ⟨K.nativePointImage p x, hK x⟩

/-- One live-source family of genuine finite closed correspondences is enough
to saturate the whole Hodge weight. -/
theorem hodge_weight_of_liveSource_correspondences
    (S : GSTClassicalHodgeSynchronizedDefectOrbit.NativeHodgeOrbitSeed
      (V := V) (H := H) (p := p))
    (K : ∀ j : ClassicalHodgeBasisIndex V H p,
      FiniteClosedCorrespondence V)
    (hK : ∀ j : ClassicalHodgeBasisIndex V H p,
      (K j).RealizesCosmicOnPoints (H := H) S.sourceIndex j) :
    rationalHodgeSubspace (H.hodgeBigrading p) ≤
      LinearMap.range (H.cycleClass p) := by
  apply GSTClassicalHodgePointwiseNativeCosmicClosure.hodge_weight_of_liveSource_pointLifts S
  intro j
  exact (K j).cosmicNativePointLifts S.sourceIndex j (hK j)

/-! ## Graphs are a special case -/

/-- The graph of an actual complex-scheme endomorphism is a finite closed
correspondence: its left projection is the identity and every left fiber is a
singleton. -/
noncomputable def graphCorrespondence
    (f : GSTClassicalHodgeAnalytificationFunctoriality.ComplexSchemeEndomorphism V) :
    FiniteClosedCorrespondence V where
  carrier := V.X
  intoProduct := graph V f
  closedImmersion := inferInstance
  leftFiber_finite := by
    intro x
    have hset :
        ({z : V.X | (graph V f ≫ fst V) z = x} : Set V.X) = {x} := by
      ext z
      simp
    rw [hset]
    exact Set.finite_singleton x

/-- Graph correspondences really have identity left projection. -/
theorem graphCorrespondence_left
    (f : GSTClassicalHodgeAnalytificationFunctoriality.ComplexSchemeEndomorphism V) :
    (graphCorrespondence f).left = 𝟙 V.X := by
  change graph V f ≫ fst V = 𝟙 V.X
  exact graph_fst V f

/-- Their right projection is the original endomorphism. -/
theorem graphCorrespondence_right
    (f : GSTClassicalHodgeAnalytificationFunctoriality.ComplexSchemeEndomorphism V) :
    (graphCorrespondence f).right = f.hom := by
  change graph V f ≫ snd V = f.hom
  exact graph_snd V f

#check FiniteClosedCorrespondence
#check FiniteClosedCorrespondence.left
#check FiniteClosedCorrespondence.right
#check FiniteClosedCorrespondence.transition
#check FiniteClosedCorrespondence.nativePointImage
#check FiniteClosedCorrespondence.RealizesCosmicOnPoints
#check FiniteClosedCorrespondence.cosmicNativePointLifts
#check FiniteClosedCorrespondence.hodge_weight_of_liveSource_correspondences
#check FiniteClosedCorrespondence.graphCorrespondence
#check FiniteClosedCorrespondence.graphCorrespondence_left
#check FiniteClosedCorrespondence.graphCorrespondence_right

#print axioms FiniteClosedCorrespondence.cosmicNativePointLifts
#print axioms FiniteClosedCorrespondence.hodge_weight_of_liveSource_correspondences
#print axioms FiniteClosedCorrespondence.graphCorrespondence

end FiniteClosedCorrespondence
end GSTClassicalHodgeFiniteClosedCorrespondence
