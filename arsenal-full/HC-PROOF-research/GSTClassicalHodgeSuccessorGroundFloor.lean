import GSTClassicalHodgeRelativeSuccessorExactStratum
import GSTClassicalHodgePointClosureIrreducible
import GSTClassicalHodgeProperCutCodimensionOne
import Mathlib.Order.KrullDimension

/-!
# GST CLASSICAL HODGE — SUCCESSOR COHEIGHT GROUND FLOOR

The Route S siege study priced the successor coheight additivity law L1:
`RelativeSuccessorAmbientExact V p x` — every principal-cut successor of a
codimension-`p` point lands in the exact ambient codimension-`p + 1` stratum.

The lower bound `p + 1 ≤ ambient coheight` is already a theorem
(`ambient_coheight_ge_succ`).  The upper bound was localized to the
catenarity residue, and that localization is honest: Mathlib has no
catenarity (`catenary`: 0 hits, `IsCatenary`: 0 hits, relevant `height_add`:
0 hits — GitHub code-search receipts in the project worklog), and
`NoetherNormalization` alone does not deliver the height-additivity
equality.  The `p ≥ 1` rungs therefore remain priced.

THIS MODULE closes the GROUND FLOOR unconditionally: at `p = 0`, for a
codimension-zero (generic) source point of an irreducible carrier, the whole
exactness statement is a THEOREM, by pure order theory:

* a coheight-zero point of an irreducible quasi-sober carrier is the generic
  point (`Order.coheight_eq_zero`, `QuasiSober.sober`), so its point closure
  is the entire carrier;
* the point-closure inclusion is then a surjective order embedding: it
  preserves and reflects the specialization order
  (`Topology.IsInducing.closure_eq_preimage_closure_image`);
* `LTSeries` chains transport both ways (`LTSeries.map` forward,
  `LTSeries.comap` backward), so ambient and closure-scheme coheights agree;
* every successor candidate in the relative finset subtype has
  closure-scheme coheight `1` by construction, hence ambient coheight
  `1 = 0 + 1`.

This is the first `hExact` instance in the repository that is DISCHARGED
rather than assumed.  Every downstream consumer
(`selected_successorAtomPresentation_eq_single`,
`successorMass_eq_relativeCard`, `successorMass_ne_zero_of_nonempty`,
`successorNativeOperator_point_ne_zero`,
`relative_successor_exact_stratum_crown`) can now be instantiated at the
bottom weight with no exactness hypothesis at all — the corollaries below
do exactly that.

AUTHORITY 005 audit: the ONLY hypothesis in this module is the geometric
instance `[IrreducibleSpace V.X]` (the same hypothesis shape the repo already
uses in `GSTClassicalHodgeProperCutCodimensionOne.finite_principal_cut_coheight_one`).
No Hodge statement, cycle-class datum, ghost, seed, or closure law is assumed
anywhere.  Nothing here is Hodge-equivalent: the zero-cycle semantic
countermodel is irrelevant to pure order theory of the carrier topology.

STATUS: meta-design level, no local Lean (AUTHORITY 002).  COMPARE notes mark
orientation-sensitive lines for the compiling brother.
-/

set_option maxHeartbeats 60000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry
open TopologicalSpace

namespace GSTClassicalHodgeSuccessorGroundFloor

open GSTProjectiveOverC
open GSTNativeCodimensionCyclePresentation
open GSTClassicalHodgePointClosurePrincipalCut
open GSTClassicalHodgePointClosureRelativeCut
open GSTClassicalHodgePointClosureIrreducible
open GSTClassicalHodgePrincipalCutSuccessorOperator
open GSTClassicalHodgeRelativeSuccessorExactStratum
open GSTClassicalHodgeProperCutCodimensionOne
open GSTClassicalHodgeNativeCycleCosmicShadow

attribute [local instance] specializationOrder

variable {V : SmoothProjectiveComplexScheme}

/-! ## §1. A coheight-zero source is the generic point -/

/-- **CLOSURE OF A GROUND POINT IS EVERYTHING.**

In an irreducible carrier, a point of ambient coheight zero — a maximal point
of the specialization order, i.e. a minimal prime of the underlying space —
has singleton closure equal to the whole carrier.  The proof follows the
repository's own generic-point pattern from
`GSTClassicalHodgeCodimensionZeroFundamentalCycle`. -/
theorem closure_eq_univ_of_coheight_zero
    [IrreducibleSpace V.X]
    (x : V.X) (hx : Order.coheight x = 0) :
    closure ({x} : Set V.X) = Set.univ := by
  have hmax : IsMax x := (Order.coheight_eq_zero).mp hx
  obtain ⟨η, hη⟩ : ∃ η : V.X, IsGenericPoint η (Set.univ : Set V.X) :=
    QuasiSober.sober (IrreducibleSpace.isIrreducible_univ V.X) isClosed_univ
  have hxη : x ≤ η := hη.specializes (Set.mem_univ x)
  have hηx : η ≤ x := hmax hxη
  have hxeq : x = η := by
    refine (inseparable_iff_eq).mp ?_
    exact le_antisymm
      (show nhds x ≤ nhds η from hηx)
      (show nhds η ≤ nhds x from hxη)
  rw [hxeq]
  exact hη.def

#print axioms closure_eq_univ_of_coheight_zero
/-! ## §2. Surjectivity and order behavior of the closure inclusion -/

/-- The point-closure inclusion is injective (it is an embedding of the
reduced closure subscheme).  COMPARE: the `.isEmbedding` projection is the
repository's own expression from `GSTClassicalHodgePointClosureIrreducible`
(`pointClosureHomeomorph`). -/
theorem pointClosureι_injective
    (x : V.X) :
    Function.Injective (pointClosureι V x) :=
  (pointClosureι V x).isEmbedding.injective

#print axioms pointClosureι_injective
/-- **THE CLOSURE INCLUSION IS SURJECTIVE AT A GROUND POINT.**

When the source is a coheight-zero point of an irreducible carrier, the
closure scheme covers the whole carrier. -/
theorem pointClosureι_surjective_of_coheight_zero
    [IrreducibleSpace V.X]
    (x : V.X) (hx : Order.coheight x = 0) :
    Function.Surjective (pointClosureι V x) := by
  intro w
  have hrange : w ∈ Set.range (pointClosureι V x) := by
    rw [range_pointClosureι, closure_eq_univ_of_coheight_zero (V := V) x hx]
    trivial
  exact hrange

#print axioms pointClosureι_surjective_of_coheight_zero
/-- **ORDER CORRESPONDENCE OF THE CLOSURE INCLUSION.**

The point-closure inclusion preserves and reflects the specialization order:
both directions come at once from the induced-topology closure bridge
`Topology.IsInducing.closure_eq_preimage_closure_image`, the same weapon the
repository already uses in `GSTClassicalHodgeProperCutCodimensionOne`. -/
theorem pointClosureι_le_iff
    (x : V.X) (z w : pointClosureScheme V x) :
    z ≤ w ↔ pointClosureι V x z ≤ pointClosureι V x w := by
  have hind : Topology.IsInducing (pointClosureι V x) :=
    (pointClosureι V x).isEmbedding.isInducing
  have hbridge :
      closure ({w} : Set (pointClosureScheme V x)) =
        (pointClosureι V x) ⁻¹'
          closure (Set.image (pointClosureι V x) {w}) :=
    Topology.IsInducing.closure_eq_preimage_closure_image
      (f := (pointClosureι V x)) hind {w}
  rw [Set.image_singleton] at hbridge
  constructor
  · intro hle
    have hz : z ∈ closure ({w} : Set (pointClosureScheme V x)) :=
      (specializationOrder_iff_specializes).1 hle
    rw [hbridge] at hz
    exact (specializationOrder_iff_specializes).2 hz
  · intro hle
    have hz : pointClosureι V x z ∈ closure ({pointClosureι V x w} : Set V.X) :=
      (specializationOrder_iff_specializes).1 hle
    have hz' : z ∈ closure ({w} : Set (pointClosureScheme V x)) := by
      rw [hbridge]
      exact hz
    exact (specializationOrder_iff_specializes).2 hz'

#print axioms pointClosureι_le_iff
/-- **THE CLOSURE INCLUSION IS STRICTLY MONOTONE.** -/
theorem pointClosureι_strictMono
    (x : V.X) :
    StrictMono (pointClosureι V x) := by
  intro z w hzw
  refine ⟨(pointClosureι_le_iff (V := V) x z w).1 hzw.1, ?_⟩
  intro hback
  exact hzw.2 ((pointClosureι_le_iff (V := V) x w z).2 hback)

#print axioms pointClosureι_strictMono
/-- **THE CLOSURE INCLUSION REFLECTS STRICT ORDER.**

Exactly the reflection shape demanded by `LTSeries.comap`. -/
theorem pointClosureι_reflects_lt
    (x : V.X) {z w : pointClosureScheme V x}
    (h : pointClosureι V x z < pointClosureι V x w) :
    z < w := by
  refine ⟨(pointClosureι_le_iff (V := V) x z w).2 h.1, ?_⟩
  intro hback
  exact h.2 ((pointClosureι_le_iff (V := V) x w z).1 hback)

#print axioms pointClosureι_reflects_lt
/-! ## §3. Coheight transport at a ground point -/

/-- **AMBIENT AND CLOSURE-SCHEME COHEIGHTS AGREE AT A GROUND SOURCE.**

When the point closure of `x` is the entire carrier, the closure inclusion
is a surjective strictly monotone order reflection — an order isomorphism —
and `Order.coheight` is invariant under it.  Strict chains transport both
ways: `LTSeries.map` pushes closure chains out to ambient chains, and
`LTSeries.comap` pulls ambient chains back through the surjective
reflection. -/
theorem coheight_pointClosureι_eq_of_coheight_zero
    [IrreducibleSpace V.X]
    (x : V.X) (hx : Order.coheight x = 0)
    (y : pointClosureScheme V x) :
    Order.coheight (pointClosureι V x y) = Order.coheight y := by
  have hsurj : Function.Surjective (pointClosureι V x) :=
    pointClosureι_surjective_of_coheight_zero (V := V) x hx
  have hmono : StrictMono (pointClosureι V x) :=
    pointClosureι_strictMono (V := V) x
  have hrefl : ∀ {z w : pointClosureScheme V x},
      pointClosureι V x z < pointClosureι V x w → z < w :=
    pointClosureι_reflects_lt (V := V) x
  -- The closure inclusion is a surjective strictly monotone order
  -- reflection; Mathlib's own coheight transport under a strict
  -- monotone map with a surjective strict-lift witness closes the
  -- theorem directly (replacing the hand-rolled LTSeries transport).
  refine (Order.coheight_eq_of_strictMono (pointClosureι V x) hmono ?_ y).symm
  intro a b hab
  obtain ⟨a', ha'⟩ := hsurj b
  exact ⟨a', hrefl (by rw [ha']; exact hab), ha'⟩

#print axioms coheight_pointClosureι_eq_of_coheight_zero
/-! ## §4. The ground floor of the coheight additivity -/

/-- **THE GROUND FLOOR OF L1.**

The first `hExact` instance in the repository, DISCHARGED rather than
assumed: for a codimension-zero source point of an irreducible carrier, every
selected relative successor candidate has ambient coheight exactly
`0 + 1 = 1`.  The finset-membership hypothesis is not even needed — the
coheight transport holds for every point of the closure scheme. -/
theorem relativeSuccessorAmbientExact_of_coheight_zero
    [IrreducibleSpace V.X]
    (x : CodimensionPoint V.X 0) :
    RelativeSuccessorAmbientExact V 0 x := by
  intro y _hy
  show Order.coheight (pointClosureι V x.1 y.1) = 0 + 1
  rw [coheight_pointClosureι_eq_of_coheight_zero (V := V) x.1 x.2 y.1, y.2]
  push_cast
  rfl

#print axioms relativeSuccessorAmbientExact_of_coheight_zero
/-- **THE GROUND-FLOOR SLICE OF THE SHEET-SIEGE L1 LAW.** -/
theorem sheetSiegeCoheightAdditivity_ground_floor
    [IrreducibleSpace V.X] :
    ∀ x : CodimensionPoint V.X 0, RelativeSuccessorAmbientExact V 0 x :=
  fun x => relativeSuccessorAmbientExact_of_coheight_zero (V := V) x

#print axioms sheetSiegeCoheightAdditivity_ground_floor
/-! ## §5. Discharged bottom-weight corollaries

The four downstream consumers of `RelativeSuccessorAmbientExact`, previously
available only under an exactness HYPOTHESIS, are now unconditional at the
bottom weight (modulo the nonemptiness of the relative successor locus, which
remains the separately priced liveness input). -/

/-- Bottom-weight successor mass equals the relative successor count. -/
theorem successorMass_eq_relativeCard_of_ground
    [IrreducibleSpace V.X]
    (x : CodimensionPoint V.X 0) :
    successorMass V 0 x =
      (relativeCodimensionOneFinset V x.1).card :=
  successorMass_eq_relativeCard V 0 x
    (relativeSuccessorAmbientExact_of_coheight_zero (V := V) x)

#print axioms successorMass_eq_relativeCard_of_ground
/-- A nonempty ground-floor successor locus has strictly positive native
successor mass — no exactness hypothesis. -/
theorem successorMass_ne_zero_of_nonempty_of_ground
    [IrreducibleSpace V.X]
    (x : CodimensionPoint V.X 0)
    (hNonempty : (relativeCodimensionOneFinset V x.1).Nonempty) :
    successorMass V 0 x ≠ 0 :=
  successorMass_ne_zero_of_nonempty V 0 x
    (relativeSuccessorAmbientExact_of_coheight_zero (V := V) x) hNonempty

#print axioms successorMass_ne_zero_of_nonempty_of_ground
/-- The geometry-built successor of a ground point atom is a nonzero native
codimension-one cycle whenever the relative cut is nonempty — no exactness
hypothesis. -/
theorem successorNativeOperator_point_ne_zero_of_ground
    [IrreducibleSpace V.X]
    (x : CodimensionPoint V.X 0)
    (hNonempty : (relativeCodimensionOneFinset V x.1).Nonempty) :
    successorNativeOperator V 0 (codimensionPointCycle V.X 0 x) ≠ 0 :=
  successorNativeOperator_point_ne_zero V 0 x
    (relativeSuccessorAmbientExact_of_coheight_zero (V := V) x) hNonempty

#print axioms successorNativeOperator_point_ne_zero_of_ground
/-- **GROUND-FLOOR EXACT-STRATUM CROWN.**
The bundled bottom-weight crown: mass formula, mass positivity, and nonzero
next-stratum point image — all with the exactness premise discharged by the
ground-floor theorem. -/
theorem relative_successor_exact_stratum_crown_of_ground
    [IrreducibleSpace V.X]
    (x : CodimensionPoint V.X 0)
    (hNonempty : (relativeCodimensionOneFinset V x.1).Nonempty) :
    successorMass V 0 x = (relativeCodimensionOneFinset V x.1).card
      ∧ successorMass V 0 x ≠ 0
      ∧ successorNativeOperator V 0
          (codimensionPointCycle V.X 0 x) ≠ 0 :=
  relative_successor_exact_stratum_crown V 0 x
    (relativeSuccessorAmbientExact_of_coheight_zero (V := V) x) hNonempty

#check closure_eq_univ_of_coheight_zero
#check pointClosureι_surjective_of_coheight_zero
#check pointClosureι_le_iff
#check pointClosureι_strictMono
#check pointClosureι_reflects_lt
#check coheight_pointClosureι_eq_of_coheight_zero
#check relativeSuccessorAmbientExact_of_coheight_zero
#check sheetSiegeCoheightAdditivity_ground_floor
#check successorMass_eq_relativeCard_of_ground
#check successorMass_ne_zero_of_nonempty_of_ground
#check successorNativeOperator_point_ne_zero_of_ground
#check relative_successor_exact_stratum_crown_of_ground

#print axioms closure_eq_univ_of_coheight_zero
#print axioms pointClosureι_le_iff
#print axioms coheight_pointClosureι_eq_of_coheight_zero
#print axioms relativeSuccessorAmbientExact_of_coheight_zero
#print axioms successorNativeOperator_point_ne_zero_of_ground
#print axioms relative_successor_exact_stratum_crown_of_ground

end GSTClassicalHodgeSuccessorGroundFloor
