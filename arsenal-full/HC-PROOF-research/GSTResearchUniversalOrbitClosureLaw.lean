import GSTResearchGeometricOrbitSynthesis

/-!
# GST Universal Minimal Geometric Orbit Law

Mathematical advance over the previous irreducible-orbit criterion:
the user wants a universal law proving native geometric directions.
Instead of assuming GLOBAL irreducibility of every actual geometric
correspondence on the WHOLE Hodge fiber, we identify the smallest
genuinely geometric invariant subspace of ONE native algebraic seed.

This orbit is CONSTRUCTED by finite words of actual realized
Hodge-compatible finite-closed correspondences on native cycles.
Unconditionally it is the SMALLEST Hodge subspace which:
  1. contains the genuine native algebraic seed class, and
  2. is stable under all actual geometric correspondences.

We prove an if-and-only-if: the constructed native orbit spans the
whole Hodge fiber EXACTLY when every invariant Hodge subspace
containing the fixed seed is all of it.

The latter is a strictly LOCAL cyclicity target for the chosen seed,
not the stronger global operator irreducibility used previously.
This can hold in representations that are NOT globally irreducible.

This is a universally quantified, axiom-free geometric law for
every V/H/p admitting the established GeometricCycleClassSpine.
It does not assert the local cyclicity criterion ALWAYS holds:
doing so would assume the still-unproved Hodge algebraicity target.
-/

set_option maxHeartbeats 20000000
noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeGeometricMatrixRankLanding
open GSTClassicalHodgeActualGeometricIrreducibility
open GSTResearchGeometricOrbitSynthesis

namespace GSTResearchUniversalOrbitClosureLaw

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- UNIVERSAL MINIMALITY:
any Hodge subspace preserved by every genuinely realized
Hodge-compatible finite-closed correspondence and containing the
given genuine algebraic seed necessarily contains EVERY
constructible native geometric correspondence-word class. -/
theorem native_orbit_minimal_among_actual_geometric_invariants
    (G : GeometricCycleClassSpine V H)
    (Z : codimensionCycles V.X p)
    (S : Submodule ℚ (ClassicalHodgeFiber V H p))
    (hstable : InvariantUnderActualHodgeCorrespondences S)
    (hseed : geometricHodgeClass G Z ∈ S) :
    nativeOrbitHodgeSpan G Z ≤ S := by
  unfold nativeOrbitHodgeSpan
  apply Submodule.span_le.mpr
  rintro x ⟨w, rfl⟩
  induction w with
  | seed =>
      exact hseed
  | next R hR w ih =>
      change geometricHodgeClass G
        (nativeOrbitCycle Z (.next R hR w)) ∈ S
      rw [nativeOrbitCycle_next_class G Z R hR w]
      exact hstable R hR _ ih

/-- LOCAL geometric cyclicity:
every actual-correspondence-stable Hodge subspace that contains this
one specific native seed is the whole Hodge fiber. This is an exact
geometric condition and strictly weaker than requiring all invariant
subspaces to be zero or everything. -/
def SeedCyclicForActualGeometry
    (G : GeometricCycleClassSpine V H)
    (Z : codimensionCycles V.X p) : Prop :=
  ∀ S : Submodule ℚ (ClassicalHodgeFiber V H p),
    InvariantUnderActualHodgeCorrespondences S →
    geometricHodgeClass G Z ∈ S → S = ⊤

/-- EXACT EQUIVALENCE, not a mere sufficient statement:
local geometric cyclicity of the native seed equals full-span
generation by its EXPLICIT, ACTUAL native-correspondence orbit. -/
theorem native_orbit_top_iff_seed_geometrically_cyclic
    (G : GeometricCycleClassSpine V H)
    (Z : codimensionCycles V.X p) :
    nativeOrbitHodgeSpan G Z = ⊤ ↔
      SeedCyclicForActualGeometry G Z := by
  constructor
  · intro htop S hstable hseed
    have hle :=
      native_orbit_minimal_among_actual_geometric_invariants
        G Z S hstable hseed
    rw [htop] at hle
    exact top_unique hle
  · intro hcyclic
    exact hcyclic (nativeOrbitHodgeSpan G Z)
      (nativeOrbitHodgeSpan_invariant G Z)
      (seed_in_nativeOrbitHodgeSpan G Z)

/-- A local actual-geometric cyclic seed, without GLOBAL
irreducibility, is enough to construct a rational algebraic-cycle
representative for EVERY target Hodge class in the weight. -/
theorem hodge_cycles_from_one_geometrically_cyclic_native_seed
    (G : GeometricCycleClassSpine V H)
    (Z : codimensionCycles V.X p)
    (hcyclic : SeedCyclicForActualGeometry G Z)
    (alpha : RationalSingularCohomology H.analytification (2 * p))
    (halpha : alpha ∈ rationalHodgeSubspace (H.hodgeBigrading p)) :
    ∃ C : codimensionCycles V.X p,
      H.cycleClass p C = alpha := by
  have htop :=
    (native_orbit_top_iff_seed_geometrically_cyclic G Z).2 hcyclic
  have hin : (⟨alpha, halpha⟩ : ClassicalHodgeFiber V H p) ∈
      nativeOrbitHodgeSpan G Z := by
    rw [htop]
    trivial
  obtain ⟨C, hC⟩ :=
    native_orbit_span_within_actual_cycle_range G Z hin
  exact ⟨C, congrArg Subtype.val hC⟩

/-- The previous stronger global geometric irreducibility assumption
implies this weaker local cyclicity whenever the actual native seed
is nonzero. -/
theorem local_cyclicity_of_global_geometric_irreducibility
    (G : GeometricCycleClassSpine V H)
    (Z : codimensionCycles V.X p)
    (hnz : geometricHodgeClass G Z ≠ 0)
    (hirred : ActualHodgeCorrespondenceIrreducible
      (V := V) (H := H) (p := p)) :
    SeedCyclicForActualGeometry G Z := by
  intro S hstable hseed
  rcases hirred S hstable with hbot | htop
  · have hzero : geometricHodgeClass G Z = 0 := by
      have hz : geometricHodgeClass G Z ∈
          (⊥ : Submodule ℚ (ClassicalHodgeFiber V H p)) := by
        rw [← hbot]
        exact hseed
      simpa using hz
    exact False.elim (hnz hzero)
  · exact htop

#check native_orbit_minimal_among_actual_geometric_invariants
#check SeedCyclicForActualGeometry
#check native_orbit_top_iff_seed_geometrically_cyclic
#check hodge_cycles_from_one_geometrically_cyclic_native_seed
#check local_cyclicity_of_global_geometric_irreducibility

#print axioms native_orbit_minimal_among_actual_geometric_invariants
#print axioms native_orbit_top_iff_seed_geometrically_cyclic
#print axioms hodge_cycles_from_one_geometrically_cyclic_native_seed

end GSTResearchUniversalOrbitClosureLaw
