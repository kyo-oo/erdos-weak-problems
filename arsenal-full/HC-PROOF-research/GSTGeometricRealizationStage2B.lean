import Mathlib
import GSTGeometricRealizationStage2

/-!
# STAGE 2B — HODGE SUBSPACE REALIZATION

Stage 2A proved a non-circular finite realization criterion using an
arbitrary Hodge predicate.  This layer strengthens the semantic interface:
the Hodge classes are now an honest rational submodule of cohomology and the
cycle-class map is an honest Q-linear map.

For a supplied geometric fiber the target is exactly

  HodgeSubspace <= LinearMap.range cycleClass.

The proof still uses only finite coordinates, injectivity, support control,
and algebraic realization of the support basis coordinates.  It does NOT
assume surjectivity of the cycle-class map.

A literal proof of the classical Hodge conjecture still requires a native
instantiation in which the fiber is the actual rational cohomology of every
smooth projective complex variety, HodgeSubspace is its genuine (p,p)
subspace, and cycleClass is the genuine algebraic cycle-class map.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000000

namespace GSTGeometricRealizationStage2B

open GSTGeometricRealizationStage2

structure HodgeSubspaceRealization
    (N : Nat) (Coh CycleQ : Type*)
    [AddCommGroup Coh] [Module ℚ Coh]
    [AddCommGroup CycleQ] [Module ℚ CycleQ] where
  hodge : Submodule ℚ Coh
  cycleClass : CycleQ →ₗ[ℚ] Coh
  encode : Coh →ₗ[ℚ] RatAddress N
  encode_injective : Function.Injective encode
  hodgeSupport : Finset (Fin N)
  hodge_supported :
    ∀ alpha : Coh, alpha ∈ hodge ->
      SupportedOn hodgeSupport (encode alpha)
  basisCycle : Fin N -> CycleQ
  basisCycle_address :
    ∀ i : Fin N, i ∈ hodgeSupport ->
      encode (cycleClass (basisCycle i)) = addressBasis i

variable {N : Nat} {Coh CycleQ : Type*}
  [AddCommGroup Coh] [Module ℚ Coh]
  [AddCommGroup CycleQ] [Module ℚ CycleQ]

/-- Forget only the extra submodule structure.  No mathematical assumption
is added: membership in the Hodge submodule becomes the Stage-2A predicate. -/
def HodgeSubspaceRealization.toFiniteHodgeRealization
    (R : HodgeSubspaceRealization N Coh CycleQ) :
    FiniteHodgeRealization N Coh CycleQ where
  isHodge := fun alpha => alpha ∈ R.hodge
  cycleClass := R.cycleClass
  encode := R.encode
  encode_injective := R.encode_injective
  hodgeSupport := R.hodgeSupport
  hodge_supported := R.hodge_supported
  basisCycle := R.basisCycle
  basisCycle_address := R.basisCycle_address

/-- The constructive algebraic-cycle witness inherited from Stage 2A. -/
noncomputable def subspaceCycleWitness
    (R : HodgeSubspaceRealization N Coh CycleQ)
    (alpha : Coh) : CycleQ :=
  cycleWitness R.toFiniteHodgeRealization alpha

/-- The witness has exactly the same encoded cohomology class as alpha. -/
theorem subspaceCycleWitness_address
    (R : HodgeSubspaceRealization N Coh CycleQ)
    (alpha : Coh) (halpha : alpha ∈ R.hodge) :
    R.encode (R.cycleClass (subspaceCycleWitness R alpha)) =
      R.encode alpha := by
  exact cycleWitness_address R.toFiniteHodgeRealization alpha halpha

/-- Explicit cycle selector on the Hodge submodule of a Stage-2B
realization. -/
noncomputable def subspaceCycleSelector
    (R : HodgeSubspaceRealization N Coh CycleQ)
    (alpha : R.hodge) : CycleQ :=
  subspaceCycleWitness R alpha.1

/-- The Stage-2B selector is a verified right inverse of the linear cycle
class map on the Hodge submodule. -/
theorem subspaceCycleSelector_spec
    (R : HodgeSubspaceRealization N Coh CycleQ)
    (alpha : R.hodge) :
    R.cycleClass (subspaceCycleSelector R alpha) = alpha.1 := by
  apply R.encode_injective
  exact subspaceCycleWitness_address R alpha.1 alpha.2

/-- **STAGE-2B FIBER THEOREM.**
Every class in the rational Hodge subspace lies in the linear range of the
cycle-class map.  This is the exact submodule form of the target. -/
theorem hodge_subspace_le_cycleClass_range
    (R : HodgeSubspaceRealization N Coh CycleQ) :
    R.hodge ≤ LinearMap.range R.cycleClass := by
  intro alpha halpha
  obtain ⟨Z, hZ⟩ :=
    hodge_class_has_cycle_witness
      R.toFiniteHodgeRealization alpha halpha
  exact ⟨Z, hZ⟩

/-- Elementwise form of the same Stage-2B fiber theorem. -/
theorem hodge_class_has_geometric_cycle
    (R : HodgeSubspaceRealization N Coh CycleQ)
    (alpha : Coh) (halpha : alpha ∈ R.hodge) :
    ∃ Z : CycleQ, R.cycleClass Z = alpha := by
  exact hodge_class_has_cycle_witness
    R.toFiniteHodgeRealization alpha halpha

/-- The exact universal subspace-shaped Hodge target. -/
def UniversalHodgeSubspaceStatement
    {Variety : Type*}
    (eligible : Variety -> Prop)
    (Coh CycleQ : Variety -> Nat -> Type*)
    [∀ X p, AddCommGroup (Coh X p)]
    [∀ X p, Module ℚ (Coh X p)]
    [∀ X p, AddCommGroup (CycleQ X p)]
    [∀ X p, Module ℚ (CycleQ X p)]
    (HodgeSubspace : ∀ X p, Submodule ℚ (Coh X p))
    (cycleClass : ∀ X p, CycleQ X p →ₗ[ℚ] Coh X p) : Prop :=
  ∀ X : Variety, eligible X ->
    ∀ p : Nat,
      HodgeSubspace X p ≤ LinearMap.range (cycleClass X p)

/-- **VARIABLE-RANK STAGE-2B FAMILY THEOREM.**

The address rank may vary with X and p.  If every eligible geometric fiber
admits a HodgeSubspaceRealization whose Hodge submodule and cycle-class map
are definitionally identified with the intended geometric ones, then the
exact universal subspace target follows.

This theorem contains no fixed Fin 12 carrier. -/
theorem universal_hodge_subspace_of_realization_family
    {Variety : Type*}
    (eligible : Variety -> Prop)
    (Coh CycleQ : Variety -> Nat -> Type*)
    [∀ X p, AddCommGroup (Coh X p)]
    [∀ X p, Module ℚ (Coh X p)]
    [∀ X p, AddCommGroup (CycleQ X p)]
    [∀ X p, Module ℚ (CycleQ X p)]
    (HodgeSubspace : ∀ X p, Submodule ℚ (Coh X p))
    (cycleClass : ∀ X p, CycleQ X p →ₗ[ℚ] Coh X p)
    (N : Variety -> Nat -> Nat)
    (R : ∀ X p, eligible X ->
      HodgeSubspaceRealization (N X p) (Coh X p) (CycleQ X p))
    (hHodge : ∀ X p hX,
      (R X p hX).hodge = HodgeSubspace X p)
    (hCycle : ∀ X p hX,
      (R X p hX).cycleClass = cycleClass X p) :
    UniversalHodgeSubspaceStatement
      eligible Coh CycleQ HodgeSubspace cycleClass := by
  intro X hX p alpha halpha
  have halphaR : alpha ∈ (R X p hX).hodge := by
    rw [hHodge X p hX]
    exact halpha
  obtain ⟨Z, hZ⟩ :=
    hodge_class_has_geometric_cycle (R X p hX) alpha halphaR
  refine ⟨Z, ?_⟩
  rw [← hCycle X p hX]
  exact hZ

/-- Predicate-shaped Stage 2A and submodule-shaped Stage 2B agree
elementwise when the predicate is submodule membership. -/
theorem subspace_target_implies_predicate_target
    (R : HodgeSubspaceRealization N Coh CycleQ) :
    HodgeCycleSurjectivity
      (fun alpha => alpha ∈ R.hodge)
      R.cycleClass := by
  intro alpha halpha
  exact hodge_class_has_geometric_cycle R alpha halpha

/-- The exact remaining obligation for one geometric fiber: construct the
realization data.  This proposition is intentionally a type of data, not an
primitive assumption and not a theorem claimed solved by the finite GST carrier. -/
def FiberRealizationObligation
    (H : Submodule ℚ Coh)
    (cl : CycleQ →ₗ[ℚ] Coh) : Prop :=
  ∃ N : Nat, ∃ R : HodgeSubspaceRealization N Coh CycleQ,
    R.hodge = H ∧ R.cycleClass = cl

/-- Once the per-fiber realization obligation is supplied, the Hodge
subspace conclusion follows immediately and non-circularly. -/
theorem hodge_of_fiber_realization_obligation
    (H : Submodule ℚ Coh)
    (cl : CycleQ →ₗ[ℚ] Coh)
    (hR : FiberRealizationObligation H cl) :
    H ≤ LinearMap.range cl := by
  rcases hR with ⟨N, R, hH, hcl⟩
  intro alpha halpha
  have halphaR : alpha ∈ R.hodge := by
    rw [hH]
    exact halpha
  obtain ⟨Z, hZ⟩ := hodge_class_has_geometric_cycle R alpha halphaR
  refine ⟨Z, ?_⟩
  rw [← hcl]
  exact hZ

#check HodgeSubspaceRealization
#check HodgeSubspaceRealization.toFiniteHodgeRealization
#check subspaceCycleWitness
#check subspaceCycleWitness_address
#check subspaceCycleSelector
#check subspaceCycleSelector_spec
#check hodge_subspace_le_cycleClass_range
#check hodge_class_has_geometric_cycle
#check UniversalHodgeSubspaceStatement
#check universal_hodge_subspace_of_realization_family
#check subspace_target_implies_predicate_target
#check FiberRealizationObligation
#check hodge_of_fiber_realization_obligation

#print axioms subspaceCycleWitness_address
#print axioms subspaceCycleSelector_spec
#print axioms hodge_subspace_le_cycleClass_range
#print axioms hodge_class_has_geometric_cycle
#print axioms universal_hodge_subspace_of_realization_family
#print axioms hodge_of_fiber_realization_obligation

end GSTGeometricRealizationStage2B
