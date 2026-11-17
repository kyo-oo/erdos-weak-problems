import Mathlib

/-!
# STAGE 2 — FINITE GEOMETRIC REALIZATION CRITERION

This file is the semantic upgrade demanded by the audit of the HC proof.

The old transfer bridge used one fixed carrier, Fin 12 -> Z, and a
rank-one support condition. That is a valid finite theorem, but it cannot
serve as the cohomology of arbitrary smooth projective complex varieties.

Stage 2 therefore removes both restrictions.

* the address dimension is an arbitrary N;
* the Hodge sector may occupy an arbitrary finite set of coordinates;
* the geometric cohomology type and rational cycle type are arbitrary;
* an injective address map must be supplied;
* each Hodge-support basis coordinate must be realized by an algebraic
  cycle;
* the cycle-class and address maps are honest Q-linear maps.

From these data Lean proves the exact transfer theorem: every Hodge class
has a rational algebraic-cycle preimage.

This theorem is NON-CIRCULAR: the structure does not assume cycle-class
surjectivity on Hodge classes. It asks only for coordinate preservation,
injectivity, finite Hodge support, and algebraic realization of the
individual support-basis coordinates.

What remains for a literal classical Hodge-conjecture proof is an
instantiation of this criterion for the actual cohomology and algebraic
cycles of every smooth projective complex variety. Current Mathlib does
not yet expose the complete classical Hodge/Chow/cycle-class stack needed
to write that instantiation natively.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000000

namespace GSTGeometricRealizationStage2

abbrev RatAddress (N : Nat) : Type := Fin N -> ℚ

def addressBasis {N : Nat} (i : Fin N) : RatAddress N :=
  fun j => if j = i then 1 else 0

def SupportedOn {N : Nat} (S : Finset (Fin N)) (phi : RatAddress N) : Prop :=
  ∀ i : Fin N, i ∉ S -> phi i = 0

theorem address_reconstruct {N : Nat}
    (S : Finset (Fin N)) (phi : RatAddress N)
    (hphi : SupportedOn S phi) :
    phi = ∑ i ∈ S, (phi i) • addressBasis i := by
  classical
  funext j
  by_cases hj : j ∈ S
  · simp [addressBasis, hj]
  · have hz := hphi j hj
    simp [addressBasis, hj, hz]

structure FiniteHodgeRealization
    (N : Nat) (Coh CycleQ : Type*)
    [AddCommGroup Coh] [Module ℚ Coh]
    [AddCommGroup CycleQ] [Module ℚ CycleQ] where
  isHodge : Coh -> Prop
  cycleClass : CycleQ →ₗ[ℚ] Coh
  encode : Coh →ₗ[ℚ] RatAddress N
  encode_injective : Function.Injective encode
  hodgeSupport : Finset (Fin N)
  hodge_supported :
    ∀ alpha : Coh, isHodge alpha -> SupportedOn hodgeSupport (encode alpha)
  basisCycle : Fin N -> CycleQ
  basisCycle_address :
    ∀ i : Fin N, i ∈ hodgeSupport ->
      encode (cycleClass (basisCycle i)) = addressBasis i

variable {N : Nat} {Coh CycleQ : Type*}
  [AddCommGroup Coh] [Module ℚ Coh]
  [AddCommGroup CycleQ] [Module ℚ CycleQ]

noncomputable def cycleWitness
    (R : FiniteHodgeRealization N Coh CycleQ) (alpha : Coh) : CycleQ :=
  ∑ i ∈ R.hodgeSupport, (R.encode alpha i) • R.basisCycle i

theorem cycleWitness_address
    (R : FiniteHodgeRealization N Coh CycleQ)
    (alpha : Coh) (halpha : R.isHodge alpha) :
    R.encode (R.cycleClass (cycleWitness R alpha)) = R.encode alpha := by
  classical
  have hs : SupportedOn R.hodgeSupport (R.encode alpha) :=
    R.hodge_supported alpha halpha
  calc
    R.encode (R.cycleClass (cycleWitness R alpha))
        = ∑ i ∈ R.hodgeSupport,
            (R.encode alpha i) •
              R.encode (R.cycleClass (R.basisCycle i)) := by
              simp [cycleWitness]
    _ = ∑ i ∈ R.hodgeSupport,
          (R.encode alpha i) • addressBasis i := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [R.basisCycle_address i hi]
    _ = R.encode alpha :=
      (address_reconstruct R.hodgeSupport (R.encode alpha) hs).symm

theorem hodge_class_has_cycle_witness
    (R : FiniteHodgeRealization N Coh CycleQ)
    (alpha : Coh) (halpha : R.isHodge alpha) :
    ∃ Z : CycleQ, R.cycleClass Z = alpha := by
  refine ⟨cycleWitness R alpha, ?_⟩
  apply R.encode_injective
  exact cycleWitness_address R alpha halpha

theorem cycleClass_surjective_on_hodge
    (R : FiniteHodgeRealization N Coh CycleQ) :
    ∀ alpha : Coh, R.isHodge alpha ->
      ∃ Z : CycleQ, R.cycleClass Z = alpha :=
  fun alpha halpha => hodge_class_has_cycle_witness R alpha halpha

theorem singleton_support_rank_one
    (R : FiniteHodgeRealization N Coh CycleQ)
    (i : Fin N) (hS : R.hodgeSupport = {i})
    (alpha : Coh) (halpha : R.isHodge alpha) :
    R.encode alpha = (R.encode alpha i) • addressBasis i := by
  classical
  have hs := R.hodge_supported alpha halpha
  rw [hS] at hs
  have hrec := address_reconstruct ({i} : Finset (Fin N)) (R.encode alpha) hs
  simpa [addressBasis] using hrec

theorem stage2_realization_crown
    (R : FiniteHodgeRealization N Coh CycleQ) :
    ∀ alpha : Coh, R.isHodge alpha ->
      ∃ Z : CycleQ, R.cycleClass Z = alpha :=
  cycleClass_surjective_on_hodge R


/-- The exact cycle-class-surjectivity statement for a supplied geometric
cohomology/cycle pair.  In a native classical instantiation, isHodge is the
rational (p,p)-Hodge predicate and cycleClass is the rational algebraic
cycle-class map. -/
def HodgeCycleSurjectivity
    {Coh CycleQ : Type*}
    (isHodge : Coh -> Prop) (cycleClass : CycleQ -> Coh) : Prop :=
  ∀ alpha : Coh, isHodge alpha -> ∃ Z : CycleQ, cycleClass Z = alpha

/-- **SURJECTIVE TARGET SELECTOR.**  Any supplied cycle-surjectivity
proof can be Skolemized into an explicit witness function on the Hodge
subtype.  No realization data is invented: the selector exists exactly when
the stated surjectivity proof is available. -/
noncomputable def hodgeCycleSelector
    {Coh CycleQ : Type*}
    (isHodge : Coh -> Prop) (cycleClass : CycleQ -> Coh)
    (h : HodgeCycleSurjectivity isHodge cycleClass) :
    {alpha : Coh // isHodge alpha} -> CycleQ :=
  fun alpha => Classical.choose (h alpha.1 alpha.2)

/-- The selector is a verified right inverse of the cycle-class map on the
Hodge sector. -/
theorem hodgeCycleSelector_spec
    {Coh CycleQ : Type*}
    (isHodge : Coh -> Prop) (cycleClass : CycleQ -> Coh)
    (h : HodgeCycleSurjectivity isHodge cycleClass)
    (alpha : {alpha : Coh // isHodge alpha}) :
    cycleClass (hodgeCycleSelector isHodge cycleClass h alpha) = alpha.1 :=
  Classical.choose_spec (h alpha.1 alpha.2)

/-- A concrete finite realization therefore carries its own explicit
right-inverse selector on Hodge classes. -/
theorem finite_realization_selector_spec
    (R : FiniteHodgeRealization N Coh CycleQ)
    (alpha : {alpha : Coh // R.isHodge alpha}) :
    R.cycleClass (cycleWitness R alpha.1) = alpha.1 := by
  apply R.encode_injective
  exact cycleWitness_address R alpha.1 alpha.2

/-- Stage 2A closes the exact cycle-surjectivity target for every geometric
fiber carrying a FiniteHodgeRealization.  Stage 2B is precisely the task of
constructing such a realization for each genuine classical fiber. -/
theorem stage2_closes_cycle_surjectivity
    (R : FiniteHodgeRealization N Coh CycleQ) :
    HodgeCycleSurjectivity R.isHodge R.cycleClass :=
  stage2_realization_crown R


/-- The exact arbitrary-object shape of the classical Hodge target.

In a future native instantiation:
* Variety is the type of complex algebraic varieties under consideration;
* eligible means smooth and projective over C;
* Coh X p is rational degree-2p cohomology;
* isHodge X p alpha is the rational (p,p)-condition;
* CycleQ X p is the rational codimension-p cycle space;
* cycleClass is the classical cycle-class map.

No one of those semantic identifications is supplied by the twelve-cell
GST carrier itself. -/
def UniversalHodgeStatement
    {Variety : Type*}
    (eligible : Variety -> Prop)
    (Coh CycleQ : Variety -> Nat -> Type*)
    (isHodge : ∀ X p, Coh X p -> Prop)
    (cycleClass : ∀ X p, CycleQ X p -> Coh X p) : Prop :=
  ∀ X : Variety, eligible X ->
    ∀ p : Nat, ∀ alpha : Coh X p,
      isHodge X p alpha ->
        ∃ Z : CycleQ X p, cycleClass X p Z = alpha

/-- Once cycle-surjectivity has been proved fiber-by-fiber, the universal
arbitrary-object target follows with no additional mathematical content. -/
theorem universal_hodge_of_fiberwise_surjectivity
    {Variety : Type*}
    (eligible : Variety -> Prop)
    (Coh CycleQ : Variety -> Nat -> Type*)
    (isHodge : ∀ X p, Coh X p -> Prop)
    (cycleClass : ∀ X p, CycleQ X p -> Coh X p)
    (h : ∀ X : Variety, eligible X ->
      ∀ p : Nat,
        HodgeCycleSurjectivity (isHodge X p) (cycleClass X p)) :
    UniversalHodgeStatement eligible Coh CycleQ isHodge cycleClass := by
  intro X hX p alpha halpha
  exact h X hX p alpha halpha


/-- **VARIABLE-RANK STAGE-2 FAMILY THEOREM.**

The address dimension is allowed to depend on both the geometric object X
and the codimension p.  Two semantic preservation laws prevent a fake
realization:

* the internal realization predicate is equivalent to the intended Hodge
  predicate on the actual cohomology fiber;
* the internal linear cycle-class map agrees pointwise with the intended
  geometric cycle-class map.

Consequently, a FiniteHodgeRealization for every eligible X and p proves
the exact universal Hodge target.  No global Fin 12 identification appears
anywhere in this theorem. -/
theorem universal_hodge_of_realization_family
    {Variety : Type*}
    (eligible : Variety -> Prop)
    (Coh CycleQ : Variety -> Nat -> Type*)
    [∀ X p, AddCommGroup (Coh X p)]
    [∀ X p, Module ℚ (Coh X p)]
    [∀ X p, AddCommGroup (CycleQ X p)]
    [∀ X p, Module ℚ (CycleQ X p)]
    (isHodge : ∀ X p, Coh X p -> Prop)
    (cycleClass : ∀ X p, CycleQ X p -> Coh X p)
    (N : Variety -> Nat -> Nat)
    (R : ∀ X p, eligible X ->
      FiniteHodgeRealization (N X p) (Coh X p) (CycleQ X p))
    (hHodge : ∀ X p hX alpha,
      (R X p hX).isHodge alpha ↔ isHodge X p alpha)
    (hCycle : ∀ X p hX Z,
      (R X p hX).cycleClass Z = cycleClass X p Z) :
    UniversalHodgeStatement eligible Coh CycleQ isHodge cycleClass := by
  intro X hX p alpha halpha
  have hRealHodge : (R X p hX).isHodge alpha :=
    (hHodge X p hX alpha).mpr halpha
  obtain ⟨Z, hZ⟩ :=
    hodge_class_has_cycle_witness (R X p hX) alpha hRealHodge
  refine ⟨Z, ?_⟩
  rw [← hCycle X p hX Z]
  exact hZ

#check RatAddress
#check SupportedOn
#check FiniteHodgeRealization
#check address_reconstruct
#check cycleWitness
#check cycleWitness_address
#check hodge_class_has_cycle_witness
#check cycleClass_surjective_on_hodge
#check singleton_support_rank_one
#check stage2_realization_crown
#check HodgeCycleSurjectivity
#check hodgeCycleSelector
#check hodgeCycleSelector_spec
#check finite_realization_selector_spec
#check stage2_closes_cycle_surjectivity
#check UniversalHodgeStatement
#check universal_hodge_of_fiberwise_surjectivity
#check universal_hodge_of_realization_family

#print axioms address_reconstruct
#print axioms cycleWitness_address
#print axioms hodge_class_has_cycle_witness
#print axioms stage2_realization_crown
#print axioms stage2_closes_cycle_surjectivity
#print axioms hodgeCycleSelector_spec
#print axioms finite_realization_selector_spec
#print axioms universal_hodge_of_fiberwise_surjectivity
#print axioms universal_hodge_of_realization_family


/-! ## Unbounded algebraic address realization

The address universe need not have any fixed finite rank. Each encoded class
has its own finite support. Basis cycle generation remains an explicit
geometric obligation and is not inferred from GST coordinates alone.
-/
structure CompactHodgeRealization (ι : Type*) (Coh CycleQ : Type*)
    [AddCommGroup Coh] [Module ℚ Coh] [AddCommGroup CycleQ] [Module ℚ CycleQ] where
  isHodge : Coh → Prop
  cycleClass : CycleQ →ₗ[ℚ] Coh
  encode : Coh →ₗ[ℚ] (ι →₀ ℚ)
  encode_injective : Function.Injective encode
  hodgeSupport : Set ι
  hodge_supported : ∀ alpha, isHodge alpha →
    ∀ i ∈ (encode alpha).support, i ∈ hodgeSupport
  basisCycle : ι → CycleQ
  basisCycle_address : ∀ i ∈ hodgeSupport,
    encode (cycleClass (basisCycle i)) = Finsupp.single i 1

noncomputable def compactCycleWitness {ι : Type*}
    (R : CompactHodgeRealization ι Coh CycleQ) (alpha : Coh) : CycleQ :=
  (R.encode alpha).sum (fun i q => q • R.basisCycle i)

theorem compactCycleWitness_spec {ι : Type*}
    (R : CompactHodgeRealization ι Coh CycleQ) (alpha : Coh) (ha : R.isHodge alpha) :
    R.cycleClass (compactCycleWitness R alpha) = alpha := by
  classical
  apply R.encode_injective
  change R.encode (R.cycleClass
    (∑ i ∈ (R.encode alpha).support, (R.encode alpha i) • R.basisCycle i)) = _
  simp only [map_sum, map_smul]
  have hb : (∑ i ∈ (R.encode alpha).support,
      (R.encode alpha i) • R.encode (R.cycleClass (R.basisCycle i))) =
      ∑ i ∈ (R.encode alpha).support,
        (R.encode alpha i) • Finsupp.single i 1 := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [R.basisCycle_address i (R.hodge_supported alpha ha i hi)]
  rw [hb]
  simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
  change (R.encode alpha).sum Finsupp.single = R.encode alpha
  exact (R.encode alpha).sum_single

theorem compact_realization_surjectivity {ι : Type*}
    (R : CompactHodgeRealization ι Coh CycleQ) :
    ∀ alpha, R.isHodge alpha → ∃ Z, R.cycleClass Z=alpha := by
  intro alpha ha
  exact ⟨compactCycleWitness R alpha, compactCycleWitness_spec R alpha ha⟩

#print axioms compactCycleWitness_spec

end GSTGeometricRealizationStage2
