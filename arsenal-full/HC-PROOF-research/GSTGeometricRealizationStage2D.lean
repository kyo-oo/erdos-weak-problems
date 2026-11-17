import Mathlib
import Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic
import GSTGeometricRealizationStage2C

/-!
# STAGE 2D — NATIVE CODIMENSION-p CYCLES

Stage 2C replaced the abstract geometric carrier by actual Mathlib schemes
and actual Mathlib algebraic cycles.  Stage 2D removes one more abstract
parameter: the cycle space itself.

For a scheme X and p : Nat we define the rational codimension-p cycle
submodule directly as those native algebraic cycles whose support lies on
points of coheight p.  For p = 1 this is exactly Mathlib's Weil-divisor
support condition.

The remaining supplied semantics are now exactly the objects not natively
provided by the pinned Mathlib stack:

* rational degree-2p cohomology;
* the genuine rational (p,p) Hodge subspace;
* the genuine cohomological cycle-class map;
* the smooth-projective-over-C eligibility predicate.

No fixed Fin 12 geometry occurs in the universal theorem.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000000

namespace GSTGeometricRealizationStage2D

open GSTGeometricRealizationStage2
open GSTGeometricRealizationStage2B
open GSTGeometricRealizationStage2C
open AlgebraicGeometry

universe u

/-- Native rational codimension-p algebraic cycles on X:
support is contained in the coheight-p locus. -/
noncomputable def codimensionCycles
    (X : Scheme.{u}) (p : Nat) :
    Submodule ℚ (AlgebraicCycle X ℚ) where
  carrier :=
    {Z | Z.support ⊆ {x : X | Order.coheight x = p}}
  zero_mem' := by
    intro x hx
    exact (hx rfl).elim
  add_mem' := by
    intro Z W hZ hW
    exact (Function.support_add _ _).trans (Set.union_subset hZ hW)
  smul_mem' := by
    intro a Z hZ x hx
    apply hZ
    show Z x ≠ 0
    intro hzx
    apply hx
    simp [hzx]

@[simp]
theorem mem_codimensionCycles_iff
    (X : Scheme.{u}) (p : Nat) (Z : AlgebraicCycle X ℚ) :
    Z ∈ codimensionCycles X p ↔
      Z.support ⊆ {x : X | Order.coheight x = p} :=
  Iff.rfl

/-- Codimension one specializes to the expected coheight-one support
condition.  The pinned Mathlib revision has native AlgebraicCycle but does
not yet expose its later IsWeilDivisor predicate. -/
theorem mem_codimensionCycles_one_iff
    (X : Scheme.{u}) (Z : AlgebraicCycle X ℚ) :
    Z ∈ codimensionCycles X 1 ↔
      Z.support ⊆ {x : X | Order.coheight x = 1} :=
  Iff.rfl

/-- A realization whose cycle domain is the canonical native codimension-p
cycle submodule; no arbitrary cycleSpace field remains. -/
structure CodimensionHodgeRealization
    (N p : Nat) (X : Scheme.{u}) (Coh : Type*)
    [AddCommGroup Coh] [Module ℚ Coh] where
  hodge : Submodule ℚ Coh
  cycleClass : codimensionCycles X p →ₗ[ℚ] Coh
  encode : Coh →ₗ[ℚ] RatAddress N
  encode_injective : Function.Injective encode
  hodgeSupport : Finset (Fin N)
  hodge_supported :
    ∀ alpha : Coh, alpha ∈ hodge ->
      SupportedOn hodgeSupport (encode alpha)
  basisCycle : Fin N -> codimensionCycles X p
  basisCycle_address :
    ∀ i : Fin N, i ∈ hodgeSupport ->
      encode (cycleClass (basisCycle i)) = addressBasis i

variable {N p : Nat} {X : Scheme.{u}} {Coh : Type*}
  [AddCommGroup Coh] [Module ℚ Coh]

/-- Forgetting that the cycle submodule was canonically determined by
codimension gives exactly a Stage-2C realization. -/
noncomputable def CodimensionHodgeRealization.toNativeSchemeRealization
    (R : CodimensionHodgeRealization N p X Coh) :
    NativeSchemeHodgeRealization N X Coh where
  hodge := R.hodge
  cycleSpace := codimensionCycles X p
  cycleClass := R.cycleClass
  encode := R.encode
  encode_injective := R.encode_injective
  hodgeSupport := R.hodgeSupport
  hodge_supported := R.hodge_supported
  basisCycle := R.basisCycle
  basisCycle_address := R.basisCycle_address

/-- Explicit codimension-p cycle selector on the Hodge submodule. -/
noncomputable def codimensionCycleSelector
    (R : CodimensionHodgeRealization N p X Coh)
    (alpha : R.hodge) : codimensionCycles X p :=
  nativeCycleSelector R.toNativeSchemeRealization alpha

/-- The codimension selector is a verified right inverse of the canonical
codimension-p cycle-class map on the Hodge sector. -/
theorem codimensionCycleSelector_spec
    (R : CodimensionHodgeRealization N p X Coh)
    (alpha : R.hodge) :
    R.cycleClass (codimensionCycleSelector R alpha) = alpha.1 := by
  exact nativeCycleSelector_spec R.toNativeSchemeRealization alpha

/-- **NATIVE CODIMENSION-p FIBER THEOREM.**
Every Hodge class in a supplied realization is represented by an actual
Mathlib algebraic cycle supported in codimension p. -/
theorem hodge_class_has_codimension_cycle
    (R : CodimensionHodgeRealization N p X Coh)
    (alpha : Coh) (halpha : alpha ∈ R.hodge) :
    ∃ Z : AlgebraicCycle X ℚ, ∃ hZ : Z ∈ codimensionCycles X p,
      R.cycleClass ⟨Z, hZ⟩ = alpha := by
  exact hodge_class_has_native_algebraic_cycle
    R.toNativeSchemeRealization alpha halpha

/-- Exact submodule form of the codimension-p fiber theorem. -/
theorem codimension_hodge_subspace_le_cycleClass_range
    (R : CodimensionHodgeRealization N p X Coh) :
    R.hodge ≤ LinearMap.range R.cycleClass := by
  exact native_hodge_subspace_le_cycleClass_range
    R.toNativeSchemeRealization

/-- The universal target with cycle domains now canonically fixed by
scheme and codimension. -/
def UniversalCodimensionHodgeStatement
    (eligible : Scheme.{u} -> Prop)
    (Coh : Scheme.{u} -> Nat -> Type*)
    [∀ X p, AddCommGroup (Coh X p)]
    [∀ X p, Module ℚ (Coh X p)]
    (HodgeSubspace : ∀ X p, Submodule ℚ (Coh X p))
    (cycleClass :
      ∀ X p, codimensionCycles X p →ₗ[ℚ] Coh X p) : Prop :=
  ∀ X : Scheme.{u}, eligible X ->
    ∀ p : Nat,
      HodgeSubspace X p ≤ LinearMap.range (cycleClass X p)

/-- **STAGE-2D VARIABLE-RANK FAMILY THEOREM.**

For every eligible actual scheme X and every codimension p, a finite
realization of the genuine Hodge subspace by native codimension-p cycles
implies the exact universal Hodge subspace target.

The address rank N X p may vary arbitrarily with X and p. -/
theorem universal_codimension_hodge_of_realization_family
    (eligible : Scheme.{u} -> Prop)
    (Coh : Scheme.{u} -> Nat -> Type*)
    [∀ X p, AddCommGroup (Coh X p)]
    [∀ X p, Module ℚ (Coh X p)]
    (HodgeSubspace : ∀ X p, Submodule ℚ (Coh X p))
    (cycleClass :
      ∀ X p, codimensionCycles X p →ₗ[ℚ] Coh X p)
    (N : Scheme.{u} -> Nat -> Nat)
    (R : ∀ X p, eligible X ->
      CodimensionHodgeRealization (N X p) p X (Coh X p))
    (hHodge : ∀ X p hX,
      (R X p hX).hodge = HodgeSubspace X p)
    (hCycleClass : ∀ X p hX,
      (R X p hX).cycleClass = cycleClass X p) :
    UniversalCodimensionHodgeStatement
      eligible Coh HodgeSubspace cycleClass := by
  intro X hX p alpha halpha
  have halphaR : alpha ∈ (R X p hX).hodge := by
    rw [hHodge X p hX]
    exact halpha
  obtain ⟨Z, hZmem, hZclass⟩ :=
    hodge_class_has_codimension_cycle
      (R X p hX) alpha halphaR
  refine ⟨⟨Z, hZmem⟩, ?_⟩
  have hcompat :=
    congrArg (fun f => f ⟨Z, hZmem⟩) (hCycleClass X p hX)
  calc
    cycleClass X p ⟨Z, hZmem⟩
        = (R X p hX).cycleClass ⟨Z, hZmem⟩ := hcompat.symm
    _ = alpha := hZclass

/-- The remaining obligation for one actual scheme and one codimension. -/
def CodimensionFiberRealizationObligation
    (X : Scheme.{u}) (p : Nat) (Coh : Type*)
    [AddCommGroup Coh] [Module ℚ Coh]
    (H : Submodule ℚ Coh)
    (cl : codimensionCycles X p →ₗ[ℚ] Coh) : Prop :=
  ∃ N : Nat, ∃ R : CodimensionHodgeRealization N p X Coh,
    R.hodge = H ∧ R.cycleClass = cl

/-- Closing the native codimension-p realization obligation closes the
Hodge subspace target for that fiber. -/
theorem hodge_of_codimension_fiber_realization
    (X : Scheme.{u}) (p : Nat) (Coh : Type*)
    [AddCommGroup Coh] [Module ℚ Coh]
    (H : Submodule ℚ Coh)
    (cl : codimensionCycles X p →ₗ[ℚ] Coh)
    (hR : CodimensionFiberRealizationObligation X p Coh H cl) :
    H ≤ LinearMap.range cl := by
  rcases hR with ⟨N, R, hH, hcl⟩
  intro alpha halpha
  have halphaR : alpha ∈ R.hodge := by
    rw [hH]
    exact halpha
  obtain ⟨Z, hZmem, hZclass⟩ :=
    hodge_class_has_codimension_cycle R alpha halphaR
  refine ⟨⟨Z, hZmem⟩, ?_⟩
  have hcompat := congrArg (fun f => f ⟨Z, hZmem⟩) hcl
  calc
    cl ⟨Z, hZmem⟩
        = R.cycleClass ⟨Z, hZmem⟩ := hcompat.symm
    _ = alpha := hZclass

#check codimensionCycles
#check mem_codimensionCycles_iff
#check mem_codimensionCycles_one_iff
#check CodimensionHodgeRealization
#check codimensionCycleSelector
#check codimensionCycleSelector_spec
#check hodge_class_has_codimension_cycle
#check codimension_hodge_subspace_le_cycleClass_range
#check UniversalCodimensionHodgeStatement
#check universal_codimension_hodge_of_realization_family
#check CodimensionFiberRealizationObligation
#check hodge_of_codimension_fiber_realization

#print axioms mem_codimensionCycles_one_iff
#print axioms codimensionCycleSelector_spec
#print axioms hodge_class_has_codimension_cycle
#print axioms codimension_hodge_subspace_le_cycleClass_range
#print axioms universal_codimension_hodge_of_realization_family
#print axioms hodge_of_codimension_fiber_realization

end GSTGeometricRealizationStage2D
