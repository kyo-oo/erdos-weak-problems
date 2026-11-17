import GSTTruncatedWorldCohomologyRing
import Mathlib
import Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic
import GSTGeometricRealizationStage2B

/-!
# STAGE 2C — NATIVE SCHEME / ALGEBRAIC-CYCLE FRONT

Stage 2B upgraded the Hodge side to an honest rational submodule.
Stage 2C upgrades the geometric carrier itself:

* X is an actual Mathlib algebraic scheme;
* algebraic cycles are actual Mathlib AlgebraicGeometry.AlgebraicCycle X Q;
* the codimension-p cycle space is represented by a supplied Q-submodule
  of those native algebraic cycles;
* the rational Hodge subspace and cycle-class map remain supplied data,
  because the pinned Mathlib revision does not yet provide the complete
  classical Hodge/Chow/Betti cycle-class stack.

Thus the only abstract objects left are exactly the pieces Mathlib does
not natively expose.  No fixed Fin 12 geometry is used.

A literal classical Hodge proof still requires:
1. eligible X to mean smooth projective over C;
2. Coh X p to be genuine H^(2p)(X,Q);
3. hodge to be the genuine rational (p,p) subspace;
4. cycleSpace to represent codimension-p cycles modulo the appropriate
   rational equivalence / Chow construction;
5. cycleClass to be the genuine cohomological cycle-class map;
6. a realization certificate for every eligible X and p.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000000

namespace GSTGeometricRealizationStage2C

open GSTGeometricRealizationStage2
open GSTGeometricRealizationStage2B
open AlgebraicGeometry

universe u

/-! ### Rational scalar structure on native algebraic cycles

The pinned Mathlib revision gives locally-finite algebraic cycles their
additive-group structure, but not the ambient rational module instance.
For rational coefficients the missing action is canonical: scalar
multiplication is pointwise and cannot enlarge support, hence preserves
local finiteness. -/

noncomputable instance algebraicCycleRatSMul (X : Scheme.{u}) :
    SMul ℚ (AlgebraicCycle X ℚ) where
  smul q D :=
    { toFun := fun x => q * D x
      supportWithinDomain' := by
        intro x hx
        trivial
      supportLocallyFiniteWithinDomain' := by
        intro z hz
        obtain ⟨t, ht, hfin⟩ :=
          D.supportLocallyFiniteWithinDomain z (by trivial)
        refine ⟨t, ht, hfin.subset ?_⟩
        intro x hx
        rcases hx with ⟨hxt, hxq⟩
        refine ⟨hxt, ?_⟩
        show D x ≠ 0
        intro hDx
        apply hxq
        simp [hDx] }

@[simp]
theorem algebraicCycleRatSMul_apply
    (X : Scheme.{u}) (q : ℚ) (D : AlgebraicCycle X ℚ) (x : X) :
    (q • D) x = q * D x :=
  rfl

noncomputable instance algebraicCycleRatModule (X : Scheme.{u}) :
    Module ℚ (AlgebraicCycle X ℚ) := by
  let coeAdd : AlgebraicCycle X ℚ →+ (X → ℚ) :=
    { toFun := fun D => D
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  exact Function.Injective.module ℚ coeAdd
    Function.locallyFinsuppWithin.coe_injective
    (by
      intro q D
      rfl)

/-- A Stage-2 realization whose geometric cycle carrier is Mathlib's actual
algebraic-cycle type on an actual scheme. -/
structure NativeSchemeHodgeRealization
    (N : Nat) (X : Scheme.{u}) (Coh : Type*)
    [AddCommGroup Coh] [Module ℚ Coh] where
  hodge : Submodule ℚ Coh
  cycleSpace : Submodule ℚ (AlgebraicCycle X ℚ)
  cycleClass : cycleSpace →ₗ[ℚ] Coh
  encode : Coh →ₗ[ℚ] RatAddress N
  encode_injective : Function.Injective encode
  hodgeSupport : Finset (Fin N)
  hodge_supported :
    ∀ alpha : Coh, alpha ∈ hodge ->
      SupportedOn hodgeSupport (encode alpha)
  basisCycle : Fin N -> cycleSpace
  basisCycle_address :
    ∀ i : Fin N, i ∈ hodgeSupport ->
      encode (cycleClass (basisCycle i)) = addressBasis i

variable {N : Nat} {X : Scheme.{u}} {Coh : Type*}
  [AddCommGroup Coh] [Module ℚ Coh]

/-- Stage 2C forgets only the fact that its cycles came from an actual scheme;
it lands exactly in the Stage-2B interface. -/
def NativeSchemeHodgeRealization.toSubspaceRealization
    (R : NativeSchemeHodgeRealization N X Coh) :
    HodgeSubspaceRealization N Coh R.cycleSpace where
  hodge := R.hodge
  cycleClass := R.cycleClass
  encode := R.encode
  encode_injective := R.encode_injective
  hodgeSupport := R.hodgeSupport
  hodge_supported := R.hodge_supported
  basisCycle := R.basisCycle
  basisCycle_address := R.basisCycle_address

/-- Explicit native algebraic-cycle selector on the Hodge submodule.  Its
value lies in the supplied geometric cycle submodule by construction. -/
noncomputable def nativeCycleSelector
    (R : NativeSchemeHodgeRealization N X Coh)
    (alpha : R.hodge) : R.cycleSpace :=
  subspaceCycleSelector R.toSubspaceRealization alpha

/-- The native selector is a verified right inverse of the native cycle-class
map on the Hodge sector. -/
theorem nativeCycleSelector_spec
    (R : NativeSchemeHodgeRealization N X Coh)
    (alpha : R.hodge) :
    R.cycleClass (nativeCycleSelector R alpha) = alpha.1 := by
  exact subspaceCycleSelector_spec R.toSubspaceRealization alpha

/-- **NATIVE SCHEME FIBER THEOREM.**
Every rational Hodge class in a supplied native scheme realization has a
cycle witness drawn from an actual submodule of Mathlib algebraic cycles. -/
theorem hodge_class_has_native_algebraic_cycle
    (R : NativeSchemeHodgeRealization N X Coh)
    (alpha : Coh) (halpha : alpha ∈ R.hodge) :
    ∃ Z : AlgebraicCycle X ℚ, ∃ hZ : Z ∈ R.cycleSpace,
      R.cycleClass ⟨Z, hZ⟩ = alpha := by
  obtain ⟨Z, hZ⟩ :=
    hodge_class_has_geometric_cycle
      R.toSubspaceRealization alpha halpha
  exact ⟨Z.1, Z.2, hZ⟩

/-- Exact submodule form of the native scheme fiber theorem. -/
theorem native_hodge_subspace_le_cycleClass_range
    (R : NativeSchemeHodgeRealization N X Coh) :
    R.hodge ≤ LinearMap.range R.cycleClass := by
  exact hodge_subspace_le_cycleClass_range R.toSubspaceRealization

/-- Universal target with the geometric objects now actual Mathlib schemes
and actual Mathlib algebraic cycles.

The supplied cycleSpace X p is where a future native codimension-p / Chow
construction plugs in. -/
def UniversalNativeSchemeHodgeStatement
    (eligible : Scheme.{u} -> Prop)
    (Coh : Scheme.{u} -> Nat -> Type*)
    [∀ X p, AddCommGroup (Coh X p)]
    [∀ X p, Module ℚ (Coh X p)]
    (HodgeSubspace : ∀ X p, Submodule ℚ (Coh X p))
    (CycleSpace :
      ∀ X p, Submodule ℚ (AlgebraicCycle X ℚ))
    (cycleClass :
      ∀ X p, CycleSpace X p →ₗ[ℚ] Coh X p) : Prop :=
  ∀ X : Scheme.{u}, eligible X ->
    ∀ p : Nat,
      HodgeSubspace X p ≤ LinearMap.range (cycleClass X p)

/-- **VARIABLE-RANK NATIVE-SCHEME FAMILY THEOREM.**

If every eligible scheme and weight p carries a NativeSchemeHodgeRealization
compatible with the intended Hodge subspace, native cycle submodule, and
cycle-class map, then the exact universal native-scheme Hodge target follows.

No global Fin 12 identification occurs in the theorem. -/
theorem universal_native_scheme_hodge_of_realization_family
    (eligible : Scheme.{u} -> Prop)
    (Coh : Scheme.{u} -> Nat -> Type*)
    [∀ X p, AddCommGroup (Coh X p)]
    [∀ X p, Module ℚ (Coh X p)]
    (HodgeSubspace : ∀ X p, Submodule ℚ (Coh X p))
    (CycleSpace :
      ∀ X p, Submodule ℚ (AlgebraicCycle X ℚ))
    (cycleClass :
      ∀ X p, CycleSpace X p →ₗ[ℚ] Coh X p)
    (N : Scheme.{u} -> Nat -> Nat)
    (R : ∀ X p, eligible X ->
      NativeSchemeHodgeRealization (N X p) X (Coh X p))
    (hHodge : ∀ X p hX,
      (R X p hX).hodge = HodgeSubspace X p)
    (hCycles : ∀ X p hX,
      (R X p hX).cycleSpace = CycleSpace X p)
    (hCycleClass : ∀ X p hX,
      ∀ Z : (R X p hX).cycleSpace,
        (R X p hX).cycleClass Z =
          cycleClass X p
            ⟨Z.1, by
              rw [← hCycles X p hX]
              exact Z.2⟩) :
    UniversalNativeSchemeHodgeStatement
      eligible Coh HodgeSubspace CycleSpace cycleClass := by
  intro X hX p alpha halpha
  have halphaR : alpha ∈ (R X p hX).hodge := by
    rw [hHodge X p hX]
    exact halpha
  obtain ⟨Z, hZmem, hZclass⟩ :=
    hodge_class_has_native_algebraic_cycle
      (R X p hX) alpha halphaR
  have hZtarget : Z ∈ CycleSpace X p := by
    rw [← hCycles X p hX]
    exact hZmem
  refine ⟨⟨Z, hZtarget⟩, ?_⟩
  have hcompat :=
    hCycleClass X p hX ⟨Z, hZmem⟩
  calc
    cycleClass X p ⟨Z, hZtarget⟩
        = (R X p hX).cycleClass ⟨Z, hZmem⟩ := hcompat.symm
    _ = alpha := hZclass

/-- The exact remaining native geometric obligation for one scheme fiber.
The equality of cycle submodules is bound before it is used to transport
cycle witnesses into the intended cycle-class domain. -/
def NativeSchemeFiberRealizationObligation
    (X : Scheme.{u}) (Coh : Type*)
    [AddCommGroup Coh] [Module ℚ Coh]
    (H : Submodule ℚ Coh)
    (CycleSpace : Submodule ℚ (AlgebraicCycle X ℚ))
    (cl : CycleSpace →ₗ[ℚ] Coh) : Prop :=
  ∃ N : Nat, ∃ R : NativeSchemeHodgeRealization N X Coh,
    ∃ hS : R.cycleSpace = CycleSpace,
      R.hodge = H ∧
      ∀ Z : R.cycleSpace,
        R.cycleClass Z =
          cl ⟨Z.1, by
            rw [← hS]
            exact Z.2⟩

/-- A completed native-scheme fiber obligation implies the exact Hodge
subspace inclusion for the intended cycle-class map. -/
theorem hodge_of_native_scheme_fiber_obligation
    (X : Scheme.{u}) (Coh : Type*)
    [AddCommGroup Coh] [Module ℚ Coh]
    (H : Submodule ℚ Coh)
    (CycleSpace : Submodule ℚ (AlgebraicCycle X ℚ))
    (cl : CycleSpace →ₗ[ℚ] Coh)
    (hR : NativeSchemeFiberRealizationObligation X Coh H CycleSpace cl) :
    H ≤ LinearMap.range cl := by
  rcases hR with ⟨N, R, hS, hH, hcl⟩
  intro alpha halpha
  have halphaR : alpha ∈ R.hodge := by
    rw [hH]
    exact halpha
  obtain ⟨Z, hZmem, hZclass⟩ :=
    hodge_class_has_native_algebraic_cycle R alpha halphaR
  have hZtarget : Z ∈ CycleSpace := by
    rw [← hS]
    exact hZmem
  refine ⟨⟨Z, hZtarget⟩, ?_⟩
  have hcompat := hcl ⟨Z, hZmem⟩
  calc
    cl ⟨Z, hZtarget⟩
        = R.cycleClass ⟨Z, hZmem⟩ := hcompat.symm
    _ = alpha := hZclass

#check NativeSchemeHodgeRealization
#check NativeSchemeHodgeRealization.toSubspaceRealization
#check nativeCycleSelector
#check nativeCycleSelector_spec
#check hodge_class_has_native_algebraic_cycle
#check native_hodge_subspace_le_cycleClass_range
#check UniversalNativeSchemeHodgeStatement
#check universal_native_scheme_hodge_of_realization_family
#check NativeSchemeFiberRealizationObligation
#check hodge_of_native_scheme_fiber_obligation

#print axioms nativeCycleSelector_spec
#print axioms hodge_class_has_native_algebraic_cycle
#print axioms native_hodge_subspace_le_cycleClass_range
#print axioms universal_native_scheme_hodge_of_realization_family
#print axioms hodge_of_native_scheme_fiber_obligation


/-! ## Actual affine schemes for GST universal and finite coordinate geometry -/
open CategoryTheory GSTTruncatedWorldCohomologyRing

noncomputable def cosmicCoordinateScheme : Scheme :=
  Spec (CommRingCat.of WorldPoly)

noncomputable def windowCoordinateScheme (A B : ℕ) : Scheme :=
  Spec (CommRingCat.of (WorldCohomologyRing A B))

/-- This is an actual Mathlib scheme morphism induced by the quotient map. -/
noncomputable def windowToCosmicScheme (A B : ℕ) :
    windowCoordinateScheme A B ⟶ cosmicCoordinateScheme :=
  Spec.map (CommRingCat.ofHom (coordinateProjection A B))

noncomputable def windowSchemeInclusion {A B C D : ℕ}
    (hA : A ≤ C) (hB : B ≤ D) :
    windowCoordinateScheme A B ⟶ windowCoordinateScheme C D :=
  Spec.map (CommRingCat.ofHom (quotientRestriction A B hA hB))

/-- Contravariance reverses the quotient maps into compatible inclusions. -/
theorem windowScheme_triangle {A B C D : ℕ} (hA : A ≤ C) (hB : B ≤ D) :
    windowSchemeInclusion hA hB ≫ windowToCosmicScheme C D =
      windowToCosmicScheme A B := by
  have hring : CommRingCat.ofHom (coordinateProjection C D) ≫
      CommRingCat.ofHom (quotientRestriction A B hA hB) =
      CommRingCat.ofHom (coordinateProjection A B) := by
    refine Eq.trans (CommRingCat.ofHom_comp
      (coordinateProjection C D) (quotientRestriction A B hA hB)).symm ?_
    rfl
  unfold windowSchemeInclusion windowToCosmicScheme
    windowCoordinateScheme cosmicCoordinateScheme
  rw [← Spec.map_comp, hring]

end GSTGeometricRealizationStage2C
