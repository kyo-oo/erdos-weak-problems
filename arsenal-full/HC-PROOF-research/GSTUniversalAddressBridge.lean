import Mathlib
import GSTWorldRecoordinationGroupoid

/-!
# GST UNIVERSAL ADDRESS BRIDGE

The historical transfer layer uses one hard-coded address module

    Fin 12 -> Z.

That is only the 4 x 3 chart of a dimension-free fact.

Every GSTWorldShape S of total cardinality N has a canonical code
equivalence ShapeState S ≃ Fin N.  Therefore every coefficient field on S
is canonically and linearly equivalent to the universal N-address module

    AddressRing N := Fin N -> Z.

This file proves:
* exact linear address equivalence for every world shape;
* exact inverse reconstruction;
* chart-independence under world recoordination;
* naturality of every exact code projector;
* naturality of polynomial code observables;
* basis transport and coordinate extraction;
* recovery of the old Fin 12 address as N = 12.

No fixed 4 x 3 case analysis appears.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000000

namespace GSTUniversalAddressBridge

open GSTWorldRecoordinationGroupoid

/-- Universal integer address module of an N-state GST universe. -/
abbrev AddressRing (N : Nat) : Type :=
  Fin N -> ℤ

/-- Read a shaped coefficient field in the canonical underlying code basis. -/
def worldAddress
    {N : Nat} (S : GSTWorldShape N)
    (f : ShapeCoef S) : AddressRing N :=
  fun i => f ((shapeCodeEquiv S).symm i)

/-- Reassemble a shaped coefficient field from a universal address vector. -/
def addressWorld
    {N : Nat} (S : GSTWorldShape N)
    (phi : AddressRing N) : ShapeCoef S :=
  fun x => phi (shapeCodeEquiv S x)

@[simp]
theorem addressWorld_worldAddress
    {N : Nat} (S : GSTWorldShape N)
    (f : ShapeCoef S) :
    addressWorld S (worldAddress S f) = f := by
  funext x
  simp [addressWorld, worldAddress]

@[simp]
theorem worldAddress_addressWorld
    {N : Nat} (S : GSTWorldShape N)
    (phi : AddressRing N) :
    worldAddress S (addressWorld S phi) = phi := by
  funext i
  simp [addressWorld, worldAddress]

/-- **UNIVERSAL LINEAR ADDRESS EQUIVALENCE.**
Every rectangular presentation of an N-state GST universe has exactly the
same free Z-module of addresses. -/
def worldAddressLinearEquiv
    {N : Nat} (S : GSTWorldShape N) :
    ShapeCoef S ≃ₗ[ℤ] AddressRing N where
  toFun := worldAddress S
  invFun := addressWorld S
  left_inv := addressWorld_worldAddress S
  right_inv := worldAddress_addressWorld S
  map_add' := by
    intro f g
    funext i
    rfl
  map_smul' := by
    intro z f
    funext i
    rfl

@[simp]
theorem worldAddressLinearEquiv_apply
    {N : Nat} (S : GSTWorldShape N)
    (f : ShapeCoef S) :
    worldAddressLinearEquiv S f = worldAddress S f :=
  rfl

@[simp]
theorem worldAddressLinearEquiv_symm_apply
    {N : Nat} (S : GSTWorldShape N)
    (phi : AddressRing N) :
    (worldAddressLinearEquiv S).symm phi = addressWorld S phi :=
  rfl

/-- One address coordinate is exactly one shaped state value. -/
theorem worldAddress_at_code
    {N : Nat} (S : GSTWorldShape N)
    (f : ShapeCoef S) (x : ShapeState S) :
    worldAddress S f (shapeCodeEquiv S x) = f x := by
  simp [worldAddress]

/-- Reconstruction at one state is exactly lookup at its invariant code. -/
theorem addressWorld_at_state
    {N : Nat} (S : GSTWorldShape N)
    (phi : AddressRing N) (x : ShapeState S) :
    addressWorld S phi x = phi (shapeCodeEquiv S x) :=
  rfl

/-- **CHART INDEPENDENCE.**
Transporting a field to any equal-cardinality world presentation leaves its
universal address vector literally unchanged. -/
theorem worldAddress_transportCoef
    {N : Nat} (S T : GSTWorldShape N)
    (f : ShapeCoef S) :
    worldAddress T (transportCoef S T f) =
      worldAddress S f := by
  funext i
  unfold worldAddress transportCoef
  change
    f ((worldRecoordinate S T).symm ((shapeCodeEquiv T).symm i)) =
      f ((shapeCodeEquiv S).symm i)
  congr 1
  apply (shapeCodeEquiv S).injective
  simp [worldRecoordinate]

/-- The address equivalences themselves form a natural cone over the
world-recoordination groupoid. -/
theorem worldAddressLinearEquiv_natural
    {N : Nat} (S T : GSTWorldShape N)
    (f : ShapeCoef S) :
    worldAddressLinearEquiv T (transportCoef S T f) =
      worldAddressLinearEquiv S f :=
  worldAddress_transportCoef S T f

/-- Universal address projector onto one exact state code. -/
def addressSectorProj
    {N : Nat} (k : Nat)
    (phi : AddressRing N) : AddressRing N :=
  fun i => if i.1 = k then phi i else 0

theorem addressSectorProj_idempotent
    {N : Nat} (k : Nat) (phi : AddressRing N) :
    addressSectorProj k (addressSectorProj k phi) =
      addressSectorProj k phi := by
  funext i
  by_cases h : i.1 = k <;>
    simp [addressSectorProj, h]

theorem addressSectorProj_orthogonal
    {N : Nat} (j k : Nat) (hjk : j ≠ k)
    (phi : AddressRing N) :
    addressSectorProj j (addressSectorProj k phi) = fun _ => 0 := by
  funext i
  by_cases hj : i.1 = j
  · have hk : i.1 ≠ k := by
      intro h
      exact hjk (hj.symm.trans h)
    unfold addressSectorProj
    rw [if_pos hj, if_neg hk]
  · unfold addressSectorProj
    rw [if_neg hj]

/-- Every address vector is the sum of its N exact coordinate sectors. -/
theorem addressSectorProj_sum
    {N : Nat} (phi : AddressRing N) :
    (fun i => ∑ k ∈ Finset.range N, addressSectorProj k phi i) = phi := by
  funext i
  classical
  rw [Finset.sum_eq_single i.1]
  · simp [addressSectorProj]
  · intro b hb hbi
    have hne : i.1 ≠ b := hbi.symm
    simp [addressSectorProj, hne]
  · intro hnot
    exact (hnot (Finset.mem_range.mpr i.2)).elim

/-- **SPECTRAL NATURALITY OF THE ADDRESS DICTIONARY.**
The exact code projector on any world chart becomes the exact coordinate
projector on the universal address module. -/
theorem worldAddress_codeSectorProj
    {N : Nat} (S : GSTWorldShape N)
    (k : Nat) (f : ShapeCoef S) :
    worldAddress S (codeSectorProj S k f) =
      addressSectorProj k (worldAddress S f) := by
  funext i
  unfold worldAddress codeSectorProj addressSectorProj worldCode
  simp

/-- Universal polynomial code observable on the address module. -/
def addressPolyOp
    {N : Nat} (p : Polynomial ℤ)
    (phi : AddressRing N) : AddressRing N :=
  fun i => p.eval (i.1 : ℤ) * phi i

/-- Polynomial code observables are transported exactly by the address
dictionary. -/
theorem worldAddress_codePolyOp
    {N : Nat} (S : GSTWorldShape N)
    (p : Polynomial ℤ) (f : ShapeCoef S) :
    worldAddress S (codePolyOp S p f) =
      addressPolyOp p (worldAddress S f) := by
  funext i
  unfold worldAddress codePolyOp addressPolyOp worldCode
  simp

/-- Universal Kronecker basis vector of one address coordinate. -/
def addressBasis
    {N : Nat} (k : Fin N) : AddressRing N :=
  fun i => if i = k then 1 else 0

/-- Shaped basis vector at one world state. -/
def worldBasis
    {N : Nat} (S : GSTWorldShape N)
    (x : ShapeState S) : ShapeCoef S :=
  fun y => if y = x then 1 else 0

/-- Every shaped basis state is sent to the universal basis vector carrying
the same invariant code. -/
theorem worldAddress_worldBasis
    {N : Nat} (S : GSTWorldShape N)
    (x : ShapeState S) :
    worldAddress S (worldBasis S x) =
      addressBasis (shapeCodeEquiv S x) := by
  funext i
  unfold worldAddress worldBasis addressBasis
  by_cases hi : i = shapeCodeEquiv S x
  · subst i
    simp
  · have hx : (shapeCodeEquiv S).symm i ≠ x := by
      intro hxeq
      apply hi
      have hcode := congrArg (shapeCodeEquiv S) hxeq
      simpa using hcode
    simp [hi, hx]

/-- One address coordinate completely separates shaped coefficient fields. -/
theorem worldAddress_injective
    {N : Nat} (S : GSTWorldShape N) :
    Function.Injective (worldAddress S) :=
  (worldAddressLinearEquiv S).injective

/-- Every universal address vector is realized in every world chart. -/
theorem worldAddress_surjective
    {N : Nat} (S : GSTWorldShape N) :
    Function.Surjective (worldAddress S) :=
  (worldAddressLinearEquiv S).surjective

/-- The historical classical address carrier is the N=12 specialization. -/
abbrev HCAddressRing : Type :=
  AddressRing 12

/-- Capstone: the address module is an invariant of the N-state universe,
not of any rectangular presentation. -/
theorem universal_address_bridge_crown :
    (∀ N (S : GSTWorldShape N),
      Function.Bijective (worldAddress S))
    ∧ (∀ N (S T : GSTWorldShape N) (f : ShapeCoef S),
      worldAddress T (transportCoef S T f) =
        worldAddress S f)
    ∧ (∀ N (S : GSTWorldShape N) k (f : ShapeCoef S),
      worldAddress S (codeSectorProj S k f) =
        addressSectorProj k (worldAddress S f))
    ∧ (∀ N (S : GSTWorldShape N)
        (p : Polynomial ℤ) (f : ShapeCoef S),
      worldAddress S (codePolyOp S p f) =
        addressPolyOp p (worldAddress S f)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro N S
    exact (worldAddressLinearEquiv S).bijective
  · intro N S T f
    exact worldAddress_transportCoef S T f
  · intro N S k f
    exact worldAddress_codeSectorProj S k f
  · intro N S p f
    exact worldAddress_codePolyOp S p f

#check AddressRing
#check worldAddressLinearEquiv
#check worldAddress_at_code
#check worldAddress_transportCoef
#check addressSectorProj_sum
#check worldAddress_codeSectorProj
#check worldAddress_codePolyOp
#check worldAddress_worldBasis
#check universal_address_bridge_crown

#print axioms worldAddressLinearEquiv
#print axioms worldAddress_transportCoef
#print axioms worldAddress_codeSectorProj
#print axioms worldAddress_worldBasis
#print axioms universal_address_bridge_crown


/-! ## Countably infinite addresses -/
open GSTWorldCosmology

/-- The cosmic address dictionary uses both unbounded coordinates. -/
def cosmicAddressEquiv : CosmicCell ≃ ℕ where
  toFun := fun c => Nat.pair c.1 c.2
  invFun := Nat.unpair
  left_inv := by intro c; exact Nat.unpair_pair c.1 c.2
  right_inv := Nat.pair_unpair

def completedAddressEquiv : CompletedCosmos ≃ₗ[ℤ] (ℕ → ℤ) where
  toFun := fun f n => f (cosmicAddressEquiv.symm n)
  invFun := fun a c => a (cosmicAddressEquiv c)
  left_inv := by intro f; funext c; simp
  right_inv := by intro a; funext n; simp
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

noncomputable def compactAddressEquiv : CompactCosmos ≃+ (ℕ →₀ ℤ) :=
  Finsupp.domCongr cosmicAddressEquiv

@[simp] theorem cosmic_address_reads_window (A B : ℕ) (f : CompletedCosmos)
    (c : WorldCell A B) :
    completedAddressEquiv f (cosmicAddressEquiv (c.1.val, c.2.val)) =
      observe A B f c := by simp [completedAddressEquiv, observe]

/-- The historical row-major finite code is a chart coordinate; its cosmic
address is obtained by decoding that chart first. -/
theorem finite_address_cosmic_naturality {A B : ℕ} (f : CompletedCosmos)
    (i : Fin (A*B)) :
    worldAddress (outputShape A B) (observe A B f) i =
      completedAddressEquiv f (cosmicAddressEquiv
        (((shapeCodeEquiv (outputShape A B)).symm i).1.val,
         ((shapeCodeEquiv (outputShape A B)).symm i).2.val)) := by
  simp [completedAddressEquiv, worldAddress, observe]

end GSTUniversalAddressBridge
