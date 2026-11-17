import GSTGeneralSpace
import Mathlib

/-!
# GST cardinal-indexed topology and native-Hodge transport

An arbitrary indexing type has arbitrary cardinality. Its fibers carry
separately typed topology, native cycles, cohomology and fold operations.
The all-cardinal index is NOT a finite-dimensional smooth projective variety.
For rational algebraic cycles, combinations have finite support (Finsupp).
No Hodge surjectivity, limit-ordinal power, source-birth axiom, or new
universal Chow realization is introduced in this formal layer.
-/

set_option maxHeartbeats 2000000
noncomputable section

namespace GSTCardinalIndexedNativeHodge

universe u v w

/-- Cardinal-indexed General Space fibers and their topologies. -/
structure IndexedSpace (ι : Type u) where
  Point : ι → Type v
  topology : (a : ι) → TopologicalSpace (Point a)
  Native : ι → Type w
  Hodge : ι → Type w
  cycleClass : (a : ι) → Native a → Hodge a
  nativeFold : (a : ι) → Native a → Native a
  hodgeFold : (a : ι) → Hodge a → Hodge a
  fold_natural :
    ∀ (a : ι) (z : Native a),
      cycleClass a (nativeFold a z) =
        hodgeFold a (cycleClass a z)

/-- Index cardinality, distinct from complex dimension and power exponent. -/
def indexCardinality {ι : Type u} (_C : IndexedSpace.{u,v,w} ι) :
    Cardinal := Cardinal.mk ι

/-- Typed finite-support cardinal-indexed rational packets. -/
abbrev FinitePacket (ι : Type u) := ι →₀ ℚ

/-- Natural-number iteration of a native fold at a selected cardinal index. -/
def nativeOrbit {ι : Type u}
    (C : IndexedSpace.{u,v,w} ι) (a : ι) (z : C.Native a) :
    ℕ → C.Native a
  | 0 => z
  | n + 1 => C.nativeFold a (nativeOrbit C a z n)

/-- Corresponding Hodge-space iteration. -/
def hodgeOrbit {ι : Type u}
    (C : IndexedSpace.{u,v,w} ι) (a : ι) (x : C.Hodge a) :
    ℕ → C.Hodge a
  | 0 => x
  | n + 1 => C.hodgeFold a (hodgeOrbit C a x n)

/-- Genuine stagewise naturality extends to all finite iterates at
EVERY index, regardless of the index type's cardinality. -/
theorem cardinal_family_orbit_natural {ι : Type u}
    (C : IndexedSpace.{u,v,w} ι) (a : ι) (z : C.Native a)
    (n : ℕ) :
    C.cycleClass a (nativeOrbit C a z n) =
      hodgeOrbit C a (C.cycleClass a z) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change C.cycleClass a (C.nativeFold a (nativeOrbit C a z n)) =
        C.hodgeFold a (hodgeOrbit C a (C.cycleClass a z) n)
      rw [C.fold_natural, ih]


/-- The user's new GST F-function:
a cardinal-indexed world, a NATURAL iteration input and an actual
native seed produce a typed Hodge/cohomology state. This is a finite-
iterate construction; it does NOT insert a target-to-native inverse. -/
def cardinalHodgeF {ι : Type u}
    (C : IndexedSpace.{u,v,w} ι)
    (a : ι) (z : C.Native a) (n : ℕ) : C.Hodge a :=
  C.cycleClass a (nativeOrbit C a z n)

/-- The new F-function is exactly the BETTI/Hodge fold orbit of the
canonical native source, uniformly at every cardinal tag. -/
theorem cardinalHodgeF_exact {ι : Type u}
    (C : IndexedSpace.{u,v,w} ι)
    (a : ι) (z : C.Native a) (n : ℕ) :
    cardinalHodgeF C a z n =
      hodgeOrbit C a (C.cycleClass a z) n :=
  cardinal_family_orbit_natural C a z n

section NativeRetract

variable {A B A' B' : Type*}
variable [AddCommGroup A] [Module ℚ A]
variable [AddCommGroup B] [Module ℚ B]
variable [AddCommGroup A'] [Module ℚ A']
variable [AddCommGroup B'] [Module ℚ B']

/-- A geometric Hodge/native retraction prevents cardinal enlargement
from introducing a native representative of a previously missing
class merely by changing its index or ambient world. -/
theorem native_retraction_reflects_algebraicity
    (cl : A →ₗ[ℚ] B) (cl' : A' →ₗ[ℚ] B')
    (hodgeForward : B →ₗ[ℚ] B')
    (nativeBack : A' →ₗ[ℚ] A)
    (hodgeBack : B' →ₗ[ℚ] B)
    (hback : ∀ z : A',
      cl (nativeBack z) = hodgeBack (cl' z))
    (hsplit : ∀ x : B, hodgeBack (hodgeForward x) = x)
    (x : B) :
    (∃ z' : A', cl' z' = hodgeForward x) →
      (∃ z : A, cl z = x) := by
  rintro ⟨z', hz'⟩
  refine ⟨nativeBack z', ?_⟩
  calc
    cl (nativeBack z') = hodgeBack (cl' z') := hback z'
    _ = hodgeBack (hodgeForward x) := by rw [hz']
    _ = x := hsplit x

/-- Missing original-world classes stay missing under a compatible
native/Hodge geometric retract from a larger cardinal-indexed world. -/
theorem missing_native_class_survives_retract
    (cl : A →ₗ[ℚ] B) (cl' : A' →ₗ[ℚ] B')
    (hodgeForward : B →ₗ[ℚ] B')
    (nativeBack : A' →ₗ[ℚ] A)
    (hodgeBack : B' →ₗ[ℚ] B)
    (hback : ∀ z : A',
      cl (nativeBack z) = hodgeBack (cl' z))
    (hsplit : ∀ x : B, hodgeBack (hodgeForward x) = x)
    (x : B) (hmissing : ¬ ∃ z : A, cl z = x) :
    ¬ ∃ z' : A', cl' z' = hodgeForward x := by
  intro hnew
  exact hmissing (native_retraction_reflects_algebraicity
    cl cl' hodgeForward nativeBack hodgeBack hback hsplit x hnew)

end NativeRetract

section FiniteCorrespondenceFamily

variable {A B : Type*} [AddCommGroup A] [Module ℚ A]
variable [AddCommGroup B] [Module ℚ B]

/-- Finite sums of geometric native actions preserve the cycle-class square. -/
theorem finite_correspondence_sum_natural
    {ι : Type*} [Fintype ι]
    (cl : A →ₗ[ℚ] B)
    (native : ι → Module.End ℚ A)
    (betti : ι → Module.End ℚ B)
    (hcompat : ∀ i z, cl (native i z) = betti i (cl z))
    (z : A) :
    cl (∑ i : ι, native i z) = ∑ i : ι, betti i (cl z) := by
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact hcompat i z

end FiniteCorrespondenceFamily

#check cardinalHodgeF
#check cardinalHodgeF_exact
#check IndexedSpace
#check FinitePacket
#check cardinal_family_orbit_natural
#check native_retraction_reflects_algebraicity
#check missing_native_class_survives_retract
#check finite_correspondence_sum_natural

#print axioms cardinalHodgeF_exact
#print axioms cardinal_family_orbit_natural
#print axioms native_retraction_reflects_algebraicity
#print axioms missing_native_class_survives_retract
#print axioms finite_correspondence_sum_natural

end GSTCardinalIndexedNativeHodge
