import GSTFourPowerAffinePrefixIsometry

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
# GST finite-prefix ontological completeness

The existing affine-prefix-isometry theorem says that two exponent
residues agree exactly when the physical 4-power affine orbit prefixes
agree. Since both prefix spaces have exactly 3^p elements, this
injective correspondence is also SURJECTIVE at EVERY finite depth.

This is an essential structural caution for Problem 406: a finite
arbitrary BAD-controller coordinate cannot be excluded from the
perfect-power physical world solely from its finite ternary prefix.
Every such prefix is matched by a genuine nonnegative integer exponent.

This does not produce an all-depth BAD physical exponent, nor refute
hGate. The missing universal theorem must use an unbounded or
termination-sensitive condition, not a finite-prefix origin filter.
-/

namespace GSTFourPowerAffineOntologicalCompleteness

open GSTFourPowerAffineOrbit
open GSTFourPowerAffinePrefixIsometry

/-- A finite original-exponent-to-physical-affine-prefix map. -/
def prefixMap (p : Nat) : Fin (3^p) → Fin (3^p) :=
  fun k => ⟨affineOrbit k.val % 3^p,
    Nat.mod_lt _ (by positivity : 0 < 3^p)⟩

/-- Injectivity is the already kernel-proved GST affine prefix isometry. -/
theorem prefixMap_injective (p : Nat) :
    Function.Injective (prefixMap p) := by
  intro a b hab
  have hmod :
      affineOrbit a.val % 3^p =
        affineOrbit b.val % 3^p := by
    have h := congrArg Fin.val hab
    simpa only [prefixMap] using h
  have hval :
      a.val % 3^p = b.val % 3^p :=
    (affineOrbit_residue_eq_iff_exponent_residue_eq
      p a.val b.val).mp hmod
  have ha : a.val % 3^p = a.val := Nat.mod_eq_of_lt a.isLt
  have hb : b.val % 3^p = b.val := Nat.mod_eq_of_lt b.isLt
  apply Fin.ext
  simpa only [ha, hb] using hval

/-- Finite-prefix GST completeness: EVERY physical affine residue is
attained by some nonnegative perfect-power exponent below 3^p. -/
theorem prefixMap_surjective (p : Nat) :
    Function.Surjective (prefixMap p) := by
  exact (Finite.injective_iff_surjective).mp
    (prefixMap_injective p)

/-- The residue-level result, with no abstract finite-state surrogate.
Any prescribed ternary prefix is exactly the physical orbit prefix
of a real perfect-power exponent. -/
theorem every_affine_prefix_is_physical
    (p r : Nat) (hr : r < 3^p) :
    ∃ K : Nat, K < 3^p ∧ affineOrbit K % 3^p = r := by
  obtain ⟨k,hk⟩ :=
    prefixMap_surjective p (⟨r,hr⟩ : Fin (3^p))
  refine ⟨k.val,k.isLt,?_⟩
  have h := congrArg Fin.val hk
  simpa only [prefixMap] using h

/-- Strong version: any arbitrary source coordinate X, regardless of
whether it came from an actual perfect power, matches an exact physical
Worldtrace/affine orbit to any preassigned finite depth. -/
theorem every_arbitrary_coordinate_has_physical_prefix
    (p X : Nat) :
    ∃ K : Nat, K < 3^p ∧
      affineOrbit K % 3^p = X % 3^p := by
  have hpos : 0 < 3^p := by positivity
  obtain ⟨K,hK,hmod⟩ :=
    every_affine_prefix_is_physical p (X%3^p)
      (Nat.mod_lt X hpos)
  exact ⟨K,hK,hmod⟩

#print axioms prefixMap_injective
#print axioms prefixMap_surjective
#print axioms every_affine_prefix_is_physical
#print axioms every_arbitrary_coordinate_has_physical_prefix

end GSTFourPowerAffineOntologicalCompleteness
