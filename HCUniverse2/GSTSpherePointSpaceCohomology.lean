import HCUniverse2.GSTSphereCycleLegs
import HCUniverse2.GSTFinitePointCohomology

/-
Copyright (c) 2026. The HC-PROOF campaign. All rights reserved.

# GST POINT-SPACE COHOMOLOGY (Wave 58, file F2)

The degree-two vanishing on the point space, and the const-factorization
of the constant sphere map through it.  This is the second input of the
weight-1 point-class gate: the restriction of an off-slice point class to
a slice factors through the point space, whose H² vanishes — so the
off-slice restriction is ZERO, and the honest sphere class (nonzero by the
gate's hypothesis) survives the on-slice restriction.

The vanishing is NOT re-proved: the point space is definitionally the
finite-point lane's certified one-point discrete world
(`TopCat.of ↥(finitePointSpace 1)` ≡ `finitePointSpace 1` — the carrier
and ⊥-topology both reduce at default transparency), so the CI-green
`finitePointCohomology_subsingleton` at `N = 1` applies verbatim.

Honesty ledger: every statement is proved unconditionally.  No `sorry`, no
new axioms, no `native_decide`.  The GitHub CI lane
`gst-sphere-point-class-gate.yml` owns the kernel check.
-/

set_option maxHeartbeats 200000000
set_option maxRecDepth 1000000

noncomputable section

open CategoryTheory
open GSTSphereUnionComponents
open GSTSingularCohomologyMaps
open GSTSphereCycleLegs
open GSTFinitePointAnalytification
open GSTFinitePointCohomology

namespace GSTSpherePointSpaceCohomology

/-! ## §1 The point carrier -/

/-- The one-point discrete space, definitionally the finite-point lane's
certified `finitePointSpace 1` (the `TopCat.of ↥X`-of-a-`discrete.obj`
roundtrip reduces on the carrier and the ⊥-topology at default
transparency). -/
abbrev pointSpace : TopCat :=
  TopCat.of ↥(finitePointSpace 1)

/-- The unique point of the point space. -/
def pointPt : ↥(finitePointSpace 1) :=
  ⟨0, NeZero.pos 1⟩

/-! ## §2 The const-factorization legs -/

/-- The terminal leg: every point of the sphere goes to the point. -/
def sphereToPt (M : ℕ) :
    TopCat.of unitSphereType ⟶ pointSpace :=
  TopCat.ofHom ⟨fun _ => pointPt, continuous_const⟩

/-- the initial leg: the point goes to the base point of the sphere. -/
def sphereFromPt (M : ℕ) :
    pointSpace ⟶ TopCat.of unitSphereType :=
  TopCat.ofHom ⟨fun _ => sphereBase, continuous_const⟩

/-- The constant sphere map factors through the point space. -/
theorem constSphereMap_eq (M : ℕ) :
    sphereToPt M ≫ sphereFromPt M = constSphereMap M := by
  apply TopCat.ext
  intro x
  rfl

/-! ## §3 The degree-two vanishing on the point space -/

/-- **THE POINT-SPACE H² VANISHING.**  The degree-two rational singular
cohomology of the one-point space is a subsingleton — the finite-point
lane's certified vanishing at `N = 1`, transported along the definitional
identification of the carriers (the space field of
`finitePointAnalytification 1` is the constant `finitePointSpace 1`, and
`singularCohomologyOf` is the `rfl`-bridge of the corpus's
`RationalSingularCohomology`). -/
theorem pointCohomology_two_subsingleton :
    Subsingleton (singularCohomologyOf pointSpace 2) := by
  have h := finitePointCohomology_subsingleton (N := 1) 2 (by norm_num)
  exact h

/-! ## §4 The const-pullback vanishing -/

/-- **THE OFF-SLICE DETECTION INPUT.**  The pullback along the constant
sphere map kills every degree-two class: the constant map factors through
the point space, whose H² is a subsingleton. -/
theorem constSphere_pullback_two (M : ℕ)
    (ω : singularCohomologyOf (TopCat.of unitSphereType) 2) :
    (cohomologyPullbackOf (constSphereMap M) 2) ω = 0 := by
  have hfac : constSphereMap M = sphereToPt M ≫ sphereFromPt M :=
    (constSphereMap_eq M).symm
  rw [hfac, cohomologyPullbackOf_comp (sphereToPt M) (sphereFromPt M) 2]
  show (cohomologyPullbackOf (sphereToPt M) 2)
      ((cohomologyPullbackOf (sphereFromPt M) 2) ω) = 0
  have hmid : (cohomologyPullbackOf (sphereFromPt M) 2) ω = 0 := by
    have hsub : Subsingleton (singularCohomologyOf pointSpace 2) :=
      pointCohomology_two_subsingleton
    exact Subsingleton.elim _ _
  rw [hmid, map_zero]

end GSTSpherePointSpaceCohomology
