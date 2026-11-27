import Mathlib
import HCUniverse2.GSTSphereNonzeroClass

/-
Copyright (c) 2026. The HC-PROOF campaign. All rights reserved.

# THE ROUTE CORRECTION — THE PROJECTED BOUNDARY BOUNDS (wave 10-D)

The designated FENCE-Z route of the fence-discharge cascade is CLOSED by a
kernel certificate.  The projected tetrahedron boundary cycle `tetraCycle`
is DEFINED as the boundary of its own generator `tetraGen` — the singular
3-simplex `tetraSimplex : Δ³ → S²` is a continuous map from the SOLID
tetrahedron INTO the sphere (the camera sits outside the tetrahedron, so
the central projection is defined and continuous on all of it), hence
`tetraGen` is an honest degree-three singular chain OF THE SPHERE and

  `tetraCycle = d₃(tetraGen)`  — the cycle bounds its own generator.

THE THREE CERTIFICATES:

* `tetraCycle_bounds` — `sphereBoundaryThree tetraGen = tetraCycle` (both
  definitions unfold to the same chain differential applied to the same
  generator);
* `separator_vanishes_on_tetraCycle` — every rational linear functional
  vanishing on all degree-three boundaries reads ZERO on the projected
  boundary cycle (the positive form of the obstruction);
* `not_TetraSeparator` — the separator shape `TetraSeparator` of
  `GSTSphereNonzeroClass.lean` is FALSE: a separator must vanish on
  `sphereBoundaryThree tetraGen = tetraCycle` yet read `1` there.

CONSEQUENCES FOR THE CAMPAIGN (the honest ledger):

1. FENCE-Z (`⟦tetraCycle⟧ ≠ 0` in H₂(S²; ℚ)) is FALSE at THIS cycle: the
   class of the projected boundary is zero, because the projected SOLID
   tetrahedron is itself a singular 3-chain of the sphere.  The designated
   next appends that build on this cycle — TET-6's nonvanishing theorem,
   NZC-5's separator construction from `⟦tetraCycle⟧ ≠ 0` — are CANCELLED
   at this design.
2. The certified corpus is UNAFFECTED: every green statement of the wave-10
   trio (the cycle law `d₂(tetraCycle) = 0`, the camera separation, the
   face distinctness, the separator SHAPE as a mere definition, and the
   whole exists-flip master, which takes `∃ ω ≠ 0` as an explicit
   hypothesis) remains exactly as certified at `00463dc`
   (run 45780735883).
3. THE CORRECTED ROUTE for FENCE-Ω (`∃ ω : singularCohomologyOf
   (TopCat.of unitSphereType) 2, ω ≠ 0`): a genuinely NON-BOUNDING cycle
   is required — the classical generator of H₂(S²; ℚ) ≅ ℚ.  Classically
   this is Mayer-Vietoris on the two closed hemispheres.  The pinned
   Mathlib (v4.33.0-rc2, 51e6992e) has NO sphere-homology machinery
   (verified against the pin: `Mathlib/AlgebraicTopology/` carries
   Dold-Kan, simplicial sets, singular homology basics, `HomologyZero`,
   homotopy invariance, and the Eilenberg-Steenrod AXIOMS only — no sphere
   computation, no degree theory, no no-retraction theorem, no
   Mayer-Vietoris).  The formalization of the corrected route is the
   campaign's designated research front.

HONESTY LEDGER. Every statement here is unconditional, and the main one is
NEGATIVE (an impossibility certificate). No `sorry`, no new axioms, no
`native_decide`. The GitHub CI lane `gst-sphere-fence-discharge.yml` owns
the kernel check (Ladder 4/4).
-/

set_option maxHeartbeats 70000000
set_option maxRecDepth 20000

noncomputable section

open GSTSphereTetrahedronCycle
open GSTSphereNonzeroClass

namespace GSTSphereRouteCorrection

/-! ## §1 The bounding certificate -/

/-- **THE PROJECTED BOUNDARY BOUNDS ITS OWN GENERATOR.**  The cycle
`tetraCycle` is the image of the generator `tetraGen` under the degree-3
boundary operator — both definitions unfold to the same chain differential
applied to the same singular 3-chain. -/
theorem tetraCycle_bounds :
    sphereBoundaryThree tetraGen = tetraCycle := by
  unfold sphereBoundaryThree tetraCycle
  rfl

/-- **THE EXPLICIT FILLING.**  The projected tetrahedron boundary cycle is
the boundary of an honest degree-three singular chain of the sphere (the
projected solid tetrahedron). -/
theorem tetraCycle_is_boundary :
    ∃ w : sphereChainsThree, sphereBoundaryThree w = tetraCycle :=
  ⟨tetraGen, tetraCycle_bounds⟩

/-! ## §2 The obstruction certificates -/

/-- **THE POSITIVE OBSTRUCTION FORM.**  Every rational linear functional on
the degree-two chains that vanishes on all degree-three boundaries reads
ZERO on the projected boundary cycle. -/
theorem separator_vanishes_on_tetraCycle
    (φ : sphereChainsTwo →ₗ[ℚ] ℚ)
    (hvan : ∀ w : sphereChainsThree, φ (sphereBoundaryThree w) = 0) :
    φ tetraCycle = 0 := by
  rw [← tetraCycle_bounds]
  exact hvan tetraGen

/-- **THE SEPARATOR SHAPE IS FALSE.**  `TetraSeparator` — a functional
vanishing on all boundaries and reading `1` on the projected boundary
cycle — cannot exist: the cycle is itself a boundary (of the projected
solid tetrahedron). -/
theorem not_TetraSeparator : ¬TetraSeparator := by
  rintro ⟨φ, hvan, hone⟩
  have h0 : φ (sphereBoundaryThree tetraGen) = 0 := hvan tetraGen
  rw [tetraCycle_bounds] at h0
  exact zero_ne_one (h0.symm.trans hone)

/-! ## Receipts -/

#check tetraCycle_bounds
#check tetraCycle_is_boundary
#check separator_vanishes_on_tetraCycle
#check not_TetraSeparator

#print axioms tetraCycle_bounds
#print axioms tetraCycle_is_boundary
#print axioms separator_vanishes_on_tetraCycle
#print axioms not_TetraSeparator

end GSTSphereRouteCorrection

end -- noncomputable section
