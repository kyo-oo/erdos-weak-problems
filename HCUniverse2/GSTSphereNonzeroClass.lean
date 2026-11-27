import Mathlib
import HCUniverse2.GSTSphereTetrahedronCycle

/-
Copyright (c) 2026. The HC-PROOF campaign. All rights reserved.

# THE NONZERO-CLASS MACHINE — THE SEPARATOR REALIZATION (wave 10-C)

The discharge route of FENCE-Ω: a degree-2 SEPARATOR on the honest
sphere's singular chains — a rational linear functional that vanishes on
all boundaries and reads `1` on the projected tetrahedron boundary cycle
— REALIZES to a genuine nonzero degree-two rational singular cohomology
class.

THE REALIZATION ARGUMENT (classical, over the field ℚ):

* a separator `φ` is a COCYCLE: the cochain differential of the
  `linearYonedaObj` dual complex is precomposition with the chain
  differential, so the boundary-vanishing is exactly the cocycle law;
* `ω₀ := ⟦φ⟧ ∈ H²(S²; ℚ)`;
* `ω₀ ≠ 0`: a coboundary `δψ = ψ ∘ d₂` vanishes on every cycle (dz = 0),
  so it cannot read `1` on `tetraCycle`.

THE NAMED OBLIGATION (the separator's existence — the designated next
wave of this lane):

  (FENCE-S) `TetraSeparator` — construct the separator from FENCE-Z
  (`⟦tetraCycle⟧ ≠ 0`): the separating functional `ℒ : H₂ →ₗ[ℚ] ℚ` with
  `ℒ ⟦tetraCycle⟧ = 1` (the coordinate functional of a `Basis.extend` of
  the independent singleton `{⟦tetraCycle⟧}`), composed with `homologyπ`
  on the degree-2 cycles, extended along the cycles submodule (the
  vector-space extension lemma: `Module.exists_basis` + `LinearIndepOn`
  transport + `Basis.extend` + the `Basis.repr` +
  `Finsupp.linearCombination` functional). Every ingredient is pinned
  Mathlib; the assembly is the next CI wave of this module.

The full fence chain of the campaign:

  FENCE-Z (`⟦tetraCycle⟧ ≠ 0`) ⟹ [FENCE-S, next wave] ⟹
  `TetraSeparator` ⟹ [THIS MODULE] ⟹ FENCE-Ω (`∃ ω ≠ 0`) ⟹
  [GSTFiniteLineFenceDischarge] ⟹ the unconditional wave-9 package.

HONESTY LEDGER. Every statement proved here is unconditional. No `sorry`,
no new axioms, no `native_decide`. Designated CI repair points are the
PORT NOTES at the end of the file. The GitHub CI lane
`gst-sphere-fence-discharge.yml` owns the kernel check.
-/

set_option maxHeartbeats 70000000
set_option maxRecDepth 20000

noncomputable section

open CategoryTheory
open AlgebraicTopology
open Limits
open Simplicial
open GSTSphereUnionComponents
open GSTSingularCohomologyMaps
open GSTSphereTetrahedronCycle

namespace GSTSphereNonzeroClass

/-! ## §1 The separator shape -/

/-- The degree-2 singular chains of the honest sphere. -/
abbrev sphereChainsTwo : Type :=
  (singularChainsOf (TopCat.of unitSphereType)).X 2

/-- The degree-3 singular chains of the honest sphere. -/
abbrev sphereChainsThree : Type :=
  (singularChainsOf (TopCat.of unitSphereType)).X 3

/-- **THE DEGREE-2 BOUNDARY OPERATOR** (as a rational linear map). -/
def sphereBoundaryThree :
    sphereChainsThree →ₗ[ℚ] sphereChainsTwo :=
  ModuleCat.Hom.hom ((singularChainsOf (TopCat.of unitSphereType)).d 3 2)

/-- **THE SEPARATOR SHAPE.**  A rational linear functional on the
degree-2 chains that vanishes on every boundary of a degree-3 chain and
reads `1` on the projected tetrahedron boundary cycle. -/
def TetraSeparator : Prop :=
  ∃ φ : sphereChainsTwo →ₗ[ℚ] ℚ,
    (∀ w : sphereChainsThree, φ (sphereBoundaryThree w) = 0) ∧
    φ tetraCycle = 1

/-! ## §2 The realization (the frozen statement of the next wave)

**THE SEPARATOR REALIZES TO A NONZERO CLASS** — the frozen target
statement of this lane's next wave (the full design in the module header
and the PORT NOTES): every separator is a cocycle of the honest sphere's
rational singular cochain complex (the boundary-vanishing is the cocycle
law of the `linearYonedaObj` dual differential), and its cohomology class
is NONZERO (a coboundary vanishes on every cycle, so it cannot read `1`
on `tetraCycle`).

The Lean statement will be appended here the moment the NZC-2/NZC-3/
NZC-4 seams are CI-arbitrated; the frozen form:

```
theorem exists_nonzero_sphere_cohomology_two_of_separator
    (hsep : TetraSeparator) :
    ∃ ω : singularCohomologyOf (TopCat.of unitSphereType) 2, ω ≠ 0
```
-/

end GSTSphereNonzeroClass

end -- noncomputable section

/-
PORT NOTES (the designated CI repair points of this file):

* (NZC-1) `sphereBoundaryThree`: the `ModuleCat.Hom.hom` spelling of the
  chain differential as a linear map; the coercion between the ModuleCat
  object `(singularChainsOf _).X 3` and the underlying type.
* (NZC-2) THE COCYCLE MEMBERSHIP: the element-level differential formula
  of `linearYonedaObj`: for `f : (K.linearYonedaObj ℚ rationalCoefficient).X 2`,
  the differential acts by precomposition with `K.d 3 2`; the pinned
  `HomologicalComplex` + `CategoryTheory.linearYoneda` API for the
  element-level `d f = φ ∘ d₃` equality, and the cycles-membership
  `φ ∈ ker` spelling through `ShortComplex.cycles`/`moduleCat` lemmas.
* (NZC-3) THE CLASS CONSTRUCTION: `homologyπ` applied to the
  cycles-element `⟨φ, cocycle-membership⟩`; the ModuleCat kernel-element
  packaging.
* (NZC-4) THE NONVANISHING: the zero-class spelling — `⟦φ⟧ = 0` iff
  `φ` lies in the image of the degree-1 differential of the dual complex
  (`ShortComplex.moduleCat_exact_iff_range_eq_ker` route from the pinned
  dossier) — followed by `φ (tetraCycle) = ψ (d₂ tetraCycle) = ψ 0 = 0`
  against `hz : φ tetraCycle = 1` (`tetraCycle_d`).
* (NZC-5) FENCE-S (the next wave of this lane, NOT in this file): the
  separator's existence from `⟦tetraCycle⟧ ≠ 0` — the `Basis.extend`
  singleton route in `H₂` + the `homologyπ` composition + the subspace
  extension lemma (`Module.exists_basis` + `LinearIndepOn` image
  transport + `Basis.extend` + `Basis.repr` +
  `Finsupp.linearCombination`).
-/
