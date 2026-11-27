# The pinned Mathlib source cache (the F2 recon artifacts)

Fetched verbatim from leanprover-community/mathlib4 at the campaign pin
`51e6992efd06126df61a496bebf8f49482a4e129` (v4.33.0-rc2, the CI-verified
revision of every lane) for local API verification of the finite-line
carrier's next waves. Apache 2.0, (c) the Mathlib community — attribution
preserved here; these are reference copies, not corpus sources.

* `Functor.lean` — `Proj.map` (l.148), `map_preimage_basicOpen` (l.160),
  `awayι_comp_map` (l.192 — THE per-chart square), `mapAffineOpenCover` (l.203),
  `map_comp` (l.210), `map_id` (l.217).
* `Basic.lean` — `awayToSection` (l.134), `basicOpenToSpec` (l.140),
  `basicOpenIsoSpec` (l.161), `basicOpenIsoAway` (l.176), `awayι` (l.186),
  `IsOpenImmersion (awayι ..)` (l.193), `opensRange_awayι` (l.196).
* `Scheme.lean` — `HomogeneousLocalization.Away` usage (l.151).
* `HomogeneousLocalization.lean` — `Away` (l.601), `Away.mk` (l.609),
  `Away.mk_surjective` (l.618), `Away.map` (l.727), `Away.map_mk` (l.732,
  simp), `Away.map_comp` (l.738). NO Away-surjectivity lemma exists at the
  pin — the F2 sub-battle proves it (see the F2 recon record).

Wave 66-C additions (same pin, fetched for the `chart_closed` kill — the
per-chart closed immersion of the finite-line embedding):

* `Restrict.lean` (Mathlib/AlgebraicGeometry/Restrict.lean) — `Opens.ι`
  (l.52, open-immersion instance l.57), `morphismRestrict` (l.569, the `∣_`
  infix l.573), `morphismRestrict_ι` (l.581, simp — THE restriction law),
  `IsIso (f ∣_ U)` instance (l.639), `morphismRestrictOpensRange` (l.702),
  `resLE` (l.775), `resLE_eq_morphismRestrict` (l.780).
* `MorphismProperty_Basic.lean` (Mathlib/CategoryTheory/MorphismProperty/
  Basic.lean) — `cancel_left_of_respectsIso` (l.517),
  `cancel_right_of_respectsIso` (l.521) — the iso-cancellation family.
* `ClosedImmersion.lean` (Mathlib/AlgebraicGeometry/Morphisms/
  ClosedImmersion.lean) — `IsClosedImmersion` (l.45), `RespectsIso`
  instance (l.91), `spec_of_surjective` (l.101 — the affine closer).
* `Morphisms_Basic.lean` (Mathlib/AlgebraicGeometry/Morphisms/Basic.lean) —
  `IsZariskiLocalAtTarget` (l.112), `of_iSup_eq_top` (l.146) — Agent A's
  assembly input.
* `Iso.lean` (Mathlib/CategoryTheory/Iso.lean) — `inv_comp_eq` (l.186),
  `isIso_hom` (l.264), `isIso_inv` (l.268).
* `Category_Basic.lean` (Mathlib/CategoryTheory/Category/Basic.lean) —
  `Mono` (l.328), `cancel_epi`/`cancel_mono` (l.337, the to_dual pair).
* `GradedRingHom.lean` (Mathlib/RingTheory/GradedAlgebra/RingHom.lean) —
  `GradedRingHom` (l.46, the `→+*ᵍ` notation l.52), the protected `map_mem`
  field (l.47 — accessed positionally as `f.2`, the pin's own idiom at
  Functor.lean:204).
* `MvPolynomial_Homogeneous.lean` (Mathlib/RingTheory/MvPolynomial/
  Homogeneous.lean) — `homogeneousSubmodule` (l.90),
  `mem_homogeneousSubmodule` (l.101, simp), `isHomogeneous_X` (l.178).
