import Mathlib
import Mathlib.RingTheory.MvPolynomial.Homogeneous

import HCUniverse2.GSTFiniteLineRing
import HCUniverse2.GSTProjectiveOverC
import HCUniverse2.GSTFiniteLineWorldCarrier

/-
Copyright (c) 2026. The HC-PROOF campaign. All rights reserved.

# Wave 66-B — THE AWAY-LIFT SURJECTIVITY (F2's sub-battle)

THE KILL of the B-lane: the ring-level chart surjectivity of the graded
quotient presentation's Away-map — THE sub-battle of the closed-immersion
certification of `finiteLineEmbedding M` (the frozen F2 design,
`research/records/2026-11-21-wave65-2R-f2-recon.md`).  Per chart `j` of the
ambient cover (`D₊(X j)` of `ℙ^{2M-1}`), the embedding's chart ring map is

  `Away.map (lineGradedQuotientHom M) (MvPolynomial.X j) :`
  `Away (ProjectiveGrading (2*M-1)) (X j) →+*`
  `Away (lineGrading M) (lineGradedQuotientHom M (X j))`,

and its surjectivity is exactly what `IsClosedImmersion.spec_of_surjective`
consumes (the finite-point carrier's `chartRingMap_surjective`,
GSTFinitePointWorldCarrier.lean:460, is the green sibling — the consumption
shape at its lines 642-643).

THE ROUTE (the frozen design, executed):

  1. `Away.mk_surjective` (pin HomogeneousLocalization.lean:618): every
     target element is `.mk ℬ hImg n a ha` — the fraction
     `a / (image of X j) ^ n` with numerator `a` in the line grading's
     `(n • 1)`-piece;
  2. `mem_lineGrading` (GSTFiniteLineRing.lean:160, green): THE piece-level
     lift — `a = lineQuotientMap M t` for an ambient homogeneous `t` of
     degree `n • 1`;
  3. the preimage is `Away.mk 𝒜 hX n (rename (lineFinEquiv M).symm t) hs` —
     the numerator back-lifted along the arity bridge
     `Fin (2*M-1+1) ≃ Fin (2*M)`, homogeneous of the same degree
     (`IsHomogeneous.rename_isHomogeneous`);
  4. `Away.map_mk` (pin :730, simp) evaluates the map on the fraction;
  5. the arity roundtrip (`rename_rename` + `Equiv.self_comp_symm` +
     `rename_id_apply` — Mathlib's own `renameEquiv` right_inv computation,
     Algebra/MvPolynomial/Rename.lean:218) identifies the transported
     numerator with the lifted one, and the fraction equality closes by
     proof irrelevance (both `.mk`-slots then prove the same propositions)
     — with the `val_injective` + `Away.val_mk` route recorded as the
     `first`-fallback (the point carrier's `first | rfl | …` idiom,
     GSTFinitePointWorldCarrier.lean:404-407).

## MATHLIB LEMMA LEDGER (pin 51e6992efd06126df61a496bebf8f49482a4e129)

Reference copies of the AlgebraicGeometry/graded files live under
`research/pin/mathlib-51e6992/` (line numbers identical to upstream); the
remaining files were fetched from the pin and verified this round
(`Mathlib/RingTheory/GradedAlgebra/HomogeneousLocalization.lean` is the
upstream path of the pinned reference copy).

* `HomogeneousLocalization.Away` (abbrev) —
  Mathlib/RingTheory/GradedAlgebra/HomogeneousLocalization.lean:601.
* `HomogeneousLocalization.Away.mk` (protected def) — same file:609.
* `HomogeneousLocalization.Away.mk_surjective` (protected lemma) — :618.
* `HomogeneousLocalization.Away.map` (protected def) — :727.
* `HomogeneousLocalization.Away.map_mk` (simp) — :730.
* `HomogeneousLocalization.Away.val_mk` (simp, rfl) — :613  [fallback only].
* `HomogeneousLocalization.val_injective` (ext) — :312              [fallback
  only; applied bare — `x`/`𝒜` resolve from the goal].
* `Graded.map_mem` — Mathlib/Data/FunLike/Graded.lean:38 (the
  `GradedFunLike` projection; the exact `map_mem g hf` of the pin's own
  `Away.map_mk` statement, HomogeneousLocalization.lean:732, whose `open
  Graded` is spelled out here).
* `MvPolynomial.mem_homogeneousSubmodule` (Iff.rfl) —
  Mathlib/RingTheory/MvPolynomial/Homogeneous.lean:101.
* `MvPolynomial.isHomogeneous_X` — same file:178.
* `MvPolynomial.IsHomogeneous.rename_isHomogeneous` — same file:332.
* `MvPolynomial.rename` (def) — Mathlib/Algebra/MvPolynomial/Rename.lean:54.
* `MvPolynomial.renameEquiv` (def) — same file:213.
* `MvPolynomial.renameEquiv_apply` — the `@[simps apply]` projection lemma
  of `renameEquiv` (:213); rw-mirror green in the carrier (:637).
* `MvPolynomial.rename_rename` (simp) — same file:80.
* `MvPolynomial.rename_id_apply` — same file:91.
* `Equiv.self_comp_symm` (simp) — Mathlib/Logic/Equiv/Defs.lean:256.
* `MvPolynomial.gradedAlgebra` (abbrev; made a LOCAL instance — NOT global
  in Mathlib by design) — Mathlib/RingTheory/MvPolynomial/
  Homogeneous.lean:619, with Mathlib's own local-instance idiom at :633.

## GREEN-CORPUS DEPENDENCIES (CI run 44899187702 at 99f6366)

* `ProjectiveCoordinateRing` / `ProjectiveGrading` —
  GSTProjectiveOverC.lean:40 / :44.
* `lineQuotientMap` / `lineGrading` / `mem_lineGrading` —
  GSTFiniteLineRing.lean:126 / :155 / :160.
* `lineFinEquiv` / `lineGradedQuotientHom` —
  GSTFiniteLineWorldCarrier.lean:563 / :596.
* Proof-shape mirrors (all green in the carrier): `ambientQuotientHom_mem`
  (:583-591 — the rename-homogeneity composite), `ambientQuotient_surjective`
  (:601-608 — the arity-roundtrip `show` + the exact
  `rename_rename, Equiv.self_comp_symm, rename_id_apply` chain),
  `line_irrelevant_le` (:628-647 — the `mem_lineGrading` destructure and the
  back-lift membership), and the point carrier's `hXj` mirror
  (GSTFinitePointWorldCarrier.lean:482-484, `mem_homogeneousSubmodule` +
  `isHomogeneous_X`).

## INTEGRATION (for the F2 assembler)

* The theorem body pastes verbatim into `GSTFiniteLineWorldCarrier.lean`
  (§5, after `finiteLineEmbedding`): every name resolves under the carrier's
  own opens (`open GSTProjectiveOverC GSTFiniteLineRing`) plus the enclosing
  `GSTFiniteLineWorldCarrier` namespace — all `HomogeneousLocalization`
  names are fully qualified, so NO new `open` is needed there.
* When pasting into the carrier, DROP the duplicate
  `attribute [local instance] MvPolynomial.gradedAlgebra` below (the carrier
  already has it at its line 54).
* The cover index is `Fin (2 * M - 1 + 1)` — the AMBIENT variable index:
  the domain of the Away-map is `Away (ProjectiveGrading (2*M-1)) (X j)`
  with `X j : ProjectiveCoordinateRing (2*M-1) = ℂ[Fin (2*M-1+1)]`.  (The
  recon sketch's binder `Fin (2 * M)` names the same finite set through
  `lineFinEquiv`, but the STATEMENT must use the ambient index type; the
  bridge itself stays internal to the proof.)
* Consumption (the point-carrier's shape, GSTFinitePointWorldCarrier.lean:
  642-643):
  `IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom
  (HomogeneousLocalization.Away.map (lineGradedQuotientHom M)
  (MvPolynomial.X j))) (awayMap_surjective M j)`.

Honesty ledger: proved unconditionally; no `sorry`, no new axioms, no
`native_decide`.  Kernel check owned by the CI lane (repo law: no local
Lean, CI owns compilation).
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open GSTProjectiveOverC GSTFiniteLineRing GSTFiniteLineWorldCarrier

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GSTFiniteLineWorldCarrier

/-- **THE AWAY-LIFT SURJECTIVITY** — F2's sub-battle: on each ambient chart
`D₊(X j)` of `ℙ^{2M-1}`, the graded quotient presentation's Away-map is
surjective.  Every element of `Away (lineGrading M) (image of X j)` is a
fraction `a / (image of X j) ^ n` (`Away.mk_surjective`); the numerator `a`
lifts through the line grading's piece-level lift `mem_lineGrading` to an
ambient homogeneous `t` of degree `n • 1`; the back-lift
`rename (lineFinEquiv M).symm t` is the numerator of the preimage fraction
`Away.mk (ProjectiveGrading (2*M-1)) hX n (back-lift) hs`; `Away.map_mk`
evaluates, and the arity roundtrip identifies the transported numerator with
the lifted one, so the two fractions are equal by proof irrelevance. -/
theorem awayMap_surjective (M : ℕ) [NeZero M] (j : Fin (2 * M - 1 + 1)) :
    Function.Surjective
      (HomogeneousLocalization.Away.map (lineGradedQuotientHom M)
        (MvPolynomial.X j)) := by
  intro z
  -- STEP 1: the chart variable is homogeneous of degree one (ambient side)
  -- — the point carrier's `hXj` mirror.
  have hX : (MvPolynomial.X j : ProjectiveCoordinateRing (2 * M - 1))
      ∈ ProjectiveGrading (2 * M - 1) 1 := by
    rw [MvPolynomial.mem_homogeneousSubmodule]
    exact MvPolynomial.isHomogeneous_X ℂ j
  -- STEP 2: its image is homogeneous of degree one (line side) — the
  -- graded-map law of `lineGradedQuotientHom` (the pin's own `map_mem g hf`
  -- of `Away.map_mk`'s right-hand side).
  have hImg : lineGradedQuotientHom M (MvPolynomial.X j) ∈ lineGrading M 1 :=
    Graded.map_mem (lineGradedQuotientHom M) hX
  -- STEP 3: every target element is a fraction `a / (image of X j) ^ n`
  -- (`Away.mk_surjective`; the `rfl` substitutes `z` by the fraction).
  obtain ⟨n, a, ha, rfl⟩ :=
    HomogeneousLocalization.Away.mk_surjective (lineGrading M) hImg z
  -- STEP 4: the piece-level lift (`mem_lineGrading`'s existential) — `a` is
  -- the image of an ambient homogeneous `t` of degree `n • 1`.
  obtain ⟨t, ht, hta⟩ := (mem_lineGrading M (n • 1) a).mp ha
  -- STEP 5: the back-lift numerator — rename along the arity bridge's
  -- inverse preserves the homogeneous degree (the carrier's
  -- `ambientQuotientHom_mem` composite).
  have hs : MvPolynomial.renameEquiv ℂ (lineFinEquiv M).symm t
      ∈ ProjectiveGrading (2 * M - 1) (n • 1) := by
    rw [MvPolynomial.renameEquiv_apply]
    exact (MvPolynomial.mem_homogeneousSubmodule _ _).mpr
      (MvPolynomial.IsHomogeneous.rename_isHomogeneous
        ((MvPolynomial.mem_homogeneousSubmodule _ _).mp ht))
  -- STEP 6: the arity roundtrip — the transported numerator IS the lifted
  -- one (the carrier's `ambientQuotient_surjective` show; the rewrite chain
  -- is Mathlib's own `renameEquiv` right_inv computation).
  have hgs : lineGradedQuotientHom M
      (MvPolynomial.renameEquiv ℂ (lineFinEquiv M).symm t) = a := by
    show lineQuotientMap M (MvPolynomial.rename ⇑(lineFinEquiv M)
      (MvPolynomial.rename ⇑((lineFinEquiv M).symm) t)) = a
    rw [MvPolynomial.rename_rename, Equiv.self_comp_symm, MvPolynomial.rename_id_apply]
    exact hta
  -- STEP 7: the preimage fraction — the back-lift over `(X j) ^ n`.
  refine ⟨HomogeneousLocalization.Away.mk (ProjectiveGrading (2 * M - 1)) hX
    n (MvPolynomial.renameEquiv ℂ (lineFinEquiv M).symm t) hs, ?_⟩
  -- STEP 8: the evaluation cascade (`Away.map_mk`).
  first
  | rw [HomogeneousLocalization.Away.map_mk]
  | simp only [HomogeneousLocalization.Away.map_mk]
  -- STEP 9: the fraction equality — substitute the numerator equation; the
  -- two `.mk`-terms then differ only in membership proofs of the SAME
  -- propositions, so proof irrelevance closes it.  Fallback (the point
  -- carrier's `first`-idiom): the `val`-injectivity route.
  subst hgs
  first
  | rfl
  | (apply HomogeneousLocalization.val_injective; rw [HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.val_mk])

/-! ## Receipts -/

#check GSTFiniteLineWorldCarrier.awayMap_surjective
#print axioms GSTFiniteLineWorldCarrier.awayMap_surjective

end GSTFiniteLineWorldCarrier

end
