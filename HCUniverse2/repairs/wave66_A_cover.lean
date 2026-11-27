/-!
# Wave 66-A — THE LINE-COVER TWINS (the D+(X j) cover inputs of F2)

THE MISSION SECTION (the repairs-lane convention of `wave65_1_A`-`_D`): the
two cover lemmas that feed `Proj.iSup_basicOpen_eq_top'` in the F2
closed-immersion certification of `finiteLineEmbedding M`
(research/records/2026-11-21-wave65-2R-f2-recon.md, the frozen design) — the
arity-(2M) analogues of the green finite-point carrier's `span_cover`
(GSTFinitePointWorldCarrier.lean:202) and `variables_homogeneous`
(GSTFinitePointWorldCarrier.lean:219), transposed from that lane's target
grading `MvPolynomial.homogeneousSubmodule (Fin 2) ℂ` to the finite-line
lane's TARGET grading `ProjectiveGrading (2 * M - 1)`.

## Paste point

Splice into `GSTFiniteLineWorldCarrier.lean` as the new section after §5
(right after `finiteLineEmbedding`, before the receipts).  The section
consumes the carrier's ambient preamble, already in scope above the paste
point:

* imports `Mathlib`, `Mathlib.RingTheory.MvPolynomial.Homogeneous`,
  `GSTFiniteLineRing`, `GSTProjectiveOverC` (carrier l. 1-4);
* `noncomputable section` (l. 48) and `open AlgebraicGeometry CategoryTheory`
  / `open GSTProjectiveOverC GSTFiniteLineRing` / `open MvPolynomial
  DirectSum` (l. 50-52);
* `attribute [local instance] MvPolynomial.gradedAlgebra` (l. 54) — REQUIRED
  by `lineCover_iSup` (the pinned lemma's `[GradedRing 𝒜]` binder);
* inside `namespace GSTFiniteLineWorldCarrier` (l. 56).

No new imports, no new instances, no `variable` lines (the lane binder
discipline: every declaration re-binds its parameters at its head).

## THE ARITY RESOLUTION (the `Fin (2 * M - 1 + 1)` vs `Fin (2 * M)` question)

The cover lives on the TARGET side: `projectiveSpace (2 * M - 1) =
Proj (ProjectiveGrading (2 * M - 1))`, whose homogeneous coordinate ring is
`MvPolynomial (Fin (2 * M - 1 + 1)) ℂ` (GSTProjectiveOverC.lean:44-45:
`ProjectiveGrading n = MvPolynomial.homogeneousSubmodule (Fin (n + 1)) ℂ`,
an `abbrev`).  The variables `MvPolynomial.X j` of THAT ring are indexed by
`j : Fin (2 * M - 1 + 1)`, which is NOT definitionally equal to `Fin (2 * M)`
for variable `M` (both `2 * M - 1 + 1` and `2 * M` are stuck on the free
variable `M`; the former whnf-reduces only to `succ (pred (2 * M))`, which
does not fold back to `2 * M`) — exactly the reason the carrier carries the
explicit arity bridge `lineFinEquiv : Fin (2 * M - 1 + 1) ≃ Fin (2 * M)`
(carrier §5, l. 563).

RESOLUTION: NO bridge is needed for the cover.  The green finite-point
carrier's cover is indexed by the grading's OWN arity (`Fin 2` for
`ProjectiveGrading 1`) with `MvPolynomial.X` applied directly
(GSTFinitePointWorldCarrier.lean:650-652); mirroring that pattern exactly,
the twins are stated at the target grading's own arity
`Fin (2 * M - 1 + 1)`, where `MvPolynomial.X` applies directly.  In the
frozen design

    (Proj.iSup_basicOpen_eq_top' (ProjectiveGrading (2 * M - 1)) MvPolynomial.X
      lineCoverHomogeneous lineCoverSpan)

the `f := MvPolynomial.X` argument forces the index type to
`Fin (2 * M - 1 + 1)` by unification (the lemma's `f : ι → A` against
`A = MvPolynomial (Fin (2 * M - 1 + 1)) ℂ`), and the assembler's cover
family `(fun j => Proj.basicOpen (ProjectiveGrading (2 * M - 1))
(MvPolynomial.X j))` elaborates its `j` at the same type.  CONSEQUENCE for
the assembler: the per-chart argument `(fun j => chart_closed M j)` must be
indexed by `Fin (2 * M - 1 + 1)` as well.  (The F2 recon record's prose
`j : Fin (2 * M)` is loose: the chart cascade's own `Away.map
(lineGradedQuotientHom M) (MvPolynomial.X j)` also forces
`Fin (2 * M - 1 + 1)`, the source ring of `lineGradedQuotientHom M` being
`MvPolynomial (Fin (2 * M - 1 + 1)) ℂ`.  The `Fin (2 * M)` world is the
QUOTIENT side — `lineRing M` — reached only through `lineFinEquiv M`, at
the chart internals, not at the cover.)  The twins take `M` EXPLICIT (the
lane binder discipline), so the frozen design's bare names become
`(lineCoverHomogeneous M) (lineCoverSpan M)` — or, better, the packaged
`lineCover_iSup M` below.

## The pinned lemma (verbatim; pin 51e6992efd06126df61a496bebf8f49482a4e129)

Ambient section variables
(Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Basic.lean:44-47):

    variable {σ : Type*} {A : Type u}
    variable [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    variable (𝒜 : ℕ → σ)
    variable [GradedRing 𝒜]

The lemma (Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Basic.lean:97-100):

    lemma iSup_basicOpen_eq_top' {ι : Type*} (f : ι → A)
        (hfn : ∀ i, ∃ n, f i ∈ 𝒜 n)
        (hf : Algebra.adjoin (𝒜 0) (Set.range f) = ⊤) :
        ⨆ i, Proj.basicOpen 𝒜 (f i) = ⊤

Twin 1 (`lineCoverHomogeneous`) instantiates `hfn` with
`f := MvPolynomial.X` and `𝒜 := ProjectiveGrading (2 * M - 1)`; twin 2
(`lineCoverSpan`) instantiates `hf` with the same substitution.  Note that
the pin's `(𝒜 0)` elaborates through `SetLike.coeSort` to the degree-zero
subtype, and that `Algebra.adjoin` carries its base ring as an EXPLICIT
first argument (Mathlib/Algebra/Algebra/Subalgebra/Lattice.lean:27-34).

## Mathlib API used (pin-verified at 51e6992efd06126df61a496bebf8f49482a4e129)

* `AlgebraicGeometry.Proj.iSup_basicOpen_eq_top'` —
  Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Basic.lean:97-100 (the
  reference copy `research/pin/mathlib-51e6992/Basic.lean` is byte-identical
  to the fetched original — verified by diff).
* `AlgebraicGeometry.Proj.basicOpen` (the `D+(f)` open) — same file, :54.
* `Algebra.adjoin` (base ring R EXPLICIT, then `s : Set A`) —
  Mathlib/Algebra/Algebra/Subalgebra/Lattice.lean:32.
* `Algebra.subset_adjoin` (`s ⊆ adjoin R s`) — same file, :516.
* `Subalgebra.algebraMap_mem` —
  Mathlib/Algebra/Algebra/Subalgebra/Basic.lean:137.
* `Subalgebra.add_mem` — same file, :163.
* `Subalgebra.mul_mem` — same file, :154.
* `top_unique` (`(⊤ ≤ a) → a = ⊤`) —
  Mathlib/Order/BoundedOrder/Basic.lean:173.
* `MvPolynomial.induction_on` (cases `C`, `add`, `mul_X`) —
  Mathlib/Algebra/MvPolynomial/Basic.lean:386-390.
* `MvPolynomial.homogeneousSubmodule` —
  Mathlib/RingTheory/MvPolynomial/Homogeneous.lean:90.
* `MvPolynomial.mem_homogeneousSubmodule` (an `Iff.rfl`) — same file, :101.
* `MvPolynomial.isHomogeneous_C` (`IsHomogeneous (C r) 0`, σ R implicit) —
  same file, :160.
* `MvPolynomial.isHomogeneous_X` (R explicit, then the index;
  `IsHomogeneous (X i) 1`) — same file, :178.
* `Set.mem_range_self`, `MvPolynomial.X`, `MvPolynomial.C`, `Set.range` —
  corpus-verbatim, CI-green at HEAD (GSTFinitePointWorldCarrier.lean:204,
  :212, :215).

Instance chain (no names in the code; fires from the ambient preamble):

* `MvPolynomial.HomogeneousSubmodule.gcommSemiring` — the
  `SetLike.GradedMonoid` instance, Homogeneous.lean:505 (GLOBAL instance).
* `MvPolynomial.gradedAlgebra` — an `abbrev`, deliberately NOT a global
  instance, Homogeneous.lean:619-620; activated by the carrier's
  `attribute [local instance]` (l. 54); provides the pinned lemma's
  `[GradedRing 𝒜]` binder.
* `SetLike.GradeZero.instCommSemiring` —
  Mathlib/Algebra/DirectSum/Internal.lean:364 (the `CommSemiring (A 0)` of
  `Algebra.adjoin`'s base ring).
* the `SetLike.GradeZero` `Algebra (A 0) R` instance —
  Mathlib/Algebra/DirectSum/Internal.lean:366-368, with
  `algebraMap_apply (x : A 0) : algebraMap (A 0) R x = x := rfl` at :369
  (the definitional fold that closes the `C a` case of `lineCoverSpan`).

Corpus names: `ProjectiveGrading` (GSTProjectiveOverC.lean:44, `abbrev`).

## Proof provenance

Both proof bodies are the green finite-point carrier's `span_cover` /
`variables_homogeneous` (GSTFinitePointWorldCarrier.lean:202-223) ported
verbatim under the arity rename `Fin 2 → Fin (2 * M - 1 + 1)` and the
grading rename `grading → ProjectiveGrading (2 * M - 1)`; the identical
span-induction shape is CI-green twice over in the corpus (also
GSTCompactNativeCyclePresentation.lean:87-103 — the same adjoin-span core
at `ProjectiveGrading n`, for every `n`, with the same `C`/`add`/`mul_X`
cascade).
-/

/-! ## §6 The D+(X j) cover of the target projective space — the line-cover twins -/

/-- **THE COVER TWIN (HOMOGENEITY)** — every ambient variable `X j` is
homogeneous of degree one in the target grading `ProjectiveGrading (2 * M - 1)`:
the `hfn` side condition of `Proj.iSup_basicOpen_eq_top'`
(Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Basic.lean:98) at
`f := MvPolynomial.X`, `𝒜 := ProjectiveGrading (2 * M - 1)`.  The arity is
the target grading's own, `Fin (2 * M - 1 + 1)` (see the arity resolution in
the file header); the body is the green twin `variables_homogeneous`
(GSTFinitePointWorldCarrier.lean:219-223) verbatim under the renames. -/
theorem lineCoverHomogeneous (M : ℕ) (j : Fin (2 * M - 1 + 1)) :
    ∃ n : ℕ, MvPolynomial.X j ∈ ProjectiveGrading (2 * M - 1) n := by
  refine ⟨1, ?_⟩
  rw [MvPolynomial.mem_homogeneousSubmodule]
  exact MvPolynomial.isHomogeneous_X ℂ j

/-- **THE COVER TWIN (SPAN)** — the ambient variables generate the target
homogeneous coordinate ring `MvPolynomial (Fin (2 * M - 1 + 1)) ℂ` as an
algebra over its degree-zero piece: the `hf` side condition of
`Proj.iSup_basicOpen_eq_top'`
(Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Basic.lean:99) at
`f := MvPolynomial.X`, `𝒜 := ProjectiveGrading (2 * M - 1)`.  The body is
the green twin `span_cover` (GSTFinitePointWorldCarrier.lean:202-215)
verbatim under the renames: every polynomial is built from constants
(degree zero, hence in the base ring, via `algebraMap_mem` and the
`IsHomogeneous (C a) 0` membership, definitionally the submodule membership)
and variables (in the adjoined set). -/
theorem lineCoverSpan (M : ℕ) :
    Algebra.adjoin ↥(ProjectiveGrading (2 * M - 1) 0)
      (Set.range (MvPolynomial.X : Fin (2 * M - 1 + 1) →
        MvPolynomial (Fin (2 * M - 1 + 1)) ℂ)) = ⊤ := by
  set S := Algebra.adjoin ↥(ProjectiveGrading (2 * M - 1) 0)
      (Set.range (MvPolynomial.X : Fin (2 * M - 1 + 1) →
        MvPolynomial (Fin (2 * M - 1 + 1)) ℂ))
  refine top_unique fun p hp => ?_
  clear hp
  induction p using MvPolynomial.induction_on with
  | C a =>
      exact S.algebraMap_mem
        ⟨MvPolynomial.C a,
          MvPolynomial.isHomogeneous_C (σ := Fin (2 * M - 1 + 1)) (R := ℂ) a⟩
  | add p q hp hq => exact S.add_mem hp hq
  | mul_X p j hp => exact S.mul_mem hp (Algebra.subset_adjoin (Set.mem_range_self j))

/-- **THE APPLIED COVER LEMMA** — the `D+(X j)` charts cover the target
`Proj (ProjectiveGrading (2 * M - 1))`: the pinned
`Proj.iSup_basicOpen_eq_top'` fed with the two cover twins.  This is the
assembler's iSup argument for `IsZariskiLocalAtTarget.of_iSup_eq_top`
(pinned signature: Mathlib/AlgebraicGeometry/Morphisms/Basic.lean:146-148,
`{ι} (U : ι → Y.Opens) (hU : iSup U = ⊤) (H : ∀ i, P (f ∣_ U i)) : P f`,
with `P`/`f` implicit), pre-packaged so the F2 assembly site needs no twin
application at all. -/
theorem lineCover_iSup (M : ℕ) :
    ⨆ j : Fin (2 * M - 1 + 1),
      Proj.basicOpen (ProjectiveGrading (2 * M - 1)) (MvPolynomial.X j) = ⊤ :=
  Proj.iSup_basicOpen_eq_top' (ProjectiveGrading (2 * M - 1)) MvPolynomial.X
    (lineCoverHomogeneous M) (lineCoverSpan M)

/- ASSEMBLY PREVIEW (the F2 design with this section's pieces slotted in;
`lineCover_iSup M` is the second explicit argument, the twins already
applied inside it):

    theorem finiteLine_closedImmersion (M : ℕ) [NeZero M] :
        IsClosedImmersion (finiteLineEmbedding M) :=
      IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsClosedImmersion)
        (fun j => Proj.basicOpen (ProjectiveGrading (2 * M - 1)) (MvPolynomial.X j))
        (lineCover_iSup M)
        (fun j => chart_closed M j)

Both `j`-binders elaborate at `Fin (2 * M - 1 + 1)` (see the arity
resolution in the file header); `chart_closed` must take that same index
type.  The design's inline form
`(Proj.iSup_basicOpen_eq_top' (ProjectiveGrading (2 * M - 1)) MvPolynomial.X
(lineCoverHomogeneous M) (lineCoverSpan M))` is equally valid. -/

/-! ## Receipts -/

#check lineCoverHomogeneous
#check lineCoverSpan
#check lineCover_iSup
