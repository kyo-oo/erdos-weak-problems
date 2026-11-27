/-! ## §5 The arity bridge and the closed embedding into ℙ^{2M-1} -/

/-- **THE ARITY BRIDGE** — `Fin (2M-1+1) ≃ Fin (2M)` (equal cardinalities;
`Nat.sub_add_cancel` — not defeq for variable `M`, hence the explicit
bridge). -/
def lineFinEquiv (M : ℕ) [NeZero M] : Fin (2 * M - 1 + 1) ≃ Fin (2 * M) :=
  Equiv.ofBijective
    (fun a => ⟨a.val, Nat.lt_of_lt_of_le a.isLt (by
      have hM : 0 < M := Nat.pos_of_neZero ‹_›
      omega)⟩)
    ⟨fun a b h => Fin.val_injective (congrArg Fin.val h),
     fun b => ⟨⟨b.val, by
       have hM : 0 < M := Nat.pos_of_neZero ‹_›
       omega⟩, rfl⟩⟩⟩

/-- **THE AMBIENT QUOTIENT HOM** — the frozen `lineQuotientMap` transported
along the rename of the arity bridge. -/
noncomputable def ambientQuotientHom (M : ℕ) [NeZero M] :
    ProjectiveCoordinateRing (2 * M - 1) →ₐ[ℂ] lineQuotient M :=
  (lineQuotientMap M).comp (MvPolynomial.renameEquiv ℂ (lineFinEquiv M)).toAlgHom

theorem ambientQuotientHom_mem (M : ℕ) [NeZero M]
    (t : ProjectiveCoordinateRing (2 * M - 1)) {n : ℕ}
    (ht : t ∈ ProjectiveGrading (2 * M - 1) n) :
    ambientQuotientHom M t ∈ lineGrading M n := by
  show lineQuotientMap M (MvPolynomial.rename ⇑(lineFinEquiv M) t) ∈ lineGrading M n
  exact lineQuotientMap_mem_lineGrading M n _
    ((mem_homogeneousSubmodule _ _).mpr
      (IsHomogeneous.rename_isHomogeneous
        ((mem_homogeneousSubmodule _ _).mp ht)))

/-- **THE GRADED QUOTIENT PRESENTATION** — the `→+*ᵍ` hom feeding
`Proj.map` (the flat `GradedRingHom` structure: the ring hom plus the
piece-preservation field). -/
noncomputable def lineGradedQuotientHom (M : ℕ) [NeZero M] :
    ProjectiveGrading (2 * M - 1) →+*ᵍ lineGrading M where
  toRingHom := (ambientQuotientHom M).toRingHom
  map_mem := fun {_ x} hx => ambientQuotientHom_mem M x hx

private theorem ambientQuotient_surjective (M : ℕ) [NeZero M] :
    Function.Surjective (lineGradedQuotientHom M).toRingHom := by
  intro z
  obtain ⟨t, rfl⟩ := lineQuotientMap_surjective M z
  refine ⟨MvPolynomial.renameEquiv ℂ (lineFinEquiv M).symm t, ?_⟩
  show lineQuotientMap M (MvPolynomial.rename ⇑(lineFinEquiv M)
    (MvPolynomial.rename ⇑((lineFinEquiv M).symm) t)) = z
  rw [rename_rename, Equiv.self_comp_symm, rename_id_apply]

/-- **THE IRRELEVANT-IDEAL HYPOTHESIS** for the embedding's `Proj.map`:
the quotient's irrelevant ideal lies in the image of the ambient one.
Route: piecewise — `y ∈ ℬ i` (i > 0) lifts along the image-grading to
`y = lineQuotientMap t` with `t` homogeneous of degree `i`; the rename
back-lift is the ambient witness (homogeneous of the same degree, hence
in the ambient irrelevant ideal), and the arity roundtrip closes the
image equation. -/
theorem line_irrelevant_le (M : ℕ) [NeZero M] :
    HomogeneousIdeal.irrelevant (lineGrading M) ≤
      HomogeneousIdeal.map (lineGradedQuotientHom M)
        (HomogeneousIdeal.irrelevant (ProjectiveGrading (2 * M - 1))) := by
  show (HomogeneousIdeal.irrelevant (lineGrading M)).toIdeal ≤
    (HomogeneousIdeal.map (lineGradedQuotientHom M)
      (HomogeneousIdeal.irrelevant (ProjectiveGrading (2 * M - 1)))).toIdeal
  rw [HomogeneousIdeal.toIdeal_map, HomogeneousIdeal.toIdeal_irrelevant_le]
  intro i hi
  rw [SetLike.le_def]
  intro y hy
  obtain ⟨t, ht, hty⟩ := (mem_lineGrading M i y).mp hy
  have hsurj : Function.Surjective (lineGradedQuotientHom M).toRingHom :=
    ambientQuotient_surjective M
  show y ∈ Ideal.map (lineGradedQuotientHom M).toRingHom
    (HomogeneousIdeal.irrelevant (ProjectiveGrading (2 * M - 1))).toIdeal
  refine (Ideal.mem_map_iff_of_surjective _ hsurj).mpr
    ⟨MvPolynomial.renameEquiv ℂ (lineFinEquiv M).symm t, ?_, ?_⟩
  · show MvPolynomial.renameEquiv ℂ (lineFinEquiv M).symm t ∈
      HomogeneousIdeal.irrelevant (ProjectiveGrading (2 * M - 1))
    rw [MvPolynomial.renameEquiv_apply]
    exact HomogeneousIdeal.mem_irrelevant_of_mem hi
      ((mem_homogeneousSubmodule _ _).mpr
        (IsHomogeneous.rename_isHomogeneous
          ((mem_homogeneousSubmodule _ _).mp ht)))
  · show (lineGradedQuotientHom M)
      (MvPolynomial.renameEquiv ℂ (lineFinEquiv M).symm t) = y
    show lineQuotientMap M (MvPolynomial.rename ⇑(lineFinEquiv M)
      (MvPolynomial.rename ⇑((lineFinEquiv M).symm) t)) = y
    rw [rename_rename, Equiv.self_comp_symm, rename_id_apply]
    exact hty

/-- **THE CLOSED EMBEDDING** of the line world into `ℙ^{2M-1}` — `Proj.map`
of the graded quotient presentation.  Its closed-immersion certification
(the chartwise `IsZariskiLocalAtTarget.of_iSup_eq_top` battle, transposed
from the green finite-point carrier) is the next wave's kill; the
immersion term itself is the `ProjectiveOverC` witness input. -/
noncomputable def finiteLineEmbedding (M : ℕ) [NeZero M] :
    finiteLineScheme M ⟶ projectiveSpace (2 * M - 1) :=
  Proj.map (lineGradedQuotientHom M) (line_irrelevant_le M)
