/-! ## §3 The rotation on the coordinate ring and its descent -/

/-- **THE ROTATION AT THE COORDINATE-RING LEVEL.** -/
def lineRename (M : ℕ) : lineRing M ≃ₐ[ℂ] lineRing M :=
  MvPolynomial.renameEquiv ℂ (blockRot M)

/-- The application bridge: the rotation is definitionally `rename`. -/
theorem lineRename_apply (M : ℕ) (p : lineRing M) :
    lineRename M p = MvPolynomial.rename (blockRotFn M) p :=
  MvPolynomial.renameEquiv_apply ℂ (blockRot M) p

theorem lineRename_X (M : ℕ) (a : Fin (2 * M)) :
    lineRename M (X a : lineRing M) = X (blockRot M a) := by
  show lineRename M (X a : lineRing M) = X (blockRotFn M a)
  rw [lineRename_apply, rename_X]

/-- **DEGREE PRESERVATION**: the rotation of a degree-`n` homogeneous
polynomial is degree-`n` homogeneous. -/
theorem lineRename_mem_homogeneousSubmodule (M : ℕ) (n : ℕ) (t : lineRing M)
    (ht : t ∈ MvPolynomial.homogeneousSubmodule (Fin (2 * M)) ℂ n) :
    lineRename M t ∈ MvPolynomial.homogeneousSubmodule (Fin (2 * M)) ℂ n := by
  rw [lineRename_apply]
  exact (mem_homogeneousSubmodule _ _).mpr
    (IsHomogeneous.rename_isHomogeneous
      ((mem_homogeneousSubmodule _ _).mp ht))

/-- Cross-monomials map into cross-monomials (same-block ↔ same-block). -/
theorem lineRename_crossMonomials_mem (M : ℕ) {p : lineRing M}
    (hp : p ∈ crossMonomials M) : lineRename M p ∈ crossMonomials M := by
  obtain ⟨a, b, hab, rfl⟩ := hp
  refine ⟨blockRot M a, blockRot M b,
    fun hcon => hab ((blockRot_sameBlock M a b).mp hcon), ?_⟩
  show MvPolynomial.renameEquiv ℂ (blockRot M) (X a * X b) =
    X (blockRot M a) * X (blockRot M b)
  rw [map_mul, MvPolynomial.renameEquiv_apply, MvPolynomial.renameEquiv_apply,
    rename_X, rename_X]

/-- The ideal-level invariance (the `≤` direction — all the descent needs). -/
theorem lineRename_crossIdeal_map_le (M : ℕ) :
    (crossIdeal M).map (lineRename M).toRingEquiv.toRingHom ≤ crossIdeal M := by
  show Ideal.map _ (Ideal.span (crossMonomials M)) ≤ crossIdeal M
  rw [Ideal.map_span, Ideal.span_le]
  rintro _ ⟨p, hp, rfl⟩
  exact Ideal.subset_span (lineRename_crossMonomials_mem M hp)

/-- The elementwise invariance, from the ideal-level map lemma. -/
theorem lineRename_mem_crossIdeal (M : ℕ) {p : lineRing M}
    (hp : p ∈ crossIdeal M) : lineRename M p ∈ crossIdeal M := by
  have h : lineRename M p ∈
      (crossIdeal M).map (lineRename M).toRingEquiv.toRingHom :=
    Ideal.mem_map_of_mem (lineRename M).toRingEquiv.toRingHom hp
  exact lineRename_crossIdeal_map_le M h

/-- The symm-rotation preserves the cross ideal (from the iff + the
involution character of the same-block predicate). -/
theorem lineRenameSymm_mem_crossIdeal (M : ℕ) {p : lineRing M}
    (hp : p ∈ crossIdeal M) :
    MvPolynomial.renameEquiv ℂ (blockRot M).symm p ∈ crossIdeal M := by
  have hmap : (crossIdeal M).map
      (MvPolynomial.renameEquiv ℂ (blockRot M).symm).toRingEquiv.toRingHom ≤
      crossIdeal M := by
    show Ideal.map _ (Ideal.span (crossMonomials M)) ≤ crossIdeal M
    rw [Ideal.map_span, Ideal.span_le]
    rintro _ ⟨q, hq, rfl⟩
    obtain ⟨a, b, hab, rfl⟩ := hq
    refine Ideal.subset_span ⟨(blockRot M).symm a, (blockRot M).symm b, ?_, ?_⟩
    · exact fun hcon => hab ((blockRot_symm_sameBlock M a b).mp hcon)
    · show MvPolynomial.renameEquiv ℂ (blockRot M).symm (X a * X b) = _
      rw [map_mul, MvPolynomial.renameEquiv_apply, MvPolynomial.renameEquiv_apply,
        rename_X, rename_X]
  exact hmap (Ideal.mem_map_of_mem
    (MvPolynomial.renameEquiv ℂ (blockRot M).symm).toRingEquiv.toRingHom hp)

/-- The rotation precomposed with the quotient map. -/
def lineRotateLift₀ (M : ℕ) : lineRing M →ₐ[ℂ] lineQuotient M :=
  (lineQuotientMap M).comp (lineRename M).toAlgHom

theorem lineRotateLift₀_mk (M : ℕ) (t : lineRing M) :
    lineRotateLift₀ M t = lineQuotientMap M (lineRename M t) := rfl

/-- **THE ROTATED QUOTIENT HOM** — the descent of the rotation to the
cross-monomial quotient (the universal property of the quotient algebra:
`Ideal.Quotient.liftₐ`). -/
def lineRotateHom (M : ℕ) : lineQuotient M →ₐ[ℂ] lineQuotient M :=
  Ideal.Quotient.liftₐ (crossIdeal M) (lineRotateLift₀ M)
    (fun p hp => (lineQuotientMap_eq_zero_iff M (lineRename M p)).mpr
      (lineRename_mem_crossIdeal M hp))

/-- **THE COMMUTATION SQUARE**: rotate-then-quotient = quotient-then-rotate. -/
theorem lineRotateHom_mk (M : ℕ) (t : lineRing M) :
    lineRotateHom M (lineQuotientMap M t) = lineQuotientMap M (lineRename M t) := rfl

theorem lineRotateHom_comp_map (M : ℕ) :
    (lineRotateHom M).comp (lineQuotientMap M) = lineRotateLift₀ M :=
  Ideal.Quotient.liftₐ_comp (crossIdeal M) (lineRotateLift₀ M) _

/-- The inverse rotation, precomposed with the quotient map. -/
def lineRotateInvLift₀ (M : ℕ) : lineRing M →ₐ[ℂ] lineQuotient M :=
  (lineQuotientMap M).comp (MvPolynomial.renameEquiv ℂ (blockRot M).symm).toAlgHom

theorem lineRotateInvLift₀_mk (M : ℕ) (t : lineRing M) :
    lineRotateInvLift₀ M t =
      lineQuotientMap M (MvPolynomial.renameEquiv ℂ (blockRot M).symm t) :=
  rfl

/-- The inverse descent. -/
def lineRotateInvHom (M : ℕ) : lineQuotient M →ₐ[ℂ] lineQuotient M :=
  Ideal.Quotient.liftₐ (crossIdeal M) (lineRotateInvLift₀ M)
    (fun p hp => (lineQuotientMap_eq_zero_iff M
      (MvPolynomial.renameEquiv ℂ (blockRot M).symm p)).mpr
      (lineRenameSymm_mem_crossIdeal M hp))

theorem lineRotateInvHom_mk (M : ℕ) (t : lineRing M) :
    lineRotateInvHom M (lineQuotientMap M t) =
      lineQuotientMap M (MvPolynomial.renameEquiv ℂ (blockRot M).symm t) := rfl

theorem lineRotateInvHom_comp_map (M : ℕ) :
    (lineRotateInvHom M).comp (lineQuotientMap M) = lineRotateInvLift₀ M :=
  Ideal.Quotient.liftₐ_comp (crossIdeal M) (lineRotateInvLift₀ M) _
