/-! # Wave 65.1-C — §3-tail + §4 (lines 299–495) repair of `GSTFiniteLineWorldCarrier.lean`

REPLACEMENT TEXT for the original lines 299 through 495 (from the `-- The roundtrip`
comment preceding `theorem lineRotateHom_comp_inv` through `theorem
finiteLineCycle_isIso`).  All declaration names and statements are unchanged; only
proofs are redesigned (as the wave law allows).  Upstream §3 forms (Agent B,
`wave65_1_B.lean`) are consumed unchanged: `lineRename := MvPolynomial.renameEquiv ℂ
(blockRot M)`, `lineRename_apply`, `lineRotateHom_mk`, `lineRotateInvHom_mk`,
`lineRotateHom_comp_map`, `lineRotateInvHom_comp_map`.

Pin: Mathlib 51e6992efd06126df61a496bebf8f49482a4e129.  All Mathlib lemmas below are
pin-verified (see the mission report).

NOTE (downstream dependencies owned by other agents): this section consumes
`blockRotFn_pow' M` (§2, line 146 of the original — needs the postfix-parse fix
`blockRotFn M^[M]` → `(blockRotFn M)^[M]`, together with `blockRotFn_iterate_val`
line 128 and `blockRotFn_pow` line 139 — Agent A / §2's repair), and the receipt line
593 `#check blockRotFn_pow` must read `#check blockRotFn_pow'` (the §2 constant is
primed).  Neither is inside lines 299–495, so both are left to their owners.

Paste point: replace the original lines 299–495 with the text below verbatim.
-/

/-- The roundtrip: rotate after unrotate is the identity on the quotient. -/
theorem lineRotateHom_comp_inv (M : ℕ) :
    (lineRotateHom M).comp (lineRotateInvHom M) = AlgHom.id ℂ (lineQuotient M) := by
  refine Ideal.Quotient.algHom_ext (R₁ := ℂ) (I := crossIdeal M) ?_
  calc ((lineRotateHom M).comp (lineRotateInvHom M)).comp (lineQuotientMap M)
      = (lineRotateHom M).comp ((lineRotateInvHom M).comp (lineQuotientMap M)) :=
        AlgHom.comp_assoc _ _ _
    _ = (lineRotateHom M).comp (lineRotateInvLift₀ M) := by
        rw [lineRotateInvHom_comp_map]
    _ = (lineQuotientMap M).comp (AlgHom.id ℂ (lineRing M)) := by
        ext t
        show lineRotateHom M (lineQuotientMap M
            (MvPolynomial.renameEquiv ℂ (blockRot M).symm t)) = lineQuotientMap M t
        rw [lineRotateHom_mk]
        congr 1
        show MvPolynomial.renameEquiv ℂ (blockRot M)
            (MvPolynomial.renameEquiv ℂ (blockRot M).symm t) = t
        rw [MvPolynomial.renameEquiv_apply, MvPolynomial.renameEquiv_apply,
          rename_rename, Equiv.self_comp_symm, rename_id_apply]
    _ = (AlgHom.id ℂ (lineQuotient M)).comp (lineQuotientMap M) := by
        rw [AlgHom.comp_id, AlgHom.id_comp]

/-- The roundtrip: unrotate after rotate is the identity on the quotient. -/
theorem lineRotateInvHom_comp (M : ℕ) :
    (lineRotateInvHom M).comp (lineRotateHom M) = AlgHom.id ℂ (lineQuotient M) := by
  refine Ideal.Quotient.algHom_ext (R₁ := ℂ) (I := crossIdeal M) ?_
  calc ((lineRotateInvHom M).comp (lineRotateHom M)).comp (lineQuotientMap M)
      = (lineRotateInvHom M).comp ((lineRotateHom M).comp (lineQuotientMap M)) :=
        AlgHom.comp_assoc _ _ _
    _ = (lineRotateInvHom M).comp (lineRotateLift₀ M) := by
        rw [lineRotateHom_comp_map]
    _ = (lineQuotientMap M).comp (AlgHom.id ℂ (lineRing M)) := by
        ext t
        show lineRotateInvHom M (lineQuotientMap M (lineRename M t)) = lineQuotientMap M t
        rw [lineRotateInvHom_mk]
        congr 1
        show MvPolynomial.renameEquiv ℂ (blockRot M).symm
            (MvPolynomial.renameEquiv ℂ (blockRot M) t) = t
        rw [MvPolynomial.renameEquiv_apply, MvPolynomial.renameEquiv_apply,
          rename_rename, Equiv.symm_comp_self, rename_id_apply]
    _ = (AlgHom.id ℂ (lineQuotient M)).comp (lineQuotientMap M) := by
        rw [AlgHom.comp_id, AlgHom.id_comp]

theorem lineRotateHom_bijective (M : ℕ) : Function.Bijective (lineRotateHom M) := by
  constructor
  · intro x y h
    have hx : (lineRotateInvHom M) ((lineRotateHom M) x) = x :=
      DFunLike.congr_fun (lineRotateInvHom_comp M) x
    have hy : (lineRotateInvHom M) ((lineRotateHom M) y) = y :=
      DFunLike.congr_fun (lineRotateInvHom_comp M) y
    calc x = (lineRotateInvHom M) ((lineRotateHom M) x) := hx.symm
      _ = (lineRotateInvHom M) ((lineRotateHom M) y) :=
          congrArg (⇑(lineRotateInvHom M)) h
      _ = y := hy
  · intro y
    exact ⟨(lineRotateInvHom M) y, DFunLike.congr_fun (lineRotateHom_comp_inv M) y⟩

/-- The iterate law at the quotient level. -/
theorem lineRotateHom_iterate (M : ℕ) (n : ℕ) (t : lineRing M) :
    (lineRotateHom M)^[n] (lineQuotientMap M t) =
      lineQuotientMap M (MvPolynomial.rename ((blockRotFn M)^[n]) t) := by
  induction n with
  | zero =>
      show lineQuotientMap M t = lineQuotientMap M (MvPolynomial.rename id t)
      rw [rename_id_apply]
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, lineRotateHom_mk, lineRename_apply,
        rename_rename, ← Function.iterate_succ']

/-- **THE M-TH POWER OF THE ROTATION IS THE IDENTITY** (quotient level). -/
theorem lineRotateHom_pow (M : ℕ) : (lineRotateHom M)^[M] = id := by
  funext y
  obtain ⟨t, rfl⟩ := lineQuotientMap_surjective M y
  rw [lineRotateHom_iterate M M t, blockRotFn_pow' M, rename_id_apply]
  rfl

/-! ## §4 The graded rotation and the M-cycle automorphism -/

/-- **THE GRADED ROTATION** — the M-cycle as a graded ring homomorphism
(`GradedRingHom`, the flat structure: a ring hom plus the
piece-preservation field). -/
noncomputable def lineRotateGraded (M : ℕ) : lineGrading M →+*ᵍ lineGrading M where
  toRingHom := (lineRotateHom M).toRingHom
  map_mem := fun {i x} hx => by
    obtain ⟨t, ht, hxt⟩ := (mem_lineGrading M i x).mp hx
    subst hxt
    show lineRotateHom M (lineQuotientMap M t) ∈ lineGrading M i
    rw [lineRotateHom_mk]
    exact lineQuotientMap_mem_lineGrading M i _
      (lineRename_mem_homogeneousSubmodule M i t ht)

/-- The inverse graded rotation. -/
noncomputable def lineRotateInvGraded (M : ℕ) : lineGrading M →+*ᵍ lineGrading M where
  toRingHom := (lineRotateInvHom M).toRingHom
  map_mem := fun {i x} hx => by
    obtain ⟨t, ht, hxt⟩ := (mem_lineGrading M i x).mp hx
    subst hxt
    show lineRotateInvHom M (lineQuotientMap M t) ∈ lineGrading M i
    rw [lineRotateInvHom_mk, MvPolynomial.renameEquiv_apply]
    exact lineQuotientMap_mem_lineGrading M i _
      ((mem_homogeneousSubmodule _ _).mpr
        (IsHomogeneous.rename_isHomogeneous
          ((mem_homogeneousSubmodule _ _).mp ht)))

theorem lineRotateGraded_comp_inv (M : ℕ) :
    (lineRotateGraded M).comp (lineRotateInvGraded M) =
      GradedRingHom.id (lineGrading M) := by
  ext x
  show lineRotateHom M (lineRotateInvHom M x) = x
  exact DFunLike.congr_fun (lineRotateHom_comp_inv M) x

theorem lineRotateInvGraded_comp (M : ℕ) :
    (lineRotateInvGraded M).comp (lineRotateGraded M) =
      GradedRingHom.id (lineGrading M) := by
  ext x
  show lineRotateInvHom M (lineRotateHom M x) = x
  exact DFunLike.congr_fun (lineRotateInvHom_comp M) x

theorem lineRotateGraded_surjective (M : ℕ) :
    Function.Surjective (lineRotateGraded M).toRingHom :=
  (lineRotateHom_bijective M).surjective

theorem lineRotateInvGraded_surjective (M : ℕ) :
    Function.Surjective (lineRotateInvGraded M).toRingHom := by
  intro z
  refine ⟨(lineRotateGraded M) z, ?_⟩
  show (lineRotateInvGraded M) ((lineRotateGraded M) z) = z
  rw [← GradedRingHom.comp_apply, lineRotateInvGraded_comp,
    GradedRingHom.id_apply]

/-- **THE M-TH POWER OF THE GRADED ROTATION IS THE IDENTITY** — the
cycle law receipt at the graded-ring level (the geometric scheme-level
pow rides the F3 wave where the letters consume it). -/
theorem lineRotateGraded_pow (M : ℕ) :
    (lineRotateGraded M) ^ M = GradedRingHom.id (lineGrading M) := by
  ext x
  rw [GradedRingHom.coe_pow]
  show (lineRotateHom M)^[M] x = x
  rw [lineRotateHom_pow]
  rfl

/-- **THE IRRELEVANT-IDEAL HYPOTHESIS** for the rotation's `Proj.map`:
the quotient's irrelevant ideal lies in the image of the ambient one
under the graded rotation.  Route: elementwise via the inverse witness —
`y ∈ ℬ₊` (i.e. `proj ℬ 0 y = 0`) has preimage `g y` with
`proj 𝒜 0 (g y) = g (proj ℬ 0 y) = 0`. -/
theorem lineRotate_irrelevant_le (M : ℕ) :
    HomogeneousIdeal.irrelevant (lineGrading M) ≤
      HomogeneousIdeal.map (lineRotateGraded M)
        (HomogeneousIdeal.irrelevant (lineGrading M)) := by
  rw [SetLike.le_def]
  intro y hy
  rw [HomogeneousIdeal.mem_irrelevant_iff] at hy
  have hsurj : Function.Surjective (lineRotateGraded M).toRingHom :=
    lineRotateGraded_surjective M
  show y ∈ Ideal.map (lineRotateGraded M).toRingHom
    (HomogeneousIdeal.irrelevant (lineGrading M)).toIdeal
  refine (Ideal.mem_map_iff_of_surjective _ hsurj).mpr
    ⟨(lineRotateInvGraded M) y, ?_, ?_⟩
  · show (lineRotateInvGraded M) y ∈
      HomogeneousIdeal.irrelevant (lineGrading M)
    rw [HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply,
      ← GradedRingHom.map_directSumDecompose, ← GradedRing.proj_apply, hy]
    exact map_zero _
  · show (lineRotateGraded M) ((lineRotateInvGraded M) y) = y
    rw [← GradedRingHom.comp_apply, lineRotateGraded_comp_inv,
      GradedRingHom.id_apply]

theorem lineRotate_inv_irrelevant_le (M : ℕ) :
    HomogeneousIdeal.irrelevant (lineGrading M) ≤
      HomogeneousIdeal.map (lineRotateInvGraded M)
        (HomogeneousIdeal.irrelevant (lineGrading M)) := by
  rw [SetLike.le_def]
  intro y hy
  rw [HomogeneousIdeal.mem_irrelevant_iff] at hy
  have hsurj : Function.Surjective (lineRotateInvGraded M).toRingHom :=
    lineRotateInvGraded_surjective M
  show y ∈ Ideal.map (lineRotateInvGraded M).toRingHom
    (HomogeneousIdeal.irrelevant (lineGrading M)).toIdeal
  refine (Ideal.mem_map_iff_of_surjective _ hsurj).mpr
    ⟨(lineRotateGraded M) y, ?_, ?_⟩
  · show (lineRotateGraded M) y ∈
      HomogeneousIdeal.irrelevant (lineGrading M)
    rw [HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply,
      ← GradedRingHom.map_directSumDecompose, ← GradedRing.proj_apply, hy]
    exact map_zero _
  · show (lineRotateInvGraded M) ((lineRotateGraded M) y) = y
    rw [← GradedRingHom.comp_apply, lineRotateInvGraded_comp,
      GradedRingHom.id_apply]

/-- **THE M-CYCLE AUTOMORPHISM OF THE FINITE-LINE WORLD** — `Proj.map` of
the graded rotation (Functor.lean:148). -/
noncomputable def finiteLineCycle (M : ℕ) :
    finiteLineScheme M ⟶ finiteLineScheme M :=
  Proj.map (lineRotateGraded M) (lineRotate_irrelevant_le M)

/-- The inverse of the M-cycle automorphism. -/
noncomputable def finiteLineCycleInv (M : ℕ) :
    finiteLineScheme M ⟶ finiteLineScheme M :=
  Proj.map (lineRotateInvGraded M) (lineRotate_inv_irrelevant_le M)

/-- **THE TRANSPORT BRIDGE for `Proj.map`**: if a graded hom is (on the nose)
the identity, then its `Proj.map` is the identity — the dependent
second argument of `Proj.map` (the `ℬ₊ ≤ 𝒜₊.map f` hypothesis, whose
type mentions `f`) is transported by `subst` (which eliminates the binder
`f`, transporting `hf`'s type with it), and the resulting
`Proj.map (GradedRingHom.id 𝒜) hf'` is closed by `Proj.map_id`: its
hardcoded `(by simp)` proof and the transported `hf'` inhabit the very
same proposition, so proof irrelevance identifies them definitionally.
This is the whole point the plain `rw [h, Proj.map_id]` chain cannot do:
rewriting `f` inside `Proj.map f hf` breaks the motive because `hf`'s
type mentions `f`. -/
private theorem map_id_of_eq {A σ : Type u} [CommRing A] [SetLike σ A]
    [AddSubgroupClass σ A] {𝒜 : ℕ → σ} [GradedRing 𝒜] {f : 𝒜 →+*ᵍ 𝒜}
    (h : f = GradedRingHom.id 𝒜)
    (hf : HomogeneousIdeal.irrelevant 𝒜 ≤
      HomogeneousIdeal.map f (HomogeneousIdeal.irrelevant 𝒜)) :
    Proj.map f hf = 𝟙 (Proj 𝒜) := by
  subst h
  exact Proj.map_id

/-- **THE M-CYCLE AUTOMORPHISM IS AN ISOMORPHISM** — the flat `IsIso`
constructor with the graded roundtrips (map_comp + map_id).  The two
composition goals are reduced by `← Proj.map_comp` to `Proj.map` of the
two graded roundtrips (`(lineRotateGraded M).comp (lineRotateInvGraded M)`
and its mirror), which equal `GradedRingHom.id` by the graded comp laws;
the `map_id_of_eq` bridge then transports each to `𝟙` via `Proj.map_id`. -/
theorem finiteLineCycle_isIso (M : ℕ) : IsIso (finiteLineCycle M) :=
  ⟨finiteLineCycleInv M, by
    rw [finiteLineCycle, finiteLineCycleInv, ← Proj.map_comp]
    exact map_id_of_eq (lineRotateGraded_comp_inv M) _,
  by
    rw [finiteLineCycle, finiteLineCycleInv, ← Proj.map_comp]
    exact map_id_of_eq (lineRotateInvGraded_comp M) _⟩
