import Mathlib
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import HCUniverse2.GSTFiniteLineRing
import HCUniverse2.GSTProjectiveOverC

/-
Copyright (c) 2026. The HC-PROOF campaign. All rights reserved.

# THE FINITE-LINE WORLD CARRIER (Wave 65, F1 — the algebraic core)

THE CARRIER MODULE of the finite-line world construction, on the CI-green
substrate `GSTFiniteLineRing.lean` (run 44744364603 at 3ddf33b): the
disjoint union of `M` projective lines, presented as the `Proj` of the
cross-monomial quotient grading — the frozen wave-44/60/62 design.

THIS MODULE lands the carrier's algebraic core:

* `finiteLineScheme M` — `Proj (lineGrading M)` (the scheme carrier);
* `finiteLineStructureMap M` — the structure morphism to `Spec(ℂ)`, in the
  corpus's `projectiveSpaceToBase` shape (`Proj.toSpecZero` composed with
  the `Spec.map` of the degree-zero scalar algebra map);
* `blockRot` — the block rotation `a ↦ (a + 2) mod 2M` on the coordinate
  indices, the `M`-cycle with `blockRotFn^[M] = id`;
* `lineRename` / `lineRotateHom` / `lineRotateGraded` — the M-cycle
  rotation descended to the cross-monomial quotient as a graded ring
  automorphism (the W1-D atlas: `renameEquiv + Ideal.Quotient.liftₐ +
  GradedRingHom + Proj.map + map_comp/map_id → IsIso`);
* `finiteLineCycle M` — **THE M-CYCLE AUTOMORPHISM** of the finite-line
  world: `Proj.map` of the graded rotation, an isomorphism (`finiteLineCycle_isIso`)
  whose graded `M`-th power is the identity (`lineRotateGraded_pow`) — the
  geometric input of the wave-64 cyclic word's realization gate (the letters
  of the final law landing are the graphs of this automorphism);
* `lineFinEquiv` / `lineGradedQuotientHom` / `finiteLineEmbedding M` —
  the arity bridge `Fin (2M-1+1) ≃ Fin (2M)` and the graded quotient
  presentation, whose `Proj.map` is the closed embedding of the line
  world into `ℙ^{2M-1}` (the `ProjectiveOverC` witness's immersion —
  the closed-immersion certification is the next wave's chartwise battle,
  per the frozen Route-A order).

Honesty ledger: every statement is proved unconditionally. No `sorry`, no
new axioms, no `native_decide`. The GitHub CI lane
`gst-finite-line-world-carrier.yml` owns the kernel check.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry CategoryTheory
open GSTProjectiveOverC GSTFiniteLineRing
open MvPolynomial DirectSum

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GSTFiniteLineWorldCarrier

/-! ## §1 The scheme carrier and its structure map -/

/-- **THE FINITE-LINE SCHEME** — the `Proj` of the cross-monomial quotient
grading (`lineGrading`, the CI-green substrate).  An `abbrev` (reducible
alias), per the point-world carrier law: `rw` pattern matching and
instance synthesis run at `.instances` transparency, where a plain `def`
is opaque. -/
abbrev finiteLineScheme (M : ℕ) : Scheme :=
  Proj (lineGrading M)

/-- **THE STRUCTURE MORPHISM TO `Spec(ℂ)`** — the transposed
`projectiveSpaceToBase` (GSTProjectiveOverC.lean:55-59): `Proj.toSpecZero`
to the degree-zero homogeneous piece, composed with the `Spec.map` of the
scalar algebra map.  The instances (`CommRing ↥(lineGrading M 0)` via
`SetLike.GradeZero.instCommRing`, `Algebra ℂ ↥(lineGrading M 0)` via
`SetLike.GradeZero.instAlgebra` — both fire because `lineGrading M` is
literally a `Submodule`-family with `lineGrading_gradedMonoid`) require no
hand-rolled provisioning; `GradedRing (lineGrading M)` rides the
`GradedAlgebra` abbrev of the substrate instance. -/
noncomputable def finiteLineStructureMap (M : ℕ) :
    finiteLineScheme M ⟶ complexBase :=
  Proj.toSpecZero (lineGrading M) ≫
    Spec.map (CommRingCat.ofHom (algebraMap ℂ (lineGrading M 0)))
/-! ## §2 The block rotation on the coordinate indices -/

/-- **THE BLOCK ROTATION FUNCTION** — `a ↦ (a + 2) mod 2M`: rotates the `M`
coordinate blocks cyclically (block `i` ↦ block `i + 1 mod M`).  The corpus
pattern is `cyclicSucc` (GSTSingularCohomologyMaps.lean:244). -/
def blockRotFn (M : ℕ) : Fin (2 * M) → Fin (2 * M) := fun a =>
  ⟨(a.val + 2) % (2 * M),
    Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le a.val) a.isLt)⟩

/-- The inverse rotation `a ↦ (a + (2M − 2)) mod 2M`. -/
def blockRotInvFn (M : ℕ) : Fin (2 * M) → Fin (2 * M) := fun a =>
  ⟨(a.val + (2 * M - 2)) % (2 * M),
    Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le a.val) a.isLt)⟩

theorem blockRotInvFn_fn (M : ℕ) (a : Fin (2 * M)) :
    blockRotInvFn M (blockRotFn M a) = a := by
  have ha : a.val < 2 * M := a.isLt
  apply Fin.ext
  show ((a.val + 2) % (2 * M) + (2 * M - 2)) % (2 * M) = a.val
  rw [Nat.mod_add_mod]
  have hadd : a.val + 2 + (2 * M - 2) = a.val + 2 * M := by omega
  rw [hadd, Nat.add_mod_right]
  exact Nat.mod_eq_of_lt ha

theorem blockRotFn_invFn (M : ℕ) (a : Fin (2 * M)) :
    blockRotFn M (blockRotInvFn M a) = a := by
  have ha : a.val < 2 * M := a.isLt
  apply Fin.ext
  show ((a.val + (2 * M - 2)) % (2 * M) + 2) % (2 * M) = a.val
  rw [Nat.mod_add_mod]
  have hadd : a.val + (2 * M - 2) + 2 = a.val + 2 * M := by omega
  rw [hadd, Nat.add_mod_right]
  exact Nat.mod_eq_of_lt ha

/-- **THE BLOCK-ROTATION EQUIV** on the coordinate indices. -/
def blockRot (M : ℕ) : Fin (2 * M) ≃ Fin (2 * M) where
  toFun := blockRotFn M
  invFun := blockRotInvFn M
  left_inv := blockRotInvFn_fn M
  right_inv := blockRotFn_invFn M

theorem blockRot_val (M : ℕ) (a : Fin (2 * M)) :
    (blockRot M a).val = (a.val + 2) % (2 * M) := rfl

/-- The function-level value bridge (the rotation function applied). -/
theorem blockRotFn_val (M : ℕ) (a : Fin (2 * M)) :
    (blockRotFn M a).val = (a.val + 2) % (2 * M) := rfl

/-- The iterate law: `n` rotations shift the index by `2n`. -/
theorem blockRotFn_iterate_val (M : ℕ) (n : ℕ) (a : Fin (2 * M)) :
    ((blockRotFn M)^[n] a).val = (a.val + 2 * n) % (2 * M) := by
  induction n generalizing a with
  | zero =>
      show a.val = (a.val + 2 * 0) % (2 * M)
      exact (Nat.mod_eq_of_lt a.isLt).symm
  | succ n ih =>
      rw [Function.iterate_succ_apply', blockRotFn_val, ih a, Nat.mod_add_mod]
      have hA : a.val + 2 * n + 2 = a.val + 2 * (n + 1) := by omega
      rw [hA]

/-- **THE M-TH POWER IS THE IDENTITY** — the cycle law at the index level. -/
theorem blockRotFn_pow (M : ℕ) (a : Fin (2 * M)) :
    (blockRotFn M)^[M] a = a := by
  apply Fin.ext
  have h := blockRotFn_iterate_val M M a
  rw [Nat.add_mod_right, Nat.mod_eq_of_lt a.isLt] at h
  exact h

/-- The function-level form of the cycle law. -/
theorem blockRotFn_pow' (M : ℕ) : (blockRotFn M)^[M] = id :=
  funext (blockRotFn_pow M)

/-- The two faces of the rotation value: the no-wrap and the wrap case,
with their wrap conditions (the case lemma carries its bound — required
for the same-block preservation below). -/
theorem blockRot_val_cases (M : ℕ) (c : Fin (2 * M)) :
    ((blockRot M c).val = c.val + 2 ∧ c.val + 2 < 2 * M) ∨
    ((blockRot M c).val = c.val + 2 - 2 * M ∧ 2 * M ≤ c.val + 2) := by
  have hc := c.isLt
  rcases Nat.lt_or_ge (c.val + 2) (2 * M) with h | h
  · exact Or.inl ⟨Nat.mod_eq_of_lt h, h⟩
  · refine Or.inr ⟨?_, h⟩
    have hX : c.val + 2 - 2 * M + 2 * M = c.val + 2 := by omega
    have hlt : c.val + 2 - 2 * M < 2 * M := by omega
    have hmod : (c.val + 2 - 2 * M + 2 * M) % (2 * M) = c.val + 2 - 2 * M := by
      rw [Nat.add_mod_right]
      exact Nat.mod_eq_of_lt hlt
    have hbr : (c.val + 2) % (2 * M) =
        (c.val + 2 - 2 * M + 2 * M) % (2 * M) := by rw [hX]
    show (c.val + 2) % (2 * M) = c.val + 2 - 2 * M
    rw [hbr, hmod]

/-- **SAME-BLOCK PRESERVATION** — the block structure is preserved in both
directions (the iff, not the equality: the rotation moves every block). -/
theorem blockRot_sameBlock (M : ℕ) (a b : Fin (2 * M)) :
    (blockRot M a).val / 2 = (blockRot M b).val / 2 ↔ a.val / 2 = b.val / 2 := by
  have ha := a.isLt
  have hb := b.isLt
  rcases blockRot_val_cases M a with ⟨ha', ha''⟩ | ⟨ha', ha''⟩ <;>
    rcases blockRot_val_cases M b with ⟨hb', hb''⟩ | ⟨hb', hb''⟩ <;>
    simp only [ha', hb'] <;> constructor <;> intro h <;> omega

/-- The symm version, for free from the iff and `Equiv.apply_symm_apply`. -/
theorem blockRot_symm_sameBlock (M : ℕ) (a b : Fin (2 * M)) :
    ((blockRot M).symm a).val / 2 = ((blockRot M).symm b).val / 2 ↔
      a.val / 2 = b.val / 2 := by
  have ea : blockRot M ((blockRot M).symm a) = a :=
    Equiv.apply_symm_apply (blockRot M) a
  have eb : blockRot M ((blockRot M).symm b) = b :=
    Equiv.apply_symm_apply (blockRot M) b
  constructor
  · intro h
    have h2 := (blockRot_sameBlock M ((blockRot M).symm a) ((blockRot M).symm b)).mpr h
    rwa [ea, eb] at h2
  · intro h
    have h2 : (blockRot M ((blockRot M).symm a)).val / 2
        = (blockRot M ((blockRot M).symm b)).val / 2 := by
      rw [ea, eb]
      exact h
    exact (blockRot_sameBlock M ((blockRot M).symm a) ((blockRot M).symm b)).mp h2

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
            (MvPolynomial.renameEquiv ℂ (blockRot M).symm (X t))) = lineQuotientMap M (X t)
        rw [lineRotateHom_mk]
        congr 1
        show MvPolynomial.renameEquiv ℂ (blockRot M)
            (MvPolynomial.renameEquiv ℂ (blockRot M).symm (X t)) = X t
        rw [MvPolynomial.renameEquiv_apply, MvPolynomial.renameEquiv_apply,
          rename_X, rename_X, Equiv.apply_symm_apply]
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
        show lineRotateInvHom M (lineQuotientMap M (lineRename M (X t))) =
          lineQuotientMap M (X t)
        rw [lineRotateInvHom_mk]
        congr 1
        show MvPolynomial.renameEquiv ℂ (blockRot M).symm
            (MvPolynomial.renameEquiv ℂ (blockRot M) (X t)) = X t
        rw [MvPolynomial.renameEquiv_apply, MvPolynomial.renameEquiv_apply,
          rename_X, rename_X, Equiv.symm_apply_apply]
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

/-! ## §5 The arity bridge and the closed embedding into ℙ^{2M-1} -/

/-- **THE ARITY BRIDGE** — `Fin (2M-1+1) ≃ Fin (2M)` (equal cardinalities;
`Nat.sub_add_cancel` — not defeq for variable `M`, hence the explicit
bridge). -/
def lineFinEquiv (M : ℕ) [NeZero M] : Fin (2 * M - 1 + 1) ≃ Fin (2 * M) where
  toFun a := ⟨a.val, Nat.lt_of_lt_of_le a.isLt (by
    have hM : 0 < M := Nat.pos_of_neZero ‹_›
    omega)⟩
  invFun b := ⟨b.val, Nat.lt_of_lt_of_le b.isLt (by
    have hM : 0 < M := Nat.pos_of_neZero ‹_›
    omega)⟩
  left_inv a := by
    apply Fin.ext
    rfl
  right_inv b := by
    apply Fin.ext
    rfl

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
    (MvPolynomial.rename ⇑((lineFinEquiv M).symm) t)) = lineQuotientMap M t
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
    exact HomogeneousIdeal.mem_irrelevant_of_mem (ProjectiveGrading (2 * M - 1)) hi
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

/-! ## Receipts -/

#check finiteLineScheme
#check finiteLineStructureMap
#check blockRot
#check blockRotFn_pow
#check lineRotateHom
#check lineRotateHom_bijective
#check lineRotateHom_pow
#check lineRotateGraded
#check lineRotateGraded_pow
#check lineRotate_irrelevant_le
#check finiteLineCycle
#check finiteLineCycle_isIso
#check lineGradedQuotientHom
#check line_irrelevant_le
#check finiteLineEmbedding

#print axioms finiteLineCycle
#print axioms finiteLineCycle_isIso
#print axioms finiteLineEmbedding

end GSTFiniteLineWorldCarrier

end
