import HCUniverse2.GSTTwelvePointAnalytification
import HCUniverse2.GSTGeometricRealizationStage2F

/-!
# GST TWELVE-POINT COHOMOLOGY

The rational singular cohomology of the twelve-point discrete world, computed
from Mathlib's genuine singular cochain machinery rather than postulated:

  `RationalSingularCohomology twelvePointAnalytification 0 ≃ₗ[ℚ] (Fin 12 → ℚ)`

with vanishing in every nonzero degree.  The computation runs through the
pinned Mathlib isomorphism `singularChainComplexFunctorIsoOfTotallyDisconnectedSpace`
(identifying the singular chain complex of a totally disconnected space with
`ChainComplex.alternatingConst.obj (∐ fun _ : X ↦ R)`), followed by the
corpus-verified linear-Yoneda dualization of that chain isomorphism, and a
direct computation of the resulting alternating dual cochain complex
(differential pattern `0, 𝟙, 0, 𝟙, ...`).

Steps flagged `-- AUDIT(n):` rest on pinned-Mathlib lemma names that could not
be byte-verified against the local partial checkout (no `Mathlib/CategoryTheory`
or `Mathlib/Algebra/Homology` source available here); they are the designated
repair points if CI reports a name mismatch.  No `sorry`, no fake axioms.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open CategoryTheory
open AlgebraicTopology
open GSTGeometricRealizationStage2F
-- AUDIT(1): the upstream W4-B module is assumed to follow the campaign
-- module-matching namespace convention, and
-- `twelvePointAnalytification.space` is assumed definitionally equal to the
-- contract constant `twelvePointSpace` (with `↥twelvePointSpace ≡ Fin 12`).
open GSTTwelvePointAnalytification

namespace GSTTwelvePointCohomology

/-! ## §1. The linear-Yoneda dualization machinery (corpus-verified pattern) -/

section Dualization

variable {K L : ChainComplex (ModuleCat ℚ) ℕ}

/-- Contravariant cochain dual of a chain map, with exactly the corpus
construction (`GSTClassicalHodgeAmbientBettiSelfProduct`). -/
noncomputable def dualChainHom (f : K ⟶ L) :
    L.linearYonedaObj ℚ rationalCoefficient ⟶
      K.linearYonedaObj ℚ rationalCoefficient :=
  (HomologicalComplex.unopFunctor (ModuleCat ℚ) (ComplexShape.down ℕ)).map
    (Quiver.Hom.op
      ((((CategoryTheory.linearYoneda ℚ (ModuleCat ℚ)).obj rationalCoefficient).rightOp
        |>.mapHomologicalComplex (ComplexShape.down ℕ)).map
        (f)))

/-- The cochain dual isomorphism of a chain isomorphism.  Both iso laws are
proved with the same op-arithmetic `rfl` steps the corpus used for
`swapCohomology_involutive`. -/
noncomputable def dualChainIso (e : K ≅ L) :
    K.linearYonedaObj ℚ rationalCoefficient ≅
      L.linearYonedaObj ℚ rationalCoefficient where
  hom := dualChainHom e.inv
  inv := dualChainHom e.hom
  hom_inv_id := by
    let F := (HomologicalComplex.unopFunctor (ModuleCat ℚ) (ComplexShape.down ℕ))
    let G := (((CategoryTheory.linearYoneda ℚ (ModuleCat ℚ)).obj rationalCoefficient).rightOp
      |>.mapHomologicalComplex (ComplexShape.down ℕ))
    change F.map (Quiver.Hom.op (G.map e.inv)) ≫
      F.map (Quiver.Hom.op (G.map e.hom)) = 𝟙 _
    rw [← F.map_comp,
      show (G.map e.inv).op ≫ (G.map e.hom).op
          = (G.map e.hom ≫ G.map e.inv).op from rfl,
      ← G.map_comp, e.hom_inv_id, G.map_id,
      -- WAVE 16 (run-15 errors at :77/:89): the two `show` rewrites had their
      -- variables SWAPPED — `hom_inv_id` reduces through
      -- `e.hom ≫ e.inv = 𝟙 K`, so the op-identity is at `G.obj K`.
      show (𝟙 (G.obj K)).op = 𝟙 (Opposite.op (G.obj K)) from rfl,
      F.map_id]
  inv_hom_id := by
    let F := (HomologicalComplex.unopFunctor (ModuleCat ℚ) (ComplexShape.down ℕ))
    let G := (((CategoryTheory.linearYoneda ℚ (ModuleCat ℚ)).obj rationalCoefficient).rightOp
      |>.mapHomologicalComplex (ComplexShape.down ℕ))
    change F.map (Quiver.Hom.op (G.map e.hom)) ≫
      F.map (Quiver.Hom.op (G.map e.inv)) = 𝟙 _
    rw [← F.map_comp,
      show (G.map e.hom).op ≫ (G.map e.inv).op
          = (G.map e.inv ≫ G.map e.hom).op from rfl,
      ← G.map_comp, e.inv_hom_id, G.map_id,
      -- WAVE 16: `inv_hom_id` reduces through `e.inv ≫ e.hom = 𝟙 L`.
      show (𝟙 (G.obj L)).op = 𝟙 (Opposite.op (G.obj L)) from rfl,
      F.map_id]

/-- Homology transport along an isomorphism of cochain complexes, via the
corpus-verified `homologyMap_comp` / `homologyMap_id` lemmas. -/
noncomputable def homologyIsoOfIso {C D : CochainComplex (ModuleCat ℚ) ℕ}
    (e : C ≅ D) (n : ℕ) : C.homology n ≅ D.homology n where
  hom := HomologicalComplex.homologyMap e.hom n
  inv := HomologicalComplex.homologyMap e.inv n
  hom_inv_id := by
    have h : HomologicalComplex.homologyMap e.hom n ≫
        HomologicalComplex.homologyMap e.inv n =
        HomologicalComplex.homologyMap (e.hom ≫ e.inv) n := by
      rw [HomologicalComplex.homologyMap_comp]
    rw [h, e.hom_inv_id, HomologicalComplex.homologyMap_id]
  inv_hom_id := by
    have h : HomologicalComplex.homologyMap e.inv n ≫
        HomologicalComplex.homologyMap e.hom n =
        HomologicalComplex.homologyMap (e.inv ≫ e.hom) n := by
      rw [HomologicalComplex.homologyMap_comp]
    rw [h, e.inv_hom_id, HomologicalComplex.homologyMap_id]

end Dualization

/-! ## §2. The twelve-point chain complex and its alternating form -/

/-- The coproduct of twelve copies of the rational coefficient object. -/
noncomputable def twelvePointE : ModuleCat ℚ :=
  ∐ fun _ : ↥twelvePointSpace ↦ rationalCoefficient

/-- Mathlib's pinned isomorphism: the singular chain complex of the totally
disconnected twelve-point space is the alternating constant complex on
`twelvePointE`. -/
noncomputable def twelvePointChainIso :
    rationalSingularChains twelvePointAnalytification ≅
      ChainComplex.alternatingConst.obj twelvePointE :=
  singularChainComplexFunctorIsoOfTotallyDisconnectedSpace (ModuleCat ℚ)
    rationalCoefficient twelvePointSpace

/-- The dual alternating cochain complex of the twelve-point world. -/
noncomputable def twelvePointDualCochains : CochainComplex (ModuleCat ℚ) ℕ :=
  (ChainComplex.alternatingConst.obj twelvePointE).linearYonedaObj
    ℚ rationalCoefficient

/-- The corpus definition unfolds definitionally to the linear-Yoneda dual. -/
theorem rationalSingularCochains_eq :
    rationalSingularCochains twelvePointAnalytification =
      (rationalSingularChains twelvePointAnalytification).linearYonedaObj
        ℚ rationalCoefficient := rfl

/-- The dualized chain isomorphism. -/
noncomputable def twelvePointDualIso :
    rationalSingularCochains twelvePointAnalytification ≅
      twelvePointDualCochains :=
  dualChainIso twelvePointChainIso

/-! ## §3. The alternating differential pattern -/

/-- The alternating constant complex has `d (2*k+1) (2*k) = 0`.
-- WAVE 16: the d-component is definitionally the parity ite (the functor's
-- obj is `HomologicalComplex.alternatingConst X` with φ := 𝟙, ψ := 0 at the
-- pin — AlternatingConst.lean:55/:159, the identities supplied through
-- `Category.id_comp 0` / `Category.comp_id 0`); the `show` states the ite
-- directly (checked at default transparency where the functor and complex
-- projections reduce), replacing the simps-unfolding that made no progress
-- (run-15 error at :154 — the generated `alternatingConst_obj` equation is
-- backward-oriented by `set_option backward.defeqAttrib.useBackward true`). -/
theorem altChain_d_odd (k : ℕ) :
    (ChainComplex.alternatingConst.obj twelvePointE).d (2*k+1) (2*k) = 0 := by
  have heven : ¬ Even (2*k+1) := by
    rw [Nat.even_iff]
    omega
  show (if _ : (ComplexShape.down ℕ).Rel (2*k+1) (2*k) then
      if _ : Even (2*k+1) then (𝟙 twelvePointE) else (0 : twelvePointE ⟶ twelvePointE)
      else 0) = 0
  -- WAVE 17 (run-16 errors at :169/:171): split_ifs bound `hi` in a different
  -- subgoal than the bullet that used it; the deterministic dite rewrites
  -- close the parity ite without any case-split bookkeeping.
  rw [dif_pos (show (ComplexShape.down ℕ).Rel (2*k+1) (2*k) from rfl), dif_neg heven]

/-- The alternating constant complex has `d (2*k+2) (2*k+1) = 𝟙`.
-- WAVE 16: the RHS is stated at the projected term (the bare `𝟙 twelvePointE`
-- fails the equation's implicit-transparency typecheck — run-15 error at
-- :166 — the X-projection through the functor is semireducible); the body
-- mirrors `altChain_d_odd`'s direct ite route. -/
theorem altChain_d_even (k : ℕ) :
    (ChainComplex.alternatingConst.obj twelvePointE).d (2*k+2) (2*k+1) =
      (𝟙 twelvePointE :
        (ChainComplex.alternatingConst.obj twelvePointE).X (2*k+2) ⟶
        (ChainComplex.alternatingConst.obj twelvePointE).X (2*k+1)) := by
  have heven : Even (2*k+2) := ⟨k+1, by omega⟩
  -- WAVE 17 (run-16 error at :218 downstream): the RHS is ascribed at the
  -- SLOT shape (X (2*k+2) ⟶ X (2*k+1)) so that `rw` transports it into the
  -- `Linear.leftComp` slot type-correctly at instances transparency; the
  -- endomorphism-shaped `𝟙 (X (2*k+2))` made the transported goal ill-typed.
  show (if _ : (ComplexShape.down ℕ).Rel (2*k+2) (2*k+1) then
      if _ : Even (2*k+2) then (𝟙 twelvePointE) else (0 : twelvePointE ⟶ twelvePointE)
      else 0) =
    (𝟙 twelvePointE :
      (ChainComplex.alternatingConst.obj twelvePointE).X (2*k+2) ⟶
      (ChainComplex.alternatingConst.obj twelvePointE).X (2*k+1))
  rw [dif_pos (show (ComplexShape.down ℕ).Rel (2*k+2) (2*k+1) from rfl), dif_pos heven]

/-- The dual differential on even indices is zero.
-- AUDIT(3): pinned `linearYonedaObj_d` simps lemma, `Linear.leftComp_apply`,
-- and module hom extensionality. -/
theorem dualCochains_d_even (k : ℕ) :
    twelvePointDualCochains.d (2*k) (2*k+1) = 0 := by
  -- WAVE 19 (run-18 error at :215): `ModuleCat.Hom.ext` abstracts the PRIMED
  -- field `hom'` (ModuleCat/Basic.lean:91-95) while `ModuleCat.hom_ofHom` /
  -- `hom_zero` are stated through the UNPRIMED alias `Hom.hom`
  -- (ModuleCat/Basic.lean:114-127) — a non-reducible ConcreteCategory
  -- projection; the semi-match it gets at instances transparency produces an
  -- ill-typed motive (the of ℚ-spelling vs twelvePointDualCochains.X-spelling
  -- clash).  The route is abandoned: the zero is transported INSIDE ofHom at
  -- the LinearMap level (ext + leftComp_apply, mirroring the green hid below;
  -- zero_comp and LinearMap.zero_apply are default simp lemmas at the pin),
  -- then `ModuleCat.ofHom_zero` (ModuleCat/Basic.lean:390, an rfl-lemma)
  -- closes by exact at default transparency — the same dual.X-defeq the
  -- hd-have's linearYonedaObj_d exact already exercised.
  have hd : twelvePointDualCochains.d (2*k) (2*k+1) =
      ModuleCat.ofHom (Linear.leftComp ℚ rationalCoefficient
        ((ChainComplex.alternatingConst.obj twelvePointE).d (2*k+1) (2*k))) := by
    unfold twelvePointDualCochains
    exact ChainComplex.linearYonedaObj_d _ _ _ _ _
  rw [hd, altChain_d_odd k]
  have h0 : Linear.leftComp ℚ rationalCoefficient
      (0 : (ChainComplex.alternatingConst.obj twelvePointE).X (2*k+1) ⟶
       (ChainComplex.alternatingConst.obj twelvePointE).X (2*k)) = 0 := by
    ext g
    simp [Linear.leftComp_apply, CategoryTheory.Limits.zero_comp,
      LinearMap.zero_apply]
  rw [h0]
  exact ModuleCat.ofHom_zero

/-- The dual differential on odd indices is the identity.
-- AUDIT(3): pinned `linearYonedaObj_d` simps lemma, `Linear.leftComp_apply`,
-- and module hom extensionality. -/
theorem dualCochains_d_odd (k : ℕ) :
    twelvePointDualCochains.d (2*k+1) (2*k+2) =
      𝟙 (twelvePointDualCochains.X (2*k+1)) := by
  -- WAVE 19 (run-18 error at :241): the same `.hom'`-vs-`.hom` alias mismatch
  -- as the even case — `ModuleCat.hom_ofHom` / `hom_id` can never fire
  -- cleanly on a `.hom'`-goal, so Hom.ext is abandoned.  The green
  -- self-contained leftComp-id have is rewritten at the MORPHISM level; its
  -- only defeq burden (X (2*k+1) ≡ X (2*k+2) through alternatingConst's
  -- constant X-field, AlternatingConst.lean:58) is the one the green
  -- `rw [altChain_d_even k]` motive already discharged at run 18, and
  -- `ModuleCat.ofHom_id` (ModuleCat/Basic.lean:176, an rfl-lemma) closes by
  -- exact at default transparency.
  have hd : twelvePointDualCochains.d (2*k+1) (2*k+2) =
      ModuleCat.ofHom (Linear.leftComp ℚ rationalCoefficient
        ((ChainComplex.alternatingConst.obj twelvePointE).d (2*k+2) (2*k+1))) := by
    unfold twelvePointDualCochains
    exact ChainComplex.linearYonedaObj_d _ _ _ _ _
  rw [hd, altChain_d_even k]
  -- WAVE 20 (run-19 error at :256 — the sole survivor, 7-for-8 green):
  -- `rw [hid]` died because hid's `leftComp` implicit objects elaborated
  -- at the BARE {twelvePointE, twelvePointE} spelling (the 𝟙's own
  -- argument type fixes them before the ascription can act) while the
  -- goal's occurrence carries hd's d-slot spelling
  -- {X (2*k+2), X (2*k+1)} — kabstract cannot bridge the two spellings
  -- (alternatingConst is a plain def, default-transparency defeq only).
  -- The congrArg transport elaborates at hid's OWN spelling; the `.trans`
  -- with `ModuleCat.ofHom_id` (ModuleCat/Basic.lean:176, rfl) and the
  -- final unification against the goal run at default transparency —
  -- the exact-defeq discipline run 19 validated GREEN at all four
  -- Cluster-B sites.
  have hid : Linear.leftComp ℚ rationalCoefficient
      (𝟙 twelvePointE :
        (ChainComplex.alternatingConst.obj twelvePointE).X (2*k+2) ⟶
        (ChainComplex.alternatingConst.obj twelvePointE).X (2*k+1)) =
      LinearMap.id := by
    ext g
    simp [Linear.leftComp_apply, Category.id_comp]
  exact (congrArg ModuleCat.ofHom hid).trans ModuleCat.ofHom_id

/-- Degree zero differential of the dual complex. -/
theorem dualCochains_d_zero_one : twelvePointDualCochains.d 0 1 = 0 :=
  dualCochains_d_even 0

/-! ## §4. The zeroth homology of the dual alternating complex -/

-- AUDIT(4): cochain shape facts for `up ℕ` at index zero.
theorem upNext_zero : (ComplexShape.up ℕ).next 0 = 1 := by
  exact CochainComplex.next ℕ 0

theorem upPrev_zero : (ComplexShape.up ℕ).prev 0 = 0 := by
  exact CochainComplex.prev_nat_zero

theorem upNotRel_zero_zero : ¬ (ComplexShape.up ℕ).Rel 0 0 := by
  simp [ComplexShape.up_Rel]

/-- The shape zero differential. -/
theorem dualCochains_d_zero_zero : twelvePointDualCochains.d 0 0 = 0 :=
  twelvePointDualCochains.shape 0 0 upNotRel_zero_zero

/-- The zeroth homology of the dual alternating complex is its degree-zero
term. -- AUDIT(5) (wave 15): `isoHomologyι` / `pOpcyclesIso` take FOUR
explicit index/proof arguments at the pin (ShortComplex/HomologicalComplex.lean:534/:581:
`isoHomologyι (i) (j) (hj : c.next i = j) (h : K.d i j = 0) [K.HasHomology i]`,
`pOpcyclesIso (i) (j) (hi : c.prev j = i) (h : K.d i j = 0) [K.HasHomology j]`;
in-file usage `K.isoHomologyι i j hj h` at :563/:590) — the two-index call
`isoHomologyι 0 1 upNext_zero dualCochains_d_zero_one` composes with
`(pOpcyclesIso 0 0 upPrev_zero dualCochains_d_zero_zero).symm`:
`homology 0 ≅ opcycles 0 ≪≫ opcycles 0 ≅ X 0`. -/
noncomputable def twelvePointHomologyZero :
    twelvePointDualCochains.homology 0 ≅ twelvePointDualCochains.X 0 :=
  twelvePointDualCochains.isoHomologyι 0 1 upNext_zero dualCochains_d_zero_one ≪≫
    (twelvePointDualCochains.pOpcyclesIso 0 0 upPrev_zero
      dualCochains_d_zero_zero).symm

/-! ## §5. The object-level identification with `Fin 12 → ℚ` -/

/-- The coproduct of twelve rational coefficients is the function space.
-- AUDIT(6): `biproduct.isoCoproduct` / `ModuleCat.biproductIsoPi` names; also
-- relies on the upstream defeq `↥twelvePointSpace ≡ Fin 12`. -/
noncomputable def twelvePointEIso :
    twelvePointE ≅ ModuleCat.of ℚ (Fin 12 → ℚ) :=
  (Limits.biproduct.isoCoproduct
      (fun _ : Fin 12 ↦ ModuleCat.of ℚ ℚ)).symm ≪≫
    ModuleCat.biproductIsoPi (fun _ : Fin 12 ↦ ModuleCat.of ℚ ℚ)

/-- The coordinate identification of the dual of `Fin 12 → ℚ`:
a functional is its list of values on the standard single-point vectors.
-- WAVE 16 (run-15 error at :250): the invFun's anonymous `⟨...⟩` constructor
-- does not elaborate against the post-refactor LinearMap structure (which
-- extends AddHom); the named-field structure-instance syntax is the
corpus-standard idiom. -/
noncomputable def fin12DualEquiv :
    ((Fin 12 → ℚ) →ₗ[ℚ] ℚ) ≃ₗ[ℚ] (Fin 12 → ℚ) where
  toFun φ := fun i => φ (Pi.single i 1)
  map_add' φ ψ := by funext i; simp
  map_smul' r φ := by funext i; simp
  invFun c :=
    { toFun := fun x => ∑ i, c i * x i
      map_add' := by
        intro x y
        simp [Pi.add_apply, mul_add, Finset.sum_add_distrib,
          add_mul, Finset.sum_mul]
      map_smul' := by
        intro r x
        -- WAVE 17 (run-16 error at :283): the missing left pull-out was
        -- `Finset.mul_sum` (`Finset.sum_mul` is the wrong side — CI reported
        -- it unused).
        simp [Pi.smul_apply, smul_eq_mul, mul_comm, mul_assoc,
          mul_left_comm, Finset.mul_sum] }
  left_inv φ := by
    -- WAVE 17 (run-16 errors at :287/:289): bare `ext` fired the pi-single
    -- extensionality (introducing `x : Fin 12`, an index); the deterministic
    -- `LinearMap.ext` keeps `x` a vector so the never-tested calc runs.
    refine LinearMap.ext (fun x => ?_)
    have hx : x = ∑ i, x i • (Pi.single i 1 : Fin 12 → ℚ) := by
      funext j
      simp [Finset.sum_apply, Pi.single_apply, Pi.smul_apply,
        smul_eq_mul, mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq']
    show ∑ i, φ (Pi.single i 1 : Fin 12 → ℚ) * x i = φ x
    calc ∑ i, φ (Pi.single i 1 : Fin 12 → ℚ) * x i
        = ∑ i, x i * φ (Pi.single i 1 : Fin 12 → ℚ) :=
            Finset.sum_congr rfl (fun i _ => mul_comm _ _)
      _ = ∑ i, φ (x i • (Pi.single i 1 : Fin 12 → ℚ)) := by
            simp [map_smul, smul_eq_mul]
      _ = φ (∑ i, x i • (Pi.single i 1 : Fin 12 → ℚ)) :=
            (map_sum φ
              (fun i => x i • (Pi.single i 1 : Fin 12 → ℚ))
              Finset.univ).symm
      _ = φ x := (congrArg φ hx).symm
  right_inv c := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply, mul_one, mul_zero, mul_ite,
      Finset.sum_ite_eq, Finset.sum_ite_eq']

/-- The bridge from the `ModuleCat` hom-type to the linear map type: the
underlying `Hom.hom`, linear in the hom-module structure, with the inverse
`ModuleCat.ofHom`. -- WAVE 16 (run-15 error at :289): the homCongr's
codomain is the `ModuleCat.Hom` STRUCTURE type, not the `LinearMap` type —
`ModuleCat.Hom` is a one-field wrapper (ModuleCat/Basic.lean:94) — so
`fin12DualEquiv` cannot compose with it directly; this bridge (built on
Mathlib's own `ModuleCat.homEquiv`, ModuleCat/Basic.lean:195) closes the
commuting square. -/
noncomputable def homToLinearMap :
    (ModuleCat.of ℚ (Fin 12 → ℚ) ⟶ rationalCoefficient) ≃ₗ[ℚ]
      ((Fin 12 → ℚ) →ₗ[ℚ] ℚ) where
  toFun φ := φ.hom
  map_add' _φ _ψ := rfl
  map_smul' _r _φ := rfl
  invFun f := ModuleCat.ofHom f
  -- WAVE 17 (run-16 errors at :325): both triangle fields are `rfl` by
  -- structure eta (`ofHom φ.hom = φ`, `Hom.hom (ofHom f) = f`); the
  -- polymorphic `ModuleCat.homEquiv` cannot synthesize its module
  -- parameters from the LinearMap-side argument.
  left_inv _φ := rfl
  right_inv _f := rfl

/-- The degree-zero term of the dual complex, i.e. the internal Hom from
`twelvePointE`, as the function space `Fin 12 → ℚ`. -- AUDIT(8):
`Linear.homCongr`, `LinearEquiv.toModuleIso`, and the defeq
`twelvePointDualCochains.X 0 ≡ ModuleCat.of ℚ (E ⟶ R)`. -/
noncomputable def twelvePointXZeroIso :
    twelvePointDualCochains.X 0 ≅ ModuleCat.of ℚ (Fin 12 → ℚ) :=
  LinearEquiv.toModuleIso
    ((Linear.homCongr ℚ twelvePointEIso
        (Iso.refl rationalCoefficient)).trans
      (homToLinearMap.trans fin12DualEquiv))

/-! ## §6. Assembly: the degree-zero rational cohomology -/

/-- The full module-level isomorphism. -/
noncomputable def twelvePointCohomologyZeroObj :
    rationalSingularCohomologyObj twelvePointAnalytification 0 ≅
      ModuleCat.of ℚ (Fin 12 → ℚ) :=
  homologyIsoOfIso twelvePointDualIso 0 ≪≫
    twelvePointHomologyZero ≪≫ twelvePointXZeroIso

/-- **THE TARGET**: the zeroth rational singular cohomology of the twelve-point
world is the rational function space on twelve points. -- AUDIT(9):
`Iso.toLinearEquiv` name. -/
noncomputable def twelvePointCohomologyIso :
    RationalSingularCohomology twelvePointAnalytification 0 ≃ₗ[ℚ]
      (Fin 12 → ℚ) :=
  twelvePointCohomologyZeroObj.toLinearEquiv

/-! ## §7. Vanishing in nonzero degree -/

/-- Exactness of the dual alternating short complex at an odd index.
-- WAVE 16 (run-15 errors at :323/:339): the `shortComplexFunctor_obj_f/g`
simps lemmas do not fire on the bare `sc` abbrev (the wave-7 corpus idiom:
the sc's f/g fields are DEFEQ on the d-components; state them directly
through a `show`, then close with the pinned `ModuleCat.hom_zero` /
`ModuleCat.hom_id` simp lemmas — both used by Mathlib's own
`ModuleCat.subsingleton_of_isZero` proof at ModuleCat/Basic.lean:379). -/
theorem dualSc_exact_odd (k : ℕ) :
    ShortComplex.Exact (twelvePointDualCochains.sc (2*k+1)) := by
  -- WAVE 17 (run-16 error at :367): `(sc i).f = d (prev i) i` is true but NOT
  -- definitional (prev/next are choice-encoded dite's); the sc' route
  -- transports the short complex to the explicit-index form where the
  -- pinned `shortComplexFunctor'_obj_f/g` simps lemmas fire.
  have hprev : (ComplexShape.up ℕ).prev (2*k+1) = 2*k :=
    CochainComplex.prev_nat_succ (2*k)
  have hnext : (ComplexShape.up ℕ).next (2*k+1) = 2*k+2 := by
    rw [CochainComplex.next]
    omega
  have hsc : twelvePointDualCochains.sc (2*k+1) =
      twelvePointDualCochains.sc' (2*k) (2*k+1) (2*k+2) := by
    unfold HomologicalComplex.sc HomologicalComplex.sc'
      HomologicalComplex.shortComplexFunctor
    rw [hprev, hnext]
  rw [hsc, ShortComplex.moduleCat_exact_iff_range_eq_ker]
  -- WAVE 19 (run-18 errors at :420/:424): the `ModuleCat.hom_zero`/`hom_id`
  -- REWRITES died at rw's sub-default matching transparency — the 0/𝟙
  -- transported by `dualCochains_d_even/odd` carry the raw d-slot hom-type
  -- `X i ⟶ X j`, while the `ModuleCat.Hom.hom`-application's implicit object
  -- args are the sc'-projections, which only reduce at DEFAULT transparency
  -- (`shortComplexFunctor'` is a plain def). `exact` unifies at default, so
  -- the pinned rfl-lemmas close the transported goals directly.
  have hf : (twelvePointDualCochains.sc' (2*k) (2*k+1) (2*k+2)).f.hom = 0 := by
    rw [HomologicalComplex.shortComplexFunctor'_obj_f, dualCochains_d_even k]
    exact ModuleCat.hom_zero
  have hg : (twelvePointDualCochains.sc' (2*k) (2*k+1) (2*k+2)).g.hom =
      LinearMap.id := by
    rw [HomologicalComplex.shortComplexFunctor'_obj_g, dualCochains_d_odd k]
    exact ModuleCat.hom_id
  rw [hf, hg]
  -- WAVE 19 (run-18 error at :399): `simp [range_zero, ker_id]` left
  -- `⊥ = ker id` (ker_id unused — instance mismatch at simp's matching).
  -- The Eq.trans chain assigns every implicit FROM THE GOAL at default
  -- transparency; for the odd complex it is fully syntactic
  -- (range's codomain and ker's domain are both `(sc' …).X₂`).
  exact LinearMap.range_zero.trans LinearMap.ker_id.symm

/-- Exactness of the dual alternating short complex at a positive even index.
-- WAVE 16: same direct sc-field route as `dualSc_exact_odd`. -/
theorem dualSc_exact_even (k : ℕ) :
    ShortComplex.Exact (twelvePointDualCochains.sc (2*k+2)) := by
  -- WAVE 17 (run-16 error at :378): the same sc' route as
  -- dualSc_exact_odd (the author's show had the indices one degree down —
  -- the pinned sc is X (prev i) ⟶ X i ⟶ X (next i)).
  have hprev : (ComplexShape.up ℕ).prev (2*k+2) = 2*k+1 :=
    CochainComplex.prev_nat_succ (2*k+1)
  have hnext : (ComplexShape.up ℕ).next (2*k+2) = 2*k+3 := by
    rw [CochainComplex.next]
    omega
  have hsc : twelvePointDualCochains.sc (2*k+2) =
      twelvePointDualCochains.sc' (2*k+1) (2*k+2) (2*k+3) := by
    unfold HomologicalComplex.sc HomologicalComplex.sc'
      HomologicalComplex.shortComplexFunctor
    rw [hprev, hnext]
  rw [hsc, ShortComplex.moduleCat_exact_iff_range_eq_ker]
  -- WAVE 19 (run-18 errors at :452/:457): exact-closers at default
  -- transparency (same root cause as dualSc_exact_odd's run-18 failures);
  -- the g-fact keeps the 2*k+2-spelled show-restatement of
  -- dualCochains_d_even (k+1) (the 2*(k+1) Nat-mul spelling is not
  -- syntactic — run-17 error at :432).
  have hf : (twelvePointDualCochains.sc' (2*k+1) (2*k+2) (2*k+3)).f.hom =
      LinearMap.id := by
    rw [HomologicalComplex.shortComplexFunctor'_obj_f, dualCochains_d_odd k]
    exact ModuleCat.hom_id
  have hg : (twelvePointDualCochains.sc' (2*k+1) (2*k+2) (2*k+3)).g.hom = 0 := by
    rw [HomologicalComplex.shortComplexFunctor'_obj_g,
      show twelvePointDualCochains.d (2*k+2) (2*k+3) = 0 from
        dualCochains_d_even (k+1)]
    exact ModuleCat.hom_zero
  rw [hf, hg]
  -- WAVE 19 (run-18 error at :431): same trans-chain fix (`simp`'s range_id
  -- never fired — instance mismatch). The two ⊤-sides meet at
  -- `↥(X (2*k+1)) =?= ↥(X (2*k+2))`, default-defeq (the alternating dual
  -- complex is degree-constant — the same defeq run-18 already exercised
  -- when typechecking hf's statement at :449-450).
  exact LinearMap.range_id.trans LinearMap.ker_zero.symm

/-- Parity splitting of nonzero naturals.
-- WAVE 16 (run-15 error at :343): `omega` cannot discharge the existential
goal directly; split on `Nat.even_or_odd` first. -/
theorem parity_split (n : ℕ) (hn : n ≠ 0) :
    (∃ k, n = 2*k + 1) ∨ (∃ k, n = 2*k + 2) := by
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · rcases k with _ | k'
    · exact absurd (by omega) hn
    · exact Or.inr ⟨k', by omega⟩
  · exact Or.inl ⟨k, hk⟩

/-- The dual alternating complex is exact in every positive degree.
-- AUDIT(11): `ExactAt n` is definitionally `(C.sc n).Exact` in pinned
-- Mathlib (it is consumed there via `.of_iso` / `.isZero_homology` in
-- `Mathlib/AlgebraicTopology/SingularHomology/Basic.lean`). -/
theorem twelvePointDualCochains_exactAt (n : ℕ) (hn : n ≠ 0) :
    twelvePointDualCochains.ExactAt n := by
  show ShortComplex.Exact (twelvePointDualCochains.sc n)
  rcases parity_split n hn with ⟨k, hk⟩ | ⟨k, hk⟩
  · rw [hk]; exact dualSc_exact_odd k
  · rw [hk]; exact dualSc_exact_even k

/-- The dual alternating cohomology objects vanish in positive degree.
`ExactAt n` is definitionally `(C.sc n).Exact` in pinned
Mathlib (it is consumed there via `.of_iso` / `.isZero_homology` in
`Mathlib/AlgebraicTopology/SingularHomology/Basic.lean`).
-- WAVE 16 (run-15 errors at :360/:368): `IsZero` is
-- `CategoryTheory.Limits.IsZero` at the pin
-- (Limits/Shapes/ZeroObjects.lean:44) — the unqualified name does not
-- resolve under `open CategoryTheory` alone. -/
theorem twelvePointDualCochomology_isZero (n : ℕ) (hn : n ≠ 0) :
    CategoryTheory.Limits.IsZero (twelvePointDualCochains.homology n) :=
  (twelvePointDualCochains_exactAt n hn).isZero_homology

/-- **THE VANISHING TARGET**: rational singular cohomology of the twelve-point
world is trivial in every nonzero degree. -- AUDIT(12): `IsZero.eq`. -/
theorem twelvePointCohomology_subsingleton (n : ℕ) (hn : n ≠ 0) :
    Subsingleton (RationalSingularCohomology twelvePointAnalytification n) := by
  let e := (homologyIsoOfIso twelvePointDualIso n).toLinearEquiv
  have hD : CategoryTheory.Limits.IsZero (twelvePointDualCochains.homology n) :=
    twelvePointDualCochomology_isZero n hn
  refine ⟨fun a b => ?_⟩
  -- WAVE 17 (run-16 error at :429): the calc's middle step could not
  -- synthesize `Trans Eq Eq ?m` (the `congr 1` block poisoned the step's
  -- type); the explicit Eq.trans chain is deterministic.
  have key : e a = e b := by
    haveI : Subsingleton (twelvePointDualCochains.homology n) :=
      ModuleCat.subsingleton_of_isZero hD
    exact Subsingleton.elim (e a) (e b)
  exact (e.symm_apply_apply a).symm.trans
    ((congrArg e.symm key).trans (e.symm_apply_apply b))

end GSTTwelvePointCohomology

#check GSTTwelvePointCohomology.twelvePointCohomologyIso
#check GSTTwelvePointCohomology.twelvePointCohomology_subsingleton

#print axioms GSTTwelvePointCohomology.twelvePointCohomologyIso
#print axioms GSTTwelvePointCohomology.twelvePointCohomology_subsingleton
