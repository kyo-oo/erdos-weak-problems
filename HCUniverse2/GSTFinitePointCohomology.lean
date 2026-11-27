/-
Copyright (c) 2026. The HC-Proof owner's GST hypothesis program.
-/
import HCUniverse2.GSTFinitePointAnalytification
import HCUniverse2.GSTGeometricRealizationStage2F

/-!
# THE GENERAL FINITE-POINT COHOMOLOGY

The rational singular cohomology of the general finite-point discrete world,
computed from Mathlib's genuine singular cochain machinery rather than
postulated:

  `RationalSingularCohomology (finitePointAnalytification N) 0 ≃ₗ[ℚ] (Fin N → ℚ)`

with vanishing in every nonzero degree.  The computation runs through the
pinned Mathlib isomorphism `singularChainComplexFunctorIsoOfTotallyDisconnectedSpace`
(identifying the singular chain complex of a totally disconnected space with
`ChainComplex.alternatingConst.obj (∐ fun _ : X ↦ R)`), followed by the
corpus-verified linear-Yoneda dualization of that chain isomorphism, a direct
computation of the resulting alternating dual cochain complex (differential
pattern `0, 𝟙, 0, 𝟙, ...`), and the biproduct/`Pi.single` identification of
the degree-zero term with the function space on the N points.  The arity-12
source lane is the instance `N = 12` — the parity-exactness bookkeeping is
degree arithmetic, uniform in the number of points.

Contract delivered downstream (`GSTFinitePointHodgeData` and beyond):
`finitePointCohomologyIso N : RationalSingularCohomology
(finitePointAnalytification N) 0 ≃ₗ[ℚ] (Fin N → ℚ)` together with
`finitePointCohomology_subsingleton N n hn` — the vanishing of
`RationalSingularCohomology (finitePointAnalytification N) n` for every
`n ≠ 0`.

Binder discipline of the general-N lane (this is file 3, after
`GSTFinitePointWorldCarrier` and `GSTFinitePointAnalytification`): every
declaration that mentions `N` takes `(N : ℕ) [NeZero N]` as its leading
binders.  The empty world `N = 0` is rejected by the lane law.

Steps flagged `-- AUDIT(n):` rest on pinned-Mathlib lemma names that could not
be byte-verified against the local partial checkout (no `Mathlib/CategoryTheory`
or `Mathlib/Algebra/Homology` source available here); they are the designated
repair points if CI reports a name mismatch.  No `sorry`, no fake axioms,
no `native_decide`.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open CategoryTheory
open AlgebraicTopology
open GSTGeometricRealizationStage2F
-- AUDIT(1): the upstream W42-B module follows the campaign module-matching
-- namespace convention, and `(finitePointAnalytification N).space` is assumed
-- definitionally equal to the contract constant `finitePointSpace N` (with
-- `↥(finitePointSpace N) ≡ Fin N` by rfl — the sibling file's
-- `finitePointSpace_coe` receipt).
open GSTFinitePointAnalytification

namespace GSTFinitePointCohomology

variable (N : ℕ) [NeZero N]
-- Lane binder discipline: every declaration below that mentions `N`
-- re-binds `(N : ℕ) [NeZero N]` explicitly at its head (the section
-- variable above is kept per the lane law and shadowed by the explicit
-- binders, so the shipped signatures are fully deterministic).

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

/-! ## §2. The finite-point chain complex and its alternating form -/

/-- The coproduct of N copies of the rational coefficient object. -/
noncomputable def finitePointE (N : ℕ) [NeZero N] : ModuleCat ℚ :=
  ∐ fun _ : ↥(finitePointSpace N) ↦ rationalCoefficient

-- PORT RISK(W42B2-SPACE): the declared type's defeq with the pinned
-- Mathlib iso's own type requires (a) `(finitePointAnalytification N).space`
-- to reduce (default transparency) to the contract constant
-- `finitePointSpace N` — the sibling file assembles the analytification as
-- the structure instance with `space := finitePointSpace N`, so the field
-- projection closes by iota — and (b) the sibling's
-- `TotallyDisconnectedSpace ↥(finitePointSpace N)` instance
-- (`finitePointSpace_totallyDisconnected`) to be in scope for the pinned
-- iso's instance argument (the codomain coproduct then matches `finitePointE
-- N` by delta, exactly as the arity-12 source matched its own `twelvePointE`).
-- Any deviation in the sibling file is the designated CI repair point.
/-- Mathlib's pinned isomorphism: the singular chain complex of the totally
disconnected finite-point space is the alternating constant complex on
`finitePointE N`. -/
noncomputable def finitePointChainIso (N : ℕ) [NeZero N] :
    rationalSingularChains (finitePointAnalytification N) ≅
      ChainComplex.alternatingConst.obj (finitePointE N) :=
  singularChainComplexFunctorIsoOfTotallyDisconnectedSpace (ModuleCat ℚ)
    rationalCoefficient (finitePointSpace N)

/-- The dual alternating cochain complex of the finite-point world. -/
noncomputable def finitePointDualCochains (N : ℕ) [NeZero N] :
    CochainComplex (ModuleCat ℚ) ℕ :=
  (ChainComplex.alternatingConst.obj (finitePointE N)).linearYonedaObj
    ℚ rationalCoefficient

/-- The corpus definition unfolds definitionally to the linear-Yoneda dual. -/
theorem rationalSingularCochains_eq (N : ℕ) [NeZero N] :
    rationalSingularCochains (finitePointAnalytification N) =
      (rationalSingularChains (finitePointAnalytification N)).linearYonedaObj
        ℚ rationalCoefficient := rfl

/-- The dualized chain isomorphism. -/
noncomputable def finitePointDualIso (N : ℕ) [NeZero N] :
    rationalSingularCochains (finitePointAnalytification N) ≅
      finitePointDualCochains N :=
  dualChainIso (finitePointChainIso N)

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
theorem altChain_d_odd (N : ℕ) [NeZero N] (k : ℕ) :
    (ChainComplex.alternatingConst.obj (finitePointE N)).d (2*k+1) (2*k) = 0 := by
  have heven : ¬ Even (2*k+1) := by
    rw [Nat.even_iff]
    omega
  show (if _ : (ComplexShape.down ℕ).Rel (2*k+1) (2*k) then
      if _ : Even (2*k+1) then (𝟙 (finitePointE N))
        else (0 : finitePointE N ⟶ finitePointE N)
      else 0) = 0
  -- WAVE 17 (run-16 errors at :169/:171): split_ifs bound `hi` in a different
  -- subgoal than the bullet that used it; the deterministic dite rewrites
  -- close the parity ite without any case-split bookkeeping.
  rw [dif_pos (show (ComplexShape.down ℕ).Rel (2*k+1) (2*k) from rfl), dif_neg heven]

/-- The alternating constant complex has `d (2*k+2) (2*k+1) = 𝟙`.
-- WAVE 16: the RHS is stated at the projected term (the bare
-- `𝟙 (finitePointE N)` fails the equation's implicit-transparency
-- typecheck — run-15 error at :166 — the X-projection through the functor
-- is semireducible); the body mirrors `altChain_d_odd`'s direct ite
-- route. -/
theorem altChain_d_even (N : ℕ) [NeZero N] (k : ℕ) :
    (ChainComplex.alternatingConst.obj (finitePointE N)).d (2*k+2) (2*k+1) =
      (𝟙 (finitePointE N) :
        (ChainComplex.alternatingConst.obj (finitePointE N)).X (2*k+2) ⟶
        (ChainComplex.alternatingConst.obj (finitePointE N)).X (2*k+1)) := by
  have heven : Even (2*k+2) := ⟨k+1, by omega⟩
  -- WAVE 17 (run-16 error at :218 downstream): the RHS is ascribed at the
  -- SLOT shape (X (2*k+2) ⟶ X (2*k+1)) so that `rw` transports it into the
  -- `Linear.leftComp` slot type-correctly at instances transparency; the
  -- endomorphism-shaped `𝟙 (X (2*k+2))` made the transported goal ill-typed.
  show (if _ : (ComplexShape.down ℕ).Rel (2*k+2) (2*k+1) then
      if _ : Even (2*k+2) then (𝟙 (finitePointE N))
        else (0 : finitePointE N ⟶ finitePointE N)
      else 0) =
    (𝟙 (finitePointE N) :
      (ChainComplex.alternatingConst.obj (finitePointE N)).X (2*k+2) ⟶
      (ChainComplex.alternatingConst.obj (finitePointE N)).X (2*k+1))
  rw [dif_pos (show (ComplexShape.down ℕ).Rel (2*k+2) (2*k+1) from rfl), dif_pos heven]

/-- The dual differential on even indices is zero.
-- AUDIT(3): pinned `linearYonedaObj_d` simps lemma, `Linear.leftComp_apply`,
-- and module hom extensionality. -/
theorem dualCochains_d_even (N : ℕ) [NeZero N] (k : ℕ) :
    (finitePointDualCochains N).d (2*k) (2*k+1) = 0 := by
  -- WAVE 19 (run-18 error at :215): `ModuleCat.Hom.ext` abstracts the PRIMED
  -- field `hom'` (ModuleCat/Basic.lean:91-95) while `ModuleCat.hom_ofHom` /
  -- `hom_zero` are stated through the UNPRIMED alias `Hom.hom`
  -- (ModuleCat/Basic.lean:114-127) — a non-reducible ConcreteCategory
  -- projection; the semi-match it gets at instances transparency produces an
  -- ill-typed motive (the of ℚ-spelling vs finitePointDualCochains.X-spelling
  -- clash).  The route is abandoned: the zero is transported INSIDE ofHom at
  -- the LinearMap level (ext + leftComp_apply, mirroring the green hid below;
  -- zero_comp and LinearMap.zero_apply are default simp lemmas at the pin),
  -- then `ModuleCat.ofHom_zero` (ModuleCat/Basic.lean:390, an rfl-lemma)
  -- closes by exact at default transparency — the same dual.X-defeq the
  -- hd-have's linearYonedaObj_d exact already exercised.
  have hd : (finitePointDualCochains N).d (2*k) (2*k+1) =
      ModuleCat.ofHom (Linear.leftComp ℚ rationalCoefficient
        ((ChainComplex.alternatingConst.obj (finitePointE N)).d (2*k+1) (2*k))) := by
    unfold finitePointDualCochains
    exact ChainComplex.linearYonedaObj_d _ _ _ _ _
  rw [hd, altChain_d_odd N k]
  have h0 : Linear.leftComp ℚ rationalCoefficient
      (0 : (ChainComplex.alternatingConst.obj (finitePointE N)).X (2*k+1) ⟶
       (ChainComplex.alternatingConst.obj (finitePointE N)).X (2*k)) = 0 := by
    ext g
    simp [Linear.leftComp_apply, CategoryTheory.Limits.zero_comp,
      LinearMap.zero_apply]
  rw [h0]
  exact ModuleCat.ofHom_zero

/-- The dual differential on odd indices is the identity.
-- AUDIT(3): pinned `linearYonedaObj_d` simps lemma, `Linear.leftComp_apply`,
-- and module hom extensionality. -/
theorem dualCochains_d_odd (N : ℕ) [NeZero N] (k : ℕ) :
    (finitePointDualCochains N).d (2*k+1) (2*k+2) =
      𝟙 ((finitePointDualCochains N).X (2*k+1)) := by
  -- WAVE 19 (run-18 error at :241): the same `.hom'`-vs-`.hom` alias mismatch
  -- as the even case — `ModuleCat.hom_ofHom` / `hom_id` can never fire
  -- cleanly on a `.hom'`-goal, so Hom.ext is abandoned.  The green
  -- self-contained leftComp-id have is rewritten at the MORPHISM level; its
  -- only defeq burden (X (2*k+1) ≡ X (2*k+2) through alternatingConst's
  -- constant X-field, AlternatingConst.lean:58) is the one the green
  -- `rw [altChain_d_even N k]` motive already discharged at run 18, and
  -- `ModuleCat.ofHom_id` (ModuleCat/Basic.lean:176, an rfl-lemma) closes by
  -- exact at default transparency.
  have hd : (finitePointDualCochains N).d (2*k+1) (2*k+2) =
      ModuleCat.ofHom (Linear.leftComp ℚ rationalCoefficient
        ((ChainComplex.alternatingConst.obj (finitePointE N)).d (2*k+2) (2*k+1))) := by
    unfold finitePointDualCochains
    exact ChainComplex.linearYonedaObj_d _ _ _ _ _
  rw [hd, altChain_d_even N k]
  -- WAVE 20 (run-19 error at :256 — the sole survivor, 7-for-8 green):
  -- `rw [hid]` died because hid's `leftComp` implicit objects elaborated
  -- at the BARE {finitePointE N, finitePointE N} spelling (the 𝟙's own
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
      (𝟙 (finitePointE N) :
        (ChainComplex.alternatingConst.obj (finitePointE N)).X (2*k+2) ⟶
        (ChainComplex.alternatingConst.obj (finitePointE N)).X (2*k+1)) =
      LinearMap.id := by
    ext g
    simp [Linear.leftComp_apply, Category.id_comp]
  exact (congrArg ModuleCat.ofHom hid).trans ModuleCat.ofHom_id

/-- Degree zero differential of the dual complex. -/
theorem dualCochains_d_zero_one (N : ℕ) [NeZero N] :
    (finitePointDualCochains N).d 0 1 = 0 :=
  dualCochains_d_even N 0

/-! ## §4. The zeroth homology of the dual alternating complex -/

-- AUDIT(4): cochain shape facts for `up ℕ` at index zero.
theorem upNext_zero : (ComplexShape.up ℕ).next 0 = 1 := by
  exact CochainComplex.next ℕ 0

theorem upPrev_zero : (ComplexShape.up ℕ).prev 0 = 0 := by
  exact CochainComplex.prev_nat_zero

theorem upNotRel_zero_zero : ¬ (ComplexShape.up ℕ).Rel 0 0 := by
  simp [ComplexShape.up_Rel]

/-- The shape zero differential. -/
theorem dualCochains_d_zero_zero (N : ℕ) [NeZero N] :
    (finitePointDualCochains N).d 0 0 = 0 :=
  (finitePointDualCochains N).shape 0 0 upNotRel_zero_zero

/-- The zeroth homology of the dual alternating complex is its degree-zero
term. -- AUDIT(5) (wave 15): `isoHomologyι` / `pOpcyclesIso` take FOUR
explicit index/proof arguments at the pin (ShortComplex/HomologicalComplex.lean:534/:581:
`isoHomologyι (i) (j) (hj : c.next i = j) (h : K.d i j = 0) [K.HasHomology i]`,
`pOpcyclesIso (i) (j) (hi : c.prev j = i) (h : K.d i j = 0) [K.HasHomology j]`;
in-file usage `K.isoHomologyι i j hj h` at :563/:590) — the two-index call
`isoHomologyι 0 1 upNext_zero (dualCochains_d_zero_one N)` composes with
`(pOpcyclesIso 0 0 upPrev_zero (dualCochains_d_zero_zero N)).symm`:
`homology 0 ≅ opcycles 0 ≪≫ opcycles 0 ≅ X 0`. -/
noncomputable def finitePointHomologyZero (N : ℕ) [NeZero N] :
    (finitePointDualCochains N).homology 0 ≅ (finitePointDualCochains N).X 0 :=
  (finitePointDualCochains N).isoHomologyι 0 1 upNext_zero
      (dualCochains_d_zero_one N) ≪≫
    ((finitePointDualCochains N).pOpcyclesIso 0 0 upPrev_zero
      (dualCochains_d_zero_zero N)).symm

/-! ## §5. The object-level identification with `Fin N → ℚ` -/

-- PORT NOTE(n12): the source's `Fin 12`-indexed biproduct/Pi identification
-- is type-mapped to `Fin N`; no re-derivation was required — the lemma pair
-- is uniform in the index type (the arity-12 source's instances ride the
-- unconditional `Fintype (Fin N)` / `DecidableEq (Fin N)`).
-- PORT RISK(W42B2-COE): the composite's domain must be defeq (default
-- transparency) to `finitePointE N` — the coproduct over
-- `↥(finitePointSpace N)` against the biproduct over `Fin N` — through the
-- sibling's rfl receipt `finitePointSpace_coe N :
-- ↥(finitePointSpace N) = Fin N` (exactly the source's
-- `↥twelvePointSpace ≡ Fin 12`); any carrier-side redefinition of
-- `finitePointSpace` is the designated CI repair point.
/-- The coproduct of N rational coefficients is the function space.
-- AUDIT(6): `biproduct.isoCoproduct` / `ModuleCat.biproductIsoPi` names; also
-- relies on the upstream defeq `↥(finitePointSpace N) ≡ Fin N`. -/
noncomputable def finitePointEIso (N : ℕ) [NeZero N] :
    finitePointE N ≅ ModuleCat.of ℚ (Fin N → ℚ) :=
  (Limits.biproduct.isoCoproduct
      (fun _ : Fin N ↦ ModuleCat.of ℚ ℚ)).symm ≪≫
    ModuleCat.biproductIsoPi (fun _ : Fin N ↦ ModuleCat.of ℚ ℚ)

-- PORT NOTE(n12): the source name `fin12DualEquiv` encodes the arity-12
-- index type and is renamed `finNDualEquiv` under the type map (the ONE
-- name deviation beyond the mechanical `twelvePoint ↦ finitePoint` map);
-- the body is the source's verbatim under `Fin 12 ↦ Fin N` — the
-- `Pi.single` coordinate duality is uniform in N (decidability through
-- `Fin.instDecidableEqFin`, no 12-arithmetic anywhere in the source body).
/-- The coordinate identification of the dual of `Fin N → ℚ`:
a functional is its list of values on the standard single-point vectors.
-- WAVE 16 (run-15 error at :250): the invFun's anonymous `⟨...⟩` constructor
-- does not elaborate against the post-refactor LinearMap structure (which
-- extends AddHom); the named-field structure-instance syntax is the
corpus-standard idiom. -/
noncomputable def finNDualEquiv (N : ℕ) [NeZero N] :
    ((Fin N → ℚ) →ₗ[ℚ] ℚ) ≃ₗ[ℚ] (Fin N → ℚ) where
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
    -- extensionality (introducing `x : Fin N`, an index); the deterministic
    -- `LinearMap.ext` keeps `x` a vector so the never-tested calc runs.
    refine LinearMap.ext (fun x => ?_)
    have hx : x = ∑ i, x i • (Pi.single i 1 : Fin N → ℚ) := by
      funext j
      simp [Finset.sum_apply, Pi.single_apply, Pi.smul_apply,
        smul_eq_mul, mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq']
    show ∑ i, φ (Pi.single i 1 : Fin N → ℚ) * x i = φ x
    calc ∑ i, φ (Pi.single i 1 : Fin N → ℚ) * x i
        = ∑ i, x i * φ (Pi.single i 1 : Fin N → ℚ) :=
            Finset.sum_congr rfl (fun i _ => mul_comm _ _)
      _ = ∑ i, φ (x i • (Pi.single i 1 : Fin N → ℚ)) := by
            simp [map_smul, smul_eq_mul]
      _ = φ (∑ i, x i • (Pi.single i 1 : Fin N → ℚ)) :=
            (map_sum φ
              (fun i => x i • (Pi.single i 1 : Fin N → ℚ))
              Finset.univ).symm
      _ = φ x := (congrArg φ hx).symm
  right_inv c := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply, mul_one, mul_zero, mul_ite,
      Finset.sum_ite_eq, Finset.sum_ite_eq']

-- PORT NOTE(n12): the source's `Fin 12` hom-type is type-mapped to `Fin N`;
-- both triangle fields remain `rfl` (structure eta is N-uniform).
/-- The bridge from the `ModuleCat` hom-type to the linear map type: the
underlying `Hom.hom`, linear in the hom-module structure, with the inverse
`ModuleCat.ofHom`. -- WAVE 16 (run-15 error at :289): the homCongr's
codomain is the `ModuleCat.Hom` STRUCTURE type, not the `LinearMap` type —
`ModuleCat.Hom` is a one-field wrapper (ModuleCat/Basic.lean:94) — so
`finNDualEquiv` cannot compose with it directly; this bridge (built on
Mathlib's own `ModuleCat.homEquiv`, ModuleCat/Basic.lean:195) closes the
commuting square. -/
noncomputable def homToLinearMap (N : ℕ) [NeZero N] :
    (ModuleCat.of ℚ (Fin N → ℚ) ⟶ rationalCoefficient) ≃ₗ[ℚ]
      ((Fin N → ℚ) →ₗ[ℚ] ℚ) where
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
`finitePointE N`, as the function space `Fin N → ℚ`. -- AUDIT(8):
`Linear.homCongr`, `LinearEquiv.toModuleIso`, and the defeq
`finitePointDualCochains.X 0 ≡ ModuleCat.of ℚ (E ⟶ R)`. -/
noncomputable def finitePointXZeroIso (N : ℕ) [NeZero N] :
    (finitePointDualCochains N).X 0 ≅ ModuleCat.of ℚ (Fin N → ℚ) :=
  LinearEquiv.toModuleIso
    ((Linear.homCongr ℚ (finitePointEIso N)
        (Iso.refl rationalCoefficient)).trans
      ((homToLinearMap N).trans (finNDualEquiv N)))

/-! ## §6. Assembly: the degree-zero rational cohomology -/

-- PORT NOTE(n12): the codomain `Fin 12 → ℚ` of the source's assembly pair
-- is type-mapped to `Fin N → ℚ` — the only 12-content of these two
-- declarations (no proof bodies; the composite threads the explicit `N`).
/-- The full module-level isomorphism. -/
noncomputable def finitePointCohomologyZeroObj (N : ℕ) [NeZero N] :
    rationalSingularCohomologyObj (finitePointAnalytification N) 0 ≅
      ModuleCat.of ℚ (Fin N → ℚ) :=
  homologyIsoOfIso (finitePointDualIso N) 0 ≪≫
    finitePointHomologyZero N ≪≫ finitePointXZeroIso N

/-- **THE TARGET**: the zeroth rational singular cohomology of the
finite-point world is the rational function space on the N points.
-- AUDIT(9): `Iso.toLinearEquiv` name. -/
noncomputable def finitePointCohomologyIso (N : ℕ) [NeZero N] :
    RationalSingularCohomology (finitePointAnalytification N) 0 ≃ₗ[ℚ]
      (Fin N → ℚ) :=
  (finitePointCohomologyZeroObj N).toLinearEquiv

/-! ## §7. Vanishing in nonzero degree -/

/-- Exactness of the dual alternating short complex at an odd index.
-- WAVE 16 (run-15 errors at :323/:339): the `shortComplexFunctor_obj_f/g`
simps lemmas do not fire on the bare `sc` abbrev (the wave-7 corpus idiom:
the sc's f/g fields are DEFEQ on the d-components; state them directly
through a `show`, then close with the pinned `ModuleCat.hom_zero` /
`ModuleCat.hom_id` simp lemmas — both used by Mathlib's own
`ModuleCat.subsingleton_of_isZero` proof at ModuleCat/Basic.lean:379). -/
theorem dualSc_exact_odd (N : ℕ) [NeZero N] (k : ℕ) :
    ShortComplex.Exact ((finitePointDualCochains N).sc (2*k+1)) := by
  -- WAVE 17 (run-16 error at :367): `(sc i).f = d (prev i) i` is true but NOT
  -- definitional (prev/next are choice-encoded dite's); the sc' route
  -- transports the short complex to the explicit-index form where the
  -- pinned `shortComplexFunctor'_obj_f/g` simps lemmas fire.
  have hprev : (ComplexShape.up ℕ).prev (2*k+1) = 2*k :=
    CochainComplex.prev_nat_succ (2*k)
  have hnext : (ComplexShape.up ℕ).next (2*k+1) = 2*k+2 := by
    rw [CochainComplex.next]
    omega
  have hsc : (finitePointDualCochains N).sc (2*k+1) =
      (finitePointDualCochains N).sc' (2*k) (2*k+1) (2*k+2) := by
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
  have hf : ((finitePointDualCochains N).sc' (2*k) (2*k+1) (2*k+2)).f.hom = 0 := by
    rw [HomologicalComplex.shortComplexFunctor'_obj_f, dualCochains_d_even N k]
    exact ModuleCat.hom_zero
  have hg : ((finitePointDualCochains N).sc' (2*k) (2*k+1) (2*k+2)).g.hom =
      LinearMap.id := by
    rw [HomologicalComplex.shortComplexFunctor'_obj_g, dualCochains_d_odd N k]
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
theorem dualSc_exact_even (N : ℕ) [NeZero N] (k : ℕ) :
    ShortComplex.Exact ((finitePointDualCochains N).sc (2*k+2)) := by
  -- WAVE 17 (run-16 error at :378): the same sc' route as
  -- dualSc_exact_odd (the author's show had the indices one degree down —
  -- the pinned sc is X (prev i) ⟶ X i ⟶ X (next i)).
  have hprev : (ComplexShape.up ℕ).prev (2*k+2) = 2*k+1 :=
    CochainComplex.prev_nat_succ (2*k+1)
  have hnext : (ComplexShape.up ℕ).next (2*k+2) = 2*k+3 := by
    rw [CochainComplex.next]
    omega
  have hsc : (finitePointDualCochains N).sc (2*k+2) =
      (finitePointDualCochains N).sc' (2*k+1) (2*k+2) (2*k+3) := by
    unfold HomologicalComplex.sc HomologicalComplex.sc'
      HomologicalComplex.shortComplexFunctor
    rw [hprev, hnext]
  rw [hsc, ShortComplex.moduleCat_exact_iff_range_eq_ker]
  -- WAVE 19 (run-18 errors at :452/:457): exact-closers at default
  -- transparency (same root cause as dualSc_exact_odd's run-18 failures);
  -- the g-fact keeps the 2*k+2-spelled show-restatement of
  -- dualCochains_d_even (k+1) (the 2*(k+1) Nat-mul spelling is not
  -- syntactic — run-17 error at :432).
  have hf : ((finitePointDualCochains N).sc' (2*k+1) (2*k+2) (2*k+3)).f.hom =
      LinearMap.id := by
    rw [HomologicalComplex.shortComplexFunctor'_obj_f, dualCochains_d_odd N k]
    exact ModuleCat.hom_id
  have hg : ((finitePointDualCochains N).sc' (2*k+1) (2*k+2) (2*k+3)).g.hom = 0 := by
    rw [HomologicalComplex.shortComplexFunctor'_obj_g,
      show (finitePointDualCochains N).d (2*k+2) (2*k+3) = 0 from
        dualCochains_d_even N (k+1)]
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
theorem finitePointDualCochains_exactAt (N : ℕ) [NeZero N] (n : ℕ) (hn : n ≠ 0) :
    (finitePointDualCochains N).ExactAt n := by
  show ShortComplex.Exact ((finitePointDualCochains N).sc n)
  rcases parity_split n hn with ⟨k, hk⟩ | ⟨k, hk⟩
  · rw [hk]; exact dualSc_exact_odd N k
  · rw [hk]; exact dualSc_exact_even N k

/-- The dual alternating cohomology objects vanish in positive degree.
`ExactAt n` is definitionally `(C.sc n).Exact` in pinned
Mathlib (it is consumed there via `.of_iso` / `.isZero_homology` in
`Mathlib/AlgebraicTopology/SingularHomology/Basic.lean`).
-- WAVE 16 (run-15 errors at :360/:368): `IsZero` is
`CategoryTheory.Limits.IsZero` at the pin
(Limits/Shapes/ZeroObjects.lean:44) — the unqualified name does not
resolve under `open CategoryTheory` alone. -/
theorem finitePointDualCochomology_isZero (N : ℕ) [NeZero N] (n : ℕ) (hn : n ≠ 0) :
    CategoryTheory.Limits.IsZero ((finitePointDualCochains N).homology n) :=
  (finitePointDualCochains_exactAt N n hn).isZero_homology

/-- **THE VANISHING TARGET**: rational singular cohomology of the
finite-point world is trivial in every nonzero degree.
-- AUDIT(12): `IsZero.eq`. -/
theorem finitePointCohomology_subsingleton (N : ℕ) [NeZero N] (n : ℕ) (hn : n ≠ 0) :
    Subsingleton (RationalSingularCohomology (finitePointAnalytification N) n) := by
  let e := (homologyIsoOfIso (finitePointDualIso N) n).toLinearEquiv
  have hD : CategoryTheory.Limits.IsZero ((finitePointDualCochains N).homology n) :=
    finitePointDualCochomology_isZero N n hn
  refine ⟨fun a b => ?_⟩
  -- WAVE 17 (run-16 error at :429): the calc's middle step could not
  -- synthesize `Trans Eq Eq ?m` (the `congr 1` block poisoned the step's
  -- type); the explicit Eq.trans chain is deterministic.
  have key : e a = e b := by
    haveI : Subsingleton ((finitePointDualCochains N).homology n) :=
      ModuleCat.subsingleton_of_isZero hD
    exact Subsingleton.elim (e a) (e b)
  exact (e.symm_apply_apply a).symm.trans
    ((congrArg e.symm key).trans (e.symm_apply_apply b))

end GSTFinitePointCohomology

/-! ## Receipts -/

#check GSTFinitePointCohomology.dualChainHom
#check GSTFinitePointCohomology.dualChainIso
#check GSTFinitePointCohomology.homologyIsoOfIso
#check GSTFinitePointCohomology.finitePointE
#check GSTFinitePointCohomology.finitePointChainIso
#check GSTFinitePointCohomology.finitePointDualCochains
#check GSTFinitePointCohomology.rationalSingularCochains_eq
#check GSTFinitePointCohomology.finitePointDualIso
#check GSTFinitePointCohomology.altChain_d_odd
#check GSTFinitePointCohomology.altChain_d_even
#check GSTFinitePointCohomology.dualCochains_d_even
#check GSTFinitePointCohomology.dualCochains_d_odd
#check GSTFinitePointCohomology.dualCochains_d_zero_one
#check GSTFinitePointCohomology.upNext_zero
#check GSTFinitePointCohomology.upPrev_zero
#check GSTFinitePointCohomology.upNotRel_zero_zero
#check GSTFinitePointCohomology.dualCochains_d_zero_zero
#check GSTFinitePointCohomology.finitePointHomologyZero
#check GSTFinitePointCohomology.finitePointEIso
#check GSTFinitePointCohomology.finNDualEquiv
#check GSTFinitePointCohomology.homToLinearMap
#check GSTFinitePointCohomology.finitePointXZeroIso
#check GSTFinitePointCohomology.finitePointCohomologyZeroObj
#check GSTFinitePointCohomology.finitePointCohomologyIso
#check GSTFinitePointCohomology.dualSc_exact_odd
#check GSTFinitePointCohomology.dualSc_exact_even
#check GSTFinitePointCohomology.parity_split
#check GSTFinitePointCohomology.finitePointDualCochains_exactAt
#check GSTFinitePointCohomology.finitePointDualCochomology_isZero
#check GSTFinitePointCohomology.finitePointCohomology_subsingleton

#print axioms GSTFinitePointCohomology.finitePointCohomologyIso
#print axioms GSTFinitePointCohomology.finitePointCohomology_subsingleton

/-! DRAFT STATUS (W42-B2, file 3 of the general-N finite-point lane):
* Source: the arity-12 cohomology module of the native-point world lane
  (`GSTTwelvePointCohomology.lean`, 561 lines; CI-green at run 20 —
  43903976892, both receipts [propext, Classical.choice, Quot.sound]),
  ported under the wave-42 lane law.
* Declarations ported: 30 / 30 (14 noncomputable defs, 16 theorems), in
  source order.  Rename map `twelvePoint ↦ finitePoint` applied to 12 names
  (`finitePointE`, `finitePointChainIso`, `finitePointDualCochains`,
  `finitePointDualIso`, `finitePointHomologyZero`, `finitePointEIso`,
  `finitePointXZeroIso`, `finitePointCohomologyZeroObj`,
  `finitePointCohomologyIso`, `finitePointDualCochains_exactAt`,
  `finitePointDualCochomology_isZero`, `finitePointCohomology_subsingleton`);
  17 names keep their source names inside the renamed namespace, plus ONE
  arity-flavored rename `fin12DualEquiv ↦ finNDualEquiv` (the source name
  encodes the `Fin 12` index type — PORT NOTE(n12) at the site).
* Binder discipline: every N-mentioning declaration (23 of the 30) takes
  `(N : ℕ) [NeZero N]` as leading binders; the 7 arity-agnostic ones
  (`dualChainHom`, `dualChainIso`, `homologyIsoOfIso`, `upNext_zero`,
  `upPrev_zero`, `upNotRel_zero_zero`, `parity_split`) keep their exact
  source signatures; the `variable (N : ℕ) [NeZero N]` line at namespace
  top is kept per the lane law and shadowed by the explicit binders, so
  the exported signatures are deterministic.
* PORT NOTE(n12): 4 in-file sites flagged (`finitePointEIso`,
  `finNDualEquiv`, `homToLinearMap`, the §6 assembly pair); re-derivations
  required: NONE — the source's only 12-content was the fixed index type
  `Fin 12` (§5-§6 types, the fin12DualEquiv name and its `Pi.single`
  ascriptions) and prose; the whole parity-exactness block (§3, §4, §7) is
  degree arithmetic, already N-generic (no `by decide`, no `norm_num` on
  12, no 12-literals in any proof term).  All bodies are verbatim modulo
  the type map `Fin 12 ↦ Fin N`, the `twelvePoint* ↦ (finitePoint* N)`
  application map with the mandatory parentheses at `(finitePointE N)`,
  `(finitePointDualCochains N)`, `↥(finitePointSpace N)`, and the explicit
  N-threading at application sites (`altChain_d_odd N k`, etc.).
* PORT NOTE(rename-map): one exemption — `fin12DualEquiv ↦ finNDualEquiv`
  (arity-encoded name, documented above); everything else is the mechanical
  map, `TwelvePoint ↦ FinitePoint` on the namespace included.
* PORT RISK(W42B2-SPACE) at `finitePointChainIso`: the declared type's
  defeq with the pinned Mathlib iso requires `(finitePointAnalytification
  N).space` to reduce (default transparency) to `finitePointSpace N` (the
  sibling's `space := finitePointSpace N` structure-literal field) plus the
  sibling's `TotallyDisconnectedSpace ↥(finitePointSpace N)` instance —
  the exact twin of the source's `twelvePointAnalytification.space` /
  `twelvePointSpace` contract.
* PORT RISK(W42B2-COE) at `finitePointEIso`: the biproduct-vs-coproduct
  index defeq `↥(finitePointSpace N) ≡ Fin N` at default transparency (the
  sibling's rfl receipt `finitePointSpace_coe`), the exact twin of the
  source's `↥twelvePointSpace ≡ Fin 12`.
* Static verification: no `twelvePoint`/`TwelvePoint`/`GSTTwelvePoint`/
  `Fin 12`/`fin12` survives in the ported body (grep-checked over
  everything above this DRAFT STATUS block; the source-name mentions
  inside the PORT NOTEs and this block are the documentation; the in-file
  `AUDIT(n)` labels are audit indices, not arity content); external
  identifiers are exactly the source's CI-green Mathlib set plus the lane
  contract names from the sibling file (`finitePointSpace`,
  `finitePointAnalytification`, and the two receipts
  `finitePointSpace_coe` / `finitePointSpace_totallyDisconnected` cited in
  the port notes); parenthesis/bracket balance depth 0
  (docstring-excluded).  NOT COMPILED (no local Lean by repo law) — the
  two PORT RISK sites above are the designated CI repair points.
-/
end -- noncomputable section
