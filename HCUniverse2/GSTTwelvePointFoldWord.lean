import HCUniverse2.GSTTwelvePointHodgeData
import HCUniverse2.GSTTwelvePointAnalytification
import HCUniverse2.GSTClassicalHodgeRealizedClosedCorrespondenceAlgebra
import HCUniverse2.GSTClassicalHodgeFiniteClosedCorrespondence
import HCUniverse2.GSTClassicalHodgeFiniteClosedCorrespondenceOperator
import HCUniverse2.GSTNativeCodimensionCyclePresentation
import HCUniverse2.GSTClassicalHodgeProjectiveSelfCorrespondences
import HCUniverse2.GSTClassicalHodgeProjectivePointTransport
import Mathlib

/-!
# GST TWELVE-POINT — THE OWNER'S FOLD AS A GENUINE REALIZED CORRESPONDENCE WORD

This module lands Part 3 of the twelve-point native geometric world record
(`research/records/2026-11-14-gst-twelve-point-native-geometric-world.md`):
the fold matrix `T = U + J + M` is realized on the first genuine world
`(V₀, H₀)` as a `RealizedCorrespondenceWord` of 26 weighted point-pair
correspondences, and the word's cohomology operator is proved to BE the fold
matrix under the H⁰ cohomology iso.

Each letter is the closed point-pair subscheme `Spec ℂ ⟶ X ×_ℂ X` with left
leg the `c`-th point and right leg the `r`-th point:

* the ring map is the evaluation composite `ℂ¹² ⊗_ℂ ℂ¹² →ₐ[ℂ] ℂ`,
  `a ⊗ b ↦ (a c) * (b r)`, surjective, hence a closed immersion by
  `IsClosedImmersion.spec_of_surjective` composed with the `pullbackSpecIso`
  inverse;
* the left fibers are singletons or empty (`Spec ℂ` has one point);
* the right leg's residue degree at the unique carrier point is `1`
  (the residue-field extension is trivial, proved through the open-immersion
  instance for the evaluation `Spec` map).

The realization equation on the twelve point classes is the matrix column:
`matrixUnitOp r c` sends `e i ↦ (if c = i then e r else 0)`, and the word
operator sends `e c ↦ Σ_r Twave r c • e r`.  The full operator theorem uses
the point-class decomposition of `H⁰` (every class is the sum of its
coordinates times point classes).

External lemma names marked `AUDIT-n` are the author-wave uncertainty points
(this module is written before its unwritten upstream sibling modules are
compiled; the CI lane owns the kernel check).
-/

set_option maxHeartbeats 70000000
set_option maxRecDepth 1000000

noncomputable section

open CategoryTheory
open AlgebraicGeometry

-- W2-A (W1-B §15): the TYPE-level scoped tensor notation `M ⊗[R] N`
-- (LinearAlgebra/TensorProduct/Defs.lean:88, `scoped[TensorProduct]`) is OFF
-- without this open — the run-26 :105:17/:132:22 parse errors.  The
-- element-level `⊗ₜ[R]` (Defs.lean:114) is global and needs nothing.
open scoped TensorProduct
namespace GSTTwelvePointFoldWord

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTNativeCodimensionCyclePresentation
open GSTClassicalHodgeProjectiveSelfCorrespondences
open GSTClassicalHodgeFiniteClosedCorrespondence
open GSTClassicalHodgeFiniteClosedCorrespondence.FiniteClosedCorrespondence
open GSTClassicalHodgeFiniteClosedCorrespondenceOperator
open GSTClassicalHodgeProjectivePointTransport
open GSTClassicalHodgeRealizedClosedCorrespondenceAlgebra
open GSTClassicalHodgeFiberedCosmology
open GSTTwelvePointWorldCarrier
open GSTTwelvePointCohomology
open GSTTwelvePointHodgeData
open GSTTwelvePointAnalytification

/-! ## The twelve points and their classes

The carrier module supplies `twelvePointWorld : SmoothProjectiveComplexScheme`
with `twelvePointWorld.X = Spec (.of (Fin 12 → ℂ))` and the point
classification `twelvePointEquiv : Fin 12 ≃ CodimensionPoint twelvePointWorld.X 0`
(the primes `ker (eval i)`); the Hodge-data module supplies
`twelvePointHodgeData`, `zeroCycleClass`, `zeroCycleClass_point`,
`zeroFiber_eq_top` and `twelvePointCohomologyIso`.
-/

/-- The `i`-th twelve-point as a genuine codimension-0 point. -/
abbrev twelvePointPt (i : Fin 12) : CodimensionPoint twelvePointWorld.X 0 :=
  ⟨(twelvePointEquiv i).1, (twelvePointEquiv i).2⟩

/-- The unit point cycle of the `i`-th twelve-point. -/
abbrev twelvePointPtCycle (i : Fin 12) : codimensionCycles twelvePointWorld.X 0 :=
  codimensionPointCycle twelvePointWorld.X 0 (twelvePointPt i)

/-- The rational point class of the `i`-th twelve-point. -/
abbrev twelvePointPtClass (i : Fin 12) :
    RationalSingularCohomology twelvePointHodgeData.analytification 0 :=
  twelvePointHodgeData.cycleClass 0 (twelvePointPtCycle i)

/-- **AUDIT-1 (carrier bridge).** The `i`-th twelve-point IS the prime
`ker (eval i)` of `ℂ¹²`.  Both sides are `comap (eval i)` of a point of the
one-point space `Spec ℂ`: the left of the scheme-level `default`, the right of
the `default` baked into the carrier's `Equiv.sigmaUnique`.  The two `default`s
ride different `Unique (PrimeSpectrum ℂ)` instance paths (the scheme-level
instance of AlgebraicGeometry/Scheme.lean:627 resolves through `Field ℂ`, the
`sigmaUnique` binder through the artinian-krull-dim-zero-local chain visible to
`import Mathlib`), so the equation is closed by `Subsingleton.elim` on the
one-point `Spec ℂ` — never by a bare `rfl`. -/
theorem comap_evalRingHom_default (i : Fin 12) :
    PrimeSpectrum.comap (Pi.evalRingHom (fun _ : Fin 12 => ℂ) i)
      (default : Spec (CommRingCat.of ℂ)) = (twelvePointEquiv i).1 := by
  -- `Spec ℂ` is a one-point space: any two of its points are equal
  -- (`Unique.instSubsingleton`, Logic/Unique.lean:119, off any
  -- `Unique (PrimeSpectrum ℂ)` instance).
  have hdfl : ∀ x y : PrimeSpectrum ℂ, x = y :=
    fun _ _ => Subsingleton.elim _ _
  -- WAVE 32 (run-31 :146 receipt): the rewrite-chain family is DEAD — the
  -- no-re-roll law fires.  Three waves died on successive seams of the same
  -- mechanism (run-29: the LHS Spec-default at implicit; run-30: the show's
  -- default-instance mismatch; run-31: the goal-level type parameter forced
  -- to the PrimeSpectrum spelling, making the carrier-typed equiv chain
  -- ill-typed at implicit — the full-error receipt).  THE ACTUAL TRUTH: any
  -- equation mixing carrier-spelled and PrimeSpectrum-spelled terms is
  -- ill-typed at implicit transparency, so NO rewrite can ever cross the
  -- seam — the crossing must happen in TERM MODE at default transparency.
  -- THE MECHANISM: the equiv-point's comap-nature is DEFINITIONAL — the
  -- equiv was BUILT from the sigmaToPi-comap factorization
  -- (WorldCarrier:709: (sigmaUnique.symm.trans sigmaToPiHomeo.toEquiv).trans
  -- (subtypeUnivEquiv _).symm), so the bridge equation below is provable by
  -- the definitional iota-chain (rfl) with simp-normalization as the second
  -- shot; the statement's own mixed equation is then closed by ONE term-mode
  -- Eq.trans — the comap-congruence of the one-point Subsingleton composed
  -- with the bridge — no rewrite ever touches the mixed statement, no
  -- motive is ever built, the sigmaUnique section's default and the
  -- statement's default are never instance-compared (Subsingleton kills
  -- them without looking).
  have h1 : (twelvePointEquiv i).1 = PrimeSpectrum.comap
      (Pi.evalRingHom (fun _ : Fin 12 => ℂ) i)
      ((Equiv.sigmaUnique (Fin 12) (fun _ => PrimeSpectrum ℂ)).symm i).2 := by
    first
    | rfl
    | simp only [Equiv.trans_apply, Equiv.sigmaUnique_symm_apply,
        Homeomorph.coe_toEquiv, PrimeSpectrum.sigmaToPiHomeo_apply,
        PrimeSpectrum.sigmaToPi_apply, Equiv.subtypeUnivEquiv_symm_apply]
  exact (congrArg (PrimeSpectrum.comap (Pi.evalRingHom (fun _ : Fin 12 => ℂ) i))
    (hdfl _ _)).trans h1.symm

/-! ## The letter geometry: the point-pair subscheme -/

/-- The evaluation algebra map of the point pair: `a ⊗ b ↦ (a c) * (b r)`. -/
noncomputable def pointPairAlgHom (r c : Fin 12) :
    (Fin 12 → ℂ) ⊗[ℂ] (Fin 12 → ℂ) →ₐ[ℂ] ℂ :=
  (Algebra.TensorProduct.rid ℂ ℂ ℂ).toAlgHom.comp
    (Algebra.TensorProduct.map
      (Pi.evalAlgHom ℂ (fun _ : Fin 12 => ℂ) c)
      (Pi.evalAlgHom ℂ (fun _ : Fin 12 => ℂ) r))

/-- The point-pair ring map is surjective: preimage of `x` is
`Pi.single c x ⊗ₜ 1`. -/
theorem pointPairAlgHom_surjective (r c : Fin 12) :
    Function.Surjective (pointPairAlgHom r c) := by
  intro x
  refine ⟨Pi.single c x ⊗ₜ[ℂ] 1, ?_⟩
  show pointPairAlgHom r c (Pi.single c x ⊗ₜ[ℂ] 1) = x
  -- AUDIT-2 (tensor API): `map_tmul`/`rid_tmul`/`Pi.single_apply` names.
  simp [pointPairAlgHom, Algebra.TensorProduct.map_tmul,
    Algebra.TensorProduct.rid_tmul, Pi.single_apply, mul_one]

/-- The closed point-pair subscheme `Spec ℂ ⟶ X ×_ℂ X` selecting
`(point c, point r)`. -/
noncomputable def pointPairMap (r c : Fin 12) :
    Spec (CommRingCat.of ℂ) ⟶ selfProduct twelvePointWorld :=
  Spec.map (CommRingCat.ofHom (pointPairAlgHom r c).toRingHom) ≫
    (pullbackSpecIso ℂ (Fin 12 → ℂ) (Fin 12 → ℂ)).inv

/-- Ring-hom form of the left leg: evaluate at the column point. -/
theorem pointPair_left_hom (r c : Fin 12) :
    (pointPairAlgHom r c).toRingHom.comp
      (algebraMap (Fin 12 → ℂ)
        ((Fin 12 → ℂ) ⊗[ℂ] (Fin 12 → ℂ))) =
      Pi.evalRingHom (fun _ : Fin 12 => ℂ) c := by
  apply RingHom.ext
  intro a
  show pointPairAlgHom r c
      (algebraMap (Fin 12 → ℂ) ((Fin 12 → ℂ) ⊗[ℂ] (Fin 12 → ℂ)) a) =
    Pi.evalRingHom (fun _ : Fin 12 => ℂ) c a
  have htm : algebraMap (Fin 12 → ℂ) ((Fin 12 → ℂ) ⊗[ℂ] (Fin 12 → ℂ)) a =
      a ⊗ₜ[ℂ] 1 := rfl -- AUDIT-3: left algebra structure on the tensor product
  rw [htm]
  -- AUDIT-2: tensor API names as above; W2-A: `Pi.evalRingHom_apply`
  -- (Algebra/Ring/Pi.lean:170, @[simps!]-generated — pin-verified W1-B §2)
  -- normalizes the show's RHS `↑(eval c) a` to `a c` so the close is
  -- syntactic (no terminal-defeq gamble).
  simp [pointPairAlgHom, Algebra.TensorProduct.map_tmul,
    Algebra.TensorProduct.rid_tmul, Pi.evalAlgHom_apply, Pi.evalRingHom_apply,
    mul_one]

/-- Ring-hom form of the right leg: evaluate at the row point. -/
theorem pointPair_right_hom (r c : Fin 12) :
    (pointPairAlgHom r c).toRingHom.comp
      (Algebra.TensorProduct.includeRight
        (R := ℂ) (A := Fin 12 → ℂ) (B := Fin 12 → ℂ)).toRingHom =
      Pi.evalRingHom (fun _ : Fin 12 => ℂ) r := by
  apply RingHom.ext
  intro a
  show pointPairAlgHom r c
      (Algebra.TensorProduct.includeRight
        (R := ℂ) (A := Fin 12 → ℂ) (B := Fin 12 → ℂ) a) =
    Pi.evalRingHom (fun _ : Fin 12 => ℂ) r a
  have htm : Algebra.TensorProduct.includeRight
      (R := ℂ) (A := Fin 12 → ℂ) (B := Fin 12 → ℂ) a = 1 ⊗ₜ[ℂ] a := rfl -- AUDIT-3
  rw [htm]
  -- AUDIT-2 + W2-A: as the left leg (R1-8); `one_mul` covers the
  -- `rid_tmul` smul `(a r) • 1 → (a r) * 1` spelling.
  simp [pointPairAlgHom, Algebra.TensorProduct.map_tmul,
    Algebra.TensorProduct.rid_tmul, Pi.evalAlgHom_apply, Pi.evalRingHom_apply,
    one_mul]

/-- The left leg of the point pair is evaluation at the column point. -/
theorem pointPair_left (r c : Fin 12) :
    pointPairMap r c ≫ fst twelvePointWorld =
      Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun _ : Fin 12 => ℂ) c)) := by
  -- WAVE 29 (run-28 :228 receipt): the calc's Trans synthesis died on the
  -- continuation geometry (the step-2 LHS at col 5 under the step-1 LHS at
  -- col 8 — the colGe law).  Mechanism switch per the no-re-roll law: the
  -- run-27-green `happ` discipline — ground haves at the goal's own
  -- spelling, each closed by ONE term-mode application, composed by
  -- Eq.trans.  No calc parser anywhere in the chain.
  show (Spec.map (CommRingCat.ofHom (pointPairAlgHom r c).toRingHom) ≫
      (pullbackSpecIso ℂ (Fin 12 → ℂ) (Fin 12 → ℂ)).inv) ≫ fst twelvePointWorld = _
  have h1 : (Spec.map (CommRingCat.ofHom (pointPairAlgHom r c).toRingHom) ≫
        (pullbackSpecIso ℂ (Fin 12 → ℂ) (Fin 12 → ℂ)).inv) ≫ fst twelvePointWorld =
      Spec.map (CommRingCat.ofHom (pointPairAlgHom r c).toRingHom) ≫
        ((pullbackSpecIso ℂ (Fin 12 → ℂ) (Fin 12 → ℂ)).inv ≫ fst twelvePointWorld) :=
    CategoryTheory.Category.assoc _ _ _
  have h2 : Spec.map (CommRingCat.ofHom (pointPairAlgHom r c).toRingHom) ≫
        ((pullbackSpecIso ℂ (Fin 12 → ℂ) (Fin 12 → ℂ)).inv ≫ fst twelvePointWorld) =
      Spec.map (CommRingCat.ofHom (pointPairAlgHom r c).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (Fin 12 → ℂ)
          ((Fin 12 → ℂ) ⊗[ℂ] (Fin 12 → ℂ)))) :=
    congrArg _ (pullbackSpecIso_inv_fst' ℂ (Fin 12 → ℂ) (Fin 12 → ℂ))
  have h3 : Spec.map (CommRingCat.ofHom (pointPairAlgHom r c).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (Fin 12 → ℂ)
          ((Fin 12 → ℂ) ⊗[ℂ] (Fin 12 → ℂ)))) =
      Spec.map (CommRingCat.ofHom ((pointPairAlgHom r c).toRingHom.comp
        (algebraMap (Fin 12 → ℂ) ((Fin 12 → ℂ) ⊗[ℂ] (Fin 12 → ℂ))))) :=
    (Spec.map_comp _ _).symm
  have h4 : Spec.map (CommRingCat.ofHom ((pointPairAlgHom r c).toRingHom.comp
        (algebraMap (Fin 12 → ℂ) ((Fin 12 → ℂ) ⊗[ℂ] (Fin 12 → ℂ))))) =
      Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun _ : Fin 12 => ℂ) c)) :=
    congrArg Spec.map (congrArg CommRingCat.ofHom (pointPair_left_hom r c))
  exact h1.trans (h2.trans (h3.trans h4))

/-- The right leg of the point pair is evaluation at the row point. -/
theorem pointPair_right (r c : Fin 12) :
    pointPairMap r c ≫ snd twelvePointWorld =
      Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun _ : Fin 12 => ℂ) r)) := by
  -- WAVE 29 (run-28 :259 receipt): the snd twin of pointPair_left's
  -- Trans death — same mechanism switch (have-chain + Eq.trans).
  show (Spec.map (CommRingCat.ofHom (pointPairAlgHom r c).toRingHom) ≫
      (pullbackSpecIso ℂ (Fin 12 → ℂ) (Fin 12 → ℂ)).inv) ≫ snd twelvePointWorld = _
  have h1 : (Spec.map (CommRingCat.ofHom (pointPairAlgHom r c).toRingHom) ≫
        (pullbackSpecIso ℂ (Fin 12 → ℂ) (Fin 12 → ℂ)).inv) ≫ snd twelvePointWorld =
      Spec.map (CommRingCat.ofHom (pointPairAlgHom r c).toRingHom) ≫
        ((pullbackSpecIso ℂ (Fin 12 → ℂ) (Fin 12 → ℂ)).inv ≫ snd twelvePointWorld) :=
    CategoryTheory.Category.assoc _ _ _
  have h2 : Spec.map (CommRingCat.ofHom (pointPairAlgHom r c).toRingHom) ≫
        ((pullbackSpecIso ℂ (Fin 12 → ℂ) (Fin 12 → ℂ)).inv ≫ snd twelvePointWorld) =
      Spec.map (CommRingCat.ofHom (pointPairAlgHom r c).toRingHom) ≫
        Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight
            (R := ℂ) (A := Fin 12 → ℂ) (B := Fin 12 → ℂ)).toRingHom) :=
    congrArg _ (pullbackSpecIso_inv_snd ℂ (Fin 12 → ℂ) (Fin 12 → ℂ))
  have h3 : Spec.map (CommRingCat.ofHom (pointPairAlgHom r c).toRingHom) ≫
        Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight
            (R := ℂ) (A := Fin 12 → ℂ) (B := Fin 12 → ℂ)).toRingHom) =
      Spec.map (CommRingCat.ofHom ((pointPairAlgHom r c).toRingHom.comp
          (Algebra.TensorProduct.includeRight
            (R := ℂ) (A := Fin 12 → ℂ) (B := Fin 12 → ℂ)).toRingHom)) :=
    (Spec.map_comp _ _).symm
  have h4 : Spec.map (CommRingCat.ofHom ((pointPairAlgHom r c).toRingHom.comp
          (Algebra.TensorProduct.includeRight
            (R := ℂ) (A := Fin 12 → ℂ) (B := Fin 12 → ℂ)).toRingHom)) =
      Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun _ : Fin 12 => ℂ) r)) :=
    congrArg Spec.map (congrArg CommRingCat.ofHom (pointPair_right_hom r c))
  exact h1.trans (h2.trans (h3.trans h4))

/-- Point-level action of the left leg: every carrier point lands on the
column point. -/
theorem pointPair_left_apply (r c : Fin 12) (z : Spec (CommRingCat.of ℂ)) :
    (pointPairMap r c ≫ fst twelvePointWorld) z = (twelvePointEquiv c).1 := by
  rw [pointPair_left]
  show PrimeSpectrum.comap (Pi.evalRingHom (fun _ : Fin 12 => ℂ) c) z = _
  rw [Subsingleton.elim z default]
  exact comap_evalRingHom_default c

/-- Point-level action of the right leg: the unique carrier point lands on
the row point. -/
theorem pointPair_right_apply (r c : Fin 12) (z : Spec (CommRingCat.of ℂ)) :
    (pointPairMap r c ≫ snd twelvePointWorld) z = (twelvePointEquiv r).1 := by
  rw [pointPair_right]
  show PrimeSpectrum.comap (Pi.evalRingHom (fun _ : Fin 12 => ℂ) r) z = _
  rw [Subsingleton.elim z default]
  exact comap_evalRingHom_default r

/-! ## The residue degree of the right leg -/

/-- Evaluation at one point of `ℂ¹²` is surjective. -/
theorem evalRingHom_surjective (r : Fin 12) :
    Function.Surjective (Pi.evalRingHom (fun _ : Fin 12 => ℂ) r) := by
  intro x
  exact ⟨Pi.single r x, by simp [Pi.single_apply]⟩

/-- `Spec` of a surjective evaluation map is an open immersion: the kernel is
generated by the idempotent `1 - Pi.single r 1`. -/
theorem isOpenImmersion_spec_map_eval (r : Fin 12) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (Pi.evalRingHom (fun _ : Fin 12 => ℂ) r))) := by
  rw [isOpenImmersion_SpecMap_iff_of_surjective _ (evalRingHom_surjective r)]
  refine ⟨1 - Pi.single r 1, ?_, ?_⟩
  · show (1 - Pi.single r 1) * (1 - Pi.single r 1) = 1 - Pi.single r 1
    funext i
    by_cases hi : i = r
    · simp [hi, Pi.single_apply]
    · simp [hi, Pi.single_apply]
  · show RingHom.ker (Pi.evalRingHom (fun _ : Fin 12 => ℂ) r) =
      Ideal.span {1 - Pi.single r 1}
    apply le_antisymm
    · intro f hf
      rw [RingHom.mem_ker, Pi.evalRingHom_apply] at hf -- AUDIT-4: `RingHom.mem_ker`
      -- W2-A (run-26 :241:6): `hf` arrives as the COE application
      -- `↑(eval r) f = 0`; normalize to the pointwise `f r = 0` before the
      -- final simp (Mathlib's own chain: Ideal/Maps.lean:1329;
      -- `Pi.evalRingHom_apply` off Algebra/Ring/Pi.lean:170, @[simps!]).

      -- explicit args at the pin (RingTheory/Ideal/Span.lean:181, `{x y : α}`
      -- implicit, iff-RHS `y ∣ x`); the existential reader is the PRIMED
      -- `Ideal.mem_span_singleton'` (Ideal/Span.lean:94,
      -- `x ∈ span {y} ↔ ∃ a, a * y = x`) — named x/y, same witness `f`, the
      -- residual goal `f * (1 - Pi.single r 1) = f` is unchanged.
      refine (Ideal.mem_span_singleton' (x := f)
        (y := 1 - Pi.single r 1)).mpr ⟨f, ?_⟩ -- AUDIT-4: span API
      funext i
      by_cases hi : i = r
      · simp [hi, Pi.single_apply, hf]
      · simp [hi, Pi.single_apply]
    · -- W2-A (run-26 :247:10): `Ideal.span_le` (Ideal/Span.lean:71) elaborates
      -- its RHS to SET-membership on the coerced ideal (`s ⊆ ↑I` — the wave26
      -- goal display `1 - Pi.single r 1 ∈ ↑(RingHom.ker …)`), where
      -- `RingHom.mem_ker`'s Ideal-membership pattern can never match.
      -- Route through `Ideal.span_singleton_le_iff_mem` (Ideal/Span.lean:99,
      -- Ideal-membership RHS), then the Mathlib idiom
      -- `rw [RingHom.mem_ker, …]` (Ideal/Maps.lean:752 + :1329).
      rw [Ideal.span_singleton_le_iff_mem, RingHom.mem_ker]
      -- WAVE 28 (run-27 :318 receipt): the bare `show` elaborated
      -- `1 - Pi.single r 1` at ℕ; drop it — the rw's output goal is already
      -- correctly typed; simp normalizes the eval application.
      simp [Pi.evalRingHom_apply, Pi.single_apply]


/-- **AUDIT-5 (residue degree).** The residue degree of the right leg at the
unique carrier point is `1`: the right leg is an open immersion, so its
residue field map is an iso, so the induced field extension is rank one. -/
theorem residueDegree_spec_map_eval (r : Fin 12) :
    Scheme.Hom.residueDegree
        (Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun _ : Fin 12 => ℂ) r)))
        (default : Spec (CommRingCat.of ℂ)) = 1 := by
  haveI hoi : IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (Pi.evalRingHom (fun _ : Fin 12 => ℂ) r))) :=
    isOpenImmersion_spec_map_eval r
  have hsurj : Function.Surjective (Scheme.Hom.residueFieldMap
      (Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun _ : Fin 12 => ℂ) r)))
      (default : Spec (CommRingCat.of ℂ))) :=
    (ConcreteCategory.bijective_of_isIso _).2
  -- WAVE 31 (run-30 :402/:412 receipts): the local Algebra instance was a
  -- `haveI` -- an OPAQUE local hypothesis -- so `Algebra.toModule this`
  -- could never unfold to the goal's canonical
  -- `(CommRingCat.Hom.hom (residueFieldMap …)).toAlgebra`, and both the
  -- `.mpr` instance check (:402) and the calc's HSMul elaboration (:412)
  -- died on the diamond.  `letI` makes the local definition TRANSPARENT
  -- (zeta-unfoldable): `this` is now syntactically the canonical term --
  -- exactly the instance `residueDegree`'s own body binds (ResidueField.lean
  -- :148, `letI := (f.residueFieldMap x).hom.toAlgebra`) -- and the same
  -- lesson the Wave-7 audit recorded for the Fa/Fb/eCounit seams: instances
  -- that must reduce are `letI`, never `haveI`.
  letI : Algebra
      ((Spec (CommRingCat.of (Fin 12 → ℂ))).residueField
        ((Spec.map (CommRingCat.ofHom
          (Pi.evalRingHom (fun _ : Fin 12 => ℂ) r)))
          (default : Spec (CommRingCat.of ℂ))))
      ((Spec (CommRingCat.of ℂ)).residueField
        (default : Spec (CommRingCat.of ℂ))) :=
    (Scheme.Hom.residueFieldMap
      (Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun _ : Fin 12 => ℂ) r)))
      (default : Spec (CommRingCat.of ℂ))).hom.toAlgebra
  -- WAVE 29 (run-28 :390/:397/:419 receipts): the (K := …)(V := …) pin died
  -- at the pin's own elaboration — the DivisionRing class binder of
  -- finrank_eq_one_iff_of_nonzero' (FiniteDimensional/Basic.lean:605,
  -- section vars :53 `[DivisionRing K] [AddCommGroup V] [Module K V]`)
  -- could not synthesize on the pinned comap-residueField type, and the
  -- show-bridge (U2-F2) died on the residueDegree delta+zeta.  The W8
  -- U2-F3 restructure (the no-re-roll law's next in chain): `dsimp only`
  -- unfolds residueDegree ON THE GOAL itself — Mathlib's own green idiom
  -- for this def (ResidueField.lean:152-155, residueDegree_id: `dsimp
  -- [residueDegree]`) — so the finrank proof re-elaborates directly on the
  -- unfolded goal: the lemma's class binders resolve against the goal's own
  -- elaborated instances, and the `1` witness is typed by the postponed
  -- OfNat once unification assigns V.
  dsimp only [Scheme.Hom.residueDegree]
  refine (finrank_eq_one_iff_of_nonzero' 1 one_ne_zero).mpr ?_
  intro w
  obtain ⟨a, ha⟩ := hsurj w
  refine ⟨a, ?_⟩
  -- AUDIT-5 + WAVE 27: the smul_def/mul_one rewrite leaves
  -- `algebraMap … a = residueFieldMap … a` — RingHom.toAlgebra's
  -- algebraMap — closed by rfl at default.  WAVE 30 (run-29 :402 receipt):
  -- the continuation-LHS sits at col 8 — AT the first step's LHS column
  -- (the colGe law) and BELOW the by-block's tactic column 9 (the parser
  -- ate the col-9 continuation as an unknown tactic); `= w := ha` closes.
  calc a • (1 : (Spec (CommRingCat.of ℂ)).residueField
        (default : Spec (CommRingCat.of ℂ)))
      = Scheme.Hom.residueFieldMap
          (Spec.map (CommRingCat.ofHom
            (Pi.evalRingHom (fun _ : Fin 12 => ℂ) r)))
          (default : Spec (CommRingCat.of ℂ)) a := by
        rw [Algebra.smul_def, mul_one]
        rfl
       Scheme.Hom.residueFieldMap
           (Spec.map (CommRingCat.ofHom
             (Pi.evalRingHom (fun _ : Fin 12 => ℂ) r)))
           (default : Spec (CommRingCat.of ℂ)) a
      = w := ha

/-- The right-leg residue weight at the unique carrier point is `1`. -/
theorem pointPair_residueWeight (r c : Fin 12) :
    pointResidueWeight (pointPairMap r c ≫ snd twelvePointWorld)
        (default : Spec (CommRingCat.of ℂ)) = 1 := by
  -- WAVE 27 (run-26 :302): the show's residueDegree fixes the implicit
  -- Y := twelvePointWorld.X; after `rw [pointPair_right]` the morphism
  -- becomes `Spec.map …` whose codomain is spelled `Spec (of ℂ¹²)` — the
  -- residueDegree_spec_map_eval pattern (elaborated at that spelling) can
  -- never cross the non-reducible `twelvePointWorld.X` def.  Ground the
  -- lemma at the Spec-spelling (where its own pattern matches itself),
  -- then close at default transparency where the carrier's X unfolds.
  have hrd : (Scheme.Hom.residueDegree
      (Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun _ : Fin 12 => ℂ) r)))
      (default : Spec (CommRingCat.of ℂ)) : ℚ) = 1 := by
    rw [residueDegree_spec_map_eval]
    rfl
  show (Scheme.Hom.residueDegree
      (pointPairMap r c ≫ snd twelvePointWorld)
      (default : Spec (CommRingCat.of ℂ)) : ℚ) = 1
  rw [pointPair_right]
  exact hrd

/-! ## The finite closed correspondence of one point pair -/

open Classical in
/-- The finite left-fiber sets of the point pair. -/
theorem pointPair_leftFiberSet_eq (r c : Fin 12) (x : twelvePointWorld.X) :
    ({z : Spec (CommRingCat.of ℂ) |
        (pointPairMap r c ≫ fst twelvePointWorld) z = x} : Set _) =
      if (twelvePointEquiv c).1 = x then
        {(default : Spec (CommRingCat.of ℂ))} else ∅ := by
  -- WAVE 27 (run-26 :311/:312): `open Classical in` above the docstring
  -- supplies propDecidable for the point-equality ite (the wave-23 law —
  -- HodgeData:239-243 idiom); the singleton is parenthesized so it is a
  -- Set literal, not a PrimeSpectrum structure instance.
  by_cases hx : (twelvePointEquiv c).1 = x
  · rw [if_pos hx]
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    -- WAVE 27 (latent L1): compose pointPair_left_apply with hx — the bare
    -- application proves `… = (twelvePointEquiv c).1`, the iff-LHS is
    -- `… = x`; rewrite the goal to the equiv spelling first (the :362 idiom).
    rw [← hx]
    exact iff_of_true (pointPair_left_apply r c z)
      (Subsingleton.elim z default)
  · rw [if_neg hx]
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false]
    -- WAVE 27 (latent L2): the goal is an IFF, not a function — intro is
    -- dead; iff_of_false with the composed disproof.
    exact iff_of_false
      (fun hleft => hx ((pointPair_left_apply r c z).symm.trans hleft))
      False.elim

/-- The genuine finite closed correspondence of the point pair:
`Spec ℂ` closed-immersed into `X ×_ℂ X` on `(point c, point r)`. -/
noncomputable def pointPairGeometry (r c : Fin 12) :
    FiniteClosedCorrespondence twelvePointWorld where
  carrier := Spec (CommRingCat.of ℂ)
  intoProduct := pointPairMap r c
  closedImmersion := by
    -- WAVE 27 (run-26 :331): `IsClosedImmersion.comp` is an instance with
    -- the two morphisms explicit (ClosedImmersion.lean:86); bare
    -- `exact IsClosedImmersion.comp _ _` leaves ?f ?g as metavars the
    -- instance search cannot resolve.  The `show` pins the goal to the
    -- composite spelling (pointPairMap delta-unfolds at default);
    -- unification then assigns f/g from the goal and finds h1/h2 in the
    -- instance cache.
    show IsClosedImmersion (Spec.map
        (CommRingCat.ofHom (pointPairAlgHom r c).toRingHom) ≫
          (pullbackSpecIso ℂ (Fin 12 → ℂ) (Fin 12 → ℂ)).inv)
    haveI h1 : IsClosedImmersion (Spec.map
        (CommRingCat.ofHom (pointPairAlgHom r c).toRingHom)) :=
      IsClosedImmersion.spec_of_surjective _
        (pointPairAlgHom_surjective r c)
    haveI h2 : IsClosedImmersion
        ((pullbackSpecIso ℂ (Fin 12 → ℂ) (Fin 12 → ℂ)).inv) := inferInstance
    exact IsClosedImmersion.comp _ _

  leftFiber_finite := by
    intro x
    rw [pointPair_leftFiberSet_eq r c x]
    by_cases hx : (twelvePointEquiv c).1 = x
    · rw [if_pos hx]; exact Set.finite_singleton _
    · rw [if_neg hx]; exact Set.finite_empty


/-- The point-pair carrier is the one-point `Spec ℂ` — inhabited and
subsingleton by the field structure.  WAVE 28 (run-27 :477 receipt): the
def-projection `(pointPairGeometry r c).carrier` blocks instance search, so
the instances are provided explicitly, with proofs crossing the structure
field's delta once (default transparency). -/
instance pointPairGeometry_carrier_inhabited (r c : Fin 12) :
    Inhabited ↥(pointPairGeometry r c).carrier :=
  ⟨(default : Spec (CommRingCat.of ℂ))⟩

instance pointPairGeometry_carrier_subsingleton (r c : Fin 12) :
    Subsingleton ↥(pointPairGeometry r c).carrier :=
  inferInstanceAs (Subsingleton ↥(Spec (CommRingCat.of ℂ)))

/-- The left fiber of the point pair over a source point which IS the column
point is the singleton fiber of the unique carrier point. -/
theorem pointPair_leftFiberFinset_eq_singleton (r c : Fin 12)
    (x : CodimensionPoint twelvePointWorld.X 0)
    (h : (twelvePointEquiv c).1 = x.1) :
    (pointPairGeometry r c).leftFiberFinset x.1 =
      {(default : Spec (CommRingCat.of ℂ))} := by
  ext z
  simp only [mem_leftFiberFinset, Finset.mem_singleton]
  rw [← h]
  -- WAVE 29 (run-28 :538 receipt): the goal's RHS is Finset-membership
  -- `z ∈ {default}` (Finset.mem_singleton never fired as a rewrite — the
  -- unused-arg receipt); the second iff_of_true argument must be a TERM of
  -- exactly that membership type, built by mem_singleton's .mpr.
  exact iff_of_true (pointPair_left_apply r c z)
    (Finset.mem_singleton.mpr (Subsingleton.elim z default))

/-- The left fiber over any other source point is empty. -/
theorem pointPair_leftFiberFinset_eq_empty (r c : Fin 12)
    (x : CodimensionPoint twelvePointWorld.X 0)
    (h : (twelvePointEquiv c).1 ≠ x.1) :
    (pointPairGeometry r c).leftFiberFinset x.1 = ∅ := by
  ext z
  simp only [mem_leftFiberFinset, Finset.notMem_empty]
  -- WAVE 27 (run-26 :373): `intro hz` is dead on the IFF goal
  -- `left z = ↑x ↔ False`; close with iff_of_false.
  exact iff_of_false
    (fun hleft => h ((pointPair_left_apply r c z).symm.trans hleft))
    False.elim

/-- The coheight of the right image of the unique carrier point is zero. -/
theorem pointPair_right_coheight (r c : Fin 12) :
    Order.coheight
        ((pointPairMap r c ≫ snd twelvePointWorld)
          (default : Spec (CommRingCat.of ℂ))) = 0 := by
  rw [pointPair_right_apply]
  exact (twelvePointEquiv r).2

/-- Over the column point, the transition is the single atom at the row
point with residue weight one. -/
theorem pointPair_transition_eq (r c : Fin 12)
    (x : CodimensionPoint twelvePointWorld.X 0)
    (h : (twelvePointEquiv c).1 = x.1) :
    (pointPairGeometry r c).transition 0 x =
      Finsupp.single (twelvePointPt r) 1 := by
  have hfin : (pointPairGeometry r c).leftFiberFinset x.1 =
      {(default : Spec (CommRingCat.of ℂ))} :=
    pointPair_leftFiberFinset_eq_singleton r c x h
  -- WAVE 29 (run-28 :588 receipt): the whole atom chain was frankensteined
  -- across the two default spellings — the scheme-level `default` inside a
  -- carrier-typed slot left the post-rw goal not type-correct at implicit
  -- transparency (the full-error note), killing the targetAtomPresentation
  -- rewrite.  Every term of the chain is now stated at the CARRIER type
  -- (the pointPairGeometry_carrier_inhabited default), each seam crossing
  -- done once in term mode inside its own have.
  have hz : Order.coheight
      ((pointPairGeometry r c).right
        (default : ↥(pointPairGeometry r c).carrier)) = 0 :=
    pointPair_right_coheight r c
  show ((pointPairGeometry r c).leftFiberFinset x.1).sum
      ((pointPairGeometry r c).targetAtomPresentation 0) = _
  -- WAVE 30 (run-29 :576 receipt): the outer rw [hfin] consumed the
  -- leftFiberFinset pattern before rw [hsum] could fire (the receipt's
  -- goal was already the scheme-spelled singleton — not type-correct at
  -- implicit).  The hsum rewrite alone carries the goal from the show's
  -- own spelling straight to the carrier-spelled atom — well-typed
  -- throughout.
  have hsum : ((pointPairGeometry r c).leftFiberFinset x.1).sum
      ((pointPairGeometry r c).targetAtomPresentation 0) =
      (pointPairGeometry r c).targetAtomPresentation 0
        (default : ↥(pointPairGeometry r c).carrier) := by
    rw [hfin]
    exact Finset.sum_singleton _ _
  rw [hsum]
  rw [FiniteClosedCorrespondence.targetAtomPresentation_eq_single
    (pointPairGeometry r c) 0 (default : ↥(pointPairGeometry r c).carrier) hz]
  have hrw : pointResidueWeight (pointPairGeometry r c).right
      (default : ↥(pointPairGeometry r c).carrier) = 1 :=
    pointPair_residueWeight r c
  rw [hrw]
  -- the atom point is the row twelve-point
  have hr : (pointPairGeometry r c).right
      (default : ↥(pointPairGeometry r c).carrier) = (twelvePointEquiv r).1 :=
    pointPair_right_apply r c default
  -- WAVE 31 (run-30 :610 receipt): `rw [hr]` dies because the goal's fun₀
  -- pattern `| ⟨pt, hz⟩ => 1` carries `hz` in its second slot and hz's TYPE
  -- mentions the very point being rewritten, so the abstracted motive
  -- `fun _a => fun₀ | ⟨_a, hz⟩ => 1 = _` is not type correct (the receipt's
  -- `coheight _a = ↑0`; the OfNat-0 vs Nat.cast-↑0 seam only masks the
  -- deeper point-dependence -- no re-spelling of hz repairs it).  But the
  -- fun₀ display IS `Finsupp.single` (Finsupp/Notation.lean: the single-arm
  -- `fun₀ | i => a` sugar elaborates to `Finsupp.single i a`, and single
  -- itself takes NO DecidableEq argument, Finsupp/Single.lean:47), so the
  -- WHOLE subtype element `⟨pt, hz⟩` is one subterm of the goal: the goal is
  -- `Finsupp.single ⟨pt, hz⟩ 1 = Finsupp.single (twelvePointPt r) 1`.
  -- Rewrite the whole element at once -- hz travels INSIDE the rewritten
  -- subterm, so the congrArg motive `fun _e => Finsupp.single _e 1 = _` is
  -- well-typed by construction.  `Subtype.ext hr` is a pure term-mode seam:
  -- `(twelvePointPt r).1` is the abbrev's `.1`, definitionally
  -- `(twelvePointEquiv r).1`, exactly hr's right-hand side.
  have hsub : (⟨(pointPairGeometry r c).right
      (default : ↥(pointPairGeometry r c).carrier), hz⟩ :
      CodimensionPoint twelvePointWorld.X 0) = twelvePointPt r :=
    Subtype.ext hr
  exact congrArg (fun k => Finsupp.single k (1 : ℚ)) hsub

/-- Over the column point, the native image is exactly the row point cycle. -/
theorem pointPair_nativePointImage_eq (r c : Fin 12)
    (x : CodimensionPoint twelvePointWorld.X 0)
    (h : (twelvePointEquiv c).1 = x.1) :
    (pointPairGeometry r c).nativePointImage 0 x =
      codimensionPointCycle twelvePointWorld.X 0 (twelvePointPt r) := by
  show realizeFiniteCodimensionPresentation twelvePointWorld.X 0
      ((pointPairGeometry r c).transition 0 x) = _
  rw [pointPair_transition_eq r c x h]
  rw [realizeFiniteCodimensionPresentation_single]
  exact one_smul _ _

/-- Over any other source point, the native image is the zero cycle. -/
theorem pointPair_nativePointImage_eq_zero (r c : Fin 12)
    (x : CodimensionPoint twelvePointWorld.X 0)
    (h : (twelvePointEquiv c).1 ≠ x.1) :
    (pointPairGeometry r c).nativePointImage 0 x = 0 := by
  have hfin : (pointPairGeometry r c).leftFiberFinset x.1 = ∅ :=
    pointPair_leftFiberFinset_eq_empty r c x h
  show realizeFiniteCodimensionPresentation twelvePointWorld.X 0
      ((pointPairGeometry r c).transition 0 x) = _
  have htr : (pointPairGeometry r c).transition 0 x = 0 := by
    show ((pointPairGeometry r c).leftFiberFinset x.1).sum
        ((pointPairGeometry r c).targetAtomPresentation 0) = _
    rw [hfin, Finset.sum_empty]
  rw [htr]
  exact realizeFiniteCodimensionPresentation_zero twelvePointWorld.X 0

/-! ## The letter operator: the matrix unit -/

/-- The `r`-th indicator map on the twelve coordinate vectors. -/
noncomputable def matrixUnitIndicator (r c : Fin 12) :
    (Fin 12 → ℚ) →ₗ[ℚ] (Fin 12 → ℚ) where
  toFun v k := if k = r then v c else 0
  map_add' := by
    intro v w
    funext k
    by_cases hk : k = r <;> simp [hk]
  map_smul' := by
    intro q v
    funext k
    by_cases hk : k = r <;> simp [hk, Pi.smul_apply, smul_eq_mul]

/-- The matrix unit `(r, c)` operator on H⁰, transported through the
cohomology iso. -/
noncomputable def matrixUnitOp (r c : Fin 12) :
    RationalSingularCohomology twelvePointHodgeData.analytification 0 →ₗ[ℚ]
      RationalSingularCohomology twelvePointHodgeData.analytification 0 :=
  LinearMap.comp (twelvePointCohomologyIso.symm.toLinearMap)
    (LinearMap.comp (matrixUnitIndicator r c)
      twelvePointCohomologyIso.toLinearMap)

theorem matrixUnitOp_apply (r c : Fin 12)
    (u : RationalSingularCohomology twelvePointHodgeData.analytification 0) :
    twelvePointCohomologyIso (matrixUnitOp r c u) =
      fun k => if k = r then twelvePointCohomologyIso u c else 0 := by
  show twelvePointCohomologyIso
      (twelvePointCohomologyIso.symm
        (matrixUnitIndicator r c (twelvePointCohomologyIso u))) = _
  -- WAVE 19 (pre-emptive, W1-D R1): the post-show goal is
  -- `iso (iso.symm X) = X`-shaped (the symm is applied FIRST) — the correct
  -- lemma is `LinearEquiv.apply_symm_apply : e (e.symm x) = x`;
  -- `symm_apply_apply : e.symm (e x) = x` is the wrong direction and its
  -- `e.symm`-headed pattern can never match.
  rw [LinearEquiv.apply_symm_apply]
  rfl

/-- The matrix unit sends the `i`-th point class to the `r`-th indicator when
`i` is the column, and to zero otherwise. -/
theorem matrixUnitOp_pointClass (r c i : Fin 12) :
    twelvePointCohomologyIso (matrixUnitOp r c
        (zeroCycleClass (codimensionPointCycle twelvePointWorld.X 0
          (twelvePointPt i)))) =
      if c = i then Pi.single r (1 : ℚ) else 0 := by
  -- WAVE 27 (run-26 :484:6, W1-D R4/R5 -- the have-hoist): the bare
  -- `rw [matrixUnitOp_apply]` dies at the coe-instance seam -- kabstract
  -- assigns `?u := zeroCycleClass …` and then re-checks the application's
  -- type at `implicit` transparency, where
  -- `twelvePointHodgeData.analytification` (a projection on a plain def)
  -- is stuck against `twelvePointAnalytification`.  Hoist the lemma as a
  -- ground have whose TYPE is the goal's own spelling (the application
  -- elaborates once, at default transparency, in term mode) and rewrite
  -- with the have -- the match is then purely syntactic.
  have happ : twelvePointCohomologyIso (matrixUnitOp r c
      (zeroCycleClass (codimensionPointCycle twelvePointWorld.X 0
        (twelvePointPt i)))) =
      fun k => if k = r then twelvePointCohomologyIso
        (zeroCycleClass (codimensionPointCycle twelvePointWorld.X 0
          (twelvePointPt i))) c else 0 :=
    matrixUnitOp_apply r c _
  rw [happ]
  -- WAVE 19 (pre-emptive, W1-D R2): the AUDIT-6 contract lemma's LHS is
  -- stated over HodgeData's `def twelvePointPt` (stuck at instances
  -- transparency) while this goal carries the FoldWord `abbrev
  -- twelvePointPt` -- bridge it with a `show … from` restatement at the
  -- abbrev spelling (elaborator-level defeq on the from-term, syntactic
  -- match on the rewrite).
  rw [show twelvePointCohomologyIso (zeroCycleClass (codimensionPointCycle
      twelvePointWorld.X 0 (twelvePointPt i))) = Pi.single i (1 : ℚ) from
    zeroCycleClass_point i]
  funext k
  by_cases hk : k = r <;> by_cases hi : c = i <;>
    simp [hk, hi, Pi.single_apply]

/-! ## The realization theorem -/

/-- The point pair realizes exactly its matrix unit on all point classes. -/
theorem pointPairGeometry_realizes (r c : Fin 12) :
    (pointPairGeometry r c).RealizesAmbientOnPoints
        (H := twelvePointHodgeData) (p := 0) (matrixUnitOp r c) := by
  intro x
  -- every codimension-0 point is one of the twelve
  obtain ⟨i, hi⟩ := twelvePointEquiv.surjective x -- AUDIT-7: `twelvePointEquiv`
  subst hi
  by_cases hic : i = c
  · -- WAVE 27 (run-26 :503/:534, W1-D R6 -- the wave-25 subst receipt):
    -- `subst hic` would eliminate the RHS variable `c` and kill every
    -- later `c` reference.  Rewrite the goal instead -- subst-free, both
    -- binders stay alive, the case hypothesis is consumed syntactically.
    rw [hic]
    have hc : (twelvePointEquiv c).1 = (twelvePointEquiv c).1 := rfl
    have himg := pointPair_nativePointImage_eq r c (twelvePointEquiv c) hc
    show twelvePointHodgeData.cycleClass 0
        ((pointPairGeometry r c).nativePointImage 0 (twelvePointEquiv c)) = _
    rw [himg]
    have key : twelvePointCohomologyIso
        (matrixUnitOp r c (zeroCycleClass
          (codimensionPointCycle twelvePointWorld.X 0 (twelvePointPt c)))) =
        twelvePointCohomologyIso (zeroCycleClass
          (codimensionPointCycle twelvePointWorld.X 0 (twelvePointPt r))) := by
      rw [matrixUnitOp_pointClass r c c]
      rw [if_pos rfl]
      -- WAVE 19 (pre-emptive, W1-D R2): same HodgeData `def`/FoldWord `abbrev`
      -- `twelvePointPt` seam as matrixUnitOp_pointClass's proof -- restate the
      -- contract lemma at the abbrev spelling.
      rw [show twelvePointCohomologyIso (zeroCycleClass (codimensionPointCycle
          twelvePointWorld.X 0 (twelvePointPt r))) = Pi.single r (1 : ℚ) from
        zeroCycleClass_point r]
    -- WAVE 29 (run-28 :745/:746 receipts): the calc mechanism died on this
    -- chain in two consecutive waves (wave 27 :534, wave 28 :745/:746 — the
    -- parser's `true : Bool` phantom and the cycleClass-application type
    -- mismatch).  The no-re-roll law: mechanism switch — three ground haves,
    -- each stated at the previous have's own RHS spelling, each closed by a
    -- single term-mode application; composed by Eq.trans.  The WAVE-19
    -- audit-F2 explicit `rfl` inside s2 is kept (the post-rewrite sides
    -- agree only by default-transparency defeq; rw's auto-rfl runs at
    -- reducible).
    have s1 : twelvePointHodgeData.cycleClass 0
          (codimensionPointCycle twelvePointWorld.X 0 (twelvePointPt r)) =
        twelvePointCohomologyIso.symm (twelvePointCohomologyIso
          (twelvePointHodgeData.cycleClass 0
            (codimensionPointCycle twelvePointWorld.X 0 (twelvePointPt r)))) :=
      (LinearEquiv.symm_apply_apply _ _).symm
    have s2 : twelvePointCohomologyIso.symm (twelvePointCohomologyIso
          (twelvePointHodgeData.cycleClass 0
            (codimensionPointCycle twelvePointWorld.X 0 (twelvePointPt r)))) =
        twelvePointCohomologyIso.symm (twelvePointCohomologyIso
          (matrixUnitOp r c (zeroCycleClass
            (codimensionPointCycle twelvePointWorld.X 0 (twelvePointPt c))))) :=
      by rw [key]; rfl
    have s3 : twelvePointCohomologyIso.symm (twelvePointCohomologyIso
          (matrixUnitOp r c (zeroCycleClass
            (codimensionPointCycle twelvePointWorld.X 0 (twelvePointPt c))))) =
        matrixUnitOp r c (zeroCycleClass
          (codimensionPointCycle twelvePointWorld.X 0 (twelvePointPt c))) :=
      LinearEquiv.symm_apply_apply _ _
    exact s1.trans (s2.trans s3)
  · have hne : (twelvePointEquiv c).1 ≠ (twelvePointEquiv i).1 := by
      intro h
      exact hic (twelvePointEquiv.injective (Subtype.ext h)).symm
    have himg := pointPair_nativePointImage_eq_zero r c (twelvePointEquiv i) hne
    show twelvePointHodgeData.cycleClass 0
        ((pointPairGeometry r c).nativePointImage 0 (twelvePointEquiv i)) = _
    rw [himg, map_zero]
    have hzero : matrixUnitOp r c (zeroCycleClass
        (codimensionPointCycle twelvePointWorld.X 0 (twelvePointPt i))) = 0 := by
      -- WAVE 29 (run-28 :783 receipt): the calc's Trans synthesis died;
      -- mechanism switch as in the first arm -- ground haves at the
      -- goal's own spelling, one term-mode application each, Eq.trans
      -- composition.  Step 4 closed by the PINNED Mathlib lemma
      -- (Module/Equiv/Defs.lean:501, protected, e explicit) instead of
      -- `simp` (the OfNat instances differ across the analytification
      -- clans and simp's rfl-close is unattested).
      have z1 : matrixUnitOp r c (zeroCycleClass
            (codimensionPointCycle twelvePointWorld.X 0 (twelvePointPt i))) =
          twelvePointCohomologyIso.symm (twelvePointCohomologyIso
            (matrixUnitOp r c (zeroCycleClass
              (codimensionPointCycle twelvePointWorld.X 0 (twelvePointPt i))))) :=
        (LinearEquiv.symm_apply_apply _ _).symm
      have z2 : twelvePointCohomologyIso.symm (twelvePointCohomologyIso
            (matrixUnitOp r c (zeroCycleClass
              (codimensionPointCycle twelvePointWorld.X 0 (twelvePointPt i))))) =
          twelvePointCohomologyIso.symm
            (if c = i then Pi.single r (1 : ℚ) else 0) :=
        by rw [matrixUnitOp_pointClass r c i]
      have z3 : twelvePointCohomologyIso.symm
            (if c = i then Pi.single r (1 : ℚ) else 0) =
          twelvePointCohomologyIso.symm 0 :=
        by rw [if_neg (fun h => hic h.symm)]
      have z4 : twelvePointCohomologyIso.symm 0 = 0 :=
        LinearEquiv.map_zero twelvePointCohomologyIso.symm
      exact z1.trans (z2.trans (z3.trans z4))
    -- WAVE 27 (seam hardening, W1-D R5): the goal's RHS carries the projection
    -- spellings (`twelvePointHodgeData.cycleClass 0`, `twelvePointEquiv i`)
    -- while hzero's LHS carries the constant/abbrev spellings
    -- (`zeroCycleClass`, `twelvePointPt i`) -- defeq-only (cycleClass-0
    -- match-iota + twelvePointPt structure-eta + `2 * 0` Nat reduction),
    -- dead for `rw` at matching transparency.  Close in term mode: `exact`
    -- unifies once at default transparency.
    exact hzero.symm


/-! ## The letter and the 26-letter fold word -/

/-- One weighted point-pair letter: the genuine geometry plus its matrix-unit
operator plus the pointwise realization theorem. -/
noncomputable def pointPairLetter (r c : Fin 12) :
    RealizedFiniteClosedCorrespondence twelvePointWorld twelvePointHodgeData 0 where
  geometry := pointPairGeometry r c
  cohomologyOperator := matrixUnitOp r c
  realizes_on_points := pointPairGeometry_realizes r c

/-- The 26 nonzero entries of the owner's fold matrix, as
`(row, column, weight)` letter data. -/
def foldWordData : List (Fin 12 × Fin 12 × ℚ) :=
  [(0, 0, 1), (0, 11, 1), (1, 4, 1), (1, 10, 1), (2, 8, 1), (2, 9, -1),
   (3, 1, 1), (3, 8, 1), (4, 4, 1), (4, 5, 1), (4, 7, 1), (5, 6, 1),
   (5, 9, 1), (6, 2, 1), (6, 5, -1), (7, 4, -1), (7, 6, 1), (8, 3, -1),
   (8, 8, 1), (8, 10, 1), (9, 2, 1), (9, 3, 1), (10, 1, -1), (10, 7, 1),
   (11, 0, -1), (11, 11, 3)]

/-- The realized correspondence word induced by letter data. -/
noncomputable def lettersOf (L : List (Fin 12 × Fin 12 × ℚ)) :
    RealizedCorrespondenceWord twelvePointWorld twelvePointHodgeData 0 :=
  L.map (fun d => (d.2.2, pointPairLetter d.1 d.2.1))

/-- **THE FOLD WORD**: the owner's fold as a genuine realized correspondence
word of 26 weighted point-pair letters. -/
noncomputable def twelvePointFoldWord :
    RealizedCorrespondenceWord twelvePointWorld twelvePointHodgeData 0 :=
  lettersOf foldWordData

/-- The fold matrix assembled from the same letter data: the entry `(r, c)`
is the sum of the weights of the letters with right point `r` and left
point `c`. -/
def twelvePointFoldMatrix : Matrix (Fin 12) (Fin 12) ℚ :=
  fun r c => (foldWordData.map
    (fun d => if d.2.1 = c then (if d.1 = r then d.2.2 else 0) else 0)).sum

/-! ## The word operator equals the fold matrix -/

/-- Nil-case operator unfolding of the word pair. -/
theorem realizedWordPair_cohomologyOperator_nil :
    (realizedWordPair
        (lettersOf ([] : List (Fin 12 × Fin 12 × ℚ)))).cohomologyOperator =
      0 := rfl

/-- Cons-case operator unfolding of the word pair. -/
theorem realizedWordPair_cohomologyOperator_cons (q : ℚ)
    (R : RealizedFiniteClosedCorrespondence twelvePointWorld twelvePointHodgeData 0)
    (W : RealizedCorrespondenceWord twelvePointWorld twelvePointHodgeData 0) :
    (realizedWordPair ((q, R) :: W)).cohomologyOperator =
      q • R.cohomologyOperator +
        (realizedWordPair W).cohomologyOperator := rfl

/-- **AUDIT-8 (iso linearity).** Linearity of the cohomology iso through its
linear-map structure. -/
theorem cohomologyIso_sum {ι : Type*} (s : Finset ι)
    (g : ι → RationalSingularCohomology
      twelvePointHodgeData.analytification 0) :
    twelvePointCohomologyIso (∑ i ∈ s, g i) =
      ∑ i ∈ s, twelvePointCohomologyIso (g i) :=
    map_sum twelvePointCohomologyIso.toLinearMap g s

theorem cohomologyIso_smul (t : ℚ)
    (v : RationalSingularCohomology twelvePointHodgeData.analytification 0) :
    twelvePointCohomologyIso (t • v) = t • twelvePointCohomologyIso v :=
  map_smul twelvePointCohomologyIso.toLinearMap t v

theorem cohomologyIso_zero :
    twelvePointCohomologyIso (0 :
      RationalSingularCohomology twelvePointHodgeData.analytification 0) = 0 :=
  map_zero twelvePointCohomologyIso.toLinearMap

/-- Additivity of the cohomology iso through its linear-map structure. -/
theorem cohomologyIso_add (v w : RationalSingularCohomology
      twelvePointHodgeData.analytification 0) :
    twelvePointCohomologyIso (v + w) =
      twelvePointCohomologyIso v + twelvePointCohomologyIso w :=
  map_add twelvePointCohomologyIso.toLinearMap v w

/-- The word operator acts on point classes by the letter data matrix. -/
theorem wordOp_pointClass (L : List (Fin 12 × Fin 12 × ℚ)) (i : Fin 12) :
    twelvePointCohomologyIso ((realizedWordPair (lettersOf L)).cohomologyOperator
        (zeroCycleClass (codimensionPointCycle twelvePointWorld.X 0
          (twelvePointPt i)))) =
      fun j => (L.map
        (fun d => if d.2.1 = i then (if j = d.1 then d.2.2 else 0) else 0)).sum := by
  induction L with
  | nil =>
    simp only [lettersOf, List.map_nil, List.sum_nil]
    -- W2-D (run-26 :665 receipt, W1-D R4/R5): the old `show` ascribed the zero
    -- operator at the PROJECTION clan (`twelvePointHodgeData.analytification 0`)
    -- while the argument `zeroCycleClass …` lives at the CONSTANT clan
    -- (`twelvePointAnalytification 0`, its codomain, HodgeData:183-185) — the
    -- application stayed cross-clan, so `LinearMap.zero_apply`'s `0 ?x` pattern
    -- could never typecheck at instances transparency.  The fix: land the whole
    -- goal at the argument's own constant clan.  The `show` performs the entire
    -- nil-word reduction (iota on `realizedWordPair []` to the zero operator —
    -- CycleClassOperatorPair.zero's field is literally `0`; the zero-operator
    -- application — `LinearMap.zero_apply` is rfl, Defs.lean:793) at default
    -- transparency ONCE; the iso's value-at-zero is the single propositional
    -- step (`map_zero`), hoisted at the same clan.
    have hiso0 : twelvePointCohomologyIso
        (0 : RationalSingularCohomology twelvePointAnalytification 0) = 0 :=
      cohomologyIso_zero
    show twelvePointCohomologyIso
        (0 : RationalSingularCohomology twelvePointAnalytification 0) =
        fun j => 0
    exact hiso0

  | cons d L ih =>
    have hword : lettersOf (d :: L) =
        (d.2.2, pointPairLetter d.1 d.2.1) :: lettersOf L := rfl
    -- WAVE 19 (pre-emptive, W1-D R3): the word operator's field type spells
    -- the fiber as `twelvePointHodgeData.analytification (2 * 0)` while the
    -- iso-side lemmas (`cohomologyIso_add`, `cohomologyIso_smul`, and
    -- `matrixUnitOp_pointClass` behind the old projection transport) are
    -- typed at the 0 spelling — the def-projection and the unreduced `2 * 0`
    -- are stuck at instances transparency, so the plain `rw`s cannot match.
    -- Hoist the three equations as ground haves at the goal's own `(2 * 0)`
    -- spelling; each application elaborates at default transparency and the
    -- `rw` chain is purely syntactic.
    have hiso : ∀ X Y : RationalSingularCohomology
        twelvePointHodgeData.analytification (2 * 0),
        twelvePointCohomologyIso (X + Y) =
          twelvePointCohomologyIso X + twelvePointCohomologyIso Y :=
      fun X Y => cohomologyIso_add X Y
    have hisosmul : ∀ (t : ℚ) (X : RationalSingularCohomology
        twelvePointHodgeData.analytification (2 * 0)),
        twelvePointCohomologyIso (t • X) = t • twelvePointCohomologyIso X :=
      fun t X => cohomologyIso_smul t X
    have hletter : twelvePointCohomologyIso
        ((pointPairLetter d.1 d.2.1).cohomologyOperator
          (zeroCycleClass (codimensionPointCycle twelvePointWorld.X 0
            (twelvePointPt i)))) =
        if d.2.1 = i then Pi.single d.1 (1 : ℚ) else 0 :=
      matrixUnitOp_pointClass d.1 d.2.1 i
    -- W2-D (run-26 :695 receipt, W1-D R4/R5): the post-cons-unfold goal's
    -- operator application is cross-clan (operator at `(2 * 0)`, argument at
    -- `twelvePointAnalytification 0`) — `LinearMap.add_apply`'s `(?f + ?g) ?x`
    -- and `LinearMap.smul_apply`'s patterns can never typecheck at instances
    -- transparency (the full-error receipt names the two clans).  Hoist BOTH
    -- decompositions of the operator application as ground haves stated at the
    -- goal's own `(2 * 0)` operator clan, closed in TERM mode (defeq at default
    -- transparency, once each); the `rw` chain below is then purely syntactic.
    -- Both lemmas are rfl at the pin (Defs.lean:835 / :751).
    have hsplit : ((d.2.2 • (pointPairLetter d.1 d.2.1).cohomologyOperator +
        (realizedWordPair (lettersOf L)).cohomologyOperator)
        (zeroCycleClass (codimensionPointCycle twelvePointWorld.X 0
          (twelvePointPt i)))) =
        ((d.2.2 • (pointPairLetter d.1 d.2.1).cohomologyOperator)
          (zeroCycleClass (codimensionPointCycle twelvePointWorld.X 0
            (twelvePointPt i)))) +
        (realizedWordPair (lettersOf L)).cohomologyOperator
          (zeroCycleClass (codimensionPointCycle twelvePointWorld.X 0
            (twelvePointPt i))) :=
      LinearMap.add_apply _ _ _
    have hsmulsplit : ((d.2.2 • (pointPairLetter d.1 d.2.1).cohomologyOperator)
        (zeroCycleClass (codimensionPointCycle twelvePointWorld.X 0
          (twelvePointPt i)))) =
        d.2.2 • ((pointPairLetter d.1 d.2.1).cohomologyOperator
          (zeroCycleClass (codimensionPointCycle twelvePointWorld.X 0
            (twelvePointPt i)))) :=
      LinearMap.smul_apply _ _ _
    rw [hword, realizedWordPair_cohomologyOperator_cons]
    rw [hsplit, hiso, hsmulsplit, hisosmul, hletter, ih]

    funext j
    simp only [List.map_cons, List.sum_cons]
    by_cases hd : d.2.1 = i
    · by_cases hj : j = d.1 <;>
        simp [hd, hj, Pi.single_apply, Pi.smul_apply, smul_eq_mul]
    · by_cases hj : j = d.1 <;>
        simp [hd, hj, Pi.single_apply, Pi.smul_apply, smul_eq_mul]

/-- On point classes, the fold word operator is the fold matrix column. -/
theorem foldWord_op_pointClass (c : Fin 12) :
    twelvePointCohomologyIso ((realizedWordPair twelvePointFoldWord).cohomologyOperator
        (zeroCycleClass (codimensionPointCycle twelvePointWorld.X 0
          (twelvePointPt c)))) =
      fun j => twelvePointFoldMatrix j c := by
  rw [show realizedWordPair twelvePointFoldWord
      = realizedWordPair (lettersOf foldWordData) from rfl]
  rw [wordOp_pointClass foldWordData c]
  funext j
  -- AUDIT (guard orientation): the word lemma's inner guard is `j = d.1`,
  -- the fold matrix's is `d.1 = j`; `eq_comm` normalizes both sides.
  simp only [twelvePointFoldMatrix, eq_comm]

/-- Every H⁰ class is the sum of its coordinates times point classes. -/
theorem module_decomp (u : RationalSingularCohomology
    twelvePointHodgeData.analytification 0) :
    u = ∑ k : Fin 12, (twelvePointCohomologyIso u k) •
      (zeroCycleClass (codimensionPointCycle twelvePointWorld.X 0
        (twelvePointPt k))) := by
  have hsum : twelvePointCohomologyIso
      (∑ k : Fin 12, (twelvePointCohomologyIso u k) •
        (zeroCycleClass (codimensionPointCycle twelvePointWorld.X 0
          (twelvePointPt k)))) = twelvePointCohomologyIso u := by
    -- WAVE 19 (pre-emptive, W1-D R2+R3): the summands live at the
    -- `zeroCycleClass` codomain spelling `twelvePointAnalytification 0`
    -- while `cohomologyIso_sum`/`cohomologyIso_smul` are stated at the
    -- projection spelling `twelvePointHodgeData.analytification 0` (stuck
    -- at instances transparency), and the AUDIT-6 contract lemma
    -- additionally sits across the HodgeData `def`/FoldWord `abbrev`
    -- `twelvePointPt` seam — hoist all three as ground haves at the
    -- summands' own spelling.
    have hsummap : twelvePointCohomologyIso
        (∑ k : Fin 12, (twelvePointCohomologyIso u k) •
          (zeroCycleClass (codimensionPointCycle twelvePointWorld.X 0
            (twelvePointPt k)))) =
        ∑ k : Fin 12, twelvePointCohomologyIso
          ((twelvePointCohomologyIso u k) •
            (zeroCycleClass (codimensionPointCycle twelvePointWorld.X 0
              (twelvePointPt k)))) :=
      cohomologyIso_sum _ _
    have hsmulmap : ∀ (t : ℚ) (X : RationalSingularCohomology
        twelvePointAnalytification 0),
        twelvePointCohomologyIso (t • X) = t • twelvePointCohomologyIso X :=
      fun t X => cohomologyIso_smul t X
    have hpt : ∀ k : Fin 12, twelvePointCohomologyIso (zeroCycleClass
        (codimensionPointCycle twelvePointWorld.X 0 (twelvePointPt k))) =
        Pi.single k (1 : ℚ) := fun k => zeroCycleClass_point k
    rw [hsummap]
    simp only [hsmulmap, hpt]
    funext j
    rw [Finset.sum_apply] -- AUDIT-8
    simp [Pi.single_apply]
  -- WAVE 29 (run-28 :1032 receipt): the calc's Trans synthesis died on the
  -- continuation geometry (the step-2 LHS at col 5 under the first LHS
  -- `u` at col 8 — the colGe law).  Mechanism switch: the have-chain,
  -- composed by Eq.trans.
  have c1 : u = twelvePointCohomologyIso.symm (twelvePointCohomologyIso u) :=
    (LinearEquiv.symm_apply_apply _ _).symm
  have c2 : twelvePointCohomologyIso.symm (twelvePointCohomologyIso u) =
      twelvePointCohomologyIso.symm (twelvePointCohomologyIso
        (∑ k : Fin 12, (twelvePointCohomologyIso u k) •
          (zeroCycleClass (codimensionPointCycle twelvePointWorld.X 0
            (twelvePointPt k))))) :=
    congrArg _ hsum.symm
  have c3 : twelvePointCohomologyIso.symm (twelvePointCohomologyIso
        (∑ k : Fin 12, (twelvePointCohomologyIso u k) •
          (zeroCycleClass (codimensionPointCycle twelvePointWorld.X 0
            (twelvePointPt k))))) =
      ∑ k : Fin 12, (twelvePointCohomologyIso u k) •
          (zeroCycleClass (codimensionPointCycle twelvePointWorld.X 0
            (twelvePointPt k))) :=
    LinearEquiv.symm_apply_apply _ _
  exact c1.trans (c2.trans c3)

/-- **THE OPERATOR THEOREM**: under the H⁰ cohomology iso, the fold word's
cohomology operator IS the fold matrix. -/
theorem twelvePointFoldWord_op (u : RationalSingularCohomology
    twelvePointHodgeData.analytification 0) :
    twelvePointCohomologyIso
        ((realizedWordPair twelvePointFoldWord).cohomologyOperator u) =
      twelvePointFoldMatrix.mulVec (twelvePointCohomologyIso u) := by
  -- WAVE 19 (audit F1, W3-B) + W2-D (run-26 :786 receipt): the conv keeps the
  -- RHS intact (`M.mulVec (iso u)` — no sum on that side to pull).  The run-26
  -- `rw [map_sum]` died on the coe-instance seam: the sum sits under the
  -- OPERATOR's application (`wordOp (∑ …)`), whose FunLike lives at the
  -- `(2 * 0)` clan while the summands are `twelvePointAnalytification 0`-typed,
  -- so `map_sum`'s `?g (∑ x ∈ ?s, ?f x)` pattern could never typecheck at
  -- instances transparency.  The fix (W1-D R4): hoist the sum-pull as a ground
  -- have at the goal's own spelling, closed in TERM mode (map_sum unifies at
  -- default transparency, once); then the iso-sum-pull, the per-point smul
  -- decomposition and the point-class equation follow as ground haves and
  -- closed-pattern rewrites, and the tail is pure `Fin 12 → ℚ` arithmetic.
  -- WAVE 28 (run-27 :996 receipt): the conv_lhs + rw [hpull] pair died —
  -- the conv-produced term's FunLike instance args differ from the have's
  -- fresh elaboration.  ONE ground have stated at the theorem statement's
  -- own spelling (the run-27-green `happ` discipline), closed entirely in
  -- TERM MODE (congrArg chain + map_sum + the iso sum-pull — each
  -- application unifies at default transparency exactly once); then a
  -- purely syntactic rw lands the goal at the per-point chain.
  have hstep : twelvePointCohomologyIso
      ((realizedWordPair twelvePointFoldWord).cohomologyOperator u) =
      ∑ k : Fin 12, twelvePointCohomologyIso
        ((realizedWordPair twelvePointFoldWord).cohomologyOperator
          (twelvePointCohomologyIso u k •
            zeroCycleClass (codimensionPointCycle twelvePointWorld.X 0
              (twelvePointPt k)))) := by
    have hd : u = ∑ k : Fin 12, (twelvePointCohomologyIso u k) •
        (zeroCycleClass (codimensionPointCycle twelvePointWorld.X 0
          (twelvePointPt k))) :=
      module_decomp u
    have h1 : twelvePointCohomologyIso
        ((realizedWordPair twelvePointFoldWord).cohomologyOperator u) =
        twelvePointCohomologyIso
          ((realizedWordPair twelvePointFoldWord).cohomologyOperator
            (∑ k : Fin 12, (twelvePointCohomologyIso u k) •
              (zeroCycleClass (codimensionPointCycle twelvePointWorld.X 0
                (twelvePointPt k))))) :=
      -- WAVE 29 (run-28 :1090 receipt): the congrArg hole was assigned
      -- `⇑twelvePointCohomologyIso` by higher-order unification (the
      -- receipt: hd expected `op u = op ∑` while hd : `u = ∑`); the
      -- function is now EXPLICIT — the iso-wrapped operator congruence
      -- h1's own TYPE demands.
      congrArg (fun x => twelvePointCohomologyIso
        ((realizedWordPair twelvePointFoldWord).cohomologyOperator x)) hd
    have h2 : twelvePointCohomologyIso
        ((realizedWordPair twelvePointFoldWord).cohomologyOperator
          (∑ k : Fin 12, (twelvePointCohomologyIso u k) •
            (zeroCycleClass (codimensionPointCycle twelvePointWorld.X 0
              (twelvePointPt k))))) =
        twelvePointCohomologyIso
          (∑ k : Fin 12, (realizedWordPair twelvePointFoldWord).cohomologyOperator
            ((twelvePointCohomologyIso u k) •
              (zeroCycleClass (codimensionPointCycle twelvePointWorld.X 0
                (twelvePointPt k))))) :=
      congrArg _ (map_sum _ _ _)
    have h3 : twelvePointCohomologyIso
          (∑ k : Fin 12, (realizedWordPair twelvePointFoldWord).cohomologyOperator
            ((twelvePointCohomologyIso u k) •
              (zeroCycleClass (codimensionPointCycle twelvePointWorld.X 0
                (twelvePointPt k))))) =
        ∑ k : Fin 12, twelvePointCohomologyIso
          ((realizedWordPair twelvePointFoldWord).cohomologyOperator
            ((twelvePointCohomologyIso u k) •
              (zeroCycleClass (codimensionPointCycle twelvePointWorld.X 0
                (twelvePointPt k))))) :=
      cohomologyIso_sum _ _
    exact h1.trans (h2.trans h3)
  rw [hstep]
  have hpts : ∀ k : Fin 12, twelvePointCohomologyIso
      ((realizedWordPair twelvePointFoldWord).cohomologyOperator
        (twelvePointCohomologyIso u k •
          zeroCycleClass (codimensionPointCycle twelvePointWorld.X 0
            (twelvePointPt k)))) =
      twelvePointCohomologyIso u k • (fun j => twelvePointFoldMatrix j k) := by
    intro k
    -- W2-D: the smul decomposition of the operator application and the iso's
    -- smullicity — ground haves at the goal's own clan, proofs in term mode
    -- (`LinearMap.map_smul`, Defs.lean:336; `cohomologyIso_smul`, in-file :633).
    have hs : (realizedWordPair twelvePointFoldWord).cohomologyOperator
        (twelvePointCohomologyIso u k •
          zeroCycleClass (codimensionPointCycle twelvePointWorld.X 0
            (twelvePointPt k))) =
        twelvePointCohomologyIso u k •
          ((realizedWordPair twelvePointFoldWord).cohomologyOperator
            (zeroCycleClass (codimensionPointCycle twelvePointWorld.X 0
              (twelvePointPt k)))) :=
      LinearMap.map_smul _ _ _
    rw [hs]
    have hism : twelvePointCohomologyIso (twelvePointCohomologyIso u k •
        ((realizedWordPair twelvePointFoldWord).cohomologyOperator
          (zeroCycleClass (codimensionPointCycle twelvePointWorld.X 0
            (twelvePointPt k))))) =
        twelvePointCohomologyIso u k • twelvePointCohomologyIso
          ((realizedWordPair twelvePointFoldWord).cohomologyOperator
            (zeroCycleClass (codimensionPointCycle twelvePointWorld.X 0
              (twelvePointPt k)))) :=
      cohomologyIso_smul _ _
    rw [hism, foldWord_op_pointClass k]
  simp only [hpts]
  funext j
  rw [Finset.sum_apply]
  simp [Matrix.mulVec, dotProduct, mul_comm] -- AUDIT-8: matrix API


/-- The fold word preserves the rational Hodge fiber at weight zero (the
fiber is maximal on the twelve-point world). -/
theorem twelvePointFoldWord_hodge
    (alpha : ClassicalHodgeFiber twelvePointWorld twelvePointHodgeData 0) :
    (realizedWordPair twelvePointFoldWord).cohomologyOperator alpha.1 ∈
      rationalHodgeSubspace (twelvePointHodgeData.hodgeBigrading 0) := by
  have htop : rationalHodgeSubspace
      (twelvePointHodgeData.hodgeBigrading 0) = ⊤ :=
    zeroFiber_eq_top -- AUDIT-6: contract lemma (`ClassicalHodgeFiber` is the
  -- `rationalHodgeSubspace` abbreviation at weight zero)
  rw [htop]
  -- WAVE 21 (run-20 arity disease): mem_top's element is implicit at the
  -- pin (Submodule/Lattice.lean:143, `lemma mem_top {x : M}`) — the term is
  -- already the full proposition; the `_` was a "Function expected".
  exact Submodule.mem_top

#check twelvePointFoldWord
#check twelvePointFoldMatrix
#check twelvePointFoldWord_op
#check twelvePointFoldWord_hodge
#print axioms twelvePointFoldWord
#print axioms twelvePointFoldMatrix
#print axioms twelvePointFoldWord_op
#print axioms twelvePointFoldWord_hodge


end GSTTwelvePointFoldWord

end -- noncomputable section
