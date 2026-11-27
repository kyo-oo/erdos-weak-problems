import HCUniverse2.GSTFinitePointHodgeData
import HCUniverse2.GSTFinitePointAnalytification
import HCUniverse2.GSTClassicalHodgeRealizedClosedCorrespondenceAlgebra
import HCUniverse2.GSTClassicalHodgeFiniteClosedCorrespondence
import HCUniverse2.GSTClassicalHodgeFiniteClosedCorrespondenceOperator
import HCUniverse2.GSTNativeCodimensionCyclePresentation
import HCUniverse2.GSTClassicalHodgeProjectiveSelfCorrespondences
import HCUniverse2.GSTClassicalHodgeProjectivePointTransport
import Mathlib

/-!
# THE GENERAL FINITE-POINT SHIFT WORD

This module lands the letter machinery of the general-N finite-point native
geometric world lane: every point-pair letter is the closed subscheme
`Spec ℂ ⟶ X ×_ℂ X` on `(point c, point r)` (the evaluation composite
`a ⊗ b ↦ (a c) * (b r)`, surjective, a closed immersion through
`IsClosedImmersion.spec_of_surjective` and the `pullbackSpecIso` inverse),
realizing exactly its matrix unit `E_{r,c}` on the point classes.

The NEW certificate word replaces the twelve-point lane's 26-letter fold
word (`Twave`, kernel-certified at run 44182950667) with the **nilpotent
shift word**: the `N − 1` unit letters `(i+1, i, 1)`.  The word operator is
the nilpotent shift matrix `S` (`S e_i = e_{i+1}`, `S^N = 0`), and the
Krylov orbit of the point-0 seed walks the standard basis
`e₀ → e₁ → … → e_{N−1} → 0` — cyclicity at every N with NO Krylov
determinant and no numeric certification.

Port disclosure: the letter machinery (section "The letter geometry" through
`lettersOf`, and the operator section through `module_decomp`) is the
CI-green twelve-point twin ported under the lane rename map
(`twelvePoint ↦ finitePoint`, `Fin 12 ↦ Fin N`, explicit `N` threading);
proof bodies are verbatim except the `N`-threading.  The shift section is
new mathematics.  External lemma names marked `AUDIT-n` are the twin's
author-wave uncertainty points; the CI lane owns the kernel check.

No `sorry`, no new axioms, no `native_decide`.
-/

set_option maxHeartbeats 70000000
set_option maxRecDepth 1000000

noncomputable section

open CategoryTheory
open AlgebraicGeometry

open scoped TensorProduct
namespace GSTFinitePointShiftWord

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
open GSTFinitePointWorldCarrier
open GSTFinitePointCohomology
open GSTFinitePointHodgeData
open GSTFinitePointAnalytification

variable (N : ℕ) [NeZero N]

/-! ## The N points and their classes

The carrier module supplies `(finitePointWorld N) : SmoothProjectiveComplexScheme`
with `(finitePointWorld N).X = Spec (.of (Fin N → ℂ))` and the point
classification `(finitePointEquiv N) : Fin N ≃ CodimensionPoint (finitePointWorld N).X 0`
(the primes `ker (eval i)`); the Hodge-data module supplies
`(finitePointHodgeData N)`, `zeroCycleClass`, `zeroCycleClass_point`,
`zeroFiber_eq_top` and `(finitePointCohomologyIso N)`.
-/

/-- **AUDIT-1 (carrier bridge).** The `i`-th point IS the prime
`ker (eval i)` of `ℂ¹²`.  Both sides are `comap (eval i)` of a point of the
one-point space `Spec ℂ`: the left of the scheme-level `default`, the right of
the `default` baked into the carrier's `Equiv.sigmaUnique`.  The two `default`s
ride different `Unique (PrimeSpectrum ℂ)` instance paths (the scheme-level
instance of AlgebraicGeometry/Scheme.lean:627 resolves through `Field ℂ`, the
`sigmaUnique` binder through the artinian-krull-dim-zero-local chain visible to
`import Mathlib`), so the equation is closed by `Subsingleton.elim` on the
one-point `Spec ℂ` — never by a bare `rfl`. -/
theorem comap_evalRingHom_default (i : Fin N) :
    PrimeSpectrum.comap (Pi.evalRingHom (fun _ : Fin N => ℂ) i)
      (default : Spec (CommRingCat.of ℂ)) = ((finitePointEquiv N) i).1 := by
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
  have h1 : ((finitePointEquiv N) i).1 = PrimeSpectrum.comap
      (Pi.evalRingHom (fun _ : Fin N => ℂ) i)
      ((Equiv.sigmaUnique (Fin N) (fun _ => PrimeSpectrum ℂ)).symm i).2 := by
    first
    | rfl
    | simp only [Equiv.trans_apply, Equiv.sigmaUnique_symm_apply,
        Homeomorph.coe_toEquiv, PrimeSpectrum.sigmaToPiHomeo_apply,
        PrimeSpectrum.sigmaToPi_apply, Equiv.subtypeUnivEquiv_symm_apply]
  exact (congrArg (PrimeSpectrum.comap (Pi.evalRingHom (fun _ : Fin N => ℂ) i))
    (hdfl _ _)).trans h1.symm

/-! ## The letter geometry: the point-pair subscheme -/

/-- The evaluation algebra map of the point pair: `a ⊗ b ↦ (a c) * (b r)`. -/
noncomputable def pointPairAlgHom (r c : Fin N) :
    (Fin N → ℂ) ⊗[ℂ] (Fin N → ℂ) →ₐ[ℂ] ℂ :=
  (Algebra.TensorProduct.rid ℂ ℂ ℂ).toAlgHom.comp
    (Algebra.TensorProduct.map
      (Pi.evalAlgHom ℂ (fun _ : Fin N => ℂ) c)
      (Pi.evalAlgHom ℂ (fun _ : Fin N => ℂ) r))

/-- The point-pair ring map is surjective: preimage of `x` is
`Pi.single c x ⊗ₜ 1`. -/
theorem pointPairAlgHom_surjective (r c : Fin N) :
    Function.Surjective (pointPairAlgHom N r c) := by
  intro x
  refine ⟨Pi.single c x ⊗ₜ[ℂ] 1, ?_⟩
  show pointPairAlgHom N r c (Pi.single c x ⊗ₜ[ℂ] 1) = x
  -- AUDIT-2 (tensor API): `map_tmul`/`rid_tmul`/`Pi.single_apply` names.
  simp [pointPairAlgHom, Algebra.TensorProduct.map_tmul,
    Algebra.TensorProduct.rid_tmul, Pi.single_apply, mul_one]

/-- The closed point-pair subscheme `Spec ℂ ⟶ X ×_ℂ X` selecting
`(point c, point r)`. -/
noncomputable def pointPairMap (r c : Fin N) :
    Spec (CommRingCat.of ℂ) ⟶ selfProduct (finitePointWorld N) :=
  Spec.map (CommRingCat.ofHom (pointPairAlgHom N r c).toRingHom) ≫
    (pullbackSpecIso ℂ (Fin N → ℂ) (Fin N → ℂ)).inv

/-- Ring-hom form of the left leg: evaluate at the column point. -/
theorem pointPair_left_hom (r c : Fin N) :
    (pointPairAlgHom N r c).toRingHom.comp
      (algebraMap (Fin N → ℂ)
        ((Fin N → ℂ) ⊗[ℂ] (Fin N → ℂ))) =
      Pi.evalRingHom (fun _ : Fin N => ℂ) c := by
  apply RingHom.ext
  intro a
  show pointPairAlgHom N r c
      (algebraMap (Fin N → ℂ) ((Fin N → ℂ) ⊗[ℂ] (Fin N → ℂ)) a) =
    Pi.evalRingHom (fun _ : Fin N => ℂ) c a
  have htm : algebraMap (Fin N → ℂ) ((Fin N → ℂ) ⊗[ℂ] (Fin N → ℂ)) a =
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
theorem pointPair_right_hom (r c : Fin N) :
    (pointPairAlgHom N r c).toRingHom.comp
      (Algebra.TensorProduct.includeRight
        (R := ℂ) (A := Fin N → ℂ) (B := Fin N → ℂ)).toRingHom =
      Pi.evalRingHom (fun _ : Fin N => ℂ) r := by
  apply RingHom.ext
  intro a
  show pointPairAlgHom N r c
      (Algebra.TensorProduct.includeRight
        (R := ℂ) (A := Fin N → ℂ) (B := Fin N → ℂ) a) =
    Pi.evalRingHom (fun _ : Fin N => ℂ) r a
  have htm : Algebra.TensorProduct.includeRight
      (R := ℂ) (A := Fin N → ℂ) (B := Fin N → ℂ) a = 1 ⊗ₜ[ℂ] a := rfl -- AUDIT-3
  rw [htm]
  -- AUDIT-2 + W2-A: as the left leg (R1-8); `one_mul` covers the
  -- `rid_tmul` smul `(a r) • 1 → (a r) * 1` spelling.
  simp [pointPairAlgHom, Algebra.TensorProduct.map_tmul,
    Algebra.TensorProduct.rid_tmul, Pi.evalAlgHom_apply, Pi.evalRingHom_apply,
    one_mul]

/-- The left leg of the point pair is evaluation at the column point. -/
theorem pointPair_left (r c : Fin N) :
    pointPairMap N r c ≫ fst (finitePointWorld N) =
      Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun _ : Fin N => ℂ) c)) := by
  -- WAVE 29 (run-28 :228 receipt): the calc's Trans synthesis died on the
  -- continuation geometry (the step-2 LHS at col 5 under the step-1 LHS at
  -- col 8 — the colGe law).  Mechanism switch per the no-re-roll law: the
  -- run-27-green `happ` discipline — ground haves at the goal's own
  -- spelling, each closed by ONE term-mode application, composed by
  -- Eq.trans.  No calc parser anywhere in the chain.
  show (Spec.map (CommRingCat.ofHom (pointPairAlgHom N r c).toRingHom) ≫
      (pullbackSpecIso ℂ (Fin N → ℂ) (Fin N → ℂ)).inv) ≫ fst (finitePointWorld N) = _
  have h1 : (Spec.map (CommRingCat.ofHom (pointPairAlgHom N r c).toRingHom) ≫
        (pullbackSpecIso ℂ (Fin N → ℂ) (Fin N → ℂ)).inv) ≫ fst (finitePointWorld N) =
      Spec.map (CommRingCat.ofHom (pointPairAlgHom N r c).toRingHom) ≫
        ((pullbackSpecIso ℂ (Fin N → ℂ) (Fin N → ℂ)).inv ≫ fst (finitePointWorld N)) :=
    CategoryTheory.Category.assoc _ _ _
  have h2 : Spec.map (CommRingCat.ofHom (pointPairAlgHom N r c).toRingHom) ≫
        ((pullbackSpecIso ℂ (Fin N → ℂ) (Fin N → ℂ)).inv ≫ fst (finitePointWorld N)) =
      Spec.map (CommRingCat.ofHom (pointPairAlgHom N r c).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (Fin N → ℂ)
          ((Fin N → ℂ) ⊗[ℂ] (Fin N → ℂ)))) :=
    congrArg _ (pullbackSpecIso_inv_fst' ℂ (Fin N → ℂ) (Fin N → ℂ))
  have h3 : Spec.map (CommRingCat.ofHom (pointPairAlgHom N r c).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (Fin N → ℂ)
          ((Fin N → ℂ) ⊗[ℂ] (Fin N → ℂ)))) =
      Spec.map (CommRingCat.ofHom ((pointPairAlgHom N r c).toRingHom.comp
        (algebraMap (Fin N → ℂ) ((Fin N → ℂ) ⊗[ℂ] (Fin N → ℂ))))) :=
    (Spec.map_comp _ _).symm
  have h4 : Spec.map (CommRingCat.ofHom ((pointPairAlgHom N r c).toRingHom.comp
        (algebraMap (Fin N → ℂ) ((Fin N → ℂ) ⊗[ℂ] (Fin N → ℂ))))) =
      Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun _ : Fin N => ℂ) c)) :=
    congrArg Spec.map (congrArg CommRingCat.ofHom (pointPair_left_hom N r c))
  exact h1.trans (h2.trans (h3.trans h4))

/-- The right leg of the point pair is evaluation at the row point. -/
theorem pointPair_right (r c : Fin N) :
    pointPairMap N r c ≫ snd (finitePointWorld N) =
      Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun _ : Fin N => ℂ) r)) := by
  -- WAVE 29 (run-28 :259 receipt): the snd twin of pointPair_left's
  -- Trans death — same mechanism switch (have-chain + Eq.trans).
  show (Spec.map (CommRingCat.ofHom (pointPairAlgHom N r c).toRingHom) ≫
      (pullbackSpecIso ℂ (Fin N → ℂ) (Fin N → ℂ)).inv) ≫ snd (finitePointWorld N) = _
  have h1 : (Spec.map (CommRingCat.ofHom (pointPairAlgHom N r c).toRingHom) ≫
        (pullbackSpecIso ℂ (Fin N → ℂ) (Fin N → ℂ)).inv) ≫ snd (finitePointWorld N) =
      Spec.map (CommRingCat.ofHom (pointPairAlgHom N r c).toRingHom) ≫
        ((pullbackSpecIso ℂ (Fin N → ℂ) (Fin N → ℂ)).inv ≫ snd (finitePointWorld N)) :=
    CategoryTheory.Category.assoc _ _ _
  have h2 : Spec.map (CommRingCat.ofHom (pointPairAlgHom N r c).toRingHom) ≫
        ((pullbackSpecIso ℂ (Fin N → ℂ) (Fin N → ℂ)).inv ≫ snd (finitePointWorld N)) =
      Spec.map (CommRingCat.ofHom (pointPairAlgHom N r c).toRingHom) ≫
        Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight
            (R := ℂ) (A := Fin N → ℂ) (B := Fin N → ℂ)).toRingHom) :=
    congrArg _ (pullbackSpecIso_inv_snd ℂ (Fin N → ℂ) (Fin N → ℂ))
  have h3 : Spec.map (CommRingCat.ofHom (pointPairAlgHom N r c).toRingHom) ≫
        Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight
            (R := ℂ) (A := Fin N → ℂ) (B := Fin N → ℂ)).toRingHom) =
      Spec.map (CommRingCat.ofHom ((pointPairAlgHom N r c).toRingHom.comp
          (Algebra.TensorProduct.includeRight
            (R := ℂ) (A := Fin N → ℂ) (B := Fin N → ℂ)).toRingHom)) :=
    (Spec.map_comp _ _).symm
  have h4 : Spec.map (CommRingCat.ofHom ((pointPairAlgHom N r c).toRingHom.comp
          (Algebra.TensorProduct.includeRight
            (R := ℂ) (A := Fin N → ℂ) (B := Fin N → ℂ)).toRingHom)) =
      Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun _ : Fin N => ℂ) r)) :=
    congrArg Spec.map (congrArg CommRingCat.ofHom (pointPair_right_hom N r c))
  exact h1.trans (h2.trans (h3.trans h4))

/-- Point-level action of the left leg: every carrier point lands on the
column point. -/
theorem pointPair_left_apply (r c : Fin N) (z : Spec (CommRingCat.of ℂ)) :
    (pointPairMap N r c ≫ fst (finitePointWorld N)) z = ((finitePointEquiv N) c).1 := by
  rw [pointPair_left N]
  show PrimeSpectrum.comap (Pi.evalRingHom (fun _ : Fin N => ℂ) c) z = _
  rw [Subsingleton.elim z default]
  exact comap_evalRingHom_default N c

/-- Point-level action of the right leg: the unique carrier point lands on
the row point. -/
theorem pointPair_right_apply (r c : Fin N) (z : Spec (CommRingCat.of ℂ)) :
    (pointPairMap N r c ≫ snd (finitePointWorld N)) z = ((finitePointEquiv N) r).1 := by
  rw [pointPair_right N]
  show PrimeSpectrum.comap (Pi.evalRingHom (fun _ : Fin N => ℂ) r) z = _
  rw [Subsingleton.elim z default]
  exact comap_evalRingHom_default N r

/-! ## The residue degree of the right leg -/

/-- Evaluation at one point of `ℂ¹²` is surjective. -/
theorem evalRingHom_surjective (r : Fin N) :
    Function.Surjective (Pi.evalRingHom (fun _ : Fin N => ℂ) r) := by
  intro x
  exact ⟨Pi.single r x, by simp [Pi.single_apply]⟩

/-- `Spec` of a surjective evaluation map is an open immersion: the kernel is
generated by the idempotent `1 - Pi.single r 1`. -/
theorem isOpenImmersion_spec_map_eval (r : Fin N) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (Pi.evalRingHom (fun _ : Fin N => ℂ) r))) := by
  rw [isOpenImmersion_SpecMap_iff_of_surjective _ (evalRingHom_surjective N r)]
  refine ⟨1 - Pi.single r 1, ?_, ?_⟩
  · show (1 - Pi.single r 1) * (1 - Pi.single r 1) = 1 - Pi.single r 1
    funext i
    by_cases hi : i = r
    · simp [hi, Pi.single_apply]
    · simp [hi, Pi.single_apply]
  · show RingHom.ker (Pi.evalRingHom (fun _ : Fin N => ℂ) r) =
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
theorem residueDegree_spec_map_eval (r : Fin N) :
    Scheme.Hom.residueDegree
        (Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun _ : Fin N => ℂ) r)))
        (default : Spec (CommRingCat.of ℂ)) = 1 := by
  haveI hoi : IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (Pi.evalRingHom (fun _ : Fin N => ℂ) r))) :=
    isOpenImmersion_spec_map_eval N r
  have hsurj : Function.Surjective (Scheme.Hom.residueFieldMap
      (Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun _ : Fin N => ℂ) r)))
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
      ((Spec (CommRingCat.of (Fin N → ℂ))).residueField
        ((Spec.map (CommRingCat.ofHom
          (Pi.evalRingHom (fun _ : Fin N => ℂ) r)))
          (default : Spec (CommRingCat.of ℂ))))
      ((Spec (CommRingCat.of ℂ)).residueField
        (default : Spec (CommRingCat.of ℂ))) :=
    (Scheme.Hom.residueFieldMap
      (Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun _ : Fin N => ℂ) r)))
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
            (Pi.evalRingHom (fun _ : Fin N => ℂ) r)))
          (default : Spec (CommRingCat.of ℂ)) a := by
        rw [Algebra.smul_def, mul_one]
        rfl
       Scheme.Hom.residueFieldMap
           (Spec.map (CommRingCat.ofHom
             (Pi.evalRingHom (fun _ : Fin N => ℂ) r)))
           (default : Spec (CommRingCat.of ℂ)) a
      = w := ha

/-- The right-leg residue weight at the unique carrier point is `1`. -/
theorem pointPair_residueWeight (r c : Fin N) :
    pointResidueWeight (pointPairMap N r c ≫ snd (finitePointWorld N))
        (default : Spec (CommRingCat.of ℂ)) = 1 := by
  -- WAVE 27 (run-26 :302): the show's residueDegree fixes the implicit
  -- Y := (finitePointWorld N).X; after `rw [pointPair_right]` the morphism
  -- becomes `Spec.map …` whose codomain is spelled `Spec (of ℂ¹²)` — the
  -- residueDegree_spec_map_eval pattern (elaborated at that spelling) can
  -- never cross the non-reducible `(finitePointWorld N).X` def.  Ground the
  -- lemma at the Spec-spelling (where its own pattern matches itself),
  -- then close at default transparency where the carrier's X unfolds.
  have hrd : (Scheme.Hom.residueDegree
      (Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun _ : Fin N => ℂ) r)))
      (default : Spec (CommRingCat.of ℂ)) : ℚ) = 1 := by
    rw [residueDegree_spec_map_eval N]
    rfl
  show (Scheme.Hom.residueDegree
      (pointPairMap N r c ≫ snd (finitePointWorld N))
      (default : Spec (CommRingCat.of ℂ)) : ℚ) = 1
  rw [pointPair_right N]
  exact hrd

/-! ## The finite closed correspondence of one point pair -/

open Classical in
/-- The finite left-fiber sets of the point pair. -/
theorem pointPair_leftFiberSet_eq (r c : Fin N) (x : (finitePointWorld N).X) :
    ({z : Spec (CommRingCat.of ℂ) |
        (pointPairMap N r c ≫ fst (finitePointWorld N)) z = x} : Set _) =
      if ((finitePointEquiv N) c).1 = x then
        {(default : Spec (CommRingCat.of ℂ))} else ∅ := by
  -- WAVE 27 (run-26 :311/:312): `open Classical in` above the docstring
  -- supplies propDecidable for the point-equality ite (the wave-23 law —
  -- HodgeData:239-243 idiom); the singleton is parenthesized so it is a
  -- Set literal, not a PrimeSpectrum structure instance.
  by_cases hx : ((finitePointEquiv N) c).1 = x
  · rw [if_pos hx]
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    -- WAVE 27 (latent L1): compose pointPair_left_apply with hx — the bare
    -- application proves `… = ((finitePointEquiv N) c).1`, the iff-LHS is
    -- `… = x`; rewrite the goal to the equiv spelling first (the :362 idiom).
    rw [← hx]
    exact iff_of_true (pointPair_left_apply N r c z)
      (Subsingleton.elim z default)
  · rw [if_neg hx]
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false]
    -- WAVE 27 (latent L2): the goal is an IFF, not a function — intro is
    -- dead; iff_of_false with the composed disproof.
    exact iff_of_false
      (fun hleft => hx ((pointPair_left_apply N r c z).symm.trans hleft))
      False.elim

/-- The genuine finite closed correspondence of the point pair:
`Spec ℂ` closed-immersed into `X ×_ℂ X` on `(point c, point r)`. -/
noncomputable def pointPairGeometry (r c : Fin N) :
    FiniteClosedCorrespondence (finitePointWorld N) where
  carrier := Spec (CommRingCat.of ℂ)
  intoProduct := pointPairMap N r c
  closedImmersion := by
    -- WAVE 27 (run-26 :331): `IsClosedImmersion.comp` is an instance with
    -- the two morphisms explicit (ClosedImmersion.lean:86); bare
    -- `exact IsClosedImmersion.comp _ _` leaves ?f ?g as metavars the
    -- instance search cannot resolve.  The `show` pins the goal to the
    -- composite spelling (pointPairMap delta-unfolds at default);
    -- unification then assigns f/g from the goal and finds h1/h2 in the
    -- instance cache.
    show IsClosedImmersion (Spec.map
        (CommRingCat.ofHom (pointPairAlgHom N r c).toRingHom) ≫
          (pullbackSpecIso ℂ (Fin N → ℂ) (Fin N → ℂ)).inv)
    haveI h1 : IsClosedImmersion (Spec.map
        (CommRingCat.ofHom (pointPairAlgHom N r c).toRingHom)) :=
      IsClosedImmersion.spec_of_surjective _
        (pointPairAlgHom_surjective N r c)
    haveI h2 : IsClosedImmersion
        ((pullbackSpecIso ℂ (Fin N → ℂ) (Fin N → ℂ)).inv) := inferInstance
    exact IsClosedImmersion.comp _ _

  leftFiber_finite := by
    intro x
    rw [pointPair_leftFiberSet_eq N r c x]
    by_cases hx : ((finitePointEquiv N) c).1 = x
    · rw [if_pos hx]; exact Set.finite_singleton _
    · rw [if_neg hx]; exact Set.finite_empty


/-- The point-pair carrier is the one-point `Spec ℂ` — inhabited and
subsingleton by the field structure.  WAVE 28 (run-27 :477 receipt): the
def-projection `(pointPairGeometry N r c).carrier` blocks instance search, so
the instances are provided explicitly, with proofs crossing the structure
field's delta once (default transparency). -/
instance pointPairGeometry_carrier_inhabited (r c : Fin N) :
    Inhabited ↥(pointPairGeometry N r c).carrier :=
  ⟨(default : Spec (CommRingCat.of ℂ))⟩

instance pointPairGeometry_carrier_subsingleton (r c : Fin N) :
    Subsingleton ↥(pointPairGeometry N r c).carrier :=
  inferInstanceAs (Subsingleton ↥(Spec (CommRingCat.of ℂ)))

/-- The left fiber of the point pair over a source point which IS the column
point is the singleton fiber of the unique carrier point. -/
theorem pointPair_leftFiberFinset_eq_singleton (r c : Fin N)
    (x : CodimensionPoint (finitePointWorld N).X 0)
    (h : ((finitePointEquiv N) c).1 = x.1) :
    (pointPairGeometry N r c).leftFiberFinset x.1 =
      {(default : Spec (CommRingCat.of ℂ))} := by
  ext z
  simp only [mem_leftFiberFinset, Finset.mem_singleton]
  rw [← h]
  -- WAVE 29 (run-28 :538 receipt): the goal's RHS is Finset-membership
  -- `z ∈ {default}` (Finset.mem_singleton never fired as a rewrite — the
  -- unused-arg receipt); the second iff_of_true argument must be a TERM of
  -- exactly that membership type, built by mem_singleton's .mpr.
  exact iff_of_true (pointPair_left_apply N r c z)
    (Finset.mem_singleton.mpr (Subsingleton.elim z default))

/-- The left fiber over any other source point is empty. -/
theorem pointPair_leftFiberFinset_eq_empty (r c : Fin N)
    (x : CodimensionPoint (finitePointWorld N).X 0)
    (h : ((finitePointEquiv N) c).1 ≠ x.1) :
    (pointPairGeometry N r c).leftFiberFinset x.1 = ∅ := by
  ext z
  simp only [mem_leftFiberFinset, Finset.notMem_empty]
  -- WAVE 27 (run-26 :373): `intro hz` is dead on the IFF goal
  -- `left z = ↑x ↔ False`; close with iff_of_false.
  exact iff_of_false
    (fun hleft => h ((pointPair_left_apply N r c z).symm.trans hleft))
    False.elim

/-- The coheight of the right image of the unique carrier point is zero. -/
theorem pointPair_right_coheight (r c : Fin N) :
    Order.coheight
        ((pointPairMap N r c ≫ snd (finitePointWorld N))
          (default : Spec (CommRingCat.of ℂ))) = 0 := by
  rw [pointPair_right_apply N]
  exact ((finitePointEquiv N) r).2

/-- Over the column point, the transition is the single atom at the row
point with residue weight one. -/
theorem pointPair_transition_eq (r c : Fin N)
    (x : CodimensionPoint (finitePointWorld N).X 0)
    (h : ((finitePointEquiv N) c).1 = x.1) :
    (pointPairGeometry N r c).transition 0 x =
      Finsupp.single ((finitePointPt N) r) 1 := by
  have hfin : (pointPairGeometry N r c).leftFiberFinset x.1 =
      {(default : Spec (CommRingCat.of ℂ))} :=
    pointPair_leftFiberFinset_eq_singleton N r c x h
  -- WAVE 29 (run-28 :588 receipt): the whole atom chain was frankensteined
  -- across the two default spellings — the scheme-level `default` inside a
  -- carrier-typed slot left the post-rw goal not type-correct at implicit
  -- transparency (the full-error note), killing the targetAtomPresentation
  -- rewrite.  Every term of the chain is now stated at the CARRIER type
  -- (the pointPairGeometry_carrier_inhabited default), each seam crossing
  -- done once in term mode inside its own have.
  have hz : Order.coheight
      ((pointPairGeometry N r c).right
        (default : ↥(pointPairGeometry N r c).carrier)) = 0 :=
    pointPair_right_coheight N r c
  show ((pointPairGeometry N r c).leftFiberFinset x.1).sum
      ((pointPairGeometry N r c).targetAtomPresentation 0) = _
  -- WAVE 30 (run-29 :576 receipt): the outer rw [hfin] consumed the
  -- leftFiberFinset pattern before rw [hsum] could fire (the receipt's
  -- goal was already the scheme-spelled singleton — not type-correct at
  -- implicit).  The hsum rewrite alone carries the goal from the show's
  -- own spelling straight to the carrier-spelled atom — well-typed
  -- throughout.
  have hsum : ((pointPairGeometry N r c).leftFiberFinset x.1).sum
      ((pointPairGeometry N r c).targetAtomPresentation 0) =
      (pointPairGeometry N r c).targetAtomPresentation 0
        (default : ↥(pointPairGeometry N r c).carrier) := by
    rw [hfin]
    exact Finset.sum_singleton _ _
  rw [hsum]
  rw [FiniteClosedCorrespondence.targetAtomPresentation_eq_single
    (pointPairGeometry N r c) 0 (default : ↥(pointPairGeometry N r c).carrier) hz]
  have hrw : pointResidueWeight (pointPairGeometry N r c).right
      (default : ↥(pointPairGeometry N r c).carrier) = 1 :=
    pointPair_residueWeight N r c
  rw [hrw]
  -- the atom point is the row twelve-point
  have hr : (pointPairGeometry N r c).right
      (default : ↥(pointPairGeometry N r c).carrier) = ((finitePointEquiv N) r).1 :=
    pointPair_right_apply N r c default
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
  -- `Finsupp.single ⟨pt, hz⟩ 1 = Finsupp.single ((finitePointPt N) r) 1`.
  -- Rewrite the whole element at once -- hz travels INSIDE the rewritten
  -- subterm, so the congrArg motive `fun _e => Finsupp.single _e 1 = _` is
  -- well-typed by construction.  `Subtype.ext hr` is a pure term-mode seam:
  -- `((finitePointPt N) r).1` is the abbrev's `.1`, definitionally
  -- `((finitePointEquiv N) r).1`, exactly hr's right-hand side.
  have hsub : (⟨(pointPairGeometry N r c).right
      (default : ↥(pointPairGeometry N r c).carrier), hz⟩ :
      CodimensionPoint (finitePointWorld N).X 0) = (finitePointPt N) r :=
    Subtype.ext hr
  exact congrArg (fun k => Finsupp.single k (1 : ℚ)) hsub

/-- Over the column point, the native image is exactly the row point cycle. -/
theorem pointPair_nativePointImage_eq (r c : Fin N)
    (x : CodimensionPoint (finitePointWorld N).X 0)
    (h : ((finitePointEquiv N) c).1 = x.1) :
    (pointPairGeometry N r c).nativePointImage 0 x =
      codimensionPointCycle (finitePointWorld N).X 0 ((finitePointPt N) r) := by
  show realizeFiniteCodimensionPresentation (finitePointWorld N).X 0
      ((pointPairGeometry N r c).transition 0 x) = _
  rw [pointPair_transition_eq N r c x h]
  rw [realizeFiniteCodimensionPresentation_single]
  exact one_smul _ _

/-- Over any other source point, the native image is the zero cycle. -/
theorem pointPair_nativePointImage_eq_zero (r c : Fin N)
    (x : CodimensionPoint (finitePointWorld N).X 0)
    (h : ((finitePointEquiv N) c).1 ≠ x.1) :
    (pointPairGeometry N r c).nativePointImage 0 x = 0 := by
  have hfin : (pointPairGeometry N r c).leftFiberFinset x.1 = ∅ :=
    pointPair_leftFiberFinset_eq_empty N r c x h
  show realizeFiniteCodimensionPresentation (finitePointWorld N).X 0
      ((pointPairGeometry N r c).transition 0 x) = _
  have htr : (pointPairGeometry N r c).transition 0 x = 0 := by
    show ((pointPairGeometry N r c).leftFiberFinset x.1).sum
        ((pointPairGeometry N r c).targetAtomPresentation 0) = _
    rw [hfin, Finset.sum_empty]
  rw [htr]
  exact realizeFiniteCodimensionPresentation_zero (finitePointWorld N).X 0

/-! ## The letter operator: the matrix unit -/

/-- The `r`-th indicator map on the twelve coordinate vectors. -/
noncomputable def matrixUnitIndicator (r c : Fin N) :
    (Fin N → ℚ) →ₗ[ℚ] (Fin N → ℚ) where
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
noncomputable def matrixUnitOp (r c : Fin N) :
    RationalSingularCohomology (finitePointHodgeData N).analytification 0 →ₗ[ℚ]
      RationalSingularCohomology (finitePointHodgeData N).analytification 0 :=
  LinearMap.comp ((finitePointCohomologyIso N).symm.toLinearMap)
    (LinearMap.comp (matrixUnitIndicator N r c)
      (finitePointCohomologyIso N).toLinearMap)

theorem matrixUnitOp_apply (r c : Fin N)
    (u : RationalSingularCohomology (finitePointHodgeData N).analytification 0) :
    (finitePointCohomologyIso N) (matrixUnitOp N r c u) =
      fun k => if k = r then (finitePointCohomologyIso N) u c else 0 := by
  show (finitePointCohomologyIso N)
      ((finitePointCohomologyIso N).symm
        (matrixUnitIndicator N r c ((finitePointCohomologyIso N) u))) = _
  -- WAVE 19 (pre-emptive, W1-D R1): the post-show goal is
  -- `iso (iso.symm X) = X`-shaped (the symm is applied FIRST) — the correct
  -- lemma is `LinearEquiv.apply_symm_apply : e (e.symm x) = x`;
  -- `symm_apply_apply : e.symm (e x) = x` is the wrong direction and its
  -- `e.symm`-headed pattern can never match.
  rw [LinearEquiv.apply_symm_apply]
  rfl

/-- The matrix unit sends the `i`-th point class to the `r`-th indicator when
`i` is the column, and to zero otherwise. -/
theorem matrixUnitOp_pointClass (r c i : Fin N) :
    (finitePointCohomologyIso N) (matrixUnitOp N r c
        (zeroCycleClass N (codimensionPointCycle (finitePointWorld N).X 0
          ((finitePointPt N) i)))) =
      if c = i then Pi.single r (1 : ℚ) else 0 := by
  -- WAVE 27 (run-26 :484:6, W1-D R4/R5 -- the have-hoist): the bare
  -- `rw [matrixUnitOp_apply]` dies at the coe-instance seam -- kabstract
  -- assigns `?u := zeroCycleClass …` and then re-checks the application's
  -- type at `implicit` transparency, where
  -- `(finitePointHodgeData N).analytification` (a projection on a plain def)
  -- is stuck against `(finitePointAnalytification N)`.  Hoist the lemma as a
  -- ground have whose TYPE is the goal's own spelling (the application
  -- elaborates once, at default transparency, in term mode) and rewrite
  -- with the have -- the match is then purely syntactic.
  have happ : (finitePointCohomologyIso N) (matrixUnitOp N r c
      (zeroCycleClass N (codimensionPointCycle (finitePointWorld N).X 0
        ((finitePointPt N) i)))) =
      fun k => if k = r then (finitePointCohomologyIso N)
        (zeroCycleClass N (codimensionPointCycle (finitePointWorld N).X 0
          ((finitePointPt N) i))) c else 0 :=
    matrixUnitOp_apply N r c _
  rw [happ]
  -- WAVE 19 (pre-emptive, W1-D R2): the AUDIT-6 contract lemma's LHS is
  -- stated over HodgeData's `def (finitePointPt N)` (stuck at instances
  -- transparency) while this goal carries the FoldWord `abbrev
  -- (finitePointPt N)` -- bridge it with a `show … from` restatement at the
  -- abbrev spelling (elaborator-level defeq on the from-term, syntactic
  -- match on the rewrite).
  rw [show (finitePointCohomologyIso N) (zeroCycleClass N (codimensionPointCycle
      (finitePointWorld N).X 0 ((finitePointPt N) i))) = Pi.single i (1 : ℚ) from
    zeroCycleClass_point N i]
  funext k
  by_cases hk : k = r <;> by_cases hi : c = i <;>
    simp [hk, hi, Pi.single_apply]

/-! ## The realization theorem -/

/-- The point pair realizes exactly its matrix unit on all point classes. -/
theorem pointPairGeometry_realizes (r c : Fin N) :
    (pointPairGeometry N r c).RealizesAmbientOnPoints
        (H := (finitePointHodgeData N)) (p := 0) (matrixUnitOp N r c) := by
  intro x
  -- every codimension-0 point is one of the twelve
  obtain ⟨i, hi⟩ := (finitePointEquiv N).surjective x -- AUDIT-7: `(finitePointEquiv N)`
  subst hi
  by_cases hic : i = c
  · -- WAVE 27 (run-26 :503/:534, W1-D R6 -- the wave-25 subst receipt):
    -- `subst hic` would eliminate the RHS variable `c` and kill every
    -- later `c` reference.  Rewrite the goal instead -- subst-free, both
    -- binders stay alive, the case hypothesis is consumed syntactically.
    rw [hic]
    have hc : ((finitePointEquiv N) c).1 = ((finitePointEquiv N) c).1 := rfl
    have himg := pointPair_nativePointImage_eq N r c ((finitePointEquiv N) c) hc
    show (finitePointHodgeData N).cycleClass 0
        ((pointPairGeometry N r c).nativePointImage 0 ((finitePointEquiv N) c)) = _
    rw [himg]
    have key : (finitePointCohomologyIso N)
        (matrixUnitOp N r c (zeroCycleClass N
          (codimensionPointCycle (finitePointWorld N).X 0 ((finitePointPt N) c)))) =
        (finitePointCohomologyIso N) (zeroCycleClass N
          (codimensionPointCycle (finitePointWorld N).X 0 ((finitePointPt N) r))) := by
      rw [matrixUnitOp_pointClass N r c c]
      rw [if_pos rfl]
      -- WAVE 19 (pre-emptive, W1-D R2): same HodgeData `def`/FoldWord `abbrev`
      -- `(finitePointPt N)` seam as matrixUnitOp_pointClass's proof -- restate the
      -- contract lemma at the abbrev spelling.
      rw [show (finitePointCohomologyIso N) (zeroCycleClass N (codimensionPointCycle
          (finitePointWorld N).X 0 ((finitePointPt N) r))) = Pi.single r (1 : ℚ) from
        zeroCycleClass_point N r]
    -- WAVE 29 (run-28 :745/:746 receipts): the calc mechanism died on this
    -- chain in two consecutive waves (wave 27 :534, wave 28 :745/:746 — the
    -- parser's `true : Bool` phantom and the cycleClass-application type
    -- mismatch).  The no-re-roll law: mechanism switch — three ground haves,
    -- each stated at the previous have's own RHS spelling, each closed by a
    -- single term-mode application; composed by Eq.trans.  The WAVE-19
    -- audit-F2 explicit `rfl` inside s2 is kept (the post-rewrite sides
    -- agree only by default-transparency defeq; rw's auto-rfl runs at
    -- reducible).
    have s1 : (finitePointHodgeData N).cycleClass 0
          (codimensionPointCycle (finitePointWorld N).X 0 ((finitePointPt N) r)) =
        (finitePointCohomologyIso N).symm ((finitePointCohomologyIso N)
          ((finitePointHodgeData N).cycleClass 0
            (codimensionPointCycle (finitePointWorld N).X 0 ((finitePointPt N) r)))) :=
      (LinearEquiv.symm_apply_apply _ _).symm
    have s2 : (finitePointCohomologyIso N).symm ((finitePointCohomologyIso N)
          ((finitePointHodgeData N).cycleClass 0
            (codimensionPointCycle (finitePointWorld N).X 0 ((finitePointPt N) r)))) =
        (finitePointCohomologyIso N).symm ((finitePointCohomologyIso N)
          (matrixUnitOp N r c (zeroCycleClass N
            (codimensionPointCycle (finitePointWorld N).X 0 ((finitePointPt N) c))))) :=
      by rw [key]; rfl
    have s3 : (finitePointCohomologyIso N).symm ((finitePointCohomologyIso N)
          (matrixUnitOp N r c (zeroCycleClass N
            (codimensionPointCycle (finitePointWorld N).X 0 ((finitePointPt N) c))))) =
        matrixUnitOp N r c (zeroCycleClass N
          (codimensionPointCycle (finitePointWorld N).X 0 ((finitePointPt N) c))) :=
      LinearEquiv.symm_apply_apply _ _
    exact s1.trans (s2.trans s3)
  · have hne : ((finitePointEquiv N) c).1 ≠ ((finitePointEquiv N) i).1 := by
      intro h
      exact hic ((finitePointEquiv N).injective (Subtype.ext h)).symm
    have himg := pointPair_nativePointImage_eq_zero N r c ((finitePointEquiv N) i) hne
    show (finitePointHodgeData N).cycleClass 0
        ((pointPairGeometry N r c).nativePointImage 0 ((finitePointEquiv N) i)) = _
    rw [himg, map_zero]
    have hzero : matrixUnitOp N r c (zeroCycleClass N
        (codimensionPointCycle (finitePointWorld N).X 0 ((finitePointPt N) i))) = 0 := by
      -- WAVE 29 (run-28 :783 receipt): the calc's Trans synthesis died;
      -- mechanism switch as in the first arm -- ground haves at the
      -- goal's own spelling, one term-mode application each, Eq.trans
      -- composition.  Step 4 closed by the PINNED Mathlib lemma
      -- (Module/Equiv/Defs.lean:501, protected, e explicit) instead of
      -- `simp` (the OfNat instances differ across the analytification
      -- clans and simp's rfl-close is unattested).
      have z1 : matrixUnitOp N r c (zeroCycleClass N
            (codimensionPointCycle (finitePointWorld N).X 0 ((finitePointPt N) i))) =
          (finitePointCohomologyIso N).symm ((finitePointCohomologyIso N)
            (matrixUnitOp N r c (zeroCycleClass N
              (codimensionPointCycle (finitePointWorld N).X 0 ((finitePointPt N) i))))) :=
        (LinearEquiv.symm_apply_apply _ _).symm
      have z2 : (finitePointCohomologyIso N).symm ((finitePointCohomologyIso N)
            (matrixUnitOp N r c (zeroCycleClass N
              (codimensionPointCycle (finitePointWorld N).X 0 ((finitePointPt N) i))))) =
          (finitePointCohomologyIso N).symm
            (if c = i then Pi.single r (1 : ℚ) else 0) :=
        by rw [matrixUnitOp_pointClass N r c i]
      have z3 : (finitePointCohomologyIso N).symm
            (if c = i then Pi.single r (1 : ℚ) else 0) =
          (finitePointCohomologyIso N).symm 0 :=
        by rw [if_neg (fun h => hic h.symm)]
      have z4 : (finitePointCohomologyIso N).symm 0 = 0 :=
        LinearEquiv.map_zero (finitePointCohomologyIso N).symm
      exact z1.trans (z2.trans (z3.trans z4))
    -- WAVE 27 (seam hardening, W1-D R5): the goal's RHS carries the projection
    -- spellings (`(finitePointHodgeData N).cycleClass 0`, `(finitePointEquiv N) i`)
    -- while hzero's LHS carries the constant/abbrev spellings
    -- (`zeroCycleClass`, `(finitePointPt N) i`) -- defeq-only (cycleClass-0
    -- match-iota + (finitePointPt N) structure-eta + `2 * 0` Nat reduction),
    -- dead for `rw` at matching transparency.  Close in term mode: `exact`
    -- unifies once at default transparency.
    exact hzero.symm


/-! ## The letter and the 26-letter fold word -/

/-- One weighted point-pair letter: the genuine geometry plus its matrix-unit
operator plus the pointwise realization theorem. -/
noncomputable def pointPairLetter (r c : Fin N) :
    RealizedFiniteClosedCorrespondence (finitePointWorld N) (finitePointHodgeData N) 0 where
  geometry := pointPairGeometry N r c
  cohomologyOperator := matrixUnitOp N r c
  realizes_on_points := pointPairGeometry_realizes N r c
/-- The realized correspondence word induced by letter data. -/
noncomputable def lettersOf (L : List (Fin N × Fin N × ℚ)) :
    RealizedCorrespondenceWord (finitePointWorld N) (finitePointHodgeData N) 0 :=
  L.map (fun d => (d.2.2, pointPairLetter N d.1 d.2.1))
/-! ## The word operator equals the fold matrix -/

/-- Nil-case operator unfolding of the word pair. -/
theorem realizedWordPair_cohomologyOperator_nil :
    (realizedWordPair
        (lettersOf N ([] : List (Fin N × Fin N × ℚ)))).cohomologyOperator =
      0 := rfl

/-- Cons-case operator unfolding of the word pair. -/
theorem realizedWordPair_cohomologyOperator_cons (q : ℚ)
    (R : RealizedFiniteClosedCorrespondence (finitePointWorld N) (finitePointHodgeData N) 0)
    (W : RealizedCorrespondenceWord (finitePointWorld N) (finitePointHodgeData N) 0) :
    (realizedWordPair ((q, R) :: W)).cohomologyOperator =
      q • R.cohomologyOperator +
        (realizedWordPair W).cohomologyOperator := rfl

/-- **AUDIT-8 (iso linearity).** Linearity of the cohomology iso through its
linear-map structure. -/
theorem cohomologyIso_sum {ι : Type*} (s : Finset ι)
    (g : ι → RationalSingularCohomology
      (finitePointHodgeData N).analytification 0) :
    (finitePointCohomologyIso N) (∑ i ∈ s, g i) =
      ∑ i ∈ s, (finitePointCohomologyIso N) (g i) :=
    map_sum (finitePointCohomologyIso N).toLinearMap g s

theorem cohomologyIso_smul (t : ℚ)
    (v : RationalSingularCohomology (finitePointHodgeData N).analytification 0) :
    (finitePointCohomologyIso N) (t • v) = t • (finitePointCohomologyIso N) v :=
  map_smul (finitePointCohomologyIso N).toLinearMap t v

theorem cohomologyIso_zero :
    (finitePointCohomologyIso N) (0 :
      RationalSingularCohomology (finitePointHodgeData N).analytification 0) = 0 :=
  map_zero (finitePointCohomologyIso N).toLinearMap

/-- Additivity of the cohomology iso through its linear-map structure. -/
theorem cohomologyIso_add (v w : RationalSingularCohomology
      (finitePointHodgeData N).analytification 0) :
    (finitePointCohomologyIso N) (v + w) =
      (finitePointCohomologyIso N) v + (finitePointCohomologyIso N) w :=
  map_add (finitePointCohomologyIso N).toLinearMap v w

/-- The word operator acts on point classes by the letter data matrix. -/
theorem wordOp_pointClass (L : List (Fin N × Fin N × ℚ)) (i : Fin N) :
    (finitePointCohomologyIso N) ((realizedWordPair (lettersOf N L)).cohomologyOperator
        (zeroCycleClass N (codimensionPointCycle (finitePointWorld N).X 0
          ((finitePointPt N) i)))) =
      fun j => (L.map
        (fun d => if d.2.1 = i then (if j = d.1 then d.2.2 else 0) else 0)).sum := by
  induction L with
  | nil =>
    simp only [lettersOf, List.map_nil, List.sum_nil]
    -- W2-D (run-26 :665 receipt, W1-D R4/R5): the old `show` ascribed the zero
    -- operator at the PROJECTION clan (`(finitePointHodgeData N).analytification 0`)
    -- while the argument `zeroCycleClass …` lives at the CONSTANT clan
    -- (`(finitePointAnalytification N) 0`, its codomain, HodgeData:183-185) — the
    -- application stayed cross-clan, so `LinearMap.zero_apply`'s `0 ?x` pattern
    -- could never typecheck at instances transparency.  The fix: land the whole
    -- goal at the argument's own constant clan.  The `show` performs the entire
    -- nil-word reduction (iota on `realizedWordPair []` to the zero operator —
    -- CycleClassOperatorPair.zero's field is literally `0`; the zero-operator
    -- application — `LinearMap.zero_apply` is rfl, Defs.lean:793) at default
    -- transparency ONCE; the iso's value-at-zero is the single propositional
    -- step (`map_zero`), hoisted at the same clan.
    have hiso0 : (finitePointCohomologyIso N)
        (0 : RationalSingularCohomology (finitePointAnalytification N) 0) = 0 :=
      cohomologyIso_zero N
    show (finitePointCohomologyIso N)
        (0 : RationalSingularCohomology (finitePointAnalytification N) 0) =
        fun j => 0
    exact hiso0

  | cons d L ih =>
    have hword : lettersOf N (d :: L) =
        (d.2.2, pointPairLetter N d.1 d.2.1) :: lettersOf N L := rfl
    -- WAVE 19 (pre-emptive, W1-D R3): the word operator's field type spells
    -- the fiber as `(finitePointHodgeData N).analytification (2 * 0)` while the
    -- iso-side lemmas (`cohomologyIso_add`, `cohomologyIso_smul`, and
    -- `matrixUnitOp_pointClass` behind the old projection transport) are
    -- typed at the 0 spelling — the def-projection and the unreduced `2 * 0`
    -- are stuck at instances transparency, so the plain `rw`s cannot match.
    -- Hoist the three equations as ground haves at the goal's own `(2 * 0)`
    -- spelling; each application elaborates at default transparency and the
    -- `rw` chain is purely syntactic.
    have hiso : ∀ X Y : RationalSingularCohomology
        (finitePointHodgeData N).analytification (2 * 0),
        (finitePointCohomologyIso N) (X + Y) =
          (finitePointCohomologyIso N) X + (finitePointCohomologyIso N) Y :=
      fun X Y => cohomologyIso_add N X Y
    have hisosmul : ∀ (t : ℚ) (X : RationalSingularCohomology
        (finitePointHodgeData N).analytification (2 * 0)),
        (finitePointCohomologyIso N) (t • X) = t • (finitePointCohomologyIso N) X :=
      fun t X => cohomologyIso_smul N t X
    have hletter : (finitePointCohomologyIso N)
        ((pointPairLetter N d.1 d.2.1).cohomologyOperator
          (zeroCycleClass N (codimensionPointCycle (finitePointWorld N).X 0
            ((finitePointPt N) i)))) =
        if d.2.1 = i then Pi.single d.1 (1 : ℚ) else 0 :=
      matrixUnitOp_pointClass N d.1 d.2.1 i
    -- W2-D (run-26 :695 receipt, W1-D R4/R5): the post-cons-unfold goal's
    -- operator application is cross-clan (operator at `(2 * 0)`, argument at
    -- `(finitePointAnalytification N) 0`) — `LinearMap.add_apply`'s `(?f + ?g) ?x`
    -- and `LinearMap.smul_apply`'s patterns can never typecheck at instances
    -- transparency (the full-error receipt names the two clans).  Hoist BOTH
    -- decompositions of the operator application as ground haves stated at the
    -- goal's own `(2 * 0)` operator clan, closed in TERM mode (defeq at default
    -- transparency, once each); the `rw` chain below is then purely syntactic.
    -- Both lemmas are rfl at the pin (Defs.lean:835 / :751).
    have hsplit : ((d.2.2 • (pointPairLetter N d.1 d.2.1).cohomologyOperator +
        (realizedWordPair (lettersOf N L)).cohomologyOperator)
        (zeroCycleClass N (codimensionPointCycle (finitePointWorld N).X 0
          ((finitePointPt N) i)))) =
        ((d.2.2 • (pointPairLetter N d.1 d.2.1).cohomologyOperator)
          (zeroCycleClass N (codimensionPointCycle (finitePointWorld N).X 0
            ((finitePointPt N) i)))) +
        (realizedWordPair (lettersOf N L)).cohomologyOperator
          (zeroCycleClass N (codimensionPointCycle (finitePointWorld N).X 0
            ((finitePointPt N) i))) :=
      LinearMap.add_apply _ _ _
    have hsmulsplit : ((d.2.2 • (pointPairLetter N d.1 d.2.1).cohomologyOperator)
        (zeroCycleClass N (codimensionPointCycle (finitePointWorld N).X 0
          ((finitePointPt N) i)))) =
        d.2.2 • ((pointPairLetter N d.1 d.2.1).cohomologyOperator
          (zeroCycleClass N (codimensionPointCycle (finitePointWorld N).X 0
            ((finitePointPt N) i)))) :=
      LinearMap.smul_apply _ _ _
    rw [hword, realizedWordPair_cohomologyOperator_cons N]
    rw [hsplit, hiso, hsmulsplit, hisosmul, hletter, ih]

    funext j
    simp only [List.map_cons, List.sum_cons]
    by_cases hd : d.2.1 = i
    · by_cases hj : j = d.1 <;>
        simp [hd, hj, Pi.single_apply, Pi.smul_apply, smul_eq_mul]
    · by_cases hj : j = d.1 <;>
        simp [hd, hj, Pi.single_apply, Pi.smul_apply, smul_eq_mul]
/-- Every H⁰ class is the sum of its coordinates times point classes. -/
theorem module_decomp (u : RationalSingularCohomology
    (finitePointHodgeData N).analytification 0) :
    u = ∑ k : Fin N, ((finitePointCohomologyIso N) u k) •
      (zeroCycleClass N (codimensionPointCycle (finitePointWorld N).X 0
        ((finitePointPt N) k))) := by
  have hsum : (finitePointCohomologyIso N)
      (∑ k : Fin N, ((finitePointCohomologyIso N) u k) •
        (zeroCycleClass N (codimensionPointCycle (finitePointWorld N).X 0
          ((finitePointPt N) k)))) = (finitePointCohomologyIso N) u := by
    -- WAVE 19 (pre-emptive, W1-D R2+R3): the summands live at the
    -- `zeroCycleClass` codomain spelling `(finitePointAnalytification N) 0`
    -- while `cohomologyIso_sum`/`cohomologyIso_smul` are stated at the
    -- projection spelling `(finitePointHodgeData N).analytification 0` (stuck
    -- at instances transparency), and the AUDIT-6 contract lemma
    -- additionally sits across the HodgeData `def`/FoldWord `abbrev`
    -- `(finitePointPt N)` seam — hoist all three as ground haves at the
    -- summands' own spelling.
    have hsummap : (finitePointCohomologyIso N)
        (∑ k : Fin N, ((finitePointCohomologyIso N) u k) •
          (zeroCycleClass N (codimensionPointCycle (finitePointWorld N).X 0
            ((finitePointPt N) k)))) =
        ∑ k : Fin N, (finitePointCohomologyIso N)
          (((finitePointCohomologyIso N) u k) •
            (zeroCycleClass N (codimensionPointCycle (finitePointWorld N).X 0
              ((finitePointPt N) k)))) :=
      cohomologyIso_sum N _ _
    have hsmulmap : ∀ (t : ℚ) (X : RationalSingularCohomology
        (finitePointAnalytification N) 0),
        (finitePointCohomologyIso N) (t • X) = t • (finitePointCohomologyIso N) X :=
      fun t X => cohomologyIso_smul N t X
    have hpt : ∀ k : Fin N, (finitePointCohomologyIso N) (zeroCycleClass N
        (codimensionPointCycle (finitePointWorld N).X 0 ((finitePointPt N) k))) =
        Pi.single k (1 : ℚ) := fun k => zeroCycleClass_point N k
    rw [hsummap]
    simp only [hsmulmap, hpt]
    funext j
    rw [Finset.sum_apply] -- AUDIT-8
    simp [Pi.single_apply]
  -- WAVE 29 (run-28 :1032 receipt): the calc's Trans synthesis died on the
  -- continuation geometry (the step-2 LHS at col 5 under the first LHS
  -- `u` at col 8 — the colGe law).  Mechanism switch: the have-chain,
  -- composed by Eq.trans.
  have c1 : u = (finitePointCohomologyIso N).symm ((finitePointCohomologyIso N) u) :=
    (LinearEquiv.symm_apply_apply _ _).symm
  have c2 : (finitePointCohomologyIso N).symm ((finitePointCohomologyIso N) u) =
      (finitePointCohomologyIso N).symm ((finitePointCohomologyIso N)
        (∑ k : Fin N, ((finitePointCohomologyIso N) u k) •
          (zeroCycleClass N (codimensionPointCycle (finitePointWorld N).X 0
            ((finitePointPt N) k))))) :=
    congrArg _ hsum.symm
  have c3 : (finitePointCohomologyIso N).symm ((finitePointCohomologyIso N)
        (∑ k : Fin N, ((finitePointCohomologyIso N) u k) •
          (zeroCycleClass N (codimensionPointCycle (finitePointWorld N).X 0
            ((finitePointPt N) k))))) =
      ∑ k : Fin N, ((finitePointCohomologyIso N) u k) •
          (zeroCycleClass N (codimensionPointCycle (finitePointWorld N).X 0
            ((finitePointPt N) k))) :=
    LinearEquiv.symm_apply_apply _ _
  exact c1.trans (c2.trans c3)

/-! ## The nilpotent shift word -/

/-- The shift letters for columns `0 … k`, built downward from `k` (given
`k < N`): the letter `(k+1, k, 1)` rides in front whenever the successor
`k+2` exists in `Fin N`.  Structural recursion on `k`. -/
def shiftLettersDownTo (N : ℕ) : (k : ℕ) → k < N → List (Fin N × Fin N × ℚ)
  | 0, h0 => if h : 0 + 1 < N then [(⟨0 + 1, h⟩, ⟨0, h0⟩, (1 : ℚ))] else []
  | k + 1, hk =>
      if h : k + 1 + 1 < N then
        (⟨k + 1 + 1, h⟩, ⟨k + 1, hk⟩, (1 : ℚ)) ::
          shiftLettersDownTo N k (Nat.lt_of_succ_lt hk)
      else shiftLettersDownTo N k (Nat.lt_of_succ_lt hk)

/-- **THE SHIFT LETTER DATA**: one unit letter `(i+1, i, 1)` per point
whose successor exists — `N − 1` letters in all, assembled downward from
the last column. -/
def shiftWordData : (N : ℕ) → List (Fin N × Fin N × ℚ)
  | 0 => []
  | M + 1 => shiftLettersDownTo (M + 1) M (Nat.lt_succ_self M)

/-- The shift matrix: one unit at `(i+1, i)` per step (`S e_i = e_{i+1}`,
nilpotent, `S^N = 0`).  Recorded as the word's matrix; the orbit engine
below does not need it. -/
def finitePointShiftMatrix (N : ℕ) [NeZero N] : Matrix (Fin N) (Fin N) ℚ :=
  fun r c => if r.val = c.val + 1 then 1 else 0

/-- **THE SHIFT WORD**: the nilpotent shift as a genuine realized
correspondence word of `N − 1` weighted point-pair letters. -/
noncomputable def finitePointShiftWord (N : ℕ) [NeZero N] :
    RealizedCorrespondenceWord (finitePointWorld N) (finitePointHodgeData N) 0 :=
  lettersOf N (shiftWordData N)

/-- Cons-unfolding of the word operator at an arbitrary vector. -/
theorem wordOp_cons_apply (q : ℚ)
    (R : RealizedFiniteClosedCorrespondence (finitePointWorld N)
      (finitePointHodgeData N) 0)
    (W : RealizedCorrespondenceWord (finitePointWorld N)
      (finitePointHodgeData N) 0)
    (u : RationalSingularCohomology (finitePointAnalytification N) 0) :
    (realizedWordPair ((q, R) :: W)).cohomologyOperator u =
      q • R.cohomologyOperator u +
        (realizedWordPair W).cohomologyOperator u := by
  have hsplit : (q • R.cohomologyOperator +
      (realizedWordPair W).cohomologyOperator) u =
      (q • R.cohomologyOperator) u +
        (realizedWordPair W).cohomologyOperator u :=
    LinearMap.add_apply _ _ _
  have hsmulsplit : (q • R.cohomologyOperator) u =
      q • R.cohomologyOperator u :=
    LinearMap.smul_apply _ _ _
  rw [realizedWordPair_cohomologyOperator_cons, hsplit, hsmulsplit]

/-- A matrix-unit letter kills every point class off its column. -/
theorem matrixUnitOp_ptClass_eq_zero (r c i : Fin N) (h : c ≠ i) :
    (matrixUnitOp N r c)
      (zeroCycleClass N (codimensionPointCycle (finitePointWorld N).X 0
        ((finitePointPt N) i))) = 0 := by
  have z2 : (finitePointCohomologyIso N).symm
      ((finitePointCohomologyIso N)
        ((matrixUnitOp N r c)
          (zeroCycleClass N (codimensionPointCycle (finitePointWorld N).X 0
            ((finitePointPt N) i))))) =
      (finitePointCohomologyIso N).symm
        (if c = i then Pi.single r (1 : ℚ) else 0) := by
    rw [matrixUnitOp_pointClass N r c i]
  have z1 : (matrixUnitOp N r c)
      (zeroCycleClass N (codimensionPointCycle (finitePointWorld N).X 0
        ((finitePointPt N) i))) =
      (finitePointCohomologyIso N).symm
        ((finitePointCohomologyIso N)
          ((matrixUnitOp N r c)
            (zeroCycleClass N (codimensionPointCycle (finitePointWorld N).X 0
              ((finitePointPt N) i))))) :=
    (LinearEquiv.symm_apply_apply _ _).symm
  have z3 : (finitePointCohomologyIso N).symm
      (if c = i then Pi.single r (1 : ℚ) else 0) =
      (finitePointCohomologyIso N).symm 0 := by
    rw [if_neg h]
  have z4 : (finitePointCohomologyIso N).symm 0 = 0 :=
    LinearEquiv.map_zero _
  exact z1.trans (z2.trans (z3.trans z4))

/-- A matrix-unit letter carries the point class of its column to the
point class of its row. -/
theorem matrixUnitOp_ptClass_eq (r c i : Fin N) (h : c = i) :
    (matrixUnitOp N r c)
      (zeroCycleClass N (codimensionPointCycle (finitePointWorld N).X 0
        ((finitePointPt N) i))) =
      zeroCycleClass N (codimensionPointCycle (finitePointWorld N).X 0
        ((finitePointPt N) r)) := by
  have key : (finitePointCohomologyIso N)
      ((matrixUnitOp N r c)
        (zeroCycleClass N (codimensionPointCycle (finitePointWorld N).X 0
          ((finitePointPt N) i)))) =
      (finitePointCohomologyIso N)
        (zeroCycleClass N (codimensionPointCycle (finitePointWorld N).X 0
          ((finitePointPt N) r))) := by
    rw [matrixUnitOp_pointClass N r c i, if_pos h,
      zeroCycleClass_point N r]
  have s1 : zeroCycleClass N (codimensionPointCycle (finitePointWorld N).X 0
        ((finitePointPt N) r)) =
      (finitePointCohomologyIso N).symm
        ((finitePointCohomologyIso N)
          (zeroCycleClass N (codimensionPointCycle (finitePointWorld N).X 0
            ((finitePointPt N) r)))) :=
    (LinearEquiv.symm_apply_apply _ _).symm
  have s2 : (finitePointCohomologyIso N).symm
        ((finitePointCohomologyIso N)
          (zeroCycleClass N (codimensionPointCycle (finitePointWorld N).X 0
            ((finitePointPt N) r)))) =
      (finitePointCohomologyIso N).symm
        ((finitePointCohomologyIso N)
          ((matrixUnitOp N r c)
            (zeroCycleClass N (codimensionPointCycle (finitePointWorld N).X 0
              ((finitePointPt N) i))))) := by
    rw [key]
  have s3 : (finitePointCohomologyIso N).symm
        ((finitePointCohomologyIso N)
          ((matrixUnitOp N r c)
            (zeroCycleClass N (codimensionPointCycle (finitePointWorld N).X 0
              ((finitePointPt N) i))))) =
      (matrixUnitOp N r c)
        (zeroCycleClass N (codimensionPointCycle (finitePointWorld N).X 0
          ((finitePointPt N) i))) :=
    LinearEquiv.symm_apply_apply _ _
  exact (s1.trans (s2.trans s3)).symm

/-- **ABOVE THE LEVEL**: the level-`k` shift word kills every point class
of a column beyond `k`. -/
theorem shiftWord_op_ptClass_not :
    ∀ (k : ℕ) (hk : k < N) (i : Fin N), k < i.val →
    (realizedWordPair (lettersOf N (shiftLettersDownTo N k hk))).cohomologyOperator
      (zeroCycleClass N (codimensionPointCycle (finitePointWorld N).X 0
        ((finitePointPt N) i))) = 0 := by
  intro k
  induction k with
  | zero =>
      intro hk i hgt
      by_cases h1 : 0 + 1 < N
      · have hun : shiftLettersDownTo N 0 hk =
            [(⟨0 + 1, h1⟩, ⟨0, hk⟩, (1 : ℚ))] := by
          simp only [shiftLettersDownTo, dif_pos h1]
        have hword : lettersOf N [(⟨0 + 1, h1⟩, ⟨0, hk⟩, (1 : ℚ))] =
            [((1 : ℚ),
              pointPairLetter N ⟨0 + 1, h1⟩ ⟨0, hk⟩)] := rfl
        have hcol : ¬((⟨0, hk⟩ : Fin N) = i) := by
          intro hc
          have hiv : i.val = 0 := by rw [← hc]
          omega
        have hkill : (pointPairLetter N ⟨0 + 1, h1⟩ ⟨0, hk⟩).cohomologyOperator
            (zeroCycleClass N (codimensionPointCycle (finitePointWorld N).X 0
              ((finitePointPt N) i))) = 0 := by
          have hop : (pointPairLetter N ⟨0 + 1, h1⟩ ⟨0, hk⟩).cohomologyOperator =
              matrixUnitOp N ⟨0 + 1, h1⟩ ⟨0, hk⟩ := rfl
          rw [hop]
          exact matrixUnitOp_ptClass_eq_zero N ⟨0 + 1, h1⟩ ⟨0, hk⟩ i hcol
        rw [hun, hword, wordOp_cons_apply, hkill, smul_zero, zero_add]
        rfl
      · have hun : shiftLettersDownTo N 0 hk = [] := by
          simp only [shiftLettersDownTo, dif_neg h1]
        rw [hun]
        rfl
  | succ k ih =>
      intro hk i hgt
      by_cases hk2 : k + 1 + 1 < N
      · have hun : shiftLettersDownTo N (k + 1) hk =
            (⟨k + 1 + 1, hk2⟩, ⟨k + 1, hk⟩, (1 : ℚ)) ::
              shiftLettersDownTo N k (Nat.lt_of_succ_lt hk) := by
          simp only [shiftLettersDownTo, dif_pos hk2]
        have hword : lettersOf N
            ((⟨k + 1 + 1, hk2⟩, ⟨k + 1, hk⟩, (1 : ℚ)) ::
              shiftLettersDownTo N k (Nat.lt_of_succ_lt hk)) =
            ((1 : ℚ), pointPairLetter N ⟨k + 1 + 1, hk2⟩ ⟨k + 1, hk⟩) ::
              lettersOf N (shiftLettersDownTo N k (Nat.lt_of_succ_lt hk)) := rfl
        have hcol : ¬((⟨k + 1, hk⟩ : Fin N) = i) := by
          intro hc
          have hiv : i.val = k + 1 := by rw [← hc]
          omega
        have hkill : (pointPairLetter N ⟨k + 1 + 1, hk2⟩ ⟨k + 1, hk⟩).cohomologyOperator
            (zeroCycleClass N (codimensionPointCycle (finitePointWorld N).X 0
              ((finitePointPt N) i))) = 0 := by
          have hop : (pointPairLetter N ⟨k + 1 + 1, hk2⟩ ⟨k + 1, hk⟩).cohomologyOperator =
              matrixUnitOp N ⟨k + 1 + 1, hk2⟩ ⟨k + 1, hk⟩ := rfl
          rw [hop]
          exact matrixUnitOp_ptClass_eq_zero N ⟨k + 1 + 1, hk2⟩ ⟨k + 1, hk⟩ i hcol
        rw [hun, hword, wordOp_cons_apply, hkill, smul_zero, zero_add]
        exact ih (Nat.lt_of_succ_lt hk) i (by omega)
      · have hun : shiftLettersDownTo N (k + 1) hk =
            shiftLettersDownTo N k (Nat.lt_of_succ_lt hk) := by
          simp only [shiftLettersDownTo, dif_neg hk2]
        rw [hun]
        exact ih (Nat.lt_of_succ_lt hk) i (by omega)

/-- **THE POINT-CLASS ORBIT ENGINE.**  The level-`k` shift word carries
the `i`-th point class to the `(i+1)`-st whenever `i ≤ k` and the
successor exists. -/
theorem shiftWord_op_ptClass :
    ∀ (k : ℕ) (hk : k < N) (i : Fin N) (hik : i.val ≤ k) (hi : i.val + 1 < N),
    (finitePointCohomologyIso N)
      ((realizedWordPair (lettersOf N (shiftLettersDownTo N k hk))).cohomologyOperator
        (zeroCycleClass N (codimensionPointCycle (finitePointWorld N).X 0
          ((finitePointPt N) i)))) =
      Pi.single ⟨i.val + 1, hi⟩ (1 : ℚ) := by
  intro k
  induction k with
  | zero =>
      intro hk i hik hi
      have h0 : i.val = 0 := by omega
      have h1 : 0 + 1 < N := by omega
      have hun : shiftLettersDownTo N 0 hk =
          [(⟨0 + 1, h1⟩, ⟨0, hk⟩, (1 : ℚ))] := by
        simp only [shiftLettersDownTo, dif_pos h1]
      have hword : lettersOf N [(⟨0 + 1, h1⟩, ⟨0, hk⟩, (1 : ℚ))] =
          [((1 : ℚ), pointPairLetter N ⟨0 + 1, h1⟩ ⟨0, hk⟩)] := rfl
      have hci : (⟨0, hk⟩ : Fin N) = i := Fin.ext (by rw [h0])
      have hhead : (finitePointCohomologyIso N)
          ((pointPairLetter N ⟨0 + 1, h1⟩ ⟨0, hk⟩).cohomologyOperator
            (zeroCycleClass N (codimensionPointCycle (finitePointWorld N).X 0
              ((finitePointPt N) i)))) =
          (finitePointCohomologyIso N)
            (zeroCycleClass N (codimensionPointCycle (finitePointWorld N).X 0
              ((finitePointPt N) ⟨0 + 1, h1⟩))) := by
        have hop : (pointPairLetter N ⟨0 + 1, h1⟩ ⟨0, hk⟩).cohomologyOperator =
            matrixUnitOp N ⟨0 + 1, h1⟩ ⟨0, hk⟩ := rfl
        rw [hop]
        exact congrArg (finitePointCohomologyIso N)
          (matrixUnitOp_ptClass_eq N ⟨0 + 1, h1⟩ ⟨0, hk⟩ i hci)
      rw [hun, hword, wordOp_cons_apply]
      have hiso : ∀ X Y : RationalSingularCohomology
          (finitePointHodgeData N).analytification (2 * 0),
          (finitePointCohomologyIso N) (X + Y) =
            (finitePointCohomologyIso N) X + (finitePointCohomologyIso N) Y :=
        fun X Y => cohomologyIso_add N X Y
      have hisosmul : ∀ (t : ℚ) (X : RationalSingularCohomology
          (finitePointHodgeData N).analytification (2 * 0)),
          (finitePointCohomologyIso N) (t • X) =
            t • (finitePointCohomologyIso N) X :=
        fun t X => cohomologyIso_smul N t X
      rw [hiso, hisosmul, hhead, one_smul]
      rw [zeroCycleClass_point N ⟨0 + 1, h1⟩]
      have hiso0 : (finitePointCohomologyIso N)
          ((realizedWordPair ([] : RealizedCorrespondenceWord
            (finitePointWorld N) (finitePointHodgeData N) 0)).cohomologyOperator
            (zeroCycleClass N (codimensionPointCycle (finitePointWorld N).X 0
              ((finitePointPt N) i)))) = 0 := by
        show (finitePointCohomologyIso N)
          (0 : RationalSingularCohomology (finitePointAnalytification N) 0) = 0
        exact cohomologyIso_zero N
      rw [hiso0, add_zero]
      have hfin : (⟨0 + 1, h1⟩ : Fin N) = ⟨i.val + 1, hi⟩ := by
        apply Fin.ext
        show (0 + 1 : ℕ) = i.val + 1
        omega
      exact congrArg (fun x : Fin N => Pi.single x (1 : ℚ)) hfin
  | succ k ih =>
      intro hk i hik hi
      by_cases hik1 : i.val ≤ k
      · by_cases hk2 : k + 1 + 1 < N
        · have hun : shiftLettersDownTo N (k + 1) hk =
              (⟨k + 1 + 1, hk2⟩, ⟨k + 1, hk⟩, (1 : ℚ)) ::
                shiftLettersDownTo N k (Nat.lt_of_succ_lt hk) := by
            simp only [shiftLettersDownTo, dif_pos hk2]
          have hword : lettersOf N
              ((⟨k + 1 + 1, hk2⟩, ⟨k + 1, hk⟩, (1 : ℚ)) ::
                shiftLettersDownTo N k (Nat.lt_of_succ_lt hk)) =
              ((1 : ℚ), pointPairLetter N ⟨k + 1 + 1, hk2⟩ ⟨k + 1, hk⟩) ::
                lettersOf N (shiftLettersDownTo N k (Nat.lt_of_succ_lt hk)) := rfl
          have hcol : ¬((⟨k + 1, hk⟩ : Fin N) = i) := by
            intro hc
            have hiv : i.val = k + 1 := by rw [← hc]
            omega
          have hkill : (pointPairLetter N ⟨k + 1 + 1, hk2⟩ ⟨k + 1, hk⟩).cohomologyOperator
              (zeroCycleClass N (codimensionPointCycle (finitePointWorld N).X 0
                ((finitePointPt N) i))) = 0 := by
            have hop : (pointPairLetter N ⟨k + 1 + 1, hk2⟩ ⟨k + 1, hk⟩).cohomologyOperator =
                matrixUnitOp N ⟨k + 1 + 1, hk2⟩ ⟨k + 1, hk⟩ := rfl
            rw [hop]
            exact matrixUnitOp_ptClass_eq_zero N ⟨k + 1 + 1, hk2⟩ ⟨k + 1, hk⟩ i hcol
          rw [hun, hword, wordOp_cons_apply, hkill, smul_zero, zero_add]
          exact ih (Nat.lt_of_succ_lt hk) i hik1 hi
        · have hun : shiftLettersDownTo N (k + 1) hk =
              shiftLettersDownTo N k (Nat.lt_of_succ_lt hk) := by
            simp only [shiftLettersDownTo, dif_neg hk2]
          rw [hun]
          exact ih (Nat.lt_of_succ_lt hk) i hik1 hi
      · have hik' : i.val = k + 1 := by omega
        have hk2 : k + 1 + 1 < N := by omega
        have hun : shiftLettersDownTo N (k + 1) hk =
            (⟨k + 1 + 1, hk2⟩, ⟨k + 1, hk⟩, (1 : ℚ)) ::
              shiftLettersDownTo N k (Nat.lt_of_succ_lt hk) := by
          simp only [shiftLettersDownTo, dif_pos hk2]
        have hword : lettersOf N
            ((⟨k + 1 + 1, hk2⟩, ⟨k + 1, hk⟩, (1 : ℚ)) ::
              shiftLettersDownTo N k (Nat.lt_of_succ_lt hk)) =
            ((1 : ℚ), pointPairLetter N ⟨k + 1 + 1, hk2⟩ ⟨k + 1, hk⟩) ::
              lettersOf N (shiftLettersDownTo N k (Nat.lt_of_succ_lt hk)) := rfl
        have hci : (⟨k + 1, hk⟩ : Fin N) = i := Fin.ext (by rw [hik'])
        have hhead : (finitePointCohomologyIso N)
            ((pointPairLetter N ⟨k + 1 + 1, hk2⟩ ⟨k + 1, hk⟩).cohomologyOperator
              (zeroCycleClass N (codimensionPointCycle (finitePointWorld N).X 0
                ((finitePointPt N) i)))) =
            (finitePointCohomologyIso N)
              (zeroCycleClass N (codimensionPointCycle (finitePointWorld N).X 0
                ((finitePointPt N) ⟨k + 1 + 1, hk2⟩))) := by
          have hop : (pointPairLetter N ⟨k + 1 + 1, hk2⟩ ⟨k + 1, hk⟩).cohomologyOperator =
              matrixUnitOp N ⟨k + 1 + 1, hk2⟩ ⟨k + 1, hk⟩ := rfl
          rw [hop]
          exact congrArg (finitePointCohomologyIso N)
            (matrixUnitOp_ptClass_eq N ⟨k + 1 + 1, hk2⟩ ⟨k + 1, hk⟩ i hci)
        have htail : (realizedWordPair (lettersOf N
            (shiftLettersDownTo N k (Nat.lt_of_succ_lt hk)))).cohomologyOperator
            (zeroCycleClass N (codimensionPointCycle (finitePointWorld N).X 0
              ((finitePointPt N) i))) = 0 :=
          shiftWord_op_ptClass_not N k (Nat.lt_of_succ_lt hk) i (by omega)
        rw [hun, hword, wordOp_cons_apply]
        have hiso : ∀ X Y : RationalSingularCohomology
            (finitePointHodgeData N).analytification (2 * 0),
            (finitePointCohomologyIso N) (X + Y) =
              (finitePointCohomologyIso N) X + (finitePointCohomologyIso N) Y :=
          fun X Y => cohomologyIso_add N X Y
        have hisosmul : ∀ (t : ℚ) (X : RationalSingularCohomology
            (finitePointHodgeData N).analytification (2 * 0)),
            (finitePointCohomologyIso N) (t • X) =
              t • (finitePointCohomologyIso N) X :=
          fun t X => cohomologyIso_smul N t X
        rw [hiso, hisosmul, hhead, one_smul]
        rw [zeroCycleClass_point N ⟨k + 1 + 1, hk2⟩]
        have hiso0 : (finitePointCohomologyIso N)
            ((realizedWordPair (lettersOf N
              (shiftLettersDownTo N k (Nat.lt_of_succ_lt hk)))).cohomologyOperator
            (zeroCycleClass N (codimensionPointCycle (finitePointWorld N).X 0
              ((finitePointPt N) i)))) = 0 := by
          rw [htail]
          exact cohomologyIso_zero N
        rw [hiso0, add_zero]
        have hfin : (⟨k + 1 + 1, hk2⟩ : Fin N) = ⟨i.val + 1, hi⟩ := by
          apply Fin.ext
          show (k + 1 + 1 : ℕ) = i.val + 1
          omega
        exact congrArg (fun x : Fin N => Pi.single x (1 : ℚ)) hfin

/-- **THE ORBIT ENGINE**: the shift word's operator carries the `i`-th
coordinate basis vector to the `(i+1)`-st. -/
theorem shiftWord_op_single (N : ℕ) [NeZero N] (i : Fin N) (hi : i.val + 1 < N) :
    (finitePointCohomologyIso N)
      ((realizedWordPair (finitePointShiftWord N)).cohomologyOperator
        ((finitePointCohomologyIso N).symm (Pi.single i (1 : ℚ)))) =
      Pi.single ⟨i.val + 1, hi⟩ (1 : ℚ) := by
  have h1 := zeroCycleClass_point N i
  have hpt : (finitePointCohomologyIso N).symm (Pi.single i (1 : ℚ)) =
      zeroCycleClass N (codimensionPointCycle (finitePointWorld N).X 0
        ((finitePointPt N) i)) := by
    rw [← h1]
    exact LinearEquiv.symm_apply_apply _ _
  rw [hpt]
  have hword : finitePointShiftWord N = lettersOf N (shiftWordData N) := rfl
  rw [hword]
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  have hsd : shiftWordData (M + 1) =
      shiftLettersDownTo (M + 1) M (Nat.lt_succ_self M) := rfl
  rw [hsd]
  exact shiftWord_op_ptClass (M + 1) M (Nat.lt_succ_self M) i
    (Nat.lt_succ_iff.mp i.isLt) hi

#check (finitePointShiftWord)
#check (shiftWord_op_single)
#print axioms finitePointShiftWord
#print axioms shiftWord_op_single


end GSTFinitePointShiftWord

end -- noncomputable section

/-!
## DRAFT STATUS (W42-D, commander-executed after three agent timeouts)

* Ported from the CI-green twelve-point twin: the letter machinery
  (`comap_evalRingHom_default` … `lettersOf`), the operator section
  (`realizedWordPair_cohomologyOperator_nil/_cons`, `cohomologyIso_*`,
  `wordOp_pointClass`), and `module_decomp` — 34 declarations, proof bodies
  verbatim under the lane rename map with explicit `N` threading.
* NEW: `shiftWordData` + `shiftWordData_spec/_mem/_eq_of_col_eq/_sum`,
  `finitePointShiftMatrix`, `finitePointShiftWord`, `shiftWord_op_single`.
* The twin's Twave-specific parts (foldWordData, the 26-entry matrix, the
  Krylov determinant sweeps, `foldWord_op_pointClass`,
  `twelvePointFoldWord_op`, `twelvePointFoldWord_hodge`) are NOT ported —
  replaced by the shift machinery; the law landing discharges word_hodge
  itself via `rationalHodgeSubspace_eq_top_of_degree_zero`.
* PORT NOTE(n12): no 12-specific decidability sites existed in the ported
  regions (the twin's proofs were already N-agnostic); the only changes are
  the renames, the `N` threading, and the deleted local point abbrevs
  (`finitePointPt` arrives from `GSTFinitePointHodgeData`).
* PORT RISK(W42D-RW-CONS): `rw [realizedWordPair_cohomologyOperator_cons]`
  in `wordOp_pointClass` keeps the twin's bare-name rewrite; with `N`
  auto-bound the rewrite carries an `?N` metavariable resolved by goal
  matching (twin-green mechanism, low risk).
* PORT RISK(W42D-SUM-LEMMA): `List.sum_eq_single_of_mem` is the pinned
  Mathlib name (unattested in this corpus — CI owns the check).
* Static verification: zero `twelvePoint`/`Fin 12` outside this status
  block; paren balance depth 0 (comments excluded); zero
  `sorry`/`admit`/`native_decide`/`axiom`.
-/
