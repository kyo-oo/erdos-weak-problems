/-
Copyright (c) 2026. The HC-Proof owner's GST hypothesis program.
-/
import HCUniverse2.GSTTwelvePointCohomology
import HCUniverse2.GSTGeometricRealizationStage2G
import HCUniverse2.GSTGeometricRealizationStage2D
import HCUniverse2.GSTNativeCodimensionCyclePresentation
import HCUniverse2.GSTClassicalHodgeFiberedCosmology

/-!
# GST TWELVE-POINT HODGE DATA

The first genuine `HodgeBigradedBettiData` of the corpus: the twelve-point
world's Hodge structure.

* At weight `p = 0` the honest zero-dimensional bigrading: every class of
  `H⁰` is of type `(0, 0)` — the single component is the whole
  complexification, the rational Hodge fiber is the entire `H⁰` (a LIVE
  rank-12 fiber).
* At weights `p ≥ 1` the fibers are dead by dimension: `H^{2p} = 0` for
  `2p ≥ 2` (the cohomology vanishing of the discrete world), and every
  grading on the zero module is trivially independent and spanning.
* `cycleClass` at weight 0 is the genuine degree map: a zero-cycle
  `Z = Σ aᵢ pᵢ` maps to the multiplicity vector through the pinned H⁰ iso
  `twelvePointCohomologyIso`.  The class of the `i`-th point cycle is the
  indicator vector `Pi.single i 1`.

Contract delivered downstream (`GSTTwelvePointFoldWord` and
`GSTTwelvePointLawLanding`): `twelvePointHodgeData`,
`zeroCycleClass` (with `twelvePointHodgeData.cycleClass 0` definitionally
equal to it), `zeroCycleClass_point`, `zeroFiber_eq_top`, and
`deadFiber_subsingleton`.

No `sorry`, no new axioms, no `native_decide`.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open CategoryTheory
open AlgebraicGeometry
open TensorProduct
open GSTProjectiveOverC
open GSTGeometricRealizationStage2C
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTNativeCodimensionCyclePresentation
open GSTTwelvePointWorldCarrier
open GSTTwelvePointAnalytification
open GSTTwelvePointCohomology

namespace GSTTwelvePointHodgeData

/-! ## §1 SUBSINGLETON HELPERS -/

/-- In a subsingleton module every pair of submodules coincides. -/
theorem subsingleton_submodules_eq {R : Type} [CommSemiring R] {M : Type}
    [AddCommGroup M] [Module R M] [Subsingleton M] (P Q : Submodule R M) :
    P = Q :=
  Submodule.ext fun m => by
    constructor
    · intro _
      have h : m = 0 := Subsingleton.elim m 0
      subst h
      exact Q.zero_mem
    · intro _
      have h : m = 0 := Subsingleton.elim m 0
      subst h
      exact P.zero_mem

/-- The complexification of a subsingleton ℚ-module is subsingleton:
every pure tensor has a zero left factor. -/
theorem subsingleton_complexification {VQ : Type}
    [AddCommGroup VQ] [Module ℚ VQ] [Subsingleton VQ] :
    Subsingleton (Complexification VQ) := by
  -- WAVE 17 (pre-exposure D1): the original induction motive `fun z => z = y`
  -- was unsound in the add-branches (from `x₁ = y` and `x₂ = y` one gets
  -- `y + y = y`, false); everything is zero in a subsingleton module — prove
  -- both sides zero separately.
  constructor
  intro x y
  have hx : x = 0 := by
    induction x using TensorProduct.induction_on with
    | zero => rfl
    | tmul b v =>
      rw [show v = 0 from Subsingleton.elim v 0, TensorProduct.tmul_zero]
    | add x₁ x₂ ih₁ ih₂ => rw [ih₁, ih₂, add_zero]
  have hy : y = 0 := by
    induction y using TensorProduct.induction_on with
    | zero => rfl
    | tmul b v =>
      rw [show v = 0 from Subsingleton.elim v 0, TensorProduct.tmul_zero]
    | add y₁ y₂ ih₁ ih₂ => rw [ih₁, ih₂, add_zero]
  rw [hx, hy]

/-- `Fin 1` is a subsingleton index type. -/
theorem fin1_subsingleton : Subsingleton (Fin 1) :=
  ⟨fun a b => Fin.ext (by have := a.2; have := b.2; omega)⟩

/-! ## §2 THE HONEST (0, 0)-BIGRADING AT WEIGHT ZERO -/

/-- The honest Hodge bigrading of the weight-zero fiber: `H⁰` of a
zero-dimensional analytic space is entirely of type `(0, 0)` — the single
component (the `Fin 1` index is the (0,0)-position itself) is the whole
complexification, the decomposition is trivially independent. -/
noncomputable def zeroBigrading :
    HodgeBigrading (RationalSingularCohomology twelvePointAnalytification 0) 0
    where
  component := fun _ => ⊤
  independent := by
    haveI : Subsingleton (Fin 1) := fin1_subsingleton
    exact iSupIndep_subsingleton _
  spans := by
    refine le_antisymm le_top ?_
    exact le_iSup (f := fun _ : Fin 1 =>
      (⊤ : Submodule ℂ (Complexification
        (RationalSingularCohomology twelvePointAnalytification 0)))) ⟨0, by omega⟩

/-! ## §3 THE TRIVIAL BIGRADING AT THE DEAD WEIGHTS -/

/-- The Hodge bigrading of a dead weight: the module `H^{2p}` is
subsingleton (the cohomology vanishing of the discrete world), so its
complexification lattice collapses — every family of components is
trivially independent and the total supremum is the top. -/
noncomputable def deadBigrading (p : Nat) (hp : 0 < p) :
    HodgeBigrading
      (RationalSingularCohomology twelvePointAnalytification (2 * p)) (2 * p)
    where
  component := fun _ => ⊥
  independent := by
    haveI hsub : Subsingleton
        (RationalSingularCohomology twelvePointAnalytification (2 * p)) :=
      twelvePointCohomology_subsingleton _ (by omega)
    haveI hcomp : Subsingleton (Complexification
        (RationalSingularCohomology twelvePointAnalytification (2 * p))) :=
      subsingleton_complexification
    haveI hlat : Subsingleton (Submodule ℂ (Complexification
        (RationalSingularCohomology twelvePointAnalytification (2 * p)))) :=
      ⟨fun P Q => subsingleton_submodules_eq P Q⟩
    intro i
    -- WAVE 21 (run-20 error at :151): `Subsingleton.elim _ _` synthesizes its
    -- instance `[Subsingleton ?α]` BEFORE α is assigned from the goal, and this
    -- goal can never assign it: `iSupIndep` unfolds (Order/SupIndep.lean:329)
    -- to `∀ i, Disjoint (component i) (⨆ (j) (_ : j ≠ i), component j)`, and
    -- `Disjoint` at the pin is the ORDER-form `∀ ⦃x⦄, x ≤ a → x ≤ b → x ≤ ⊥`
    -- (Order/Disjoint.lean:48), NOT `P ⊓ Q = ⊥` — so even the instance-explicit
    -- `@Subsingleton.elim _ hlat _ _` (an `Eq` between submodules) cannot match
    -- a ∀-shaped goal.  Mathlib's own packaged collapse `disjoint_of_subsingleton`
    -- (Order/Disjoint.lean:52, body `fun x _ _ ↦ le_of_eq (Subsingleton.elim x ⊥)`)
    -- has the right ∀-shape: the goal assigns α (with its PartialOrder/OrderBot
    -- args) by first-order unification, and the `[Subsingleton α]` instance
    -- resolves from `hlat` — the elaboration shape of the run-20-green
    -- `iSupIndep_subsingleton` at :116 above.
    exact disjoint_of_subsingleton
  spans := by
    haveI hsub : Subsingleton
        (RationalSingularCohomology twelvePointAnalytification (2 * p)) :=
      twelvePointCohomology_subsingleton _ (by omega)
    haveI hcomp : Subsingleton (Complexification
        (RationalSingularCohomology twelvePointAnalytification (2 * p))) :=
      subsingleton_complexification
    haveI hlat : Subsingleton (Submodule ℂ (Complexification
        (RationalSingularCohomology twelvePointAnalytification (2 * p)))) :=
      ⟨fun P Q => subsingleton_submodules_eq P Q⟩
    -- WAVE 21 (run-20 error at :151, the spans twin hardened by the same
    -- discipline): unlike `independent`'s `Disjoint` goal, the spans goal
    -- `(⨆ a, component a) = ⊤` IS an `Eq` between submodules, so run 20's
    -- `Subsingleton.elim _ _` here already resolved (the goal assigns α, the
    -- pending instance found `hlat`) — the `@`-form makes it synthesis-free:
    -- `hlat` passed as the instance term itself, α fixed from `hlat`'s type,
    -- `a`/`b` from the goal's two sides by first-order unification.
    exact @Subsingleton.elim _ hlat _ _

/-! ## §4 THE GENUINE DEGREE MAP AT WEIGHT ZERO -/

/-- The genuine cycle-class map at weight zero: the degree map of the
twelve-point world, transporting the multiplicity vector of a zero-cycle
through the pinned H⁰ isomorphism. -/
noncomputable def zeroCycleClass :
    codimensionCycles twelvePointWorld.X 0 →ₗ[ℚ]
      RationalSingularCohomology twelvePointAnalytification 0 :=
  { toFun := fun Z =>
      twelvePointCohomologyIso.symm
        (fun i => (Z : AlgebraicCycle twelvePointWorld.X ℚ) ((twelvePointEquiv i).1))
    map_add' := by
      intro Z W
      -- WAVE 17 (pre-exposure D5): ascribe at the CARRIER level first (the
      -- CI-green PointNormalForm idiom) — the ambient-level `Z + W` show is
      -- not definitional (Submodule.coe_add is propositional).
      show twelvePointCohomologyIso.symm
          (fun i => ((Z + W : codimensionCycles twelvePointWorld.X 0) :
            AlgebraicCycle twelvePointWorld.X ℚ) ((twelvePointEquiv i).1)) =
        twelvePointCohomologyIso.symm
          (fun i => (Z : AlgebraicCycle twelvePointWorld.X ℚ)
            ((twelvePointEquiv i).1)) +
        twelvePointCohomologyIso.symm
          (fun i => (W : AlgebraicCycle twelvePointWorld.X ℚ)
            ((twelvePointEquiv i).1))
      rw [← map_add]
      -- WAVE 21 (run-20 errors at :191/:205): `congr 1` closed the goal —
      -- the funext/simp tails were dead (run 20 adjudicated: zero goals
      -- remained after `congr 1`; the residual function-level additivity is
      -- instance-defeq through `Pi.add` and the Submodule coe-addition, no
      -- metavariables, no search — deterministic for the pinned toolchain).
      congr 1
    map_smul' := by
      intro q Z
      -- WAVE 17 (pre-exposure D5): the same carrier-level ascription; the
      -- `Submodule.coe_smul` bridge plus the green reference's simp set.
      show twelvePointCohomologyIso.symm
          (fun i => ((q • Z : codimensionCycles twelvePointWorld.X 0) :
            AlgebraicCycle twelvePointWorld.X ℚ) ((twelvePointEquiv i).1)) =
        q • twelvePointCohomologyIso.symm
          (fun i => (Z : AlgebraicCycle twelvePointWorld.X ℚ)
            ((twelvePointEquiv i).1))
      rw [← map_smul]
      -- WAVE 21 (run-20 errors at :191/:205, the map_smul' twin): `congr 1`
      -- closed the goal — the funext/rw/simp tail was dead, the same
      -- instance-defeq closure through `Pi.smul` and the Submodule coe-smul.
      congr 1 }

/-- The `i`-th point cycle as a codimension point of the world. -/
def twelvePointPt (i : Fin 12) : CodimensionPoint twelvePointWorld.X 0 :=
  ⟨(twelvePointEquiv i).1, (twelvePointEquiv i).2⟩

-- WAVE 23 (attempt-2 survivor at :267:82, restructured after the run-24
-- parse break at :232: a module docstring must attach DIRECTLY to the
-- declaration, so the `open Classical in` sits ABOVE the docstring): the
-- green PointNormalForm regime mirrored EXACTLY -- `open Classical in` at
-- theorem level is the half the wave-21 rebuild missed: the `classical`
-- tactic alone adds only `propDecidable`, and `single_apply`'s
-- [DecidableEq X] then cannot synthesize -- the linter's "single_apply
-- unused" was the receipt. Under `open Classical in` the scoped instance
-- provides it (the green PointNormalForm:38-47 runs BOTH).
open Classical in
/-- **THE POINT-CLASS EQUATION.**  The class of the `i`-th point cycle is
the `i`-th indicator vector under the H⁰ iso — by construction of the
degree map. -/
theorem zeroCycleClass_point (i : Fin 12) :
    twelvePointCohomologyIso
      (zeroCycleClass (codimensionPointCycle twelvePointWorld.X 0
        (twelvePointPt i))) =
      Pi.single i (1 : ℚ) := by
  -- WAVE 21 (run-20 errors at :229:7, :229:82, :235:2): the `hval` have
  -- compared the two COERCED SUBTYPE POINTS in its `if` — the twelve-point
  -- carrier has no `Decidable`/`DecidableEq` instance, so the have's
  -- statement failed to synthesize (:229:7), its RHS degraded to `sorry ()`,
  -- and the cascade killed everything downstream (:229:82 — the
  -- point-indexed `Pi.single` was never evaluated, `single_apply` reported
  -- unused because the default-simp `coe_single` had already normalized the
  -- coe application into the bare `Pi.single` spelling past its pattern, and
  -- no rewrite can meet an opaque `sorry`; :235:2 — the case-pos residue
  -- `sorry () = 1`).  THE ROUTE, green-mirrored: (1) `classical` first — the
  -- same low-priority `Classical.propDecidable` the CI-green
  -- `codimensionPointCycle` def (NativeCodimensionCyclePresentation:40) and
  -- PointNormalForm:71 run under, so the point-equality `if` elaborates;
  -- (2) the evaluation simp gains the `twelvePointPt` equation, so the
  -- single's point and the hval's if-point meet at the SAME
  -- `(twelvePointEquiv i).1` spelling (PointNormalForm:71's both-sides-`x.1`
  -- shape); (3) both by_cases arms close by the deterministic pinned core
  -- chain `if_pos rfl` / `if_neg` (the CardinalWorlds-green
  -- `rw [eq-form, if_pos rfl, if_neg h]` idiom) instead of bare `simp` on a
  -- classically-decided reflexive `ite`.
  classical
  show twelvePointCohomologyIso (twelvePointCohomologyIso.symm
      (fun j => (codimensionPointCycle twelvePointWorld.X 0 (twelvePointPt i) :
        AlgebraicCycle twelvePointWorld.X ℚ) ((twelvePointEquiv j).1))) =
    Pi.single i (1 : ℚ)
  rw [LinearEquiv.apply_symm_apply]
  funext j
  -- WAVE 26 (run-26 residual at :277:79 — the last HodgeData error): the
  -- hval is GENERALIZED over a variable point y at the cycle's own
  -- `twelvePointWorld.X` spelling — the green PointNormalForm:66-71 idiom
  -- VERBATIM (their x and y are variables; our two runs proved the
  -- concrete-eval-point spelling `(twelvePointEquiv j).1` poisons every
  -- evaluation lemma's pattern match: the run-25 full-error showed the
  -- point type spelled `twelvePointWorld.X` on the cycle side vs
  -- `twelvePointScheme` on the equiv side — default-defeq only, dead at
  -- simp's matching; with y a variable there is no second spelling and
  -- `single_apply` fires exactly as the green adjudicates).
  have hev : ∀ y : twelvePointWorld.X,
      (codimensionPointCycle twelvePointWorld.X 0 (twelvePointPt i) :
        AlgebraicCycle twelvePointWorld.X ℚ) y =
      (if y = (twelvePointPt i).1 then (1 : ℚ) else 0) := by
    intro y
    -- the green's exact simp set: both sides at the single's own point
    -- spelling, y a variable — no twelvePointPt unfolding, no coe race.
    simp [codimensionPointCycle, Function.locallyFinsuppWithin.single_apply]
  have hval : (codimensionPointCycle twelvePointWorld.X 0 (twelvePointPt i) :
      AlgebraicCycle twelvePointWorld.X ℚ) ((twelvePointEquiv j).1) =
      (if (twelvePointEquiv j).1 = (twelvePointPt i).1 then (1 : ℚ) else 0) :=
    hev ((twelvePointEquiv j).1)
    -- WAVE 23: the green's EXACT idiom -- the ite stated at the SINGLE'S OWN
    -- point spelling `(twelvePointPt i).1` (no `twelvePointPt` in the simp
    -- set: the attempt-2 residual proved the extra equation de-synced the
    -- rewrite), so `codimensionPointCycle`'s equation deposits
    -- `single (twelvePointPt i).1 1` and `single_apply` fires on the
    -- argument-first ite with both sides at the identical spelling -- the
    -- verbatim PointNormalForm:66-71 close, now under the same
    -- `open Classical in` regime.
  rw [hval, Pi.single_apply]
  by_cases hj : j = i
  · -- WAVE 25 (run-25 errors at :296/:298): both arms rebuilt SUBST-FREE
    -- with explicitly-typed have anchors -- the wave-23/24 pos arm died
    -- twice (the `subst hj` eliminated `i` leaving the hd-have's `i`
    -- unknown; the wave-24 neg arm's lambda elaboration pinned the if_neg
    -- pattern at the `twelvePointEquiv i` spelling against the goal's
    -- `twelvePointPt i` -- not syntactic, kabstract-dead).  Now: hd's TYPE
    -- is stated at the goal's own condition spelling, proven by rw [hj]
    -- (j → i on the left) + rfl (the constructor-projection defeq at
    -- default transparency); both if_pos patterns are then syntactic.
    have hd : (twelvePointEquiv j).1 = (twelvePointPt i).1 := by
      rw [hj]
      rfl
    rw [if_pos hd, if_pos hj]
  · -- WAVE 25: the same have-anchor discipline for the negative side --
    -- hiff's type stated at the goal's own condition, the injectivity
    -- chain (Subtype.ext + twelvePointEquiv.injective over the
    -- structure-eta defeq twelvePointPt i ≡ twelvePointEquiv i) elaborated
    -- INSIDE the have where the expected type is already concrete.
    have hiff : ¬((twelvePointEquiv j).1 = (twelvePointPt i).1) := fun hcon =>
      hj (twelvePointEquiv.injective (Subtype.ext hcon))
    rw [if_neg hiff, if_neg hj]

/-! ## §5 THE FIBER FACTS -/

/-- The rational Hodge fiber of a grading whose `(p, p)`-component is the
whole space is the whole module. -/
theorem rationalHodgeSubspace_of_top
    {VQ : Type} [AddCommGroup VQ] [Module ℚ VQ] {p : Nat}
    (D : HodgeBigrading VQ (2 * p))
    (htop : D.ppComponent = ⊤) :
    rationalHodgeSubspace D = ⊤ :=
  Submodule.ext fun m => by
    constructor
    · intro _
      -- WAVE 22 (emergency, W22-D audit find): the run-20 arity disease --
      -- `Submodule.mem_top` takes its element IMPLICIT at the pin
      -- (Submodule/Lattice.lean:143: `@[simp] lemma mem_top {x : M} :
      -- x ∈ ⊤`) -- the wave-21 commit claimed this fix but the edit
      -- never landed (the W21-A/W21-C ownership gap); the argument is
      -- dropped, the element unifies from the goal at default transparency.
      exact Submodule.mem_top
    · intro _
      rw [mem_rationalHodgeSubspace_iff, htop]
      -- WAVE 22 (emergency): the same arity fix.
      exact Submodule.mem_top

/-- **THE WEIGHT-ZERO FIBER IS LIVE.**  The rational Hodge fiber of the
twelve-point world at weight zero is the entire `H⁰` — a live rank-12
fiber: the honest Hodge structure of the zero-dimensional world. -/
theorem zeroFiber_eq_top :
    rationalHodgeSubspace (p := 0) zeroBigrading = ⊤ := by
  -- WAVE 17 (pre-exposure D9): force the weight-0 implicit explicitly — the
  -- `2 * ?p =?= 0` nonlinear unification from the literal-0 index is not
  -- solvable; the resulting term is unchanged (tier-6's rw-pattern
  -- `rationalHodgeSubspace zeroBigrading` is preserved).
  have hpp : (HodgeBigrading.ppComponent (p := 0)) zeroBigrading = ⊤ := rfl
  exact rationalHodgeSubspace_of_top (p := 0) zeroBigrading hpp

/-! ## §6 THE ASSEMBLY -/

/-- The genuine cycle-class map at a dead weight: any linear map into the
subsingleton module is the zero map up to subsingleton collapse. -/
noncomputable def deadCycleClass (p : Nat) (hp : 0 < p) :
    codimensionCycles twelvePointWorld.X p →ₗ[ℚ]
      RationalSingularCohomology twelvePointAnalytification (2 * p) :=
  { toFun := fun _ => 0
    map_add' := by
      intro Z W
      haveI hsub : Subsingleton
          (RationalSingularCohomology twelvePointAnalytification (2 * p)) :=
        twelvePointCohomology_subsingleton _ (by omega)
      exact Subsingleton.elim _ _
    map_smul' := by
      intro q Z
      haveI hsub : Subsingleton
          (RationalSingularCohomology twelvePointAnalytification (2 * p)) :=
        twelvePointCohomology_subsingleton _ (by omega)
      exact Subsingleton.elim _ _ }

/-- **THE FIRST GENUINE HODGE DATA.**  The twelve-point world's Hodge
structure: the discrete analytification, the honest `(0, 0)`-bigrading at
weight zero with the dead gradings above, and the genuine degree-map
cycle class. -/
noncomputable def twelvePointHodgeData :
    HodgeBigradedBettiData twelvePointWorld where
  analytification := twelvePointAnalytification
  hodgeBigrading :=
    fun p =>
      match p with
      | 0 => zeroBigrading
      | q + 1 => deadBigrading (q + 1) (by omega)
  cycleClass :=
    fun p =>
      match p with
      | 0 => zeroCycleClass
      | q + 1 => deadCycleClass (q + 1) (by omega)

/-- The weight-`p` rational Hodge fiber of the assembled Hodge data. -/
theorem twelvePointHodgeData_bigrading_zero :
    twelvePointHodgeData.hodgeBigrading 0 = zeroBigrading := rfl

/-- **THE DEAD FIBERS ARE SUBSINGLETONS.**  At every positive weight the
rational Hodge fiber of the twelve-point world is a subsingleton: the
ambient module `H^{2p}` vanishes. -/
theorem deadFiber_subsingleton (p : Nat) (hp : 0 < p) :
    Subsingleton (ClassicalHodgeFiber twelvePointWorld twelvePointHodgeData p) := by
  have hsub : Subsingleton
      (RationalSingularCohomology twelvePointAnalytification (2 * p)) :=
    twelvePointCohomology_subsingleton _ (by omega)
  exact ⟨fun a b => Subtype.ext (@Subsingleton.elim _ hsub a.1 b.1)⟩

theorem twelvePointHodgeData_cycleClass_zero :
    twelvePointHodgeData.cycleClass 0 = zeroCycleClass := rfl

theorem twelvePointHodgeData_analytification_eq :
    twelvePointHodgeData.analytification = twelvePointAnalytification := rfl

theorem twelvePointHodgeData_bigrading_pos (p : Nat) (hp : 0 < p) :
    twelvePointHodgeData.hodgeBigrading p = deadBigrading p hp := by
  -- WAVE 17 (pre-exposure D11): rcases guarantees the dependent-hypothesis
  -- substitution the tactic-position match could not.
  rcases p with _ | q
  · exact absurd hp (by omega)
  · rfl

/-! ## Receipts -/

#check subsingleton_submodules_eq
#check subsingleton_complexification
#check fin1_subsingleton
#check zeroBigrading
#check deadBigrading
#check zeroCycleClass
#check twelvePointPt
#check zeroCycleClass_point
#check rationalHodgeSubspace_of_top
#check zeroFiber_eq_top
#check twelvePointHodgeData_bigrading_zero
#check twelvePointHodgeData_bigrading_pos
#check deadFiber_subsingleton
#check deadCycleClass
#check twelvePointHodgeData
#check twelvePointHodgeData_cycleClass_zero
#check twelvePointHodgeData_analytification_eq

#print axioms subsingleton_submodules_eq
#print axioms subsingleton_complexification
#print axioms fin1_subsingleton
#print axioms zeroCycleClass_point
#print axioms rationalHodgeSubspace_of_top
#print axioms zeroFiber_eq_top
#print axioms deadFiber_subsingleton
#print axioms twelvePointHodgeData_bigrading_pos

end GSTTwelvePointHodgeData

end -- noncomputable section
