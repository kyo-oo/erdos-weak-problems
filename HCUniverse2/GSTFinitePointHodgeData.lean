/-
Copyright (c) 2026. The HC-Proof owner's GST hypothesis program.
-/
import HCUniverse2.GSTFinitePointCohomology
import HCUniverse2.GSTGeometricRealizationStage2G
import HCUniverse2.GSTGeometricRealizationStage2D
import HCUniverse2.GSTNativeCodimensionCyclePresentation
import HCUniverse2.GSTClassicalHodgeFiberedCosmology

/-!
# THE GENERAL FINITE-POINT HODGE DATA

The general finite-point twin of the corpus's first genuine
`HodgeBigradedBettiData` (the N = 12 ancestor of this lane): the
canonical discrete Hodge data on the `N`-point world, for every `N ≠ 0`.

* At weight `p = 0` the FORCED zero-dimensional bigrading: the index type
  `Fin (0 + 1)` of the weight-`2·0` bigrading has exactly one slot — the
  `(0, 0)`-position — so every class of `H⁰` is of type `(0, 0)`; the
  honest bigrading takes the single component to be the whole
  complexification, the rational Hodge fiber is the entire `H⁰` (a LIVE
  rank-`N` fiber).
* At weights `p ≥ 1` the fibers are dead by dimension: `H^{2p} = 0` for
  `2p ≥ 2` (the cohomology vanishing of the discrete world), and every
  grading on the zero module is trivially independent and spanning.
* `cycleClass` at weight 0 is the genuine degree map: a zero-cycle
  `Z = Σ aᵢ pᵢ` maps to the multiplicity vector through the pinned H⁰ iso
  `finitePointCohomologyIso`.  The class of the `i`-th point cycle is the
  indicator vector `Pi.single i 1`.

NEW against the ancestor source: the generic weight-zero fiber law
`rationalHodgeSubspace_eq_top_of_degree_zero` (§7) — for ANY smooth
projective complex variety and ANY Hodge data on it, the weight-zero
rational Hodge fiber is the full `H⁰` (the `Fin 1` index type forces the
single `(0, 0)` component to span by the `spans` field) — the weight-`0`
discharger for the downstream certificate lane (`word_hodge` /
`seed_hodge`).

Contract delivered downstream (`GSTFinitePointFoldWord` and
`GSTFinitePointLawLanding`): `finitePointHodgeData`,
`zeroCycleClass` (with `finitePointHodgeData.cycleClass 0` definitionally
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
open GSTFinitePointWorldCarrier
open GSTFinitePointAnalytification
open GSTFinitePointCohomology

namespace GSTFinitePointHodgeData

variable (N : ℕ) [NeZero N]

-- PORT NOTE(n12): decidability audit of the ancestor source.  Its only
-- decidability-sensitive machinery is (a) scheme-point equality inside
-- `zeroCycleClass_point` (the carrier of the finite-point world has no
-- `Decidable`/`DecidableEq` instance for ANY `N` — resolved by the SAME
-- `open Classical in` + `classical` regime the green ancestor runs), and
-- (b) `Fin`-index equality (`by_cases`, `Pi.single`, `Pi.single_apply`),
-- uniform in `N` through `Fin.instDecidableEqFin`.  No ancestor-specific
-- decidability re-derivation was required: every proof body below is the
-- source body VERBATIM under the campaign rename map (the world/point/
-- cohomology identifier family of the lane) and the explicit-`N` type
-- map (the point index type becomes `Fin N`; definitions applied at `N`).

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
    HodgeBigrading (RationalSingularCohomology (finitePointAnalytification N) 0) 0
    where
  component := fun _ => ⊤
  independent := by
    haveI : Subsingleton (Fin 1) := fin1_subsingleton
    exact iSupIndep_subsingleton _
  spans := by
    refine le_antisymm le_top ?_
    exact le_iSup (f := fun _ : Fin 1 =>
      (⊤ : Submodule ℂ (Complexification
        (RationalSingularCohomology (finitePointAnalytification N) 0)))) ⟨0, by omega⟩

/-! ## §3 THE TRIVIAL BIGRADING AT THE DEAD WEIGHTS -/

/-- The Hodge bigrading of a dead weight: the module `H^{2p}` is
subsingleton (the cohomology vanishing of the discrete world), so its
complexification lattice collapses — every family of components is
trivially independent and the total supremum is the top. -/
noncomputable def deadBigrading (p : Nat) (hp : 0 < p) :
    HodgeBigrading
      (RationalSingularCohomology (finitePointAnalytification N) (2 * p)) (2 * p)
    where
  component := fun _ => ⊥
  independent := by
    -- PORT NOTE(n12): the vanishing call gains the explicit `N` of the type
    -- map (`finitePointCohomology_subsingleton N _ (by omega)`); the side
    -- goal `2 * p ≠ 0` is N-independent (it rides `hp : 0 < p` alone), so
    -- the body is otherwise the source's verbatim.
    haveI hsub : Subsingleton
        (RationalSingularCohomology (finitePointAnalytification N) (2 * p)) :=
      finitePointCohomology_subsingleton N _ (by omega)
    haveI hcomp : Subsingleton (Complexification
        (RationalSingularCohomology (finitePointAnalytification N) (2 * p))) :=
      subsingleton_complexification
    haveI hlat : Subsingleton (Submodule ℂ (Complexification
        (RationalSingularCohomology (finitePointAnalytification N) (2 * p)))) :=
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
        (RationalSingularCohomology (finitePointAnalytification N) (2 * p)) :=
      finitePointCohomology_subsingleton N _ (by omega)
    haveI hcomp : Subsingleton (Complexification
        (RationalSingularCohomology (finitePointAnalytification N) (2 * p))) :=
      subsingleton_complexification
    haveI hlat : Subsingleton (Submodule ℂ (Complexification
        (RationalSingularCohomology (finitePointAnalytification N) (2 * p)))) :=
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
finite-point world, transporting the multiplicity vector of a zero-cycle
through the pinned H⁰ isomorphism. -/
noncomputable def zeroCycleClass :
    codimensionCycles (finitePointWorld N).X 0 →ₗ[ℚ]
      RationalSingularCohomology (finitePointAnalytification N) 0 :=
  { toFun := fun Z =>
      (finitePointCohomologyIso N).symm
        (fun i => (Z : AlgebraicCycle (finitePointWorld N).X ℚ) ((finitePointEquiv N i).1))
    map_add' := by
      intro Z W
      -- WAVE 17 (pre-exposure D5): ascribe at the CARRIER level first (the
      -- CI-green PointNormalForm idiom) — the ambient-level `Z + W` show is
      -- not definitional (Submodule.coe_add is propositional).
      show (finitePointCohomologyIso N).symm
          (fun i => ((Z + W : codimensionCycles (finitePointWorld N).X 0) :
            AlgebraicCycle (finitePointWorld N).X ℚ) ((finitePointEquiv N i).1)) =
        (finitePointCohomologyIso N).symm
          (fun i => (Z : AlgebraicCycle (finitePointWorld N).X ℚ)
            ((finitePointEquiv N i).1)) +
        (finitePointCohomologyIso N).symm
          (fun i => (W : AlgebraicCycle (finitePointWorld N).X ℚ)
            ((finitePointEquiv N i).1))
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
      show (finitePointCohomologyIso N).symm
          (fun i => ((q • Z : codimensionCycles (finitePointWorld N).X 0) :
            AlgebraicCycle (finitePointWorld N).X ℚ) ((finitePointEquiv N i).1)) =
        q • (finitePointCohomologyIso N).symm
          (fun i => (Z : AlgebraicCycle (finitePointWorld N).X ℚ)
            ((finitePointEquiv N i).1))
      rw [← map_smul]
      -- WAVE 21 (run-20 errors at :191/:205, the map_smul' twin): `congr 1`
      -- closed the goal — the funext/rw/simp tail was dead, the same
      -- instance-defeq closure through `Pi.smul` and the Submodule coe-smul.
      congr 1 }

/-- The `i`-th point cycle as a codimension point of the world. -/
def finitePointPt (i : Fin N) : CodimensionPoint (finitePointWorld N).X 0 :=
  ⟨(finitePointEquiv N i).1, (finitePointEquiv N i).2⟩

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
theorem zeroCycleClass_point (i : Fin N) :
    (finitePointCohomologyIso N)
      (zeroCycleClass N (codimensionPointCycle (finitePointWorld N).X 0
        (finitePointPt N i))) =
      Pi.single i (1 : ℚ) := by
  classical
  -- PORT NOTE(n12): the two decidability loads of the source are N-uniform —
  -- the point-equality `if` runs on the same `Classical.propDecidable`
  -- (the finite-point carrier has no Decidable instance for ANY N), and
  -- the index-level `by_cases`/`Pi.single` decidability is
  -- `Fin.instDecidableEqFin` at `Fin N`, so the proof body below is the
  -- source's verbatim under the rename map.
  show (finitePointCohomologyIso N) ((finitePointCohomologyIso N).symm
      (fun j => (codimensionPointCycle (finitePointWorld N).X 0 (finitePointPt N i) :
        AlgebraicCycle (finitePointWorld N).X ℚ) ((finitePointEquiv N j).1))) =
    Pi.single i (1 : ℚ)
  rw [LinearEquiv.apply_symm_apply]
  funext j
  -- WAVE 26 (run-26 residual at :277:79 — the last HodgeData error): the
  -- hval is GENERALIZED over a variable point y at the cycle's own
  -- `(finitePointWorld N).X` spelling — the green PointNormalForm:66-71 idiom
  -- VERBATIM (their x and y are variables; our two runs proved the
  -- concrete-eval-point spelling `(finitePointEquiv N j).1` poisons every
  -- evaluation lemma's pattern match: the run-25 full-error showed the
  -- point type spelled `(finitePointWorld N).X` on the cycle side vs
  -- `finitePointScheme N` on the equiv side — default-defeq only, dead at
  -- simp's matching; with y a variable there is no second spelling and
  -- `single_apply` fires exactly as the green adjudicates).
  have hev : ∀ y : (finitePointWorld N).X,
      (codimensionPointCycle (finitePointWorld N).X 0 (finitePointPt N i) :
        AlgebraicCycle (finitePointWorld N).X ℚ) y =
      (if y = (finitePointPt N i).1 then (1 : ℚ) else 0) := by
    intro y
    -- the green's exact simp set: both sides at the single's own point
    -- spelling, y a variable — no finitePointPt unfolding, no coe race.
    simp [codimensionPointCycle, Function.locallyFinsuppWithin.single_apply]
  have hval : (codimensionPointCycle (finitePointWorld N).X 0 (finitePointPt N i) :
      AlgebraicCycle (finitePointWorld N).X ℚ) ((finitePointEquiv N j).1) =
      (if (finitePointEquiv N j).1 = (finitePointPt N i).1 then (1 : ℚ) else 0) :=
    hev ((finitePointEquiv N j).1)
    -- WAVE 23: the green's EXACT idiom -- the ite stated at the SINGLE'S OWN
    -- point spelling `(finitePointPt N i).1` (no `finitePointPt` in the simp
    -- set: the attempt-2 residual proved the extra equation de-synced the
    -- rewrite), so `codimensionPointCycle`'s equation deposits
    -- `single (finitePointPt N i).1 1` and `single_apply` fires on the
    -- argument-first ite with both sides at the identical spelling -- the
    -- verbatim PointNormalForm:66-71 close, now under the same
    -- `open Classical in` regime.
  rw [hval, Pi.single_apply]
  by_cases hj : j = i
  · -- WAVE 25 (run-25 errors at :296/:298): both arms rebuilt SUBST-FREE
    -- with explicitly-typed have anchors -- the wave-23/24 pos arm died
    -- twice (the `subst hj` eliminated `i` leaving the hd-have's `i`
    -- unknown; the wave-24 neg arm's lambda elaboration pinned the if_neg
    -- pattern at the `finitePointEquiv N i` spelling against the goal's
    -- `finitePointPt N i` -- not syntactic, kabstract-dead).  Now: hd's TYPE
    -- is stated at the goal's own condition spelling, proven by rw [hj]
    -- (j → i on the left) + rfl (the constructor-projection defeq at
    -- default transparency); both if_pos patterns are then syntactic.
    have hd : (finitePointEquiv N j).1 = (finitePointPt N i).1 := by
      rw [hj]
      rfl
    rw [if_pos hd, if_pos hj]
  · -- WAVE 25: the same have-anchor discipline for the negative side --
    -- hiff's type stated at the goal's own condition, the injectivity
    -- chain (Subtype.ext + (finitePointEquiv N).injective over the
    -- structure-eta defeq finitePointPt N i ≡ finitePointEquiv N i) elaborated
    -- INSIDE the have where the expected type is already concrete.
    have hiff : ¬((finitePointEquiv N j).1 = (finitePointPt N i).1) := fun hcon =>
      hj ((finitePointEquiv N).injective (Subtype.ext hcon))
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
finite-point world at weight zero is the entire `H⁰` — a live rank-`N`
fiber: the honest Hodge structure of the zero-dimensional world. -/
theorem zeroFiber_eq_top :
    rationalHodgeSubspace (p := 0) (zeroBigrading N) = ⊤ := by
  -- WAVE 17 (pre-exposure D9): force the weight-0 implicit explicitly — the
  -- `2 * ?p =?= 0` nonlinear unification from the literal-0 index is not
  -- solvable; the resulting term is unchanged (tier-6's rw-pattern
  -- `rationalHodgeSubspace zeroBigrading` is preserved).
  have hpp : (HodgeBigrading.ppComponent (p := 0)) (zeroBigrading N) = ⊤ := rfl
  exact rationalHodgeSubspace_of_top (p := 0) (zeroBigrading N) hpp

/-! ## §6 THE ASSEMBLY -/

/-- The genuine cycle-class map at a dead weight: any linear map into the
subsingleton module is the zero map up to subsingleton collapse. -/
noncomputable def deadCycleClass (p : Nat) (hp : 0 < p) :
    codimensionCycles (finitePointWorld N).X p →ₗ[ℚ]
      RationalSingularCohomology (finitePointAnalytification N) (2 * p) :=
  { toFun := fun _ => 0
    map_add' := by
      intro Z W
      haveI hsub : Subsingleton
          (RationalSingularCohomology (finitePointAnalytification N) (2 * p)) :=
        finitePointCohomology_subsingleton N _ (by omega)
      exact Subsingleton.elim _ _
    map_smul' := by
      intro q Z
      haveI hsub : Subsingleton
          (RationalSingularCohomology (finitePointAnalytification N) (2 * p)) :=
        finitePointCohomology_subsingleton N _ (by omega)
      exact Subsingleton.elim _ _ }

/-- **THE GENERAL FINITE-POINT HODGE DATA.**  The `N`-point world's Hodge
structure: the discrete analytification, the honest `(0, 0)`-bigrading at
weight zero with the dead gradings above, and the genuine degree-map
cycle class. -/
noncomputable def finitePointHodgeData :
    HodgeBigradedBettiData (finitePointWorld N) where
  analytification := finitePointAnalytification N
  hodgeBigrading :=
    fun p =>
      match p with
      | 0 => zeroBigrading N
      | q + 1 => deadBigrading N (q + 1) (by omega)
  cycleClass :=
    fun p =>
      match p with
      | 0 => zeroCycleClass N
      | q + 1 => deadCycleClass N (q + 1) (by omega)

/-- The weight-`p` rational Hodge fiber of the assembled Hodge data. -/
theorem finitePointHodgeData_bigrading_zero :
    (finitePointHodgeData N).hodgeBigrading 0 = zeroBigrading N := rfl

/-- **THE DEAD FIBERS ARE SUBSINGLETONS.**  At every positive weight the
rational Hodge fiber of the finite-point world is a subsingleton: the
ambient module `H^{2p}` vanishes. -/
theorem deadFiber_subsingleton (p : Nat) (hp : 0 < p) :
    Subsingleton (ClassicalHodgeFiber (finitePointWorld N) (finitePointHodgeData N) p) := by
  have hsub : Subsingleton
      (RationalSingularCohomology (finitePointAnalytification N) (2 * p)) :=
    finitePointCohomology_subsingleton N _ (by omega)
  exact ⟨fun a b => Subtype.ext (@Subsingleton.elim _ hsub a.1 b.1)⟩

theorem finitePointHodgeData_cycleClass_zero :
    (finitePointHodgeData N).cycleClass 0 = zeroCycleClass N := rfl

theorem finitePointHodgeData_analytification_eq :
    (finitePointHodgeData N).analytification = finitePointAnalytification N := rfl

theorem finitePointHodgeData_bigrading_pos (p : Nat) (hp : 0 < p) :
    (finitePointHodgeData N).hodgeBigrading p = deadBigrading N p hp := by
  -- WAVE 17 (pre-exposure D11): rcases guarantees the dependent-hypothesis
  -- substitution the tactic-position match could not.
  rcases p with _ | q
  · exact absurd hp (by omega)
  · rfl

/-! ## §7 THE GENERIC WEIGHT-ZERO FIBER LAW -/

/-- **THE GENERIC WEIGHT-ZERO FIBER LAW.**  For ANY smooth projective
complex variety and ANY Hodge data on it, the rational Hodge fiber at
weight zero is ALWAYS the entire `H⁰`: the weight-`2·0` bigrading has
index type `Fin (2·0+1) = Fin 1`, the `(0, 0)`-position `ppIndex 0` is
the ONLY slot, and the `spans` field forces that single component to be
the whole complexification — every degree-zero class is unconditionally
of type `(0, 0)`, so the comap-pullback fiber is full.  This is the
weight-`0` discharger for the downstream certificate lane (the generic
form of the source's instance-level `zeroFiber_eq_top`, which needed the
constant-component bigrading; here the component is FORCED by `spans`
alone, for an arbitrary `HodgeBigrading`). -/
theorem rationalHodgeSubspace_eq_top_of_degree_zero
    {V : SmoothProjectiveComplexScheme}
    (H : HodgeBigradedBettiData V) :
    rationalHodgeSubspace (H.hodgeBigrading 0) = ⊤ := by
  -- The single-slot forcing: `Fin (2·0+1)` is a subsingleton index type
  -- (the `Fin 1` of the source's §1 helpers, reached by the kernel's
  -- literal defeq `2 * 0 + 1 ≡ 1` — the same defeq class the green source
  -- rides at `zeroBigrading.independent` for `Fin (0+1)`), so every
  -- component equals the `(0, 0)`-component `ppIndex 0`, and `spans`
  -- promotes the supremum — hence the component — to the top.
  have hpp : (H.hodgeBigrading 0).ppComponent = ⊤ := by
    haveI : Subsingleton (Fin (2 * 0 + 1)) := fin1_subsingleton
    apply le_antisymm le_top
    rw [← (H.hodgeBigrading 0).spans]
    exact iSup_le fun a => le_of_eq
      (congrArg (H.hodgeBigrading 0).component (Subsingleton.elim a (ppIndex 0)))
  exact rationalHodgeSubspace_of_top (H.hodgeBigrading 0) hpp

/-! ## Receipts -/

#check subsingleton_submodules_eq
#check subsingleton_complexification
#check fin1_subsingleton
#check zeroBigrading
#check deadBigrading
#check zeroCycleClass
#check finitePointPt
#check zeroCycleClass_point
#check rationalHodgeSubspace_of_top
#check zeroFiber_eq_top
#check finitePointHodgeData_bigrading_zero
#check finitePointHodgeData_bigrading_pos
#check deadFiber_subsingleton
#check deadCycleClass
#check finitePointHodgeData
#check finitePointHodgeData_cycleClass_zero
#check finitePointHodgeData_analytification_eq
#check rationalHodgeSubspace_eq_top_of_degree_zero

#print axioms subsingleton_submodules_eq
#print axioms subsingleton_complexification
#print axioms fin1_subsingleton
#print axioms zeroCycleClass_point
#print axioms rationalHodgeSubspace_of_top
#print axioms zeroFiber_eq_top
#print axioms deadFiber_subsingleton
#print axioms finitePointHodgeData_bigrading_pos
#print axioms rationalHodgeSubspace_eq_top_of_degree_zero

end GSTFinitePointHodgeData

end -- noncomputable section

/-!
DRAFT STATUS: WAVE 42 FILE 4 (task W42-C, the general-N finite-point world
lane).  This file is the static port of the CI-green N = 12 ancestor
(the 463-line Hodge-data file of the lane) under the binding campaign
rename map (the lane identifier family), the type map (point index type
`Fin N`, `variable (N : ℕ) [NeZero N]` at namespace top, every
definition taking `N` explicitly), and the source's declaration order
(§1–§6 verbatim in order, receipts verbatim in order).  Proof bodies are
the source's verbatim except for the explicit-`N` applications; the
decidability audit found no ancestor-specific decidability to re-derive
(PORT NOTE(n12) at the top of the namespace, at
`deadBigrading.independent`, and inside `zeroCycleClass_point`).  ONE new
theorem against the source:
`rationalHodgeSubspace_eq_top_of_degree_zero` (§7), the generic weight-0
fiber law — `ppComponent = ⊤` forced by `spans` over the singleton index
type `Fin (2·0+1)` via `fin1_subsingleton` + `iSup_le`, then
`rationalHodgeSubspace_of_top`; it is the certificate lane's
word_hodge/seed_hodge weight-0 discharger.

NOT YET CI-VERIFIED — the repo law forbids local compilation; this draft
must pass the wave-42 GitHub-Actions gate (Lean v4.33.0-rc2 +
Mathlib v4.33.0-rc2, per-module `lake build`, the campaign's standard
error/proof-hole grep gates) together with the upstream lane files (Agent A
`GSTFinitePointWorldCarrier`: `finitePointWorld N [NeZero N]`,
`finitePointScheme`, `finitePointEquiv`; Agent B
`GSTFinitePointAnalytification`: `finitePointAnalytification N [NeZero N]`;
the parallel `GSTFinitePointCohomology`: `finitePointCohomologyIso N
[NeZero N]`, `finitePointCohomology_subsingleton`) before it may be cited
as evidence.  The only new-in-this-file Mathlib lemmas not already
exercised by the green ancestor's own file are `iSup_le` (the exact dual
of the ancestor-green `le_iSup`, same CompleteLattice cluster), `le_of_eq`
(core Order.Basic), and `congrArg` (core, corpus-attested in the sibling
Cohomology/FoldWord files of the lane).  No `sorry`
or `admit` tactic, no `native_decide`, and no new `axiom` declaration
appears in this file.  (This doc block is anchored on the two
post-namespace `#check` receipts below — a trailing unattached module
docstring is not valid Lean 4 syntax.)
-/
#check @GSTFinitePointHodgeData.finitePointHodgeData
#check @GSTFinitePointHodgeData.rationalHodgeSubspace_eq_top_of_degree_zero
