/-
Copyright (c) 2026. The HC-Proof owner's GST hypothesis program.
-/
import HCUniverse2.GSTFinitePointShiftWord
import HCUniverse2.GSTNativeSingleFoldOrbitLawLanding
import HCUniverse2.GSTHypothesisSpanningCompilerFace

/-!
# THE FINITE-POINT LAW LANDING — THE GENERAL-N CAPSTONE OF THE LANE

The lane's Hodge-data wave delivers the canonical discrete Hodge data
`finitePointHodgeData N` on the `N`-point world for EVERY `N ≥ 1`, with
the genuine H⁰ iso `finitePointCohomologyIso N : H⁰ ≃ₗ[ℚ] (Fin N → ℚ)`;
the parallel shift-word wave delivers the cyclic shift word — a genuine
realized correspondence word whose cohomological operator is the cell
translation `i ↦ i+1` under the H⁰ iso.

This module discharges `NativeGSTSingleFoldOrbitLaw (finitePointWorld N)
(finitePointHodgeData N)` — for EVERY `N ≥ 1`, at a LIVE weight-0 fiber
of rank `N` — and composes the capstone package:

* `finitePointCertificate`: the shift word + the genuine seed cycle (the
  point cycle of the 0-th cell);
* `finitePointHodgeOrbit_coords`: the certificate's Hodge orbit IS the
  indicator family — the n-th iterate is the n-th cell's `Pi.single` for
  every `n < N`;
* `finitePointCertificate_isKrylovCyclic`: the orbit spans the whole
  weight-0 fiber (the single-vector family spans `Fin N → ℚ`; the
  span-image transport through the H⁰ iso);
* `finitePoint_law`: the law at every weight — weight 0 by the
  certificate, dead weights `p ≥ 1` by the empty word (`H^{2p} = 0`,
  subsingleton fiber);
* `finitePoint_FS`: the native⇒typed bridge `gst_FS_of_native_law`,
  INSTANTIATED for the general-N world;
* `finitePoint_everyHodge`: `EveryHodgeClassIsRationalAlgebraic` through
  the repository's conditional chain `exactHodge_of_one_GST_fold_orbit`;
* `the_finite_point_native_world_package`: the master capstone receipt.

## The honest scope (audit-accurate)

The world is zero-dimensional and the Hodge data is the CANONICAL DISCRETE
one, for every `N ≥ 1`:

* the weight-0 rational Hodge fiber is FORCED full for ANY Hodge data on
  ANY smooth projective complex world — the lane's generic weight-zero
  fiber law `rationalHodgeSubspace_eq_top_of_degree_zero` (the `Fin 1`
  index type of the weight-`2·0` bigrading has the `(0,0)`-position as
  its only slot, and the `spans` field promotes that single component to
  the top) — so the certificate's two Hodge fields are weight-zero
  trivialities, honestly discharged;
* the every-H conclusion is honestly earned but elementary here (on a
  zero-dimensional world every rational class is `(0,0)`-type and the
  degree map is an iso); in general the every-H form is NOT available —
  for an arbitrary Hodge datum the cycle-class map is unconstrained and
  single-fold orbits are trapped in their own range;
* the discharge is a restricted-class theorem under the AGENTS.md
  acceptance test — NOT the Hodge conjecture;
* the twelve-point world (the CI-green `N = 12` ancestor of this lane) is
  the motivating instance; the FORMAL bridge between the two files (the
  `N = 12` specialization of these declarations) is future work for the
  merge wave.

## The upstream contract (the lane waves; exact names consumed below)

From the lane's delivered files: `finitePointWorld N`, `finitePointEquiv`,
`finitePointAnalytification N`, `finitePointCohomologyIso N`,
`finitePointCohomology_subsingleton N`, `finitePointHodgeData N`,
`finitePointPt N`, `zeroCycleClass N`, `zeroCycleClass_point N`,
`zeroFiber_eq_top N`, `deadFiber_subsingleton N`, and the generic
`rationalHodgeSubspace_eq_top_of_degree_zero`.  From the parallel
shift-word wave (ASSUMED, task-sheet names):
`finitePointShiftWord N` and `shiftWord_op_single N` — only these two are
consumed here; the wave's `shiftWord_op N` and `finitePointShiftMatrix N`
are its own receipts, not needed by this file.

No `sorry`, no new axioms; the GitHub CI lane owns the kernel check.
-/

set_option maxHeartbeats 200000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTNativeCodimensionCyclePresentation
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeCycleOperatorNaturality
open GSTClassicalHodgeRealizedClosedCorrespondenceAlgebra
open GSTClassicalHodgeRealizedCorrespondenceKrylovFinale
open GSTClassicalHodgeExactClayStatement
open GSTHodgeSingleHypothesisConditional
open GSTHypothesisSpanningCompilerFace
open GSTNativeSingleFoldOrbitLawLanding
open GSTFinitePointWorldCarrier
open GSTFinitePointAnalytification
open GSTFinitePointCohomology
open GSTFinitePointHodgeData
-- PORT RISK(W42E-SHIFTNAMESPACE): the shift-word exports are consumed at
-- unqualified scope below.  The lane's file convention (every sibling
-- file declares the namespace matching its module name) predicts
-- `namespace GSTFinitePointShiftWord`; if the parallel wave declares the
-- exports at ROOT instead, DELETE this `open` line (the ancestor's own
-- contract note: the merge wave only adjusts the opens).
-- PORT RISK(W42E-IMPORTCHAIN): the four lane namespaces above
-- (WorldCarrier/Analytification/Cohomology/HodgeData) arrive
-- TRANSITIVELY through `import GSTFinitePointShiftWord` (the word's own
-- type consumes `finitePointHodgeData N` and `finitePointCohomologyIso
-- N`, whose files carry the rest of the chain); if the parallel wave's
-- import list is narrower, ADD the direct lane imports here.
open GSTFinitePointShiftWord

namespace GSTFinitePointLawLanding

variable (N : ℕ) [NeZero N]

/-! ## §1 THE SEED — the genuine point cycle of the live weight 0

The certificate's native seed is the point cycle of the 0-th closed point
of the finite-point world.  Its Hodge class, read in coordinates through
the H⁰ iso, is the 0-th indicator vector — the seed of the shift word's
Krylov orbit. -/

-- PORT NOTE(n12): the ancestor's seed is the two-point cycle `p₀ + p₁`
-- (the seed of the twelve-cell fold matrix `Twave`, whose orbit needs
-- BOTH leading cells).  The general-N shift word is the cyclic
-- translation `i ↦ i+1`: the Krylov orbit of the single 0-th indicator
-- runs through ALL `N` cells, so the honest seed here is ONE point
-- cycle — the 12-content (the two-cell seed) is re-derived as the
-- N-uniform one-cell seed.
/-- **THE SEED CYCLE.**  The genuine native 0-cycle: the 0-th closed
point of the finite-point world, with multiplicity one. -/
noncomputable def finitePointSeedCycle : codimensionCycles (finitePointWorld N).X 0 :=
  codimensionPointCycle (finitePointWorld N).X 0
    (finitePointPt N ⟨0, NeZero.pos N⟩)
-- PORT RISK(W42E-NEZEROPOS): the 0-th cell's membership proof
-- `NeZero.pos N` follows the task sheet's spelling (explicit `N`).  If
-- the pinned Mathlib takes `n` implicit, respell BOTH sites (here and
-- the base case of `finitePointHodgeOrbit_coords`) as
-- `⟨0, @NeZero.pos N _⟩`.  Designated one-line CI repair point.

/-- The seed's class lies in the weight-0 rational Hodge fiber: at weight
zero the fiber is the whole `H⁰` — FORCED for any Hodge data on any
smooth projective complex world. -/
theorem finitePointSeed_hodge :
    (finitePointHodgeData N).cycleClass 0 (finitePointSeedCycle N) ∈
      rationalHodgeSubspace ((finitePointHodgeData N).hodgeBigrading 0) := by
  -- PORT NOTE(n12): the ancestor's route bridges the fiber equation
  -- through the bigrading-constant rewrite
  -- (`twelvePointHodgeData_bigrading_zero`) plus the instance-level
  -- `zeroFiber_eq_top` (the ancestor's fiber law was stated over the
  -- constant bigrading).  The lane's HodgeData wave delivers the GENERIC
  -- weight-zero fiber law `rationalHodgeSubspace_eq_top_of_degree_zero`
  -- (§7 of that file) at exactly the projection spelling — the bridge
  -- rewrites are gone, the ground-have hoist discipline remains.
  have hfib : rationalHodgeSubspace ((finitePointHodgeData N).hodgeBigrading 0) = ⊤ :=
    rationalHodgeSubspace_eq_top_of_degree_zero (finitePointHodgeData N)
  rw [hfib]
  exact Submodule.mem_top

/-- **THE SEED COORDINATES.**  Under the H⁰ iso the seed's class is the
0-th indicator vector — the lane's point-class equation at the 0-th cell.

AUDIT (contract/API): consumes the lane's `zeroCycleClass_point` at
`i := ⟨0, NeZero.pos N⟩`; the class-map projection transport (rfl by
`finitePointHodgeData_cycleClass_zero`) and the seed's delta are hoisted
as ONE ground rfl-have — the ancestor's WAVE-19 discipline (elaborator-
level defeq on the from-terms, syntactic match on every subsequent
rewrite). -/
theorem finitePointSeed_coords :
    (finitePointCohomologyIso N)
      ((finitePointHodgeData N).cycleClass 0 (finitePointSeedCycle N)) =
      Pi.single ⟨0, NeZero.pos N⟩ (1 : ℚ) := by
  -- PORT NOTE(n12): the ancestor's seed is a SUM of two point classes
  -- and its coords proof is the map_add/iso-additivity chain; the
  -- one-cell seed needs no additivity — the single point-class equation
  -- closes directly.
  have hseed : (finitePointHodgeData N).cycleClass 0 (finitePointSeedCycle N) =
      zeroCycleClass N (codimensionPointCycle (finitePointWorld N).X 0
        (finitePointPt N ⟨0, NeZero.pos N⟩)) := rfl
  rw [hseed]
  exact zeroCycleClass_point N ⟨0, NeZero.pos N⟩

/-- **THE SEED CLASS IS NONZERO.**  The seed's Hodge class is nonzero:
its coordinate vector is the 0-th indicator, whose 0-th entry is `1 ≠ 0`.
This is the live-weight receipt — the certificate's seed is a genuine
algebraic cycle with nonzero Hodge class (no-free-lunch, satisfied
honestly).

AUDIT (API): the `map_zero` is the LinearEquiv-coercion mark of the
ancestor (the zero is ascribed at the class-map's own field spelling, so
the rewrite inside `hcoords` is syntactic); the final defeq closure runs
the same ite/decide reductions at `Fin N` the ancestor ran at its
literal cells. -/
theorem finitePointSeed_class_ne_zero :
    (finitePointHodgeData N).cycleClass 0 (finitePointSeedCycle N) ≠ 0 := by
  intro h0
  have hcoords := finitePointSeed_coords N
  have hz : (finitePointCohomologyIso N)
      (0 : RationalSingularCohomology (finitePointHodgeData N).analytification (2 * 0)) = 0 :=
    map_zero (finitePointCohomologyIso N).toLinearMap
  rw [h0, hz] at hcoords
  exact one_ne_zero
    (show (1 : ℚ) = (0 : ℚ) from congrFun hcoords.symm ⟨0, NeZero.pos N⟩)

/-! ## §2 THE CERTIFICATE — the shift word with the seed

PORT NOTE(n12): the ancestor's §2 certificate consumes its own word-wave's
Hodge-preservation export.  The shift-word wave (the parallel author of
`GSTFinitePointShiftWord`) delivers the word and its operator laws only;
the Hodge-preservation field is discharged HERE — at
weight zero it is a membership in `⊤`, by the lane's generic weight-zero
fiber law. -/

/-- **THE SHIFT WORD PRESERVES THE WEIGHT-ZERO HODGE FIBER.**  At weight
zero the rational Hodge fiber is the whole `H⁰` — forced for ANY Hodge
data (the `Fin 1` index type of the weight-`2·0` bigrading has the
`(0,0)`-position as its only slot, and the `spans` field promotes it to
the top) — so every operator preserves it. -/
theorem finitePointWord_hodge :
    ∀ alpha : ClassicalHodgeFiber (finitePointWorld N) (finitePointHodgeData N) 0,
      (realizedWordPair (finitePointShiftWord N)).cohomologyOperator alpha.1 ∈
        rationalHodgeSubspace ((finitePointHodgeData N).hodgeBigrading 0) := by
  intro alpha
  have hfib : rationalHodgeSubspace ((finitePointHodgeData N).hodgeBigrading 0) = ⊤ :=
    rationalHodgeSubspace_eq_top_of_degree_zero (finitePointHodgeData N)
  rw [hfib]
  exact Submodule.mem_top

/-- **THE KR YLOV CERTIFICATE OF THE LIVE WEIGHT.**  The shift word (the
cyclic translation of the N cells, realized as a genuine correspondence
word) with the genuine 0-th-point seed cycle.  The two Hodge fields are
exactly `finitePointWord_hodge` and the `⊤`-fiber membership of the
seed's class. -/
noncomputable def finitePointCertificate :
    RealizedCorrespondenceKrylovCertificate (finitePointWorld N) (finitePointHodgeData N) 0 where
  word := finitePointShiftWord N
  word_hodge := finitePointWord_hodge N
  seedCycle := finitePointSeedCycle N
  seed_hodge := finitePointSeed_hodge N

/-! ## §3 THE ORBIT IS THE INDICATOR FAMILY

Under the H⁰ iso, the underlying classes of the certificate's Hodge orbit
are the indicator vectors — by induction on the step equation, since the
word's operator is the cell translation (`shiftWord_op_single`). -/

-- PORT NOTE(n12): the ancestor's orbit equation is UNBOUNDED (Face 2's
-- total Krylov table `C` runs on all of `Nat`); the shift orbit only
-- RUNS for `n < N` (the last cell maps to 0) — the statement carries the
-- bound, and the induction generalizes it (the successor case derives
-- `n < N` from `n + 1 < N` by omega).
/-- **THE ORBIT IS THE INDICATOR FAMILY.**  For every `n < N`, the n-th
Hodge-orbit vector is the n-th cell's indicator under the H⁰ iso. -/
theorem finitePointHodgeOrbit_coords (n : Nat) :
    ∀ hn : n < N,
      (finitePointCohomologyIso N) ((finitePointCertificate N).hodgeOrbit n).1 =
        Pi.single ⟨n, hn⟩ (1 : ℚ) := by
  induction n with
  | zero =>
      intro hn
      -- the orbit's start is the seed; its class is the 0-th point class
      -- (the certificate/seed/class-map unfoldings are all rfl-level).
      have hseed : ((finitePointCertificate N).hodgeOrbit 0).1 =
          zeroCycleClass N (codimensionPointCycle (finitePointWorld N).X 0
            (finitePointPt N ⟨0, NeZero.pos N⟩)) := rfl
      rw [hseed]
      -- PORT NOTE(n12): the RHS proof components (`hn` vs `NeZero.pos N`)
      -- close by proof irrelevance; the ancestor's base case consumed
      -- its own seed-coords theorem, ours consumes the point-class
      -- equation directly.
      exact zeroCycleClass_point N ⟨0, NeZero.pos N⟩
  | succ n ih =>
      intro hn
      have hlt : n < N := by omega
      have hstep : ((finitePointCertificate N).hodgeOrbit (n + 1)).1 =
          (realizedWordPair (finitePointShiftWord N)).cohomologyOperator
            ((finitePointCertificate N).hodgeOrbit n).1 := rfl
      have hIH' : ((finitePointCertificate N).hodgeOrbit n).1 =
          (finitePointCohomologyIso N).symm (Pi.single ⟨n, hlt⟩ (1 : ℚ)) :=
        ((finitePointCohomologyIso N).symm_apply_apply
            ((finitePointCertificate N).hodgeOrbit n).1).symm.trans
          (congrArg (finitePointCohomologyIso N).symm (ih hlt))
      rw [hstep, hIH']
      -- PORT RISK(W42E-SUCCUNIFY): the `exact` closes across two
      -- definitional seams — the index projection
      -- `(⟨n, hlt⟩ : Fin N).val ≡ n` (constructor-projection iota) and
      -- the RHS proof components (`hn` vs the supplied `hi`, proof
      -- irrelevance).  Fallback: a `show` of the fully-spelled successor
      -- goal first.  Designated CI repair point.
      exact shiftWord_op_single N ⟨n, hlt⟩ hn

/-- The underlying class of the i-th cell's orbit vector is the
inverse-iso image of the i-th indicator (the coordinate theorem read
through `LinearEquiv.symm_apply_apply`, at the index `i : Fin N`). -/
theorem finitePointHodgeOrbit_symm (i : Fin N) :
    ((finitePointCertificate N).hodgeOrbit (i.val : Nat)).1 =
      (finitePointCohomologyIso N).symm (Pi.single i (1 : ℚ)) := by
  -- PORT NOTE(n12) / PORT RISK(W42E-FINETA): the ancestor's symm-theorem
  -- runs at the total table `C`; ours reads the bounded orbit equation
  -- at `n := i.val`.  The have's stated type is at the `i`-spelling
  -- while the coordinate theorem's type is at the
  -- `⟨i.val, i.isLt⟩`-spelling — the two are DEFINITIONALLY equal by Fin
  -- structure-eta (rfl-level; no lemma consumed).  Fallback: an explicit
  -- eta rewrite if the pin's defeq check stalls.  Designated CI repair
  -- point.
  have hcoords : (finitePointCohomologyIso N)
      ((finitePointCertificate N).hodgeOrbit (i.val : Nat)).1 =
      Pi.single i (1 : ℚ) :=
    finitePointHodgeOrbit_coords N (i.val : Nat) i.isLt
  exact ((finitePointCohomologyIso N).symm_apply_apply
      ((finitePointCertificate N).hodgeOrbit (i.val : Nat)).1).symm.trans
    (congrArg (finitePointCohomologyIso N).symm hcoords)

/-! ## §4 CYCLICITY — the orbit spans the whole live fiber -/

-- PORT NOTE(n12): this is the general-N replacement of Face 2's
-- `span_range_C_eq_top` (the twelve-cell coordinate spanning law the
-- ancestor consumes directly).  The decomposition
-- `v = ∑ i, v i • Pi.single i 1` is the lane's own CI-green idiom (the
-- `finNDualEquiv` triangle of the lane's cohomology file), verbatim at
-- `Fin N`.
/-- **THE SINGLE-VECTOR FAMILY SPANS THE FUNCTION SPACE.**  The rational
span of the `N` indicator vectors is the whole `Fin N → ℚ`: every
function is the univ-sum of its coordinate multiples. -/
theorem finitePointSingles_span :
    Submodule.span ℚ
      (Set.range fun i : Fin N => (Pi.single i (1 : ℚ) : Fin N → ℚ)) = ⊤ := by
  apply top_unique
  intro v _
  have hv : v = ∑ i, v i • (Pi.single i 1 : Fin N → ℚ) := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply, Pi.smul_apply,
      smul_eq_mul, mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq']
  rw [hv]
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))

-- PORT NOTE(n12): the ancestor's range-bridge is an EQUALITY (the
-- twelve-cell orbit IS the coordinate table's range, entrywise by its
-- own symm-theorem); the shift orbit's range is the indicator-image PLUS
-- the post-cycle zero (the last cell maps to 0), so the bridge here is
-- the SUBSET `symm '' indicators ⊆ range orbit`, and the ancestor's
-- `Submodule.span_image`/`Submodule.mem_map` mechanism runs inside
-- `Submodule.span_mono`.
/-- **THE AMBIENT SPAN.**  The rational span of the underlying orbit
classes is the whole `H⁰`: every coordinate vector is in the span of the
indicator family (`finitePointSingles_span`), and the orbit's range
CONTAINS the iso-preimages of all `N` indicators (the orbit runs through
every cell) — the membership transports through the span-image chain. -/
theorem finitePoint_orbitUnderlying_span :
    Submodule.span ℚ
      (Set.range fun n : Nat => @id (RationalSingularCohomology
        (finitePointAnalytification N) 0) ((finitePointCertificate N).hodgeOrbit n).1) = ⊤ := by
  apply top_unique
  intro u _
  have hEu : (finitePointCohomologyIso N) u ∈
      Submodule.span ℚ (Set.range fun i : Fin N => (Pi.single i (1 : ℚ) : Fin N → ℚ)) := by
    rw [finitePointSingles_span N]
    exact Submodule.mem_top
  have hsub : (finitePointCohomologyIso N).symm.toLinearMap ''
      (Set.range fun i : Fin N => (Pi.single i (1 : ℚ) : Fin N → ℚ)) ⊆
      Set.range fun n : Nat => @id (RationalSingularCohomology
        (finitePointAnalytification N) 0) ((finitePointCertificate N).hodgeOrbit n).1 := by
    -- PORT RISK(W42E-RINTRO): the two-level image/range destructure
    -- (the ancestor only destructs a bare range at this site); the
    -- standard Mathlib idiom.  Fallback: `intro y hy; obtain
    -- ⟨_, ⟨i, rfl⟩, rfl⟩ := hy`.  Designated CI repair point.
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨i.val, finitePointHodgeOrbit_symm N i⟩
  have hmem : u ∈ Submodule.span ℚ
      ((finitePointCohomologyIso N).symm.toLinearMap ''
        (Set.range fun i : Fin N => (Pi.single i (1 : ℚ) : Fin N → ℚ))) := by
    rw [Submodule.span_image]
    exact Submodule.mem_map.mpr ⟨(finitePointCohomologyIso N) u, hEu,
      (finitePointCohomologyIso N).symm_apply_apply u⟩
  exact Submodule.span_mono hsub hmem

/-- **CYCLICITY.**  The certificate is Krylov-cyclic: the rational span
of its Hodge orbit is the whole weight-0 fiber.  Route: the subtype-span
statement transports through `Submodule.span_range_subtype_eq_top_iff`
(the landing module's own §7 bridge pattern, here in the `.mpr`
direction) to the ambient span of the underlying classes, which is
`finitePoint_orbitUnderlying_span` at the `⊤`-fiber.

AUDIT (API): `Submodule.span_range_subtype_eq_top_iff` is consumed with
named implicit arguments `p`/`s` and the membership witness, mirroring
the landing file's `.mp` usage; the `.mpr` direction supplies the
ambient span.

PORT NOTE(n12): the ancestor's inner fiber equation needed the
bigrading-constant bridge first; the lane's generic weight-zero fiber law
fires at the projection spelling itself. -/
theorem finitePointCertificate_isKrylovCyclic :
    (finitePointCertificate N).IsKrylovCyclic :=
  (Submodule.span_range_subtype_eq_top_iff
    (p := rationalHodgeSubspace ((finitePointHodgeData N).hodgeBigrading 0))
    (s := fun n : Nat => ((finitePointCertificate N).hodgeOrbit n).1)
    (fun n => ((finitePointCertificate N).hodgeOrbit n).2)).mpr
      (by
        have hfib : rationalHodgeSubspace ((finitePointHodgeData N).hodgeBigrading 0) = ⊤ :=
          rationalHodgeSubspace_eq_top_of_degree_zero (finitePointHodgeData N)
        rw [hfib]
        exact finitePoint_orbitUnderlying_span N)

/-! ## §5 THE LAW — every weight of the general-N world -/

-- PORT NOTE(n12): the ancestor's dead branch calls
-- `deadFiber_subsingleton p hp` (no `N`); the lane threads `N`
-- explicitly.  The zero-seed membership witness is the landing module's
-- own `zeroCycleClass_mem_hodgeFiber` at the lane's Hodge data.
/-- **THE NATIVE GST SINGLE-FOLD ORBIT LAW, DISCHARGED ON THE GENERAL
FINITE-POINT WORLD.**  Weight 0 (the LIVE rank-N fiber): the shift-word
certificate, cyclic by the N-cell spanning.  Dead weights `p ≥ 1`
(`H^{2p} = 0`): the empty-word certificate with the zero seed, cyclic by
the subsingleton argument — the landing module's own cheap-class
machinery. -/
theorem finitePoint_law :
    NativeGSTSingleFoldOrbitLaw (finitePointWorld N) (finitePointHodgeData N) := by
  intro p
  by_cases hp : 0 < p
  · refine ⟨emptyWordKrylovCertificate (p := p) 0
      (zeroCycleClass_mem_hodgeFiber (finitePointHodgeData N) p), ?_⟩
    exact isKrylovCyclic_of_subsingleton (deadFiber_subsingleton N p hp) _
  · have hp0 : p = 0 := by omega
    subst hp0
    exact ⟨finitePointCertificate N, finitePointCertificate_isKrylovCyclic N⟩

/-! ## §6 THE BRIDGE INSTANTIATION — the FS law, fed at general N -/

-- PORT NOTE(n12): the statement is spelled at
-- `(finitePointHodgeData N).analytification` — the bridge
-- `gst_FS_of_native_law`'s OWN result spelling (the ancestor's WAVE-33
-- receipt: the def-spelled statement forced a projection-vs-def isDefEq
-- that burned the heartbeat budget; the respell eliminates the
-- comparison entirely).  The master package's third conjunct is respelled
-- identically so the ⟨…, finitePoint_FS N, …⟩ component also checks
-- syntactically.
/-- **THE TYPED FS LAW, INSTANTIATED.**  Through the landing module's
native⇒typed bridge `gst_FS_of_native_law`, the law yields — for every
weight — a genuine typed `GSTHypothesisData` over the native cycle module
and the rational singular cohomology whose complete GST hypothesis holds
with the GENUINE rational Hodge fiber of that weight. -/
theorem finitePoint_FS : ∀ p : Nat,
    ∃ D : GSTHypothesisComplete.GSTHypothesisData
        (codimensionCycles (finitePointWorld N).X p)
        (RationalSingularCohomology (finitePointHodgeData N).analytification (2 * p)),
      GSTHypothesisComplete.GSTHypothesisComplete D ∧
      D.hodgeFiber = rationalHodgeSubspace ((finitePointHodgeData N).hodgeBigrading p) :=
  gst_FS_of_native_law (finitePoint_law N)

/-! ## §7 THE EXACT-HODGE CONSEQUENCE -/

/-- **EVERY HODGE CLASS OF THE FINITE-POINT WORLD IS RATIONAL
ALGEBRAIC.**  Through the repository's conditional chain
`exactHodge_of_one_GST_fold_orbit` — applied, for every `N ≥ 1`, at a
world that discharges its own hypothesis at a live weight.  Honest
scope: on a zero-dimensional world every rational class is `(0,0)`-type
and the degree map is an iso, so this carries no transcendental content;
the content of the law it consumes is the N-cell spanning at weight 0. -/
theorem finitePoint_everyHodge :
    EveryHodgeClassIsRationalAlgebraic (finitePointHodgeData N) :=
  exactHodge_of_one_GST_fold_orbit (finitePoint_law N)

/-! ## §8 THE MASTER CAPSTONE — THE GENERAL-N WORLD PACKAGE

The complete receipt of the finite-point native world:

* the law itself, discharged at the live rank-N weight 0 and free above;
* the exact-Hodge consequence through the repository's conditional chain;
* the per-weight typed FS law with the genuine rational Hodge fiber
  (the native⇒typed bridge, instantiated and fed);
* the dead-weight fact: the weight-1 fiber is a subsingleton (by
  dimension, `H² = 0`);
* the live-weight receipt: a genuine algebraic 0-cycle with nonzero Hodge
  class at the live weight — the seed (the 0-th point cycle) itself, the
  honest no-free-lunch witness (cyclicity at a live weight forces exactly
  this).

PORT NOTE(n12): the ancestor's fourth conjunct is
`deadFiber_subsingleton 1 (by norm_num)`; the lane threads `N` and uses
the `omega` form of the positivity side goal.  The fifth conjunct's
witness is the ancestor's two-point seed; ours is the one-cell seed
(the §1 re-derivation). -/
theorem the_finite_point_native_world_package :
    NativeGSTSingleFoldOrbitLaw (finitePointWorld N) (finitePointHodgeData N) ∧
    EveryHodgeClassIsRationalAlgebraic (finitePointHodgeData N) ∧
    (∀ p : Nat,
      ∃ D : GSTHypothesisComplete.GSTHypothesisData
        (codimensionCycles (finitePointWorld N).X p)
        (RationalSingularCohomology (finitePointHodgeData N).analytification (2 * p)),
        GSTHypothesisComplete.GSTHypothesisComplete D ∧
        D.hodgeFiber = rationalHodgeSubspace ((finitePointHodgeData N).hodgeBigrading p)) ∧
    Subsingleton (ClassicalHodgeFiber (finitePointWorld N) (finitePointHodgeData N) 1) ∧
    (∃ Z : codimensionCycles (finitePointWorld N).X 0,
      (finitePointHodgeData N).cycleClass 0 Z ∈
        rationalHodgeSubspace ((finitePointHodgeData N).hodgeBigrading 0) ∧
      (finitePointHodgeData N).cycleClass 0 Z ≠ 0) :=
  ⟨finitePoint_law N, finitePoint_everyHodge N, finitePoint_FS N,
    deadFiber_subsingleton N 1 (by omega),
    ⟨finitePointSeedCycle N, finitePointSeed_hodge N,
      finitePointSeed_class_ne_zero N⟩⟩

/-! ## §9 Receipts -/

#check finitePointSeedCycle
#check finitePointSeed_hodge
#check finitePointSeed_coords
#check finitePointSeed_class_ne_zero
#check finitePointWord_hodge
#check finitePointCertificate
#check finitePointHodgeOrbit_coords
#check finitePointHodgeOrbit_symm
#check finitePointSingles_span
#check finitePoint_orbitUnderlying_span
#check finitePointCertificate_isKrylovCyclic
#check finitePoint_law
#check finitePoint_FS
#check finitePoint_everyHodge
#check the_finite_point_native_world_package

#print axioms finitePointSeed_coords
#print axioms finitePointSeed_class_ne_zero
#print axioms finitePointWord_hodge
#print axioms finitePointHodgeOrbit_coords
#print axioms finitePointHodgeOrbit_symm
#print axioms finitePointSingles_span
#print axioms finitePoint_orbitUnderlying_span
#print axioms finitePointCertificate_isKrylovCyclic
#print axioms finitePoint_law
#print axioms finitePoint_FS
#print axioms finitePoint_everyHodge
#print axioms the_finite_point_native_world_package

end GSTFinitePointLawLanding

end -- noncomputable section

/-!
DRAFT STATUS: WAVE 42 FILE 6 (task W42-E2, the general-N law-landing
lane file — the KILL FILE, retry).  This file is the static port of the
CI-green `N = 12` ancestor (the 498-line law-landing capstone of the
lane) under the binding campaign rename map (the lane identifier
family), the type map (`Fin N` for the cell index type, `variable
(N : ℕ) [NeZero N]` at namespace top, every definition applied at the
explicit `N`), and the source's declaration order (§1–§8 verbatim in
order, receipts verbatim in order).  Against the source, THREE proof
architectures are re-derived (each site flagged `PORT NOTE(n12)`): the
seed is the ONE-point cycle (the shift word's orbit saturates from a
single cell; the ancestor's two-point seed was fold-matrix-specific);
the word-Hodge field is discharged HERE through the lane's generic
weight-zero fiber law (the ancestor consumed its own word-wave export);
and the cyclicity transport runs through the local single-vector
spanning law `finitePointSingles_span` (Face 2's twelve-cell coordinate
spanning law has no general-N form), with the range-bridge
weakened from equality to the subset (the shift orbit's tail is zero
after N steps).  PORT RISKs are flagged inline at the designated CI
repair points: W42E-SHIFTNAMESPACE and W42E-IMPORTCHAIN (the shift-word
seam), W42E-NEZEROPOS (the 0-th cell's membership-proof spelling),
W42E-SUCCUNIFY (the successor case's two definitional seams),
W42E-FINETA (the Fin structure-eta defeq), W42E-RINTRO (the two-level
image destructure).

NOT YET CI-VERIFIED — the repo law forbids local compilation; this draft
must pass the wave-42 GitHub-Actions gate (Lean v4.33.0-rc2 +
Mathlib v4.33.0-rc2, per-module `lake build`, the campaign's standard
error/proof-hole grep gates) together with the upstream lane files
(Agent A `GSTFinitePointWorldCarrier`, Agent B
`GSTFinitePointAnalytification`, the parallel
`GSTFinitePointCohomology`, `GSTFinitePointHodgeData`, and the parallel
`GSTFinitePointShiftWord`) before it may be cited as evidence.  No
`sorry` or `admit` tactic, no `native_decide`, and no new `axiom`
declaration appears in this file.  (This doc block is anchored on the
two post-namespace `#check` receipts below — a trailing unattached
module docstring is not valid Lean 4 syntax.)
-/
#check @GSTFinitePointLawLanding.finitePoint_law
#check @GSTFinitePointLawLanding.the_finite_point_native_world_package
