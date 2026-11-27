import Mathlib
import HCUniverse2.GSTFiniteLineHonestHodgeData
import HCUniverse2.GSTFiniteLineGeneralMLaw
import HCUniverse2.GSTFiniteLineAnalytification
import HCUniverse2.GSTFiniteLineCycleCorrespondenceBasic
/- SPLIT PIECE of GSTFiniteLineCycleCorrespondence.lean (the wave-9-G module-split law: the runner-kill window demands small pieces) -/

/-
Copyright (c) 2026. The HC-PROOF campaign. All rights reserved.

# GATE-L — THE TWO M-CYCLE LETTERS (wave 4-C)

The M-cycle automorphism's graphs as genuine realized closed
correspondences on the honest Hodge data:

* the residue-degree receipt — the M-cycle is an isomorphism, so its
  residue field maps are bijective (the composition roundtrips through
  `residueFieldMap_id`/`residueFieldMap_comp`), and the residue weight is
  one (the green finrank pattern of the finite-point lane);
* the point-action receipt — the M-cycle acts on the generic points by
  `cyclicPred` (the comap of the graded rotation permutes the block
  ideals);
* the two letters `finiteLineCycleLetterOne` (weight one) and
  `finiteLineCycleLetterZero` (weight zero): the graph correspondence of the
  M-cycle endomorphism with the transported sphere-cycle pullback (letter one)/the
  component-iso conjugate of the index shift (letter zero) as the
  cohomological operator, rotating the honest point/component families.

Honesty ledger: every statement is proved unconditionally.  No `sorry`,
no new axioms, no `native_decide`.  The GitHub CI lane
`gst-finite-line-cycle-correspondence.yml` owns the kernel check.
-/

set_option maxHeartbeats 70000000
set_option maxRecDepth 20000
set_option trace.profiler true

noncomputable section

open CategoryTheory
open AlgebraicTopology
open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeRealizedClosedCorrespondenceAlgebra
open GSTClassicalHodgeRealizedCorrespondenceKrylovFinale
open GSTClassicalHodgeAnalytificationFunctoriality
open GSTClassicalHodgeFiniteClosedCorrespondence
open GSTClassicalHodgeFiniteClosedCorrespondenceOperator
open GSTClassicalHodgeProjectivePointTransport
open GSTNativeCodimensionCyclePresentation
open GSTSphereUnionComponents
open GSTSphereUnionPointClassGate
open GSTSingularCohomologyMaps
open GSTSphereCycleLegs
open GSTPositiveDimensionalLawLanding
open GSTFiniteLineRing
open GSTFiniteLineWorldCarrier
open GSTFiniteLineOverBase
open GSTFiniteLineGeneralMLaw
open GSTFiniteLinePointAlgebra
open GSTFiniteLineHonestHodgeData
open GSTComponentCohomologyZero
open GSTFiniteLineAnalytification

namespace GSTFiniteLineCycleCorrespondence
/-! ## §2 The point-action receipts (GATE-L waves 6-C: the ideal-level §2a + the order-level §2b, spliced from repairs/wave6_sec2a.lean and repairs/wave6_sec2b.lean) -/

/-! ## §2a The point-action lemmas (the ideal-level battle) -/

/-- **THE ONE-POINT BLOCK ARITHMETIC** — rotating the even variable index of
block `i` lands in block `cyclicSucc i`: `(blockRot M (blockVarLeft M i)).val / 2
= (cyclicSucc M i).val`.  This is the only new arithmetic in §2a: the
no-wrap/wrap case split (`2*i+2 < 2*M` vs `2*M ≤ 2*i+2`; in the wrap case
`2*i+2 = 2*M` exactly since `i.val < M`, so both sides are `0`), everything
else rides the green `blockRot`/`blockVarLeft` corpus lemmas. -/
private theorem blockRot_blockVarLeft (M : ℕ) [NeZero M] (i : Fin M) :
    (blockRot M (blockVarLeft M i)).val / 2 = (cyclicSucc M i).val := by
  have hi : i.val < M := i.isLt
  show (2 * i.val + 2) % (2 * M) / 2 = (i.val + 1) % M
  rcases Nat.lt_or_ge (2 * i.val + 2) (2 * M) with h | h
  · have hlt : i.val + 1 < M := by omega
    rw [Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt hlt]
    omega
  · have heq : 2 * i.val + 2 = 2 * M := by omega
    have hiM : i.val + 1 = M := by omega
    rw [heq, hiM, Nat.mod_self, Nat.mod_self]

/-- **THE SPAN RECEIPT (+2 SHIFT)** — every generator of the i-th generic
ideal maps, under the graded rotation, into the `cyclicSucc i`-th one: the
variable `X_b` (block `b/2 ≠ i`) rotates to `X_{blockRot b}` whose block is
`(b/2 + 1) mod M ≠ cyclicSucc i`.  This is the ≥-direction of the block-ideal
permutation, stated so that it can be re-indexed by either `cyclicPred` (for
L2) or used directly (for the Inv-mirror's ≤-direction). -/
private theorem lineGenericIdeal_le_comap_rotate (M : ℕ) [NeZero M] (i : Fin M) :
    lineGenericIdeal M i ≤ (lineGenericIdeal M (cyclicSucc M i)).comap
      (lineRotateGraded M) := by
  rw [lineGenericIdeal, Ideal.span_le]
  rintro _ ⟨b, rfl⟩
  show lineQuotientMap M (MvPolynomial.X (b : Fin (2 * M))) ∈
      Ideal.comap (lineRotateGraded M) (lineGenericIdeal M (cyclicSucc M i))
  rw [Ideal.mem_comap]
  show lineRotateHom M (lineQuotientMap M (MvPolynomial.X (b : Fin (2 * M)))) ∈
      lineGenericIdeal M (cyclicSucc M i)
  rw [lineRotateHom_mk, lineRename_X]
  refine mem_lineGenericIdeal M (cyclicSucc M i) ?_
  intro hcon
  have h1 : (blockRot M (b : Fin (2 * M))).val / 2
      = (blockRot M (blockVarLeft M i)).val / 2 := by
    rw [blockRot_blockVarLeft M i]
    exact hcon
  exact b.2 (((blockRot_sameBlock M (b : Fin (2 * M)) (blockVarLeft M i)).mp h1).trans
    (blockVarLeft_block M i))

/-- **THE SPAN RECEIPT (−2 SHIFT)** — the Inv-mirror: every generator of the
i-th generic ideal maps, under the inverse graded rotation, into the
`cyclicPred i`-th one (the `blockRot.symm` index shift is `−1` at the block
level, so the outside-block span pulls back to the predecessor's).  Route
mirrors `lineGenericIdeal_le_comap_rotate` through the carrier's Inv descent
(`lineRotateInvHom_mk` + the `renameEquiv`/`rename_X` pair) and folds the
symmetric pair by `Equiv.symm_apply_apply` before the block comparison. -/
private theorem lineGenericIdeal_le_comap_rotateInv (M : ℕ) [NeZero M] (i : Fin M) :
    lineGenericIdeal M i ≤ (lineGenericIdeal M (cyclicPred M i)).comap
      (lineRotateInvGraded M) := by
  rw [lineGenericIdeal, Ideal.span_le]
  rintro _ ⟨b, rfl⟩
  show lineQuotientMap M (MvPolynomial.X (b : Fin (2 * M))) ∈
      Ideal.comap (lineRotateInvGraded M) (lineGenericIdeal M (cyclicPred M i))
  rw [Ideal.mem_comap]
  show lineRotateInvHom M (lineQuotientMap M (MvPolynomial.X (b : Fin (2 * M)))) ∈
      lineGenericIdeal M (cyclicPred M i)
  rw [lineRotateInvHom_mk, MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X]
  refine mem_lineGenericIdeal M (cyclicPred M i) ?_
  intro hcon
  have hF : (blockRot M (blockVarLeft M (cyclicPred M i))).val / 2 = i.val := by
    have h := blockRot_blockVarLeft M (cyclicPred M i)
    rw [cyclicSucc_cyclicPred M i] at h
    exact h
  have hQ : ((blockRot M).symm (b : Fin (2 * M))).val / 2
      = (blockVarLeft M (cyclicPred M i)).val / 2 :=
    hcon.trans (blockVarLeft_block M (cyclicPred M i)).symm
  have hP := (blockRot_sameBlock M ((blockRot M).symm (b : Fin (2 * M)))
    (blockVarLeft M (cyclicPred M i))).mpr hQ
  rw [Equiv.apply_symm_apply (blockRot M) (b : Fin (2 * M))] at hP
  exact b.2 (hP.trans hF)

/-- **L1 — THE CYCLE'S POINT ACTION AT THE IDEAL LEVEL.**  Applying the
M-cycle automorphism to a point takes the point's homogeneous ideal to its
comap under the graded rotation: `finiteLineCycle M` is `Proj.map
(lineRotateGraded M)` (carrier §4), and `Proj.map`'s underlying point
function is the pin's `ProjectiveSpectrum.comapFun`
(Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Functor.lean:34-37), whose
first field is exactly `p.1.comap f`.  The whole equation is definitionally
the coercion chain `coe f := f.base` (Scheme.lean:108-109) →
`sheafedSpaceMap`'s `TopCat.ofHom (comap f hf)` base (Functor.lean:100-104) →
`comap`'s `toFun` (Functor.lean:40-44) → `comapFun` — the same chain the pin
closes by `rfl` at `map_preimage_basicOpen` (Functor.lean:160-161) — so the
proof is the show-bridge `rfl` at default transparency (the
`finiteLineCycle` δ-unfolding is pre-empted by restating the goal at
`Proj.map`, keeping the defeq burden inside the single `rfl` check). -/
theorem finiteLineCycle_apply_ideal (M : ℕ) [NeZero M] (x : finiteLineScheme M) :
    ((finiteLineCycle M) x).asHomogeneousIdeal = x.asHomogeneousIdeal.comap
      (lineRotateGraded M) :=
  show ((Proj.map (lineRotateGraded M) (lineRotate_irrelevant_le M)) x).asHomogeneousIdeal
      = x.asHomogeneousIdeal.comap (lineRotateGraded M) from rfl

/-- **L1's INV-MIRROR** — the same ideal-level receipt for the inverse cycle
(`finiteLineCycleInv` is `Proj.map` of the inverse graded rotation, carrier
§4 l. 520-522).  Consumed by `finiteLineCycle_genericPoint_inv` below. -/
private theorem finiteLineCycleInv_apply_ideal (M : ℕ) [NeZero M]
    (x : finiteLineScheme M) :
    ((finiteLineCycleInv M) x).asHomogeneousIdeal = x.asHomogeneousIdeal.comap
      (lineRotateInvGraded M) :=
  show ((Proj.map (lineRotateInvGraded M) (lineRotate_inv_irrelevant_le M)) x).asHomogeneousIdeal
      = x.asHomogeneousIdeal.comap (lineRotateInvGraded M) from rfl

/-- **L2 — THE BLOCK-IDEAL PERMUTATION.**  The comap of the j-th generic
homogeneous ideal under the graded rotation is the generic homogeneous ideal
of the predecessor block: the rotation's variable action `X_b ↦ X_{blockRot
b}` (the +2 index shift, one block up) pulls the outside-block-j span back
to the outside-block-(cyclicPred j) span.  Both inclusions: ≥ is the span
receipt `lineGenericIdeal_le_comap_rotate` re-indexed by `cyclicPred j`
(`cyclicSucc (cyclicPred j) = j`), ≤ is elementwise — a member `y` (with
`f y` in the j-th ideal) is `g (f y)` by the graded roundtrip, and the −2
span receipt maps `f y`'s membership into the predecessor ideal. -/
theorem lineRotate_comap_genericIdeal (M : ℕ) [NeZero M] (j : Fin M) :
    (lineGenericHomogeneousIdeal M j).comap (lineRotateGraded M) =
      lineGenericHomogeneousIdeal M (cyclicPred M j) := by
  refine HomogeneousIdeal.ext ?_
  rw [HomogeneousIdeal.toIdeal_comap, lineGenericHomogeneousIdeal_toIdeal,
    lineGenericHomogeneousIdeal_toIdeal]
  apply le_antisymm
  · intro y hy
    rw [Ideal.mem_comap] at hy
    have hround : lineRotateInvGraded M (lineRotateGraded M y) = y := by
      rw [← GradedRingHom.comp_apply, lineRotateInvGraded_comp,
        GradedRingHom.id_apply]
    rw [← hround]
    exact Ideal.mem_comap.mp (lineGenericIdeal_le_comap_rotateInv M j hy)
  · have h := lineGenericIdeal_le_comap_rotate M (cyclicPred M j)
    rw [cyclicSucc_cyclicPred M j] at h
    exact h

/-- **L2's INV-MIRROR** — the comap of the j-th generic homogeneous ideal
under the inverse graded rotation (the −2 index shift) is the generic
homogeneous ideal of the successor block.  The two inclusions are the
mirrors of L2's (the roundtrip now rides `lineRotateGraded_comp_inv`, and
the re-indexing rides `cyclicPred (cyclicSucc j) = j`).  Consumed by
`finiteLineCycle_genericPoint_inv` below. -/
private theorem lineRotateInv_comap_genericIdeal (M : ℕ) [NeZero M] (j : Fin M) :
    (lineGenericHomogeneousIdeal M j).comap (lineRotateInvGraded M) =
      lineGenericHomogeneousIdeal M (cyclicSucc M j) := by
  refine HomogeneousIdeal.ext ?_
  rw [HomogeneousIdeal.toIdeal_comap, lineGenericHomogeneousIdeal_toIdeal,
    lineGenericHomogeneousIdeal_toIdeal]
  apply le_antisymm
  · intro y hy
    rw [Ideal.mem_comap] at hy
    have hround : lineRotateGraded M (lineRotateInvGraded M y) = y := by
      rw [← GradedRingHom.comp_apply, lineRotateGraded_comp_inv,
        GradedRingHom.id_apply]
    rw [← hround]
    exact Ideal.mem_comap.mp (lineGenericIdeal_le_comap_rotate M j hy)
  · have h := lineGenericIdeal_le_comap_rotateInv M (cyclicSucc M j)
    rw [cyclicPred_cyclicSucc M j] at h
    exact h

/-- **L3 — THE CYCLE ACTS ON THE GENERIC POINTS BY THE CYCLIC
PREDECESSOR.**  The point-action receipt: the cycle carries the j-th generic
point to the `cyclicPred j`-th one.  Route: the ideal equality implies the
point equality (`projectiveSpectrum_ext`,
GSTFiniteLinePointAlgebra.lean:789-797), and the ideal equality is L1
instantiated at `lineGenericPoint M j` composed with L2 — the composition is
term-mode `Eq.trans` (the middle types close by the definitional field
`lineGenericPoint`'s `asHomogeneousIdeal := lineGenericHomogeneousIdeal M j`,
so no re-elaborated rw atom ever touches the `.X`-typed goal). -/
theorem finiteLineCycle_genericPoint (M : ℕ) [NeZero M] (j : Fin M) :
    finiteLineCycle M (lineGenericPoint M j) = lineGenericPoint M (cyclicPred M j) := by
  have h1 := finiteLineCycle_apply_ideal M (lineGenericPoint M j)
  have h2 := lineRotate_comap_genericIdeal M j
  refine projectiveSpectrum_ext ?_
  exact h1.trans h2

/-- **L3's INV-MIRROR** — the Inv-cycle carries the j-th generic point to the
`cyclicSucc j`-th one (the same route through `finiteLineCycleInv` /
`lineRotateInvGraded`, the carrier's inverse machinery at §4 l. 415-425,
520-522). -/
theorem finiteLineCycle_genericPoint_inv (M : ℕ) [NeZero M] (j : Fin M) :
    finiteLineCycleInv M (lineGenericPoint M j) = lineGenericPoint M (cyclicSucc M j) := by
  have h1 := finiteLineCycleInv_apply_ideal M (lineGenericPoint M j)
  have h2 := lineRotateInv_comap_genericIdeal M j
  refine projectiveSpectrum_ext ?_
  exact h1.trans h2

/-! ## §2b The order-level lemmas

The M-cycle is an order-automorphism of the honest prime lattice: monotone
(L4), reflecting (the comap-inverse), strictly monotone, and coheight-preserving
(L5); and it acts on the component index by the cyclic predecessor (L6). -/

attribute [local instance] specializationOrder

/-- **L4 — THE M-CYCLE IS MONOTONE.**  Specialization is reverse ideal
inclusion (`le_iff_ideal`), the cycle's point action is the comap of the graded
rotation (`finiteLineCycle_apply_ideal`), and comap is monotone. -/
theorem finiteLineCycle_mono (M : ℕ) [NeZero M] {x y : finiteLineScheme M}
    (h : x ≤ y) : finiteLineCycle M x ≤ finiteLineCycle M y :=
  (le_iff_ideal M (finiteLineCycle M x) (finiteLineCycle M y)).mpr
    (by
      rw [finiteLineCycle_apply_ideal M y, finiteLineCycle_apply_ideal M x]
      exact Ideal.comap_mono ((le_iff_ideal M x y).mp h))

/-- The cycle is injective on points (the Inv roundtrip). -/
theorem finiteLineCycle_inj (M : ℕ) [NeZero M] :
    Function.Injective (finiteLineCycle M) := by
  intro a b hab
  have h := congrArg (fun z => finiteLineCycleInv M z) hab
  rw [finiteLineCycleInv_apply M a, finiteLineCycleInv_apply M b] at h
  exact h

/-- **THE INV-MIRROR REFLECTION.**  The cycle reflects the specialization
order: undo the comap of the graded rotation by comapping with the inverse
rotation — `Ideal.comap_comap` (a `rfl` lemma) turns the double comap into the
comap of the composite, and the green quotient-level roundtrip
`lineRotateHom_comp_inv` closes the composite at the identity, so
`Ideal.comap_id` lands back on the original ideal. -/
theorem finiteLineCycle_reflect (M : ℕ) [NeZero M] {x y : finiteLineScheme M}
    (h : finiteLineCycle M x ≤ finiteLineCycle M y) : x ≤ y := by
  have hid : (finiteLineCycle M y).asHomogeneousIdeal.toIdeal ≤
      (finiteLineCycle M x).asHomogeneousIdeal.toIdeal :=
    (le_iff_ideal M (finiteLineCycle M x) (finiteLineCycle M y)).mp h
  rw [finiteLineCycle_apply_ideal M y, finiteLineCycle_apply_ideal M x] at hid
  -- canonicalization of §2a's comap spelling (defeq bridge at default
  -- transparency: `(lineRotateGraded M).toRingHom` unfolds to
  -- `(lineRotateHom M).toRingHom`)
  have hid' : Ideal.comap ((lineRotateHom M).toRingHom)
      y.asHomogeneousIdeal.toIdeal ≤
      Ideal.comap ((lineRotateHom M).toRingHom) x.asHomogeneousIdeal.toIdeal :=
    hid
  have hcomp : (lineRotateHom M).toRingHom.comp (lineRotateInvHom M).toRingHom =
      RingHom.id (lineQuotient M) := by
    apply RingHom.ext
    intro t
    show (lineRotateHom M) ((lineRotateInvHom M) t) = t
    have hrt := DFunLike.congr_fun (lineRotateHom_comp_inv M) t
    rw [AlgHom.comp_apply] at hrt
    exact hrt
  have hundo : ∀ J : Ideal (lineQuotient M),
      Ideal.comap ((lineRotateInvHom M).toRingHom)
        (Ideal.comap ((lineRotateHom M).toRingHom) J) = J := by
    intro J
    rw [Ideal.comap_comap, hcomp, Ideal.comap_id]
  have hkey : y.asHomogeneousIdeal.toIdeal ≤ x.asHomogeneousIdeal.toIdeal := by
    have hmono2 := Ideal.comap_mono (f := (lineRotateInvHom M).toRingHom) hid'
    rw [hundo, hundo] at hmono2
    exact hmono2
  exact (le_iff_ideal M x y).mpr hkey

/-- **THE INV-MIRROR MONO.**  The Inv-cycle is monotone (the reflection
transported through the roundtrip). -/
theorem finiteLineCycleInv_mono (M : ℕ) [NeZero M] {x y : finiteLineScheme M}
    (h : x ≤ y) : finiteLineCycleInv M x ≤ finiteLineCycleInv M y := by
  have h' : finiteLineCycle M (finiteLineCycleInv M x) ≤
      finiteLineCycle M (finiteLineCycleInv M y) := by
    rw [finiteLineCycle_apply_inv M x, finiteLineCycle_apply_inv M y]
    exact h
  exact finiteLineCycle_reflect M h'

/-- The cycle is strictly monotone (the mono plus the reflection). -/
theorem finiteLineCycle_strictMono (M : ℕ) [NeZero M] :
    StrictMono (finiteLineCycle M) := by
  intro a b hab
  refine ⟨finiteLineCycle_mono M hab.le, ?_⟩
  intro hcon
  exact absurd (finiteLineCycle_reflect M hcon) (not_le_of_gt hab)

/-- The cycle reflects the strict order (the reflection plus its own
strictness). -/
theorem finiteLineCycle_strictReflect (M : ℕ) [NeZero M]
    {x y : finiteLineScheme M}
    (h : finiteLineCycle M x < finiteLineCycle M y) : x < y := by
  refine ⟨finiteLineCycle_reflect M h.le, ?_⟩
  intro hle
  exact absurd (finiteLineCycle_mono M hle) (not_le_of_gt h)

/-- **L5 — THE M-CYCLE PRESERVES COHEIGHT.**  The cycle is a strictly
monotone order reflection whose strict-lift witness is the Inv-cycle
roundtrip, so the pin's `Order.coheight_eq_of_strictMono` transports the
coheight of every point. -/
theorem finiteLineCycle_coheight (M : ℕ) [NeZero M] (x : finiteLineScheme M) :
    Order.coheight (finiteLineCycle M x) = Order.coheight x := by
  refine (Order.coheight_eq_of_strictMono (finiteLineCycle M)
    (finiteLineCycle_strictMono M) ?_ x).symm
  intro a b hab
  refine ⟨finiteLineCycleInv M b, ?_, finiteLineCycle_apply_inv M b⟩
  have h1 : finiteLineCycle M a < finiteLineCycle M (finiteLineCycleInv M b) := by
    rw [finiteLineCycle_apply_inv M b]
    exact hab
  exact finiteLineCycle_strictReflect M h1

/-- **L6 — THE M-CYCLE ACTS ON THE COMPONENT INDEX BY THE CYCLIC
PREDECESSOR.**  The strict-below receipt: a coheight-one point lies strictly
below its component's generic point, the cycle (strictly monotone) carries
that below the cycled generic point `η_{cyclicPred j}` (the §2a generic
action), `lineComponentOf_unique` fixes the cycled point's component, and
`lineIndexOfGeneric_lineGenericPoint` reads off the index. -/
theorem finiteLineCycle_componentIndex (M : ℕ) [NeZero M]
    (x : CodimensionPoint (finiteLineWorld M).X 1) :
    lineIndexOfGeneric M (lineComponentOf M
      ⟨(finiteLineCycle M) x.1, (finiteLineCycle_coheight M x.1).trans x.2⟩) =
      cyclicPred M (lineIndexOfGeneric M (lineComponentOf M x)) := by
  have hspec : lineGenericPoint M (lineIndexOfGeneric M (lineComponentOf M x)) =
      (lineComponentOf M x).1 :=
    lineIndexOfGeneric_spec M (lineComponentOf M x)
  have hstep : x.1 < lineGenericPoint M (lineIndexOfGeneric M (lineComponentOf M x)) := by
    rw [hspec]
    exact lineComponentOf_above M x
  have hbelow : (finiteLineCycle M) x.1 <
      lineGenericPoint M (cyclicPred M (lineIndexOfGeneric M (lineComponentOf M x))) := by
    have hpush : (finiteLineCycle M) x.1 <
        (finiteLineCycle M)
        (lineGenericPoint M (lineIndexOfGeneric M (lineComponentOf M x))) :=
      finiteLineCycle_strictMono M hstep
    rw [finiteLineCycle_genericPoint M
      (lineIndexOfGeneric M (lineComponentOf M x))] at hpush
    exact hpush
  have hcomp := lineComponentOf_unique M
    ⟨(finiteLineCycle M) x.1, (finiteLineCycle_coheight M x.1).trans x.2⟩
    ⟨lineGenericPoint M (cyclicPred M (lineIndexOfGeneric M (lineComponentOf M x))),
      lineGenericPoint_coheight M
        (cyclicPred M (lineIndexOfGeneric M (lineComponentOf M x)))⟩
    hbelow
  exact (congrArg (lineIndexOfGeneric M) hcomp).symm.trans
    (lineIndexOfGeneric_lineGenericPoint M
      (cyclicPred M (lineIndexOfGeneric M (lineComponentOf M x))))


end GSTFiniteLineCycleCorrespondence

end -- noncomputable section
