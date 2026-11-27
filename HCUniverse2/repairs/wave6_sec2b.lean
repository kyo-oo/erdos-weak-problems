/-
STAGING FILE — GATE-L §2b (wave 6, W3-B) — THE ORDER-LEVEL LEMMAS.

Splice target: the GATE-L module (`GSTFiniteLineCycleCorrespondence.lean`), inside
namespace `GSTFiniteLineCycleCorrespondence`, AFTER the §2a wave's lemmas land and
BEFORE the module's `end`.  This file is section text only: no imports, no
namespace opens, no `end`.

§2A DEPENDENCIES (assumed already landed in the same module, in these forms):

  theorem finiteLineCycle_apply_ideal (M : ℕ) [NeZero M] (x : finiteLineScheme M) :
      (finiteLineCycle M x).asHomogeneousIdeal.toIdeal =
        Ideal.comap (lineRotateGraded M).toRingHom x.asHomogeneousIdeal.toIdeal
  -- (the toIdeal-level comap form; the hom spelling may equally be
  --  `(lineRotateHom M).toRingHom` — both are defeq to the one used below,
  --  and the §2b proofs bridge that defeq explicitly at `have hid'`.)

  theorem finiteLineCycle_genericPoint (M : ℕ) [NeZero M] (i : Fin M) :
      finiteLineCycle M (lineGenericPoint M i) = lineGenericPoint M (cyclicPred M i)
  -- (the cyclicPred direction is forced: the comap of the i-th generic ideal
  --  under `X_a ↦ X_{a+2}` is the generic ideal of the predecessor block.)

The other two §2a lemmas (`lineRotate_comap_genericIdeal`,
`finiteLineCycle_genericPoint_inv`) are not consumed by §2b.

L5 ROUTE DECISION (W3-B): Route 1 — the order-embedding.  The pin's
`Order.coheight_eq_of_strictMono` (Mathlib.Order.KrullDimension, pin line
331-333; green usage GSTClassicalHodgeSuccessorGroundFloor.lean:216) transports
coheight through ANY strict monotone map with the strict-lift property, for ALL
points, with no point classification.  Route 2 (the closed-point-only chain)
needs `Order.coheight x ≤ 1` at ARBITRARY points, which is not green anywhere
(the corpus's no-intermediate law is only at the specific `[1:0]` closed
ideal), so it was rejected.  The Inv-mirror mono is derived inside §2b from
the comap-inverse of the graded rotation (`Ideal.comap_comap` is `rfl`,
`lineRotateHom_comp_inv` closes the composite at the identity), not from an
Inv-apply-ideal lemma.
-/

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

/-- The cycle is strictly monotone (the mono plus the injectivity). -/
theorem finiteLineCycle_strictMono (M : ℕ) [NeZero M] :
    StrictMono (finiteLineCycle M) := by
  intro a b hab
  refine ⟨finiteLineCycle_mono M hab.le, ?_⟩
  intro hcon
  exact ne_of_lt hab (finiteLineCycle_inj M hcon)

/-- The cycle reflects the strict order (the reflection plus its own
strictness). -/
theorem finiteLineCycle_strictReflect (M : ℕ) [NeZero M]
    {x y : finiteLineScheme M}
    (h : finiteLineCycle M x < finiteLineCycle M y) : x < y :=
  ⟨finiteLineCycle_reflect M h.le, ne_of_lt h⟩

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
