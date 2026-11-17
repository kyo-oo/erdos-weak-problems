import Mathlib.Topology.KrullDimension
import Mathlib.Topology.Sober
import GSTClassicalHodgePrincipalSectionDescent

/-!
# GST CLASSICAL HODGE — CODIMENSION-ONE POINTS OF PROPER PRINCIPAL CUTS

The principal-section engine gives a genuinely proper closed subset through
which recursive support cutting proceeds.  In a Noetherian quasi-sober
irreducible space, the ambient coheight-one points of a non-dense subset are
controlled by the generic points of the irreducible components of its closed
hull: a point of coheight one is covered by the ambient generic point, so its
closure is a maximal proper irreducible closed subset, hence an irreducible
component of the proper closed hull, whose generic point is unique by T0.
A Noetherian space has finitely many irreducible components, so the locus is
finite.

This module packages that theorem for closed cuts and then specializes it to
the source-dependent principal cut produced by the projective geometry layer.
The result is the first numerical codimension step from the geometric cutting
machine.
-/

set_option maxHeartbeats 30000000
set_option maxRecDepth 1000000

noncomputable section

open TopologicalSpace
open AlgebraicGeometry
open GSTProjectiveOverC
open GSTClassicalHodgePrincipalSectionDescent
open GSTClassicalHodgeProjectivePrincipalSection
open GSTClassicalHodgePrincipalSectionNoetherian
open GSTSmoothProjectiveNoetherian

/-! ### Order-theoretic prerequisites shared with the successor layers

The relative-successor module refers to these statements under their exact
names, so they are provided here once, in the module below that entire chain. -/

attribute [local instance] specializationOrder in
/-- Membership characterization of the specialization order: `a ≤ b` holds
exactly when `a` lies in the closure of `b`.  The successor-layer modules
refer to this statement under this exact name. -/
theorem specializationOrder_iff_specializes
    {X : Type*} [TopologicalSpace X] [T0Space X] {a b : X} :
    a ≤ b ↔ a ∈ closure ({b} : Set X) := by
  constructor
  · intro h
    exact (specializes_iff_mem_closure (x := b) (y := a)).mp h
  · intro h
    exact (specializes_iff_mem_closure (x := b) (y := a)).mpr h

attribute [local instance] specializationOrder in
/-- In a Noetherian quasi-sober irreducible T0-space, a subset whose closure is
proper has only finitely many points of ambient coheight one: such points are
exactly the generic points of irreducible components of the proper closed
hull, and a Noetherian space has only finitely many irreducible components. -/
theorem TopologicalSpace.NoetherianSpace.finite_coheight_one_of_closure_ne_univ
    {X : Type*} [TopologicalSpace X] [QuasiSober X] [IrreducibleSpace X]
    [T0Space X] [NoetherianSpace X] {S : Set X}
    (hS : closure S ≠ Set.univ) :
    {x ∈ S | Order.coheight x = 1}.Finite := by
  classical
  set D := closure S with hDdef
  have hDclosed : IsClosed D := isClosed_closure
  have hSD : S ⊆ D := subset_closure
  have hDne : D ≠ Set.univ := hS
  -- The ambient generic point of the irreducible space
  obtain ⟨η, hη⟩ : ∃ η : X, IsGenericPoint η (Set.univ : Set X) :=
    QuasiSober.sober (IrreducibleSpace.isIrreducible_univ X) isClosed_univ
  -- STEP 1: any strict generalization of an S-point of coheight one is η
  have hgen : ∀ x ∈ S, Order.coheight x = 1 →
      ∀ γ : X, x < γ → IsGenericPoint γ (Set.univ : Set X) := by
    intro x _hxS hco γ hγ
    have hanti : Order.coheight γ ≤ Order.coheight x :=
      Order.coheight_anti hγ.le
    have htop : Order.coheight γ < ⊤ := by
      apply hanti.trans_lt
      rw [hco]
      exact WithTop.natCast_lt_top 1
    have hstrict : Order.coheight γ < Order.coheight x :=
      Order.coheight_strictAnti hγ htop
    rw [hco] at hstrict
    have hc0 : Order.coheight γ = 0 := (Order.lt_one_iff).mp hstrict
    have hmax : IsMax γ := (Order.coheight_eq_zero).mp hc0
    -- γ ≤ η since the generic point's closure is everything; maximality
    -- of γ then forces γ = η
    have hγη : γ ≤ η := hη.specializes (Set.mem_univ γ)
    have hγeq : γ = η := le_antisymm hγη (hmax hγη)
    subst hγeq
    exact hη
  -- STEP 2: every coheight-one point of S is the generic point (inside the
  -- closed hull D) of an irreducible component of D
  have hsub : ∀ x ∈ S, Order.coheight x = 1 →
      ∃ u : D, (u : X) = x ∧ u ∈ genericPoints D := by
    intro x hxS hco
    have hxD : x ∈ D := hSD hxS
    refine ⟨⟨x, hxD⟩, rfl, ?_⟩
    -- membership in `genericPoints D` unfolds to maximality of the closure
    show Maximal IsIrreducible (closure ({⟨x, hxD⟩} : Set D))
    refine ⟨IsIrreducible.closure isIrreducible_singleton, ?_⟩
    intro W hWirr hleW
    -- the ambient image of W is irreducible
    have hWirrImg : IsIrreducible (Subtype.val '' W) :=
      hWirr.image Subtype.val continuous_subtype_val.continuousOn
    -- its ambient closure is an irreducible closed set inside D
    have hK'D : closure (Subtype.val '' W) ⊆ D := by
      apply closure_minimal _ hDclosed
      rintro y ⟨v, _, rfl⟩
      exact v.2
    -- the ambient closure of x is the image of the subtype closure
    have hbridge : Subtype.val '' (closure ({⟨x, hxD⟩} : Set D))
        = closure ({x} : Set X) := by
      have hclos : closure ({⟨x, hxD⟩} : Set D)
          = Subtype.val ⁻¹' closure (Subtype.val '' ({⟨x, hxD⟩} : Set D)) :=
        Topology.IsInducing.closure_eq_preimage_closure_image
          (f := (Subtype.val : D → X))
          (Topology.IsInducing.subtypeVal)
          ({⟨x, hxD⟩} : Set D)
      rw [hclos, Set.image_preimage_eq_inter_range,
        Set.inter_eq_self_of_subset_left
          (closure_minimal
            (Set.image_subset_range (Subtype.val : D → X)
              ({⟨x, hxD⟩} : Set D))
            (by rw [Subtype.range_coe]; exact hDclosed))]
      simp
    -- x lies in the ambient closure of the image of W
    have hxK' : x ∈ closure (Subtype.val '' W) := by
      have hxmem : x ∈ closure ({x} : Set X) :=
        subset_closure (Set.mem_singleton x)
      rw [← hbridge] at hxmem
      obtain ⟨v, hv, hval⟩ := hxmem
      have hvW : x ∈ Subtype.val '' W := ⟨v, hleW hv, hval⟩
      exact subset_closure hvW
    -- the ambient closure of the image of W has a generic point
    obtain ⟨γ, hγW⟩ : ∃ γ : X, IsGenericPoint γ (closure (Subtype.val '' W)) :=
      QuasiSober.sober (IsIrreducible.closure hWirrImg) isClosed_closure
    -- x is below γ in the specialization order
    have hxγ : x ≤ γ := hγW.specializes hxK'
    by_cases hxeq : x = γ
    · -- x = γ: the ambient closures coincide, so W lies in the subtype closure
      have hK'eq : closure (Subtype.val '' W)
          = closure ({x} : Set X) := by
        rw [hxeq]
        exact (hγW.def).symm
      intro w hw
      have hwimg : (w : X) ∈ Subtype.val '' W :=
        ⟨w, hw, rfl⟩
      have hwclos : (w : X) ∈ closure (Subtype.val '' W) :=
        subset_closure hwimg
      rw [hK'eq, ← hbridge] at hwclos
      obtain ⟨v, hv, hval⟩ := hwclos
      have hvw : v = w := Subtype.ext hval
      exact hvw ▸ hv
    · -- x < γ: STEP 1 forces γ to be the ambient generic point, so the
      -- ambient closure of W is everything, contradicting properness of D
      have hxltγ : x < γ := lt_of_le_of_ne hxγ hxeq
      have hγuniv : IsGenericPoint γ (Set.univ : Set X) :=
        hgen x hxS hco γ hxltγ
      have hK'univ : closure (Subtype.val '' W) = Set.univ :=
        hγW.def.symm.trans hγuniv.def
      rw [hK'univ] at hK'D
      exact absurd (Set.eq_univ_of_univ_subset hK'D) hDne
  -- STEP 3: finiteness of the generic points of the components of D
  -- (subtype T0 and subtype Noetherian are global Mathlib instances)
  have hcomp : (irreducibleComponents D).Finite :=
    NoetherianSpace.finite_irreducibleComponents
  have hgenfin : (genericPoints D).Finite :=
    genericPoints.finite hcomp
  -- assemble the finite bound
  have hfinimg : (Subtype.val '' (genericPoints D : Set D)).Finite :=
    hgenfin.image Subtype.val
  refine hfinimg.subset ?_
  rintro x ⟨hxS, hco⟩
  obtain ⟨u, rfl, hugen⟩ := hsub x hxS hco
  exact Set.mem_image_of_mem _ hugen

namespace GSTClassicalHodgeProperCutCodimensionOne

attribute [local instance] specializationOrder in
/-- A proper closed subset of a Noetherian quasi-sober irreducible space has
only finitely many ambient points of coheight one. -/
theorem finite_coheight_one_of_proper_closed
    {X : Type*} [TopologicalSpace X] [QuasiSober X] [IrreducibleSpace X]
    [T0Space X] [NoetherianSpace X]
    (C : Set X) (hC : IsClosed C) (hproper : C ≠ Set.univ) :
    {x ∈ C | Order.coheight x = 1}.Finite := by
  refine TopologicalSpace.NoetherianSpace.finite_coheight_one_of_closure_ne_univ ?_
  rw [hC.closure_eq]
  exact hproper

/-- Every source-specific principal cut in an irreducible smooth projective
carrier has only finitely many ambient codimension-one points. -/
theorem finite_principal_cut_coheight_one
    (V : SmoothProjectiveComplexScheme)
    [IrreducibleSpace V.X]
    (x : V.X) :
    {y ∈ cutSupport V x | Order.coheight y = 1}.Finite := by
  letI : IsNoetherian V.X := smoothProjectiveIsNoetherian V
  letI : NoetherianSpace V.X := smoothProjectiveNoetherianSpace V
  apply finite_coheight_one_of_proper_closed
  · exact (principalSectionIdeal V
      (positiveHomogeneousSeparator V.projective.n
        (V.projective.immersion x)).equation).support.isClosed
  · intro h
    refine principalSectionAt_support_ne_univ V x ?_
    apply TopologicalSpace.Closeds.ext
    simpa [cutSupport] using h

/-- A nonempty codimension-one locus of the selected cut can be packaged as a
finite set of genuine Stage-2D codimension-one points. -/
noncomputable def principalCutCodimensionOneFinset
    (V : SmoothProjectiveComplexScheme)
    [IrreducibleSpace V.X]
    (x : V.X) : Finset (GSTNativeCodimensionCyclePresentation.CodimensionPoint V.X 1) := by
  classical
  let s : Set V.X := {y ∈ cutSupport V x | Order.coheight y = 1}
  have hs : s.Finite := finite_principal_cut_coheight_one V x
  exact hs.toFinset.attach.map
    ⟨fun y => (⟨y.1, ((Set.Finite.mem_toFinset hs).mp y.2).2⟩ :
        GSTNativeCodimensionCyclePresentation.CodimensionPoint V.X 1),
      by
        intro a b h
        exact Subtype.ext
          (congrArg (Subtype.val :
            GSTNativeCodimensionCyclePresentation.CodimensionPoint V.X 1 → V.X) h)⟩

/-- Numerical one-step crown: strict projective cutting has a finite native
codimension-one target locus, expressed directly in the coheight convention
used by `codimensionCycles`. -/
theorem principal_cut_codimension_one_crown
    (V : SmoothProjectiveComplexScheme)
    [IrreducibleSpace V.X]
    (x : V.X) :
    {y ∈ cutSupport V x | Order.coheight y = 1}.Finite
      ∧ ∀ y : GSTNativeCodimensionCyclePresentation.CodimensionPoint V.X 1,
        y.1 ∈ cutSupport V x → Order.coheight y.1 = 1 := by
  refine ⟨finite_principal_cut_coheight_one V x, ?_⟩
  intro y _
  exact y.2

#check finite_coheight_one_of_proper_closed
#check finite_principal_cut_coheight_one
#check principalCutCodimensionOneFinset
#check principal_cut_codimension_one_crown

#print axioms finite_coheight_one_of_proper_closed
#print axioms finite_principal_cut_coheight_one
#print axioms principalCutCodimensionOneFinset
#print axioms principal_cut_codimension_one_crown

end GSTClassicalHodgeProperCutCodimensionOne
