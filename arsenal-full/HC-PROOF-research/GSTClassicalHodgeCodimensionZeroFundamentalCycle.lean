import GSTSmoothProjectiveNoetherian
import GSTNativeCodimensionCyclePresentation
import Mathlib.Topology.KrullDimension

/-!
# GST CLASSICAL HODGE — CANONICAL CODIMENSION-ZERO FUNDAMENTAL CYCLE

A smooth projective carrier need not be irreducible.  The correct geometry-first
base cycle therefore sums over all irreducible components rather than choosing
one component by hypothesis.

For a sober `T0` space, Mathlib identifies the coheight-zero points in the
specialization order with the irreducible components.  The smooth projective
carrier is Noetherian, so it has finitely many irreducible components.  Hence
its coheight-zero locus is finite.

Summing one native point cycle at every coheight-zero generic point produces a
canonical rational codimension-zero algebraic cycle on every smooth projective
complex scheme, with no irreducibility assumption and no Hodge semantics.
-/

set_option maxHeartbeats 30000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry
open TopologicalSpace
open GSTProjectiveOverC
open GSTSmoothProjectiveNoetherian
open GSTNativeCodimensionCyclePresentation
open GSTGeometricRealizationStage2D

namespace GSTClassicalHodgeCodimensionZeroFundamentalCycle

/-- The coheight-zero locus of a smooth projective carrier is finite: the
coheight-zero points are exactly the generic points of the finitely many
irreducible components of the Noetherian carrier. -/
theorem finite_coheight_zero
    (V : SmoothProjectiveComplexScheme) :
    {x : V.X | Order.coheight x = 0}.Finite := by
  letI : IsNoetherian V.X := smoothProjectiveIsNoetherian V
  letI : NoetherianSpace V.X := smoothProjectiveNoetherianSpace V
  have hcomp : (irreducibleComponents V.X).Finite :=
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
  have hgenfin : (genericPoints V.X).Finite := genericPoints.finite hcomp
  refine hgenfin.subset ?_
  intro x hx
  have hmax : IsMax x := (Order.coheight_eq_zero).mp hx
  show closure ({x} : Set V.X) ∈ irreducibleComponents V.X
  refine ⟨IsIrreducible.closure isIrreducible_singleton, ?_⟩
  intro W hWirr hleW
  obtain ⟨γ, hγ⟩ : ∃ γ : V.X, IsGenericPoint γ (closure (W : Set V.X)) :=
    QuasiSober.sober (IsIrreducible.closure hWirr) isClosed_closure
  have hxW : x ∈ closure (W : Set V.X) :=
    subset_closure (hleW (subset_closure (Set.mem_singleton x)))
  have hxγ : x ≤ γ := hγ.specializes hxW
  have hγx : γ ≤ x := hmax hxγ
  have hxeq : x = γ := by
    refine (inseparable_iff_eq).mp ?_
    exact le_antisymm (show nhds x ≤ nhds γ from hγx) (show nhds γ ≤ nhds x from hxγ)
  have hclos : closure (W : Set V.X) = closure ({x} : Set V.X) := by
    rw [hxeq]
    exact hγ.def.symm
  calc W ⊆ closure (W : Set V.X) := subset_closure
    _ = closure ({x} : Set V.X) := hclos

/-- Finite set of all genuine codimension-zero generic points. -/
noncomputable def codimensionZeroPointFinset
    (V : SmoothProjectiveComplexScheme) :
    Finset (CodimensionPoint V.X 0) := by
  classical
  let s : Set V.X := {x : V.X | Order.coheight x = 0}
  have hs : s.Finite := finite_coheight_zero V
  exact hs.toFinset.attach.map
    ⟨fun x => (⟨x.1, (Set.Finite.mem_toFinset hs).mp x.2⟩ :
        CodimensionPoint V.X 0),
      by
        intro a b h
        exact Subtype.ext (congrArg (Subtype.val : CodimensionPoint V.X 0 → V.X) h)⟩

/-- Canonical finite codimension-zero presentation: coefficient one on every
irreducible-component generic point. -/
noncomputable def codimensionZeroPresentation
    (V : SmoothProjectiveComplexScheme) :
    FiniteCodimensionPresentation V.X 0 := by
  classical
  exact (codimensionZeroPointFinset V).sum
    (fun x => Finsupp.single x 1)

/-- Canonical native codimension-zero component cycle. -/
noncomputable def codimensionZeroFundamentalCycle
    (V : SmoothProjectiveComplexScheme) :
    codimensionCycles V.X 0 :=
  realizeFiniteCodimensionPresentation V.X 0
    (codimensionZeroPresentation V)

/-- Native codimension receipt. -/
theorem codimensionZeroFundamentalCycle_is_native
    (V : SmoothProjectiveComplexScheme) :
    (codimensionZeroFundamentalCycle V : AlgebraicCycle V.X ℚ) ∈
      codimensionCycles V.X 0 :=
  (codimensionZeroFundamentalCycle V).2

/-- Exact cycle-class formula under any rational cycle-class map. -/
theorem cycleClass_codimensionZeroFundamentalCycle
    {Coh : Type*} [AddCommGroup Coh] [Module ℚ Coh]
    (V : SmoothProjectiveComplexScheme)
    (cl : codimensionCycles V.X 0 →ₗ[ℚ] Coh) :
    cl (codimensionZeroFundamentalCycle V) =
      (codimensionZeroPresentation V).sum
        (fun x q => q • cl (codimensionPointCycle V.X 0 x)) := by
  exact linearMap_realizeFiniteCodimensionPresentation
    V.X 0 cl (codimensionZeroPresentation V)

/-- Every point appearing in the canonical base presentation is a genuine
coheight-zero point. -/
theorem mem_codimensionZeroPointFinset_coheight
    (V : SmoothProjectiveComplexScheme)
    (x : CodimensionPoint V.X 0)
    (hx : x ∈ codimensionZeroPointFinset V) :
    Order.coheight x.1 = 0 :=
  x.2

/-- Base geometry crown. -/
theorem codimension_zero_geometry_crown
    (V : SmoothProjectiveComplexScheme) :
    {x : V.X | Order.coheight x = 0}.Finite
      ∧ ∃ Z : codimensionCycles V.X 0,
        Z = codimensionZeroFundamentalCycle V := by
  exact ⟨finite_coheight_zero V,
    ⟨codimensionZeroFundamentalCycle V, rfl⟩⟩

#check finite_coheight_zero
#check codimensionZeroPointFinset
#check codimensionZeroPresentation
#check codimensionZeroFundamentalCycle
#check cycleClass_codimensionZeroFundamentalCycle
#check codimension_zero_geometry_crown

#print axioms finite_coheight_zero
#print axioms codimensionZeroFundamentalCycle
#print axioms cycleClass_codimensionZeroFundamentalCycle
#print axioms codimension_zero_geometry_crown

end GSTClassicalHodgeCodimensionZeroFundamentalCycle
