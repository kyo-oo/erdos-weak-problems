import Mathlib.AlgebraicGeometry.Properties
import GSTSmoothProjectiveNoetherian
import GSTNativeCodimensionCyclePresentation

/-!
# GST CLASSICAL HODGE — SCHEME CODIMENSION / STALK DIMENSION BRIDGE

The native Stage-2D cycle space uses `Order.coheight x = p` as the definition
of a codimension-p point.  The pinned Mathlib scheme API proves exactly the
classical local-algebra interpretation: the Krull dimension of the stalk at a
scheme point equals its coheight.

This module packages that theorem directly for the codimension-point language
used by the Hodge landing.  It lets every later geometric construction certify
its grading either topologically (coheight) or locally algebraically (stalk
Krull dimension) without changing notions of codimension.
-/

set_option maxHeartbeats 30000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTNativeCodimensionCyclePresentation

namespace GSTClassicalHodgeSchemeCodimensionStalk

/-- Exact local-algebra formula for the codimension used by native cycles. -/
theorem stalk_dimension_eq_coheight
    (V : SmoothProjectiveComplexScheme) (x : V.X) :
    ringKrullDim (V.X.presheaf.stalk x) = Order.coheight x := by
  exact ringKrullDim_stalk_eq_coheight x

/-- A native codimension-p point has stalk Krull dimension exactly p. -/
theorem stalk_dimension_of_codimensionPoint
    (V : SmoothProjectiveComplexScheme) (p : Nat)
    (x : CodimensionPoint V.X p) :
    ringKrullDim (V.X.presheaf.stalk x.1) = p := by
  rw [stalk_dimension_eq_coheight V x.1, x.2]
  push_cast
  rfl

/-- Conversely a point whose stalk has dimension p is a native
codimension-p point. -/
noncomputable def codimensionPointOfStalkDimension
    (V : SmoothProjectiveComplexScheme) (p : Nat)
    (x : V.X)
    (hx : ringKrullDim (V.X.presheaf.stalk x) = p) :
    CodimensionPoint V.X p :=
  ⟨x, by
    have h1 := stalk_dimension_eq_coheight V x
    rw [h1] at hx
    exact_mod_cast hx⟩

/-- Exact codimension stratum as a subset of the projective carrier. -/
def codimensionStratum
    (V : SmoothProjectiveComplexScheme) (p : Nat) : Set V.X :=
  {x | Order.coheight x = p}

/-- Stalk-dimension characterization of the exact codimension stratum. -/
theorem mem_codimensionStratum_iff_stalk
    (V : SmoothProjectiveComplexScheme) (p : Nat) (x : V.X) :
    x ∈ codimensionStratum V p ↔
      ringKrullDim (V.X.presheaf.stalk x) = p := by
  rw [stalk_dimension_eq_coheight V x]
  exact ⟨fun h => by exact_mod_cast h,
    fun h => by exact WithBot.coe_injective h⟩

/-- Native codimension points are exactly the subtype of the codimension
stratum. -/
noncomputable def codimensionPointEquivStratum
    (V : SmoothProjectiveComplexScheme) (p : Nat) :
    CodimensionPoint V.X p ≃ codimensionStratum V p :=
  Equiv.refl _

/-- Codimension/stalk crown. -/
theorem native_codimension_stalk_crown
    (V : SmoothProjectiveComplexScheme) (p : Nat)
    (x : CodimensionPoint V.X p) :
    Order.coheight x.1 = p
      ∧ ringKrullDim (V.X.presheaf.stalk x.1) = p := by
  exact ⟨x.2, stalk_dimension_of_codimensionPoint V p x⟩

#check stalk_dimension_eq_coheight
#check stalk_dimension_of_codimensionPoint
#check codimensionPointOfStalkDimension
#check codimensionStratum
#check mem_codimensionStratum_iff_stalk
#check codimensionPointEquivStratum
#check native_codimension_stalk_crown

#print axioms stalk_dimension_eq_coheight
#print axioms stalk_dimension_of_codimensionPoint
#print axioms mem_codimensionStratum_iff_stalk
#print axioms native_codimension_stalk_crown

end GSTClassicalHodgeSchemeCodimensionStalk
