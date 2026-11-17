import Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic
import GSTGeometricRealizationStage2D
import GSTClassicalHodgeProjectiveSelfCorrespondences

/-!
# GST CLASSICAL HODGE — SHIFTED NATIVE CYCLE PUSHFORWARD

The full algebraic-correspondence action

  Z ↦ p₂*(C · p₁*Z)

requires a pushforward from codimension d+p on X×X to codimension p on X,
where d = dim X.  The existing projective point-transport layer only keeps the
same codimension on source and target, so it is not the correct primitive for
this projection.

Pinned Mathlib's `AlgebraicCycle.map` is more general: its source and target
weight functions may differ.  This file uses that native mechanism directly.
The source weight is

  x ↦ coheight(x) - d,

and the target weight is ordinary coheight.  Thus a source point of coheight
d+p can contribute only to a target point of coheight p.  The support proof is
obtained from Mathlib's actual locally-finite pushforward support theorem; no
Hodge, cycle-class, intersection, or correspondence-realization premise is
used.

This constructs the genuine proper/finite-type projection half of the future
full correspondence action.  Intersection/pullback remains a separate
geometric construction.
-/

set_option maxHeartbeats 20000000
set_option maxRecDepth 1000000

noncomputable section

open CategoryTheory
open AlgebraicGeometry
open GSTGeometricRealizationStage2D
open GSTClassicalHodgeProjectiveSelfCorrespondences

namespace GSTClassicalHodgeShiftedCyclePushforward

universe u

variable {X : Scheme.{u}} {Y : Scheme.{u}}

/-- Relative-codimension weight appropriate to a morphism whose relevant
components have geometric relative dimension `d`. -/
def relativeCodimensionWeight (d : Nat) (x : X) : Nat :=
  (Order.coheight x).toNat - d

/-- Coheight natification bridge: an exact ENat coheight equation determines
the natified coheight. -/
theorem coheight_toNat_of_eq
    (d p : Nat) (x : X)
    (hx : Order.coheight x = d + p) :
    (Order.coheight x).toNat = d + p := by
  rw [hx, ← Nat.cast_add]
  exact_mod_cast rfl

@[simp]
theorem relativeCodimensionWeight_of_exact
    (d p : Nat) (x : X)
    (hx : Order.coheight x = d + p) :
    relativeCodimensionWeight d x = p := by
  simp only [relativeCodimensionWeight,
    coheight_toNat_of_eq d p x hx]
  omega

/-- Raw Mathlib algebraic-cycle pushforward with the relative codimension
weight on the source and ordinary codimension on the target. -/
noncomputable def shiftedPushforwardRaw
    (f : X ⟶ Y) [QuasiCompact f]
    (d p : Nat)
    (Z : codimensionCycles X (d + p)) : AlgebraicCycle Y ℚ :=
  AlgebraicCycle.map f
    (relativeCodimensionWeight d)
    (fun y : Y => (Order.coheight y).toNat)
    Z.1

/-- **EXACT CODIMENSION SHIFT.**
The native weighted pushforward of a codimension-(d+p) cycle is supported only
in codimension p on the target.  This is forced by the actual Mathlib
pushforward weight equation. -/
theorem shiftedPushforwardRaw_support
    (f : X ⟶ Y) [QuasiCompact f]
    (d p : Nat)
    (Z : codimensionCycles X (d + p)) :
    (shiftedPushforwardRaw f d p Z).support ⊆
      {y : Y | (Order.coheight y).toNat = p} := by
  unfold shiftedPushforwardRaw AlgebraicCycle.map
  apply Function.locallyFinsupp.support_map_subset_of_forall_mem
    (s := {x : X | Order.coheight x = d + p})
    (t := {y : Y | (Order.coheight y).toNat = p})
  · exact Z.2
  · intro x hx hweight
    have hmatch :
        relativeCodimensionWeight d x = (Order.coheight (f x)).toNat := by
      by_contra hne
      simp [AlgebraicCycle.mapCoeff, hne] at hweight
    have hrel : relativeCodimensionWeight d x = p :=
      relativeCodimensionWeight_of_exact d p x hx
    simp only [hrel] at hmatch
    show (Order.coheight (f x)).toNat = p
    exact hmatch.symm

/-- Genuine codimension-shifting native algebraic-cycle pushforward, landing
in natified codimension-p coheight bookkeeping on the target. -/
noncomputable def shiftedPushforward
    (f : X ⟶ Y) [QuasiCompact f]
    (d p : Nat) :
    codimensionCycles X (d + p) → AlgebraicCycle Y ℚ :=
  fun Z => shiftedPushforwardRaw f d p Z

@[simp]
theorem shiftedPushforward_apply
    (f : X ⟶ Y) [QuasiCompact f]
    (d p : Nat)
    (Z : codimensionCycles X (d + p)) :
    shiftedPushforward f d p Z =
      shiftedPushforwardRaw f d p Z := rfl

/-- The pushforward of a codimension-(d+p) cycle has natified coheight-p
support on the target. -/
theorem shiftedPushforward_support
    (f : X ⟶ Y) [QuasiCompact f]
    (d p : Nat)
    (Z : codimensionCycles X (d + p)) :
    (shiftedPushforward f d p Z).support ⊆
      {y : Y | (Order.coheight y).toNat = p} :=
  shiftedPushforwardRaw_support f d p Z

/-- The exact native second-projection operation needed after an ambient
intersection cycle on the algebraic self-product.  The only instance required
is Mathlib quasicompactness of the genuine second projection. -/
noncomputable def selfProductSndPushforward
    (V : GSTProjectiveOverC.SmoothProjectiveComplexScheme)
    (d p : Nat)
    [QuasiCompact (snd V)] :
    codimensionCycles (selfProduct V) (d + p) →
      AlgebraicCycle V.X ℚ :=
  shiftedPushforward (snd V) d p

#check relativeCodimensionWeight
#check shiftedPushforwardRaw
#check shiftedPushforwardRaw_support
#check shiftedPushforward
#check selfProductSndPushforward

#print axioms shiftedPushforwardRaw_support

end GSTClassicalHodgeShiftedCyclePushforward
