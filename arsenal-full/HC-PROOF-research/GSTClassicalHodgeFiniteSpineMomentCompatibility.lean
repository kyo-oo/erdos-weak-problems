import GSTClassicalHodgeFiniteSpineMomentOrbit
import GSTClassicalHodgeCodimensionZeroFundamentalCycle
import GSTClassicalHodgePrincipalCutSuccessorOperator

/-!
# GST CLASSICAL HODGE — CONSERVED CHARGE -> FINITE MOMENT COMPATIBILITY

The finite-spine route is intentionally weaker than the earlier unbounded
conserved-charge route.  This module proves exact backward compatibility.

Any previously constructed `SpineTowerConservedCharge` restricts to a
`FiniteSpineMomentChain` at every finite horizon.  Therefore all earlier charge
constructions remain reusable, while new proofs are free to build only the
finite prefix required by the Hodge class currently under consideration.

The native-mass bridge also factors through this restriction automatically.
No new geometric assumption is introduced here.
-/

set_option maxHeartbeats 90000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeFiniteSpineMomentCompatibility

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeLimitlessSpinePropagation
open GSTClassicalHodgeLimitlessTowerOrbitCrown
open GSTClassicalHodgeFiniteSpineMomentOrbit

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {G : GeometricCycleClassSpine V H}

/-- Restrict an unbounded conserved charge to the finite moment interface needed
at one requested weight. -/
noncomputable def SpineTowerConservedCharge.toFiniteSpineMomentChain
    (D : SpineTowerConservedCharge (V := V) (H := H) G)
    (top : Nat) :
    FiniteSpineMomentChain G top where
  read := D.cohomologyRead
  base_ne_zero := by
    rw [spineHodgeSeed_zero]
    rw [D.cycleClass_read 0
      (GSTClassicalHodgeCodimensionZeroFundamentalCycle.codimensionZeroFundamentalCycle V)]
    exact D.base_ne_zero
  successor_read := by
    intro q hq
    have hnat :=
      (G.principalCutPair q).cycleClass_natural (spineNativeTower G q)
    rw [G.principalCutPair_native q] at hnat
    calc
      D.cohomologyRead (q + 1)
          ((G.principalCutPair q).cohomologyOperator
            (spineHodgeSeed G q).1)
          = D.cohomologyRead (q + 1)
              (H.cycleClass (q + 1)
                (GSTClassicalHodgePrincipalCutSuccessorOperator.successorNativeOperator V q
                  (spineNativeTower G q))) := by
              rw [← spineNativeTower_cycleClass G q]
              rw [← hnat]
      _ = D.nativeRead (q + 1)
            (GSTClassicalHodgePrincipalCutSuccessorOperator.successorNativeOperator V q
              (spineNativeTower G q)) := by
              exact D.cycleClass_read (q + 1) _
      _ = successorScalar q *
            D.nativeRead q (spineNativeTower G q) := by
              exact D.successor_read q (spineNativeTower G q)
      _ = successorScalar q *
            D.cohomologyRead q
              (H.cycleClass q (spineNativeTower G q)) := by
              rw [D.cycleClass_read q (spineNativeTower G q)]
      _ = successorScalar q *
            D.cohomologyRead q (spineHodgeSeed G q).1 := by
              rw [spineNativeTower_cycleClass G q]

/-- The finite detector obtained from a conserved charge proves exactly the
same top-weight seed nonvanishing, without exporting any assertion above that
horizon. -/
theorem finite_chain_recovers_conserved_seed_nonvanishing
    (D : SpineTowerConservedCharge (V := V) (H := H) G)
    (top : Nat) :
    spineHodgeSeed G top ≠ 0 :=
  (SpineTowerConservedCharge.toFiniteSpineMomentChain D top).top_spineHodgeSeed_ne_zero

/-- The older native-mass bridge factors through the finite detector via its
manufactured conserved charge. -/
noncomputable def NativeMassCycleClassBridge.toFiniteSpineMomentChain
    (M : NativeMassCycleClassBridge V H)
    (G : GeometricCycleClassSpine V H)
    (top : Nat) :
    FiniteSpineMomentChain G top :=
  (SpineTowerConservedCharge.toFiniteSpineMomentChain (M.toConservedCharge G) top)

/-- Native-mass nonvanishing at one requested horizon can therefore be routed
through the finite detector rather than through an unbounded public tower. -/
theorem finite_chain_recovers_nativeMass_seed_nonvanishing
    (M : NativeMassCycleClassBridge V H)
    (G : GeometricCycleClassSpine V H)
    (top : Nat) :
    spineHodgeSeed G top ≠ 0 :=
  (NativeMassCycleClassBridge.toFiniteSpineMomentChain M G top).top_spineHodgeSeed_ne_zero

#check SpineTowerConservedCharge.toFiniteSpineMomentChain
#check finite_chain_recovers_conserved_seed_nonvanishing
#check NativeMassCycleClassBridge.toFiniteSpineMomentChain
#check finite_chain_recovers_nativeMass_seed_nonvanishing

#print axioms SpineTowerConservedCharge.toFiniteSpineMomentChain
#print axioms finite_chain_recovers_conserved_seed_nonvanishing
#print axioms NativeMassCycleClassBridge.toFiniteSpineMomentChain
#print axioms finite_chain_recovers_nativeMass_seed_nonvanishing

end GSTClassicalHodgeFiniteSpineMomentCompatibility