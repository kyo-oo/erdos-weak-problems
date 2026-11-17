import GSTGraphV2InformationRecovery
import GSTGraphV2CMNMCoupledUniverse
import GSTInfiniteTowerCurvatureCascade
import GSTCMQuadraticNativeRankForcing

/-!
# GST seven-axis information + CM/NM + infinite fold curvature

This is an extension of the original GST graph/cosmology and the preexisting
infinite formal curvature tower. The seven axes are information observations,
not spatial dimensions. We give exact algebraic equations for CM curvature and
show how nonzero local curvature coexists with a lossless five-period orbit.
-/

namespace GSTGraphV2CMInfiniteCurvatureBridge

open GSTGraphV2InformationRecovery

section CMOperator

variable {R : Type*} [Ring R]

/-- Structural noncommutative CM curvature of one fold operator. -/
def cmDefect (J A : R) : R := J * A - A * J

/-- Doubled J-even and J-odd components of a fold; no divisions assumed. -/
def cmEvenDouble (J A : R) : R := A - J * A * J
def cmOddDouble (J A : R) : R := A + J * A * J

theorem cmDefect_zero (J : R) : cmDefect J 0 = 0 := by
  simp [cmDefect]

theorem cmDefect_add (J A B : R) :
    cmDefect J (A + B) = cmDefect J A + cmDefect J B := by
  unfold cmDefect
  noncomm_ring

theorem cmDefect_sub (J A B : R) :
    cmDefect J (A - B) = cmDefect J A - cmDefect J B := by
  unfold cmDefect
  noncomm_ring

/-- Exact fold-composition rule for CM curvature. -/
theorem cmDefect_mul (J A B : R) :
    cmDefect J (A * B) =
      cmDefect J A * B + A * cmDefect J B := by
  unfold cmDefect
  noncomm_ring

/-- The three-fold Bianchi/Jacobi identity over every associative ring. -/
theorem three_fold_bianchi (A B C : R) :
    cmDefect A (cmDefect B C) +
    cmDefect B (cmDefect C A) +
    cmDefect C (cmDefect A B) = 0 := by
  unfold cmDefect
  noncomm_ring

theorem cm_even_odd_reconstruction (J A : R) :
    cmEvenDouble J A + cmOddDouble J A = A + A := by
  unfold cmEvenDouble cmOddDouble
  noncomm_ring

private theorem J_double_left (J A : R) (hJ : J * J = -1) :
    J * (J * A * J) = -(A * J) := by
  calc
    J * (J * A * J) = (J * J) * (A * J) := by noncomm_ring
    _ = -(A * J) := by rw [hJ]; simp

private theorem J_double_right (J A : R) (hJ : J * J = -1) :
    (J * A * J) * J = -(J * A) := by
  calc
    (J * A * J) * J = (J * A) * (J * J) := by noncomm_ring
    _ = -(J * A) := by rw [hJ]; simp

/-- The even sector is exactly J-compatible. -/
theorem cm_even_commutes (J A : R) (hJ : J * J = -1) :
    J * cmEvenDouble J A = cmEvenDouble J A * J := by
  have hl := J_double_left J A hJ
  have hr := J_double_right J A hJ
  unfold cmEvenDouble
  calc
    J * (A - J * A * J) = J * A - J * (J * A * J) := by
      noncomm_ring
    _ = J * A + A * J := by rw [hl]; abel
    _ = A * J - (J * A * J) * J := by rw [hr]; abel
    _ = (A - J * A * J) * J := by noncomm_ring

/-- The odd sector is exactly J-anti-compatible. -/
theorem cm_odd_anticommutes (J A : R) (hJ : J * J = -1) :
    J * cmOddDouble J A + cmOddDouble J A * J = 0 := by
  have hl := J_double_left J A hJ
  have hr := J_double_right J A hJ
  unfold cmOddDouble
  calc
    J * (A + J * A * J) + (A + J * A * J) * J =
        J * A + J * (J * A * J) + A * J + (J * A * J) * J := by
      noncomm_ring
    _ = 0 := by rw [hl, hr]; abel

/-- Exact CM curvature is J applied to the doubled odd component. -/
theorem cmDefect_eq_J_odd (J A : R) (hJ : J * J = -1) :
    cmDefect J A = J * cmOddDouble J A := by
  have hl := J_double_left J A hJ
  calc
    cmDefect J A = J * A - A * J := rfl
    _ = J * A + J * (J * A * J) := by rw [hl]; abel
    _ = J * cmOddDouble J A := by
      simp [cmOddDouble, mul_add]

/-- A nonzero CM curvature precisely detects a nonzero odd fold sector. -/
theorem cmDefect_zero_iff_odd_zero (J A : R) (hJ : J * J = -1) :
    cmDefect J A = 0 ↔ cmOddDouble J A = 0 := by
  constructor
  · intro h
    have hz : J * cmOddDouble J A = 0 := by
      rw [← cmDefect_eq_J_odd J A hJ]
      exact h
    have recover :
        (-J) * (J * cmOddDouble J A) = cmOddDouble J A := by
      calc
        (-J) * (J * cmOddDouble J A) =
            (-(J * J)) * cmOddDouble J A := by noncomm_ring
        _ = cmOddDouble J A := by rw [hJ]; simp
    rw [hz, mul_zero] at recover
    exact recover.symm
  · intro h
    rw [cmDefect_eq_J_odd J A hJ, h]
    simp


/-- The CM J²=-1 law contracts a pair of parity conjugates. -/
private theorem cm_cross_odd_product (J A B : R) (hJ : J * J = -1) :
    (J * A * J) * (J * B * J) = -(J * A * B * J) := by
  calc
    (J * A * J) * (J * B * J) =
        (J * A) * (J * J) * (B * J) := by noncomm_ring
    _ = -(J * A * B * J) := by rw [hJ]; noncomm_ring

/-- Even composed-fold curvature is produced by even-even and odd-odd
interactions; two odd modes can create a J-compatible direction. -/
theorem cm_even_product_double (J A B : R) (hJ : J * J = -1) :
    cmEvenDouble J A * cmEvenDouble J B +
      cmOddDouble J A * cmOddDouble J B =
      cmEvenDouble J (A * B) + cmEvenDouble J (A * B) := by
  have hp := cm_cross_odd_product J A B hJ
  calc
    cmEvenDouble J A * cmEvenDouble J B +
        cmOddDouble J A * cmOddDouble J B =
        (A * B + A * B) +
          ((J * A * J) * (J * B * J) +
           (J * A * J) * (J * B * J)) := by
      unfold cmEvenDouble cmOddDouble
      noncomm_ring
    _ = cmEvenDouble J (A * B) + cmEvenDouble J (A * B) := by
      rw [hp]
      unfold cmEvenDouble
      noncomm_ring

/-- Odd composed-fold curvature is generated by mixed even-odd
interactions, giving the all-order CM parity product rule. -/
theorem cm_odd_product_double (J A B : R) (hJ : J * J = -1) :
    cmEvenDouble J A * cmOddDouble J B +
      cmOddDouble J A * cmEvenDouble J B =
      cmOddDouble J (A * B) + cmOddDouble J (A * B) := by
  have hp := cm_cross_odd_product J A B hJ
  calc
    cmEvenDouble J A * cmOddDouble J B +
        cmOddDouble J A * cmEvenDouble J B =
        (A * B + A * B) -
          ((J * A * J) * (J * B * J) +
           (J * A * J) * (J * B * J)) := by
      unfold cmEvenDouble cmOddDouble
      noncomm_ring
    _ = cmOddDouble J (A * B) + cmOddDouble J (A * B) := by
      rw [hp]
      unfold cmOddDouble
      noncomm_ring

end CMOperator

section InformationCurvature

variable {R : Type*} [Ring R]

/-- Fold potential variation for one true information shuffle. -/
def informationChange (P : Cell → R) (s : Cell) : R :=
  P (shuffle s) - P s

/-- Five consecutive original seven-axis information states. -/
def orbitFiveSum (f : Cell → R) (s : Cell) : R :=
  f s + f (shuffle s) + f (shuffle (shuffle s)) +
    f (shuffle (shuffle (shuffle s))) +
    f (shuffle (shuffle (shuffle (shuffle s))))

/-- Every additive observable has zero net exact-change around the
fivefold cycle, but its intermediate variations may be nonzero. -/
theorem informationChange_five_sum_zero (P : Cell → R) (s : Cell) :
    orbitFiveSum (informationChange P) s = 0 := by
  unfold orbitFiveSum informationChange
  rw [shuffle_five]
  abel

def informationCMCurvature (J : R) (P : Cell → R) (s : Cell) : R :=
  cmDefect J (informationChange P s)

/-- At each physical information cell the total first-order CM curvature
over the five-period orbit cancels exactly. This is not a claim of
commutative ordered holonomy. -/
theorem informationCMCurvature_five_sum_zero
    (J : R) (P : Cell → R) (s : Cell) :
    orbitFiveSum (informationCMCurvature J P) s = 0 := by
  have h := congrArg (cmDefect J) (informationChange_five_sum_zero P s)
  simpa only [orbitFiveSum, informationCMCurvature,
    cmDefect_add, cmDefect_zero] using h

/-- Unbounded information depth, with exact curvature cancellation
at EVERY natural level, not an unverified analytic infinite sum. -/
def infiniteCMCurvature (J : R) (P : Cell → R)
    (u : InfiniteInformation) (k : Nat) : R :=
  informationCMCurvature J P (u k)

theorem infiniteCMCurvature_five_sum_zero
    (J : R) (P : Cell → R) (u : InfiniteInformation) (k : Nat) :
    orbitFiveSum (informationCMCurvature J P) (u k) = 0 :=
  informationCMCurvature_five_sum_zero J P (u k)


/-- The original physical carry and trit weight two CM fold operators.
Both coefficients are observed arithmetic data, not extra dimensions. -/
def cmGraphPotential (J K : R) (s : Cell) : R :=
  s.1.val • J + s.2.val • K

/-- The FIRST physical information change from (0,1) is J. -/
theorem cmGraphPotential_first_change (J K : R) :
    informationChange (cmGraphPotential J K)
      ((0 : Fin 4), (1 : Fin 3)) = J := by
  have hstep : shuffle ((0 : Fin 4), (1 : Fin 3)) =
      ((1 : Fin 4), (1 : Fin 3)) := by decide
  simp [informationChange, hstep, cmGraphPotential]

/-- The NEXT information change from (1,1) is K. -/
theorem cmGraphPotential_second_change (J K : R) :
    informationChange (cmGraphPotential J K)
      ((1 : Fin 4), (1 : Fin 3)) = K := by
  have hstep : shuffle ((1 : Fin 4), (1 : Fin 3)) =
      ((1 : Fin 4), (2 : Fin 3)) := by decide
  simp [informationChange, hstep, cmGraphPotential, neg_one_smul]
  noncomm_ring

/-- The second-order noncommutative curvature of the first two
information fold differences is exactly [J,K], even though the
fivefold first-order curvature always cancels. -/
theorem consecutive_folds_CM_curvature (J K : R) :
    cmDefect
      (informationChange (cmGraphPotential J K)
        ((0 : Fin 4), (1 : Fin 3)))
      (informationChange (cmGraphPotential J K)
        (shuffle ((0 : Fin 4), (1 : Fin 3)))) =
      cmDefect J K := by
  have hstep : shuffle ((0 : Fin 4), (1 : Fin 3)) =
      ((1 : Fin 4), (1 : Fin 3)) := by decide
  rw [hstep, cmGraphPotential_first_change,
    cmGraphPotential_second_change]

theorem consecutive_folds_curvature_nonzero (J K : R)
    (hJK : J * K ≠ K * J) :
    cmDefect
      (informationChange (cmGraphPotential J K)
        ((0 : Fin 4), (1 : Fin 3)))
      (informationChange (cmGraphPotential J K)
        (shuffle ((0 : Fin 4), (1 : Fin 3)))) ≠ 0 := by
  rw [consecutive_folds_CM_curvature]
  intro hz
  exact hJK (sub_eq_zero.mp hz)

end InformationCurvature

section CoupledInfiniteTower

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

/-- One all-order curvature readout on the actual GST JetTowerInf carrier.
The original tower curvature is retained; the exact information change
supplies an additional testable CM curvature contribution. -/
def CMInformationTowerReadout
    (T : GSTFoldTowerSquare.JetTowerInf V)
    (J : Module.End ℚ V)
    (P : Cell → Module.End ℚ V)
    (u : InfiniteInformation) (k : Nat) :
    Module.End ℚ V :=
  cmDefect J (T.curv k + informationChange P (u k))

/-- The complete infinite curvature readout returns at the fifth
information fold; every tower level is retained without truncation. -/
theorem CMInformationTowerReadout_five
    (T : GSTFoldTowerSquare.JetTowerInf V)
    (J : Module.End ℚ V)
    (P : Cell → Module.End ℚ V)
    (u : InfiniteInformation) (k : Nat) :
    CMInformationTowerReadout T J P
      (streamFold (streamFold (streamFold (streamFold (streamFold u))))) k =
    CMInformationTowerReadout T J P u k := by
  rw [streamFold_five]

end CoupledInfiniteTower

#check GSTGraphV2CMNMCoupledUniverse.coupledClosure_sound
#check GSTFoldTowerSquare.JetTowerInf
#check GSTCMQuadraticNativeRankForcing.imaginary_quadratic_CM_no_rational_eigenline
#check cmDefect_eq_J_odd
#check cmDefect_zero_iff_odd_zero
#check three_fold_bianchi
#check informationCMCurvature_five_sum_zero
#print axioms cmDefect_zero_iff_odd_zero
#print axioms informationCMCurvature_five_sum_zero

end GSTGraphV2CMInfiniteCurvatureBridge
