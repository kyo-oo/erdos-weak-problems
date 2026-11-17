import GSTHodgeWaveAllNHoleReadout
import Mathlib

/-!
# GST all-N N-wave: connected curvature mixing without an assumed source frame

This is a SOURCE-BIRTH ROUTE in the owner's original GST, not a substitute
classical geometry example. It uses exactly the existing NShape channel
addresses, the original 12-cell Wave-I detector, holeReadoutLift, and the
native polynomial/commutator logic.

Part 1 builds a new genuine rational *information-space* inter-channel
operator from the preexisting GST wave quotient and its proved right inverse.
Its coefficient curvature is explicitly the spectral-gap weighted adjacency
graph, with each existing neighboring edge nonzero at arbitrary N.

Part 2 proves a native-to-Betti geometric source propagation lemma. Given
actual native operators realizing the nonzero edge and a previously known
algebraic seed, it constructs the next genuine native algebraic source.
NO unknown Hodge target preimage, surjectivity, arbitrary full-rank frame,
or manufactured cycle class is assumed.

The UNIVERSAL realization of this proposed cross-hole information operator
as an actual Chow correspondence on an arbitrary original projective X is
not asserted here. The full proof of the conditional connected-curvature
source mechanism is in the companion 2026-11-10 LaTeX derivation.
-/

set_option maxHeartbeats 2000000
noncomputable section

namespace GSTAllNConnectedCurvatureBirth

open GSTHodgeWaveAllNHoleReadout
open GSTGraphV2WaveNShapeCompiler
open GSTNCohomology
open GSTGraphV2CMWaveFusion

/-- The original Wave-II channel labels are dimensionless information
addresses. Neighboring labels are an additional explicit channel-coupler,
not a claim about adjacency in physical space. -/
def adjacentWeight {n : Nat} (i j : Fin n) : ℚ :=
  if i.val + 1 = j.val ∨ j.val + 1 = i.val then 1 else 0

/-- A genuinely all-N rational mixing operator on the established N-hole
information quotient. No Chow-cycle frame is used in its definition. -/
def coefficientNeighbor (s : NShape) :
    (Fin s.holes → ℚ) →ₗ[ℚ] (Fin s.holes → ℚ) where
  toFun v := fun i => ∑ j, adjacentWeight i j * v j
  map_add' := by
    intro v w
    funext i
    change (∑ j, adjacentWeight i j * (v j + w j)) =
      (∑ j, adjacentWeight i j * v j) +
      (∑ j, adjacentWeight i j * w j)
    simp only [mul_add, Finset.sum_add_distrib]
  map_smul' := by
    intro q v
    funext i
    change (∑ j, adjacentWeight i j * (q * v j)) =
      q * (∑ j, adjacentWeight i j * v j)
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring

/-- The ALREADY PROVED right inverse of GST's fixed-cell wave detector,
repackaged as one rational-linear map for algebraic composition. -/
def holeLiftLinear (s : NShape) :
    (Fin s.holes → ℚ) →ₗ[ℚ] HoleWaveSignals s where
  toFun := holeReadoutLift s
  map_add' := by
    intro v w
    funext i c
    change (if c = nullCell then v i + w i else (0 : ℚ)) =
      (if c = nullCell then v i else 0) +
        (if c = nullCell then w i else 0)
    split_ifs <;> simp
  map_smul' := by
    intro q v
    funext i c
    change (if c = nullCell then q * v i else (0 : ℚ)) =
      q * (if c = nullCell then v i else 0)
    split_ifs <;> simp

/-- One explicit cross-hole GST signal operator, not an invented geometric
realization: lift, mix, and read out using EXISTING GST constructions. -/
def crossHoleSignal (s : NShape) : Module.End ℚ (HoleWaveSignals s) :=
  (holeLiftLinear s).comp ((coefficientNeighbor s).comp (holeReadout s))

/-- The new signal coupling actually realizes EXACTLY its advertised
inter-channel operator on the original Wave-II information quotient. -/
theorem crossHoleSignal_exact_readout (s : NShape)
    (u : HoleWaveSignals s) :
    holeReadout s (crossHoleSignal s u) =
      coefficientNeighbor s (holeReadout s u) := by
  change holeReadout s
    (holeReadoutLift s (coefficientNeighbor s (holeReadout s u))) =
      coefficientNeighbor s (holeReadout s u)
  exact holeReadout_lift s _

/-- True commutator of the ESTABLISHED GST all-N spectral wave fold with
the NEW explicitly constructed inter-channel information coupling. -/
def quotientCurvature (s : NShape) :
    Module.End ℚ (Fin s.holes → ℚ) :=
  (coefficientFold s).comp (coefficientNeighbor s) -
    (coefficientNeighbor s).comp (coefficientFold s)

/-- Exact arbitrary-N curvature identity. Neighbor coupling produces
spectral gaps, not merely a count of nonzero abstract graph edges. -/
theorem quotientCurvature_exact (s : NShape)
    (v : Fin s.holes → ℚ) (i : Fin s.holes) :
    quotientCurvature s v i =
      ∑ j : Fin s.holes,
        ((channelShift s i - channelShift s j) *
          adjacentWeight i j) * v j := by
  change
    (2 + channelShift s i) *
        (∑ j, adjacentWeight i j * v j) -
      (∑ j, adjacentWeight i j *
        ((2 + channelShift s j) * v j)) =
    ∑ j : Fin s.holes,
      ((channelShift s i - channelShift s j) *
        adjacentWeight i j) * v j
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem adjacentWeight_one {n : Nat} (i j : Fin n)
    (h : i.val + 1 = j.val ∨ j.val + 1 = i.val) :
    adjacentWeight i j = 1 := by
  simp [adjacentWeight, h]

/-- Distinct GST N-hole addresses guarantee that every explicit adjacent
curvature coefficient is nonzero. This is NOT a statement that a genuine
Chow correspondence has already realized the coefficient on every X. -/
theorem adjacent_curvature_nonzero
    (s : NShape) (i j : Fin s.holes)
    (hij : i ≠ j)
    (hadj : i.val + 1 = j.val ∨ j.val + 1 = i.val) :
    (channelShift s i - channelShift s j) *
       adjacentWeight i j ≠ 0 := by
  have hshift : channelShift s i ≠ channelShift s j := by
    intro h
    exact hij (channelShift_injective s h)
  rw [adjacentWeight_one i j hadj]
  simpa using (sub_ne_zero.mpr hshift)


/-! ## Full twelve-cell GST wave, not only the readout quotient -/

/-- Mix all original Wave-I carry/trit cells across neighboring Wave-II
holes. Unlike the quotient-only operator this does NOT collapse the
11-dimensional per-hole kernel of the original fixed-cell detector. -/
def fullCellNeighbor (s : NShape)
    (u : HoleWaveSignals s) : HoleWaveSignals s :=
  fun i c => ∑ j : Fin s.holes, adjacentWeight i j * u j c

/-- Full information coupling reduces to the already established GST
N-hole coefficient coupling after the original fixed-cell readout. -/
theorem fullCellNeighbor_readout (s : NShape)
    (u : HoleWaveSignals s) :
    holeReadout s (fullCellNeighbor s u) =
      coefficientNeighbor s (holeReadout s u) := by
  funext i
  change
    (∑ j : Fin s.holes, adjacentWeight i j * u j nullCell) -
      (∑ j : Fin s.holes, adjacentWeight i j * u j maximumCell) =
    ∑ j : Fin s.holes,
      adjacentWeight i j * (u j nullCell - u j maximumCell)
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Original twelve-state U+J+M is linear on finite weighted sums
of the genuinely full Wave-II hole signals. -/
private theorem fullCell_base_fold_sum
    (s : NShape) (u : HoleWaveSignals s)
    (i : Fin s.holes) (c : GSTGraphV2InformationRecovery.Cell) :
    GSTGraphV2CMWaveFusion.T
      (fun a => ∑ j : Fin s.holes, adjacentWeight i j * u j a) c =
      ∑ j : Fin s.holes, adjacentWeight i j *
        GSTGraphV2CMWaveFusion.T (u j) c := by
  change
    (∑ j : Fin s.holes,
      adjacentWeight i j * u j (GSTGraphV2InformationRecovery.shuffle c)) +
    GSTGraphV2CMWaveFusion.cmSign c *
      (∑ j : Fin s.holes,
        adjacentWeight i j * u j (GSTGraphV2CMWaveFusion.mirrorCell c)) +
    GSTGraphV2CMWaveFusion.sourceMultiplicity c *
      (∑ j : Fin s.holes, adjacentWeight i j * u j c) =
    ∑ j : Fin s.holes,
      adjacentWeight i j *
        (u j (GSTGraphV2InformationRecovery.shuffle c) +
          GSTGraphV2CMWaveFusion.cmSign c *
            u j (GSTGraphV2CMWaveFusion.mirrorCell c) +
          GSTGraphV2CMWaveFusion.sourceMultiplicity c * u j c)
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- EXACT commutator on the ENTIRE 12-hole GST signal, not a scalar
quotient: base U+J+M terms cancel by full signal linearity and the
remaining coefficient is the channel spectral gap. -/
theorem fullCellNeighbor_curvature_exact
    (s : NShape) (u : HoleWaveSignals s)
    (i : Fin s.holes)
    (c : GSTGraphV2InformationRecovery.Cell) :
    shiftedNShapeFold s (fullCellNeighbor s u) i c -
      fullCellNeighbor s (shiftedNShapeFold s u) i c =
      ∑ j : Fin s.holes,
        ((channelShift s i - channelShift s j) *
          adjacentWeight i j) * u j c := by
  change
    GSTGraphV2CMWaveFusion.T
      (fun a => ∑ j : Fin s.holes, adjacentWeight i j * u j a) c +
      channelShift s i *
        (∑ j : Fin s.holes, adjacentWeight i j * u j c) -
      (∑ j : Fin s.holes,
        adjacentWeight i j *
          (GSTGraphV2CMWaveFusion.T (u j) c +
            channelShift s j * u j c)) =
    ∑ j : Fin s.holes,
      ((channelShift s i - channelShift s j) *
        adjacentWeight i j) * u j c
  rw [fullCell_base_fold_sum]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-! ## Genuine native source propagation along a realized curvature edge -/

section OriginalXNativeSource

variable {A B : Type*}
variable [AddCommGroup A] [Module ℚ A]
variable [AddCommGroup B] [Module ℚ B]

/-- From one ACTUALLY algebraic seed and one geometric nonzero
spectral-curvature edge, construct the next ACTUAL native cycle.
The native projector can be obtained as a rational polynomial in
the realized N-wave operator (proved in the companion derivation).
The new target vector is arbitrary rational Betti data, not supplied
with an inverse cycle-class witness. -/
theorem native_source_of_realized_spectral_edge
    (cl : A →ₗ[ℚ] B)
    (nativeProjector nativeMix : Module.End ℚ A)
    (bettiProjector bettiMix : Module.End ℚ B)
    (hproject : ∀ z : A,
      cl (nativeProjector z) = bettiProjector (cl z))
    (hmix : ∀ z : A,
      cl (nativeMix z) = bettiMix (cl z))
    (source : A) (ei ej : B)
    (hsource : cl source = ei)
    (weight : ℚ) (hweight : weight ≠ 0)
    (hedge : bettiProjector (bettiMix ei) = weight • ej) :
    ∃ nextSource : A, cl nextSource = ej := by
  refine ⟨weight⁻¹ • nativeProjector (nativeMix source), ?_⟩
  rw [map_smul, hproject, hmix, hsource, hedge]
  rw [smul_smul]
  simp [inv_mul_cancel₀ hweight]

end OriginalXNativeSource

#check fullCellNeighbor_readout
#check fullCellNeighbor_curvature_exact
#check crossHoleSignal_exact_readout
#check quotientCurvature_exact
#check adjacent_curvature_nonzero
#check native_source_of_realized_spectral_edge
#print axioms fullCellNeighbor_readout
#print axioms fullCellNeighbor_curvature_exact
#print axioms crossHoleSignal_exact_readout
#print axioms quotientCurvature_exact
#print axioms adjacent_curvature_nonzero
#print axioms native_source_of_realized_spectral_edge

end GSTAllNConnectedCurvatureBirth
