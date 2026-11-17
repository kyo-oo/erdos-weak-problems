import GSTClassicalHodgePiOmniverseBranchSynthesis
import GSTClassicalHodgeRankFreeLefschetzPoincareGeneration
import GSTClassicalHodgeGradedGeometricOrbitAlgebra
import GSTClassicalHodgeGeneralSpaceRealization

/-!
# GST CLASSICAL HODGE — HANDWRITTEN PI EQUATION DERIVATION

This file follows the two-page handwritten route in its original order.

Start with one genuine rational Hodge state

  alpha in H^(2p)(X,Q) ∩ H^(p,p)(X).

The finite live support is embedded into the unbounded GST / Pi omniverse.
Choose one live coordinate i with coefficient c != 0.  The causal branch to a
target sheet j is not left as an opaque matrix unit: the already-proved
Lefschetz/Poincare calculation identifies it with the localized normalized
Lefschetz word

  E_ij = lift_(i,j) ((1/2) L^2).

Consequently the handwritten branch-collapse equation becomes

  alpha = sum_{j in supp(alpha)} (alpha_j / c) *
            lift_(i,j) ((1/2) L^2) alpha.

The existing omniverse graph reaches every one of these localized L^2 branches
in all three historical sectors, and the N-cohomology packet separates the
finite live channels.

The geometric landing is then stated at exactly the place required by the
handwritten derivation: the live localized-Lefschetz branch states must lie in
the genuine graded geometric orbit generated from the codimension-zero
fundamental cycle.  Once that equation is established, the branch sum itself
lies in the orbit, and the master cycle-class naturality theorem returns one
actual codimension-p algebraic cycle representing alpha.

No conserved-charge packet, native-mass bridge, arbitrary same-weight source,
or supplied ambient linear operator is introduced here.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open scoped BigOperators
open AlgebraicGeometry

namespace GSTClassicalHodgeHandwrittenPiEquationDerivation

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgeRankFreePrimitiveGeneration
open GSTClassicalHodgeRankFreeLefschetzPoincareGeneration
open GSTClassicalHodgeLefschetzPoincareMatrixGeneration
open GSTClassicalHodgeOmniverseCausalBranchPacket
open GSTClassicalHodgePiOmniverseBranchSynthesis
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeGradedGeometricProgramOrbit
open GSTClassicalHodgeGradedGeometricOrbitAlgebra

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-! ## Equation 1: GST matrix unit = localized normalized L^2 -/

/-- The exact branch operator appearing in the handwritten Pi sum, written
only with the normalized universal two-step Lefschetz operator and the finite
rank-free localization associated to the ordered pair `(i,j)`. -/
noncomputable def localizedNormalizedL2
    (i j : ClassicalHodgeBasisIndex V H p) :
    Module.End ℚ (ClassicalHodgeFiber V H p) :=
  liftFiniteHodgeOperator (pairBasisIndex i j) (pureForwardShift 2)

/-- **LOCALIZED LEFSCHETZ = MATRIX UNIT.**
This is the exact equation that replaces the symbolic branch `E_ij` by the
GST Lefschetz/Poincare calculation. -/
theorem localizedNormalizedL2_eq_hodgeMatrixUnit
    (i j : ClassicalHodgeBasisIndex V H p) :
    localizedNormalizedL2 (V := V) (H := H) i j =
      hodgeMatrixUnit i j := by
  unfold localizedNormalizedL2
  exact (rankFreeMatrixUnit_eq_twoSlot_Lefschetz i j).symm

/-- Pointwise form of the same equation. -/
theorem localizedNormalizedL2_apply
    (i j : ClassicalHodgeBasisIndex V H p)
    (alpha : ClassicalHodgeFiber V H p) :
    localizedNormalizedL2 (V := V) (H := H) i j alpha =
      hodgeMatrixUnit i j alpha := by
  rw [localizedNormalizedL2_eq_hodgeMatrixUnit]

/-! ## Equation 2: the handwritten finite branch collapse -/

/-- **HANDWRITTEN BRANCH-COLLAPSE EQUATION AT A CHOSEN LIVE SOURCE.**
For any coordinate `i` with nonzero coefficient `c`, the original Hodge state
is exactly the rational sum of its localized normalized-L^2 target branches.
This is the page-two equation with `E_ij` expanded rather than hidden behind a
name. -/
theorem branch_collapse_localizedL2_at
    (alpha : ClassicalHodgeFiber V H p)
    (i : ClassicalHodgeBasisIndex V H p)
    (hi : hodgeCoordinate i alpha ≠ 0) :
    alpha =
      ∑ j ∈ ((classicalHodgeBasis V H p).repr alpha).support,
        (((classicalHodgeBasis V H p).repr alpha j) *
            (hodgeCoordinate i alpha)⁻¹) •
          localizedNormalizedL2 (V := V) (H := H) i j alpha := by
  have hsum :
      alpha =
        ∑ j ∈ ((classicalHodgeBasis V H p).repr alpha).support,
          ((classicalHodgeBasis V H p).repr alpha j) •
            classicalHodgeBasis V H p j :=
    (classicalHodgeBasis V H p).sum_repr alpha
  rw [hsum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [localizedNormalizedL2_apply, hodgeMatrixUnit_apply]
  simp only [smul_smul]
  simp [hi, mul_assoc, hodgeCoordinate]

/-- Existential live-source form, matching the handwritten omniverse packet:
every nonzero Hodge state admits one nonzero source coordinate for which the
localized-L^2 branch collapse is exact. -/
theorem branch_collapse_localizedL2
    (alpha : ClassicalHodgeFiber V H p)
    (halpha : alpha ≠ 0) :
    ∃ i : HodgeSupportIndex alpha,
      hodgeCoordinate i.1 alpha ≠ 0 ∧
      alpha =
        ∑ j ∈ ((classicalHodgeBasis V H p).repr alpha).support,
          (((classicalHodgeBasis V H p).repr alpha j) *
              (hodgeCoordinate i.1 alpha)⁻¹) •
            localizedNormalizedL2 (V := V) (H := H) i.1 j alpha := by
  obtain ⟨i, hi, _⟩ := branch_collapse_identity alpha halpha
  exact ⟨i, hi, branch_collapse_localizedL2_at alpha i.1 hi⟩

/-! ## Equation 3: the same localized L^2 branches are the omniverse events -/

/-- The existing three-sector GST causal branch theorem can be read literally
as reachability of the localized normalized-L^2 branch, because that operator
is exactly the rank-one matrix unit. -/
theorem reachable_localizedL2_target
    (alpha : ClassicalHodgeFiber V H p)
    (halpha : alpha ≠ 0)
    (s : GSTGraphV2OmniversalCore.Sector)
    (j : ClassicalHodgeBasisIndex V H p) :
    ∃ i : HodgeSupportIndex alpha,
      GSTGraphV2OmniversalCore.OmniversalGraph.Reachable
        (hodgeBranchGraph (V := V) (H := H) (p := p))
        ⟨GSTGraphV2OmniversalCore.Sector.gstPlus, alpha⟩
        ⟨s, localizedNormalizedL2 (V := V) (H := H) i.1 j alpha⟩
      ∧ hodgeCoordinate i.1 alpha ≠ 0 := by
  obtain ⟨i, hreach, hi⟩ := reachable_arbitrary_target alpha halpha s j
  refine ⟨i, ?_, hi⟩
  simpa only [localizedNormalizedL2_apply] using hreach

/-- The full non-geometric handwritten packet with the causal target rewritten
as localized normalized `L^2`: transfer-sheet entry, arbitrary-sector branch,
N-cohomology separation, and exact branch collapse all refer to the same live
Hodge state. -/
theorem handwritten_pi_equation_packet
    (alpha : ClassicalHodgeFiber V H p)
    (halpha : alpha ≠ 0) :
    (∃ i : ClassicalHodgeBasisIndex V H p,
      (classicalHodgeBasis V H p).repr alpha i ≠ 0)
    ∧ (∀ s : GSTGraphV2OmniversalCore.Sector,
      ∀ j : ClassicalHodgeBasisIndex V H p,
      ∃ i : HodgeSupportIndex alpha,
        GSTGraphV2OmniversalCore.OmniversalGraph.Reachable
          (hodgeBranchGraph (V := V) (H := H) (p := p))
          ⟨GSTGraphV2OmniversalCore.Sector.gstPlus, alpha⟩
          ⟨s, localizedNormalizedL2 (V := V) (H := H) i.1 j alpha⟩
        ∧ hodgeCoordinate i.1 alpha ≠ 0)
    ∧ (∃ basis : Fin (liveSupportNShape alpha).holes →
        GSTNCohomology.nCohoClasses 0 (liveSupportNShape alpha) 1,
      ∀ i : Fin (liveSupportNShape alpha).holes,
        (basis i).1 i =
          GSTNCohomology.towerWindow 0
            ((liveSupportNShape alpha).channel i) 1)
    ∧ (∃ i : HodgeSupportIndex alpha,
      hodgeCoordinate i.1 alpha ≠ 0 ∧
      alpha =
        ∑ j ∈ ((classicalHodgeBasis V H p).repr alpha).support,
          (((classicalHodgeBasis V H p).repr alpha j) *
              (hodgeCoordinate i.1 alpha)⁻¹) •
            localizedNormalizedL2 (V := V) (H := H) i.1 j alpha) := by
  refine ⟨?_, ?_, liveSupport_ncohomology_rank 0 alpha,
    branch_collapse_localizedL2 alpha halpha⟩
  · obtain ⟨i, hi, _, _⟩ :=
      (pi_omniverse_branch_packet alpha halpha).1
    exact ⟨i, hi⟩
  · intro s j
    exact reachable_localizedL2_target alpha halpha s j

/-! ## Equation 4: geometric landing of the handwritten branches -/

/-- The exact geometric statement required at page two: one live source
coordinate is chosen, and every localized normalized-L^2 branch appearing in
the finite collapse belongs to the genuine graded geometric orbit generated
from the codimension-zero fundamental cycle.

This deliberately mentions the actual branch states from the handwritten
formula rather than replacing them with a separate same-weight seed package. -/
def LiveLocalizedL2BranchesLandInOrbit
    (G : GeometricCycleClassSpine V H)
    (alpha : ClassicalHodgeFiber V H p) : Prop :=
  ∃ i : HodgeSupportIndex alpha,
    hodgeCoordinate i.1 alpha ≠ 0 ∧
    ∀ j ∈ ((classicalHodgeBasis V H p).repr alpha).support,
      (localizedNormalizedL2 (V := V) (H := H) i.1 j alpha).1 ∈
        geometricProgramOrbitModule G p

/-- **BRANCHES -> WHOLE CLASS.**
Once the exact live localized-L^2 branches of the handwritten formula are in
the geometric orbit, their rational finite collapse puts `alpha` itself in
that orbit. -/
theorem class_mem_geometricOrbit_of_liveLocalizedL2Branches
    (G : GeometricCycleClassSpine V H)
    (alpha : ClassicalHodgeFiber V H p)
    (hland : LiveLocalizedL2BranchesLandInOrbit G alpha) :
    alpha.1 ∈ geometricProgramOrbitModule G p := by
  rcases hland with ⟨i, hi, hbranch⟩
  have hcollapse := branch_collapse_localizedL2_at alpha i.1 hi
  have hcollapseVal := congrArg Subtype.val hcollapse
  rw [hcollapseVal]
  simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower]
  apply Submodule.sum_mem
  intro j hj
  exact (geometricProgramOrbitModule G p).smul_mem
    (((classicalHodgeBasis V H p).repr alpha j) *
      (hodgeCoordinate i.1 alpha)⁻¹)
    (hbranch j hj)

/-- **HANDWRITTEN EQUATION LANDING.**
The genuine graded-orbit cycle-class theorem turns the equation-level branch
landing into one actual codimension-p algebraic cycle whose class is exactly
`alpha`. -/
theorem native_cycle_of_liveLocalizedL2Branches
    (G : GeometricCycleClassSpine V H)
    (alpha : ClassicalHodgeFiber V H p)
    (hland : LiveLocalizedL2BranchesLandInOrbit G alpha) :
    ∃ Z : codimensionCycles V.X p,
      H.cycleClass p Z = alpha.1 := by
  exact geometricProgramOrbitModule_le_cycleClass_range G p
    (class_mem_geometricOrbit_of_liveLocalizedL2Branches G alpha hland)

/-- Global form of the exact handwritten geometric landing equation. -/
def HandwrittenPiGeometricLanding
    (G : GeometricCycleClassSpine V H) : Prop :=
  ∀ q : Nat,
    ∀ alpha : ClassicalHodgeFiber V H q,
      alpha ≠ 0 →
        LiveLocalizedL2BranchesLandInOrbit G alpha

/-- **HANDWRITTEN PI -> STAGE-2G HODGE.**
This theorem performs the two-page derivation without changing routes: Hodge
intersection -> GST finite support -> unbounded causal branches -> localized
`L^2` matrix-unit equation -> finite rational branch collapse -> genuine
geometric orbit -> actual native algebraic cycle. -/
theorem bigradedBettiHodge_of_handwritten_pi_geometric_landing
    (G : GeometricCycleClassSpine V H)
    (hgeo : HandwrittenPiGeometricLanding G) :
    BigradedBettiHodgeStatement V H := by
  intro q x hx
  let alpha : ClassicalHodgeFiber V H q := ⟨x, hx⟩
  by_cases halpha : alpha = 0
  · have hx0 : x = 0 := congrArg Subtype.val halpha
    subst x
    exact ⟨0, by simp⟩
  · exact native_cycle_of_liveLocalizedL2Branches G alpha
      (hgeo q alpha halpha)

#check localizedNormalizedL2
#check localizedNormalizedL2_eq_hodgeMatrixUnit
#check branch_collapse_localizedL2_at
#check branch_collapse_localizedL2
#check reachable_localizedL2_target
#check handwritten_pi_equation_packet
#check LiveLocalizedL2BranchesLandInOrbit
#check class_mem_geometricOrbit_of_liveLocalizedL2Branches
#check native_cycle_of_liveLocalizedL2Branches
#check HandwrittenPiGeometricLanding
#check bigradedBettiHodge_of_handwritten_pi_geometric_landing

#print axioms localizedNormalizedL2_eq_hodgeMatrixUnit
#print axioms branch_collapse_localizedL2_at
#print axioms reachable_localizedL2_target
#print axioms handwritten_pi_equation_packet
#print axioms class_mem_geometricOrbit_of_liveLocalizedL2Branches
#print axioms native_cycle_of_liveLocalizedL2Branches
#print axioms bigradedBettiHodge_of_handwritten_pi_geometric_landing

end GSTClassicalHodgeHandwrittenPiEquationDerivation
