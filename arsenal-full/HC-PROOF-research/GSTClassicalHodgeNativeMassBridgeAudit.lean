import GSTClassicalHodgeLimitlessSpinePropagation
import GSTClassicalHodgeSingleExactSuccessorSurvival
import GSTNativeCodimensionCyclePresentation
import GSTCompactNativeCyclePresentation
import GSTClassicalHodgeGeometricCycleClassPointRigidity

/-!
# GST CLASSICAL HODGE — NATIVE-MASS BRIDGE AUDIT

This file separates three logically different ingredients that had previously
been bundled inside `NativeMassCycleClassBridge`.

1. `kernel_mass_zero` is not an arbitrary extra law.  It is exactly the
   necessary-and-sufficient condition for canonical native mass to factor
   through the genuine cycle-class map.
2. `base_mass_ne_zero` is exactly nonemptiness of the codimension-zero
   component presentation: native base mass is the number of component generic
   points.
3. `successor_point_mass = successorScalar` is much stronger than native
   successor nonvanishing.  The native successor mass is the cardinality of the
   exact-relative-successor locus, whereas the GST successor scalar is the
   universal two-step Lefschetz coefficient.  The old equality is therefore
   precisely an exact cardinality constraint.  It must not be silently treated
   as a generic omniverse identity.

The point of the audit is to prevent a strong native combinatorial hypothesis
from being hidden inside a semantic bridge.  The intrinsic GST plane keeps its
universal `L^2` coefficient; native projective successor geometry keeps its own
exact-successor count.
-/

set_option maxHeartbeats 120000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry
open GSTNativeCodimensionCyclePresentation
open GSTCompactNativeCyclePresentation

namespace GSTClassicalHodgeNativeMassBridgeAudit

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeNativeCycleCosmicShadow
open GSTClassicalHodgeCodimensionZeroFundamentalCycle
open GSTClassicalHodgePrincipalCutSuccessorOperator
open GSTClassicalHodgeSingleExactSuccessorSurvival
open GSTClassicalHodgeNativeOperatorCohomologyRealization
open GSTClassicalHodgeLimitlessSpinePropagation
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeLimitlessTowerOrbitCrown

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- The exact kernel law saying that native mass depends only on genuine
cycle-class data. -/
def NativeMassKernelLaw : Prop :=
  ∀ p : Nat, ∀ Z : codimensionCycles V.X p,
    H.cycleClass p Z = 0 → nativeCycleMass V p Z = 0

/-- The corresponding factorization statement: in every weight there is a
rational cohomological readout whose value on every genuine cycle class is
exactly canonical native mass. -/
def NativeMassCohomologyFactorization : Prop :=
  ∀ p : Nat,
    ∃ read :
      RationalSingularCohomology H.analytification (2 * p) →ₗ[ℚ] ℚ,
      ∀ Z : codimensionCycles V.X p,
        read (H.cycleClass p Z) = nativeCycleMass V p Z

/-- Kernel dependence immediately gives equality of native mass on cycles with
the same genuine cycle class. -/
theorem nativeMass_congr_of_kernelLaw
    (K : NativeMassKernelLaw (V := V) (H := H))
    (p : Nat)
    {Z W : codimensionCycles V.X p}
    (hZW : H.cycleClass p Z = H.cycleClass p W) :
    nativeCycleMass V p Z = nativeCycleMass V p W := by
  have hker : H.cycleClass p (Z - W) = 0 := by
    simp [hZW]
  have hmass := K p (Z - W) hker
  simp at hmass
  linarith

/-- Descend native mass to the actual cycle-class range using only the kernel
law. -/
noncomputable def nativeMassRangeRead
    (K : NativeMassKernelLaw (V := V) (H := H))
    (p : Nat) :
    LinearMap.range (H.cycleClass p) →ₗ[ℚ] ℚ where
  toFun := fun x => nativeCycleMass V p (rangeRepresentative x)
  map_add' := by
    intro x y
    have hrep :
        H.cycleClass p (rangeRepresentative (x + y)) =
          H.cycleClass p (rangeRepresentative x + rangeRepresentative y) := by
      simp [rangeRepresentative_spec]
    rw [nativeMass_congr_of_kernelLaw K p hrep]
    simp
  map_smul' := by
    intro q x
    have hrep :
        H.cycleClass p (rangeRepresentative (q • x)) =
          H.cycleClass p (q • rangeRepresentative x) := by
      simp [rangeRepresentative_spec]
    rw [nativeMass_congr_of_kernelLaw K p hrep]
    simp

/-- Extend the descended native-mass readout to ambient rational cohomology. -/
noncomputable def nativeMassAmbientRead
    (K : NativeMassKernelLaw (V := V) (H := H))
    (p : Nat) :
    RationalSingularCohomology H.analytification (2 * p) →ₗ[ℚ] ℚ :=
  Classical.choose (LinearMap.exists_extend (nativeMassRangeRead K p))

/-- The ambient extension really factors canonical native mass through cycle
class. -/
theorem nativeMassAmbientRead_cycleClass
    (K : NativeMassKernelLaw (V := V) (H := H))
    (p : Nat)
    (Z : codimensionCycles V.X p) :
    nativeMassAmbientRead K p (H.cycleClass p Z) =
      nativeCycleMass V p Z := by
  have hcomp := LinearMap.congr_fun
    (Classical.choose_spec
      (LinearMap.exists_extend (nativeMassRangeRead K p)))
    ((H.cycleClass p).rangeRestrict Z)
  have hrep :
      H.cycleClass p
          (rangeRepresentative ((H.cycleClass p).rangeRestrict Z)) =
        H.cycleClass p Z :=
    rangeRepresentative_spec _
  have hmass := nativeMass_congr_of_kernelLaw K p hrep
  simpa [nativeMassAmbientRead, nativeMassRangeRead, hmass] using hcomp

/-- **NATIVE-MASS UNIVERSAL PROPERTY.**

`kernel_mass_zero` is exactly equivalent to factorization of native mass through
the genuine cycle-class map.  This is the legitimate semantic status of that
field: it is neither Hodge surjectivity nor an optional convenience. -/
theorem nativeMassKernelLaw_iff_cohomologyFactorization :
    NativeMassKernelLaw (V := V) (H := H) ↔
      NativeMassCohomologyFactorization (V := V) (H := H) := by
  constructor
  · intro K p
    exact ⟨nativeMassAmbientRead K p,
      nativeMassAmbientRead_cycleClass K p⟩
  · intro F p Z hZ
    obtain ⟨read, hread⟩ := F p
    have hz := hread Z
    rw [hZ] at hz
    simpa using hz.symm

/-- Canonical native mass of the codimension-zero fundamental cycle is exactly
the number of coheight-zero component generic points. -/
theorem nativeCycleMass_codimensionZeroFundamentalCycle_eq_card
    (V : SmoothProjectiveComplexScheme) :
    nativeCycleMass V 0 (codimensionZeroFundamentalCycle V) =
      ((codimensionZeroPointFinset V).card : ℚ) := by
  letI : CompactSpace V.X := smoothProjectiveCompactSpace V
  change presentationMass
      (presentationOfNativeCycle V.X 0
        (realizeFiniteCodimensionPresentation V.X 0
          (codimensionZeroPresentation V))) = _
  rw [GSTClassicalHodgeGeometricCycleClassPointRigidity.presentationOfNativeCycle_realize]
  simp [codimensionZeroPresentation, presentationMass]

/-- Hence the old base-mass nonvanishing field is exactly component
nonemptiness; no extra numerical mystery is present. -/
theorem baseMass_ne_zero_iff_codimensionZero_nonempty
    (V : SmoothProjectiveComplexScheme) :
    nativeCycleMass V 0 (codimensionZeroFundamentalCycle V) ≠ 0 ↔
      (codimensionZeroPointFinset V).Nonempty := by
  rw [nativeCycleMass_codimensionZeroFundamentalCycle_eq_card]
  constructor
  · intro h
    apply Finset.card_pos.mp
    exact_mod_cast (show (0 : ℚ) < (codimensionZeroPointFinset V).card by
      have hnat : (codimensionZeroPointFinset V).card ≠ 0 := by
        exact_mod_cast h
      exact_mod_cast Nat.pos_of_ne_zero hnat)
  · intro h
    have hcard : (codimensionZeroPointFinset V).card ≠ 0 :=
      Finset.card_ne_zero.mpr h
    exact_mod_cast hcard

/-- The one-step limitless two-slot scalar is the universal coefficient `2`.
This belongs to the intrinsic GST `L^2` plane calculus. -/
theorem successorScalar_eq_two
    (p : Nat) : successorScalar p = (2 : ℚ) := by
  simp [successorScalar,
    GSTClassicalHodgeCrossWeightNativePropagation.limitlessLefschetzScalar]

/-- Native successor mass is instead the exact-successor count.  Therefore the
old equality `successorMass = successorScalar` is equivalent to saying that the
exact-relative-successor locus has cardinality exactly two. -/
theorem successorMass_eq_successorScalar_iff_exactRelativeCard_two
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (x : CodimensionPoint V.X p) :
    successorMass V p x = successorScalar p ↔
      (exactRelativeSuccessorFinset V p x).card = 2 := by
  rw [successorMass_eq_exactRelativeCard]
  rw [successorScalar_eq_two]
  constructor
  · intro h; exact_mod_cast h
  · intro h; exact_mod_cast h

/-- Family form of the previous exact-status theorem. -/
theorem successorPointMassLaw_iff_exactTwoSuccessors
    (V : SmoothProjectiveComplexScheme) :
    (∀ p : Nat, ∀ x : CodimensionPoint V.X p,
      successorMass V p x = successorScalar p) ↔
    (∀ p : Nat, ∀ x : CodimensionPoint V.X p,
      (exactRelativeSuccessorFinset V p x).card = 2) := by
  constructor
  · intro h p x
    exact (successorMass_eq_successorScalar_iff_exactRelativeCard_two
      V p x).1 (h p x)
  · intro h p x
    exact (successorMass_eq_successorScalar_iff_exactRelativeCard_two
      V p x).2 (h p x)

/-- **EXACT LOGICAL CONTENT OF THE OLD NATIVE-MASS BRIDGE.**

The bridge is equivalent to three independent statements:

* native mass factors through genuine cycle class;
* the codimension-zero native component locus is nonempty;
* every point has exactly two exact relative successors.

This theorem prevents the third, genuinely strong cardinality law from being
hidden inside the semantic factorization requirement. -/
theorem nativeMassCycleClassBridge_iff_audited_frontier :
    Nonempty (NativeMassCycleClassBridge V H) ↔
      NativeMassCohomologyFactorization (V := V) (H := H)
      ∧ (codimensionZeroPointFinset V).Nonempty
      ∧ (∀ p : Nat, ∀ x : CodimensionPoint V.X p,
          (exactRelativeSuccessorFinset V p x).card = 2) := by
  constructor
  · rintro ⟨M⟩
    refine ⟨(nativeMassKernelLaw_iff_cohomologyFactorization
      (V := V) (H := H)).1 M.kernel_mass_zero, ?_, ?_⟩
    · exact (baseMass_ne_zero_iff_codimensionZero_nonempty V).1
        M.base_mass_ne_zero
    · exact (successorPointMassLaw_iff_exactTwoSuccessors V).1
        M.successor_point_mass
  · rintro ⟨F, hbase, hsucc⟩
    have K : NativeMassKernelLaw (V := V) (H := H) :=
      (nativeMassKernelLaw_iff_cohomologyFactorization
        (V := V) (H := H)).2 F
    refine ⟨{
      kernel_mass_zero := K
      base_mass_ne_zero :=
        (baseMass_ne_zero_iff_codimensionZero_nonempty V).2 hbase
      successor_point_mass :=
        (successorPointMassLaw_iff_exactTwoSuccessors V).2 hsucc
    }⟩

/-!
## Finite-horizon replacement of the impossible global successor requirement

The native mass bridge demanded two exact successors at every native point,
at every weight.  A terminal point with an empty exact-successor locus
refutes that global premise.  The actual tower argument only needs the
recursion through a specified finite horizon: laws beyond the horizon cannot
affect any witness at or below it.

The following native-first package is local in weight, does not assume
survival at inaccessible strata, and constructs a nonzero GST Hodge seed
through every certified level without assuming a cycle representative for
a target Hodge basis sheet.
-/

/-- Nonzero native mass propagated only to the requested depth. -/
structure FiniteHorizonNativeMassBridge
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (horizon : Nat) where
  kernel_mass_zero :
    ∀ (p : Nat), p ≤ horizon →
      ∀ Z : codimensionCycles V.X p,
        H.cycleClass p Z = 0 → nativeCycleMass V p Z = 0
  base_mass_ne_zero :
    nativeCycleMass V 0 (codimensionZeroFundamentalCycle V) ≠ 0
  successor_point_mass :
    ∀ (p : Nat), p < horizon →
      ∀ x : CodimensionPoint V.X p,
        successorMass V p x = successorScalar p

namespace FiniteHorizonNativeMassBridge

/-- The unrestricted global mass premise specializes to every finite horizon.
The converse is not assumed. -/
noncomputable def ofGlobal
    (M : NativeMassCycleClassBridge V H)
    (horizon : Nat) : FiniteHorizonNativeMassBridge V H horizon where
  kernel_mass_zero := fun p _ Z hZ => M.kernel_mass_zero p Z hZ
  base_mass_ne_zero := M.base_mass_ne_zero
  successor_point_mass := fun p _ x => M.successor_point_mass p x

/-- **HORIZON-LOCAL GST CHARGE CONSERVATION.**
At every level up to the certified horizon, the normalized native projective
spine has exactly the same mass as the original codimension-zero cycle. -/
theorem spine_mass_conserved
    {horizon : Nat}
    (M : FiniteHorizonNativeMassBridge V H horizon)
    (G : GeometricCycleClassSpine V H) :
    ∀ (p : Nat), p ≤ horizon →
      nativeCycleMass V p (spineNativeTower G p) =
        nativeCycleMass V 0 (codimensionZeroFundamentalCycle V) := by
  intro p
  induction p with
  | zero =>
      intro _
      rfl
  | succ p ih =>
      intro hp
      have hp_lt : p < horizon := Nat.lt_of_succ_le hp
      have hp_le : p ≤ horizon := Nat.le_of_lt hp_lt
      have hstep := nativeCycleMass_successor_of_pointMass V p
        (M.successor_point_mass p hp_lt) (spineNativeTower G p)
      rw [spineNativeTower_succ, LinearMap.map_smul, hstep]
      calc
        (successorScalar p)⁻¹ •
            (successorScalar p * nativeCycleMass V p (spineNativeTower G p)) =
            nativeCycleMass V p (spineNativeTower G p) := by
          rw [smul_eq_mul, ← mul_assoc,
            inv_mul_cancel₀ (successorScalar_ne_zero p), one_mul]
        _ = nativeCycleMass V 0 (codimensionZeroFundamentalCycle V) :=
          ih hp_le

/-- Nonzero native charge at each live level prevents the genuine
cycle class of that actual native cycle from vanishing. -/
theorem spine_cycleClass_ne_zero
    {horizon : Nat}
    (M : FiniteHorizonNativeMassBridge V H horizon)
    (G : GeometricCycleClassSpine V H)
    (p : Nat) (hp : p ≤ horizon) :
    H.cycleClass p (spineNativeTower G p) ≠ 0 := by
  intro hz
  have hm := M.kernel_mass_zero p hp (spineNativeTower G p) hz
  rw [M.spine_mass_conserved G p hp] at hm
  exact M.base_mass_ne_zero hm

/-- The native/cohomological spine identity now produces an actual
nonzero algebraic Hodge seed at each certified finite depth. -/
theorem spine_hodgeSeed_ne_zero
    {horizon : Nat}
    (M : FiniteHorizonNativeMassBridge V H horizon)
    (G : GeometricCycleClassSpine V H)
    (p : Nat) (hp : p ≤ horizon) :
    spineHodgeSeed G p ≠ 0 :=
  (spineHodgeSeed_ne_zero_iff_cycleClass_ne_zero G p).2
    (M.spine_cycleClass_ne_zero G p hp)

end FiniteHorizonNativeMassBridge

/-- **TERMINAL-CUT NO-GO FOR GLOBAL MASS BRIDGES.**
An empty exact successor locus is incompatible with the global native mass
axiom (which would force precisely two successors there).  Finite-horizon
bridges above do not demand the invalid law beyond their last level. -/
theorem no_global_nativeMassBridge_of_terminalCut
    (p : Nat) (x : CodimensionPoint V.X p)
    (hstop : exactRelativeSuccessorFinset V p x = ∅) :
    IsEmpty (NativeMassCycleClassBridge V H) := by
  refine ⟨?_⟩
  intro M
  have htwo :
      (exactRelativeSuccessorFinset V p x).card = 2 :=
    (successorPointMassLaw_iff_exactTwoSuccessors V).1
      M.successor_point_mass p x
  simp [hstop] at htwo

#check NativeMassKernelLaw
#check NativeMassCohomologyFactorization
#check nativeMassKernelLaw_iff_cohomologyFactorization
#check nativeCycleMass_codimensionZeroFundamentalCycle_eq_card
#check baseMass_ne_zero_iff_codimensionZero_nonempty
#check successorScalar_eq_two
#check successorMass_eq_successorScalar_iff_exactRelativeCard_two
#check successorPointMassLaw_iff_exactTwoSuccessors
#check nativeMassCycleClassBridge_iff_audited_frontier
#check FiniteHorizonNativeMassBridge
#check FiniteHorizonNativeMassBridge.spine_mass_conserved
#check FiniteHorizonNativeMassBridge.spine_cycleClass_ne_zero
#check FiniteHorizonNativeMassBridge.spine_hodgeSeed_ne_zero
#check no_global_nativeMassBridge_of_terminalCut

#print axioms nativeMassKernelLaw_iff_cohomologyFactorization
#print axioms nativeCycleMass_codimensionZeroFundamentalCycle_eq_card
#print axioms successorMass_eq_successorScalar_iff_exactRelativeCard_two
#print axioms nativeMassCycleClassBridge_iff_audited_frontier
#print axioms FiniteHorizonNativeMassBridge.spine_mass_conserved
#print axioms FiniteHorizonNativeMassBridge.spine_cycleClass_ne_zero
#print axioms FiniteHorizonNativeMassBridge.spine_hodgeSeed_ne_zero
#print axioms no_global_nativeMassBridge_of_terminalCut

end GSTClassicalHodgeNativeMassBridgeAudit
