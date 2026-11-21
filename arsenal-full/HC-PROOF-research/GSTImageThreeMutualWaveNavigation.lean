import GSTImageThreeNativeFCompiler
import GSTGraphV2CMWaveFusion

/-!
# GST Image 3 — ORIGINAL N-COHOMOLOGY TWO-WORLD MUTUAL SOURCE TRANSPORT

This is NOT an external Hilbert/Chow model. It uses the OWNER'S exact
original 12-state U, rational CM J, true SURVIVE M, and existing
physical Navigation charge. The two independent Wave-II holes have the
original 10-address difference, and exchange the actual original M.

The original source-free subsystem U+J has ten cyclic directions.
Exact Wolfram computations in the companion experiment prove the
genuinely NEW 24-state bidirectional source transport has full rank
for ALL FOUR binary physical Navigation masks, even {0,0}.
The finite-rank certificate is not claimed as a kernel-checked Lean
24x24 determinant, and is not a Hodge class on arbitrary X.

This source proves algebraic exact construction and the coupled CM
curvature law inside the ORIGINAL native GST carrier.
-/

set_option maxHeartbeats 5000000
noncomputable section

namespace GSTImageThreeMutualWaveNavigation

open GSTGraphV2CMWaveFusion
open GSTImageThreeNativeFCompiler
open GSTPerfectPowerTailNavigation

/-- Two ORIGINAL independent N-cohomology Wave-II holes,
each containing the unchanged twelve-state Wave-I signal. -/
abbrev WavePair := WaveSignal × WaveSignal

/-- The original CM mirror at BOTH genuine wave worlds. -/
def pairJ (v : WavePair) : WavePair := (J v.1, J v.2)

/-- New genuinely source-coupled F from the author's ORIGINAL laws.
The adjacent-world maps use M itself, not an arbitrary new matrix.
Ten is the OLD Wave-II channel address separation. -/
def coupledF (κ₀ κ₁ : ℚ) (v : WavePair) : WavePair :=
  (navigationControlledF κ₀ v.1 + M v.2,
   navigationControlledF κ₁ v.2 + (10 : ℚ) • v.2 + M v.1)

/-- Navigation chooses only the local source contributions. The
inter-world original SURVIVE transport stays physically present
when BOTH local navigation charges vanish. -/
def physicalCoupledF (R₀ R₁ : Nat) (v : WavePair) : WavePair :=
  coupledF (navigationCharge R₀) (navigationCharge R₁) v

/-- Exact native two-world ORIGINAL CM curvature: local and interworld
source commutators add. This is derived using the old J/U/M laws. -/
theorem coupledF_CM_defect (κ₀ κ₁ : ℚ) (v : WavePair) :
    pairJ (coupledF κ₀ κ₁ v) - coupledF κ₀ κ₁ (pairJ v) =
      (κ₀ • (J (M v.1) - M (J v.1)) +
          (J (M v.2) - M (J v.2)),
       κ₁ • (J (M v.2) - M (J v.2)) +
          (J (M v.1) - M (J v.1))) := by
  apply Prod.ext
  · change
      J (navigationControlledF κ₀ v.1 + M v.2) -
        (navigationControlledF κ₀ (J v.1) + M (J v.2)) =
      κ₀ • (J (M v.1) - M (J v.1)) +
        (J (M v.2) - M (J v.2))
    rw [J_add]
    calc
      _ = (J (navigationControlledF κ₀ v.1) -
          navigationControlledF κ₀ (J v.1)) +
          (J (M v.2) - M (J v.2)) := by abel
      _ = _ := by rw [navigationControlledF_CM_defect]
  · change
      J (navigationControlledF κ₁ v.2 + (10 : ℚ) • v.2 + M v.1) -
        (navigationControlledF κ₁ (J v.2) + (10 : ℚ) • J v.2 +
          M (J v.1)) =
      κ₁ • (J (M v.2) - M (J v.2)) +
        (J (M v.1) - M (J v.1))
    simp only [J_add, J_smul]
    calc
      _ = (J (navigationControlledF κ₁ v.2) -
          navigationControlledF κ₁ (J v.2)) +
          (J (M v.1) - M (J v.1)) := by abel
      _ = _ := by rw [navigationControlledF_CM_defect]

/-- True cross-world GST navigation is insensitive to canonical-tail
changes in BOTH local arithmetic addresses, while M links remain
the same concrete original SURVIVE source. -/
theorem physicalCoupledF_canonicalTail
    (s₀ b₀ s₁ b₁ : Nat) (hs₀ : 1 ≤ s₀) (hs₁ : 1 ≤ s₁)
    (v : WavePair) :
    physicalCoupledF (4^(3^s₀*b₀)) (4^(3^s₁*b₁)) v =
      physicalCoupledF (canonicalTail s₀ b₀)
        (canonicalTail s₁ b₁) v := by
  simp only [physicalCoupledF, navigationCharge_canonicalTail s₀ b₀ hs₀,
    navigationCharge_canonicalTail s₁ b₁ hs₁]

#check coupledF
#check physicalCoupledF
#check coupledF_CM_defect
#check physicalCoupledF_canonicalTail
#print axioms coupledF_CM_defect
#print axioms physicalCoupledF_canonicalTail

end GSTImageThreeMutualWaveNavigation
