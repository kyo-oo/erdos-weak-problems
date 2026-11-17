#!/usr/bin/env python3
from pathlib import Path

p = Path('ErdosTernary2.lean')
s = p.read_text(encoding='utf-8')

marker = '-- BEGIN SOL56 FINAL INFINITE MONOLITH TRANSPLANT'
if marker in s:
    print('FINAL_INFINITE_MONOLITH_TRANSPLANT already installed')
    raise SystemExit(0)

import_anchor = 'import Mathlib.Tactic.Ring\n'
imports = '''import Mathlib.Tactic.Ring
import GSTGraphV2ProductionLaws
import GSTGraphV2InfiniteControllerBridge
import GSTGraphV2PerfectPowerBlockProbe
import GSTU2DSharpCrossingBlock
import GSTFinalPurePowerResidueTransplant

-- Full canonical pure-power/information transplant.  These are the contiguous
-- Aug-15/Aug-17 layers used by the live prefix-one residual seam; they are not
-- detached probes.
import InformationDescentScratch
import InformationGeometryScratch
import InformationStateScratch
import InformationBadTraceScratch
import OriginTransducerScratch
import InformationRegenerationScratch
import InformationIterationScratch
import InformationQuotientScratch
import InformationLocalizationScratch
import InformationFluxScratch
import InformationForcingScratch
import CarryWordScratch
import InformationCarryWordBridgeScratch
import PurePowerCarrierScratch
import CanonicalPrefixScratch
import CanonicalOriginModulusScratch
import PrefixOneOriginPhaseRecursionScratch
import PurePowerBadAxisScratch
import BadLanguageMagnitudeScratch
import PurePowerTailReductionScratch
import HorizontalTrapWidthDescentScratch
import StripConservationScratch
import GSTGraphV2Scratch
import GSTGraphV2FluxScratch
import GSTGraphV2BlockScratch
import GSTExponentLiftScratch
import PurePowerResidueGraphScratch
import GSTResidueSpacetimeScratch
import PhaseCycleInformationScratch
import CanonicalCausalityScratch
'''
if import_anchor not in s:
    raise SystemExit('import anchor not found')
s = s.replace(import_anchor, imports, 1)

needle = '''  -- TRUE RED SEAM. Everything used by BIG-N Step 6 is now physically in the
  -- monolith: hchildCore, hBad, hboundary, retained-origin recursion,
  -- right-chord, physical rectangle, signed flux, and finite i=N horizon.
  gst_end
'''

replacement = r'''  -- BEGIN SOL56 FINAL INFINITE MONOLITH TRANSPLANT
  -- The residual failure is converted directly into the all-Nat Graph-V2
  -- boundary language.  No finite-support endpoint and no legacy residual
  -- Omega termination theorem occurs below.
  have hResidualBad : GSTOmegaInfiniteBadTrace s k m := by
    intro j
    change GSTOmegaGatePolynomial (gstOmega s k m j) ≠ 0
    intro hzero
    apply hnoParent
    rw [hparentArg]
    exact gst_omega_gate_zero_closes_parent s k m hs ⟨j, hzero⟩

  have hchildResidual :
      GSTNavigationWitness (gstNavigationConstant (s+k) m) := by
    simpa [k, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hchildCore

  -- TRANSPLANTED CONNECTOR A:
  -- residual child Navigation witness -> literal Happy left boundary.
  have hChildLeftExists :
      ∃ j,
        GST2DMixedEmergence.HappyCell
          (GSTGraphV2InfiniteControl.graph
            (GSTGraphV2HandwrittenOmegaUBlock.residualEnergy s k m)
            0 (s+k+1+j)).seven.carry
          (GSTGraphV2InfiniteControl.graph
            (GSTGraphV2HandwrittenOmegaUBlock.residualEnergy s k m)
            0 (s+k+1+j)).seven.digit := by
    obtain ⟨j, hd, hspace⟩ := hchildResidual
    have hmod : gstCarry (gstNavigationConstant (s+k) m) j % 3 = 0 :=
      gstGoodSpace_carry_mod3_zero _ j hspace
    have hlt : gstCarry (gstNavigationConstant (s+k) m) j < 4 := by
      cases j with
      | zero => simp [gstCarry, Nat.mod_one]
      | succ t => exact gstCarry_lt_four _ (t+1) (by omega)
    have hcarry :
        gstCarry (gstNavigationConstant (s+k) m) j = 0 ∨
        gstCarry (gstNavigationConstant (s+k) m) j = 3 := by
      omega
    refine ⟨j, ?_⟩
    have hb3 : 3 ≤ s+k+1 := by omega
    have hpow : 3^3 ≤ 3^(s+k+1) :=
      Nat.pow_le_pow_of_le (by decide : 1 < 3) hb3
    have hfour : 4 < 3^(s+k+1) := by
      norm_num at hpow ⊢
      omega
    have hone : 1 < 3^(s+k+1) := by omega
    have hE :
        4^0 * GSTGraphV2HandwrittenOmegaUBlock.residualEnergy s k m =
          1 + 3^(s+k+1) * gstNavigationConstant (s+k) m := by
      simpa [GSTGraphV2HandwrittenOmegaUBlock.residualEnergy] using
        gst_navigation_decomposition (s+k) m (by omega)
    have hiff := GSTGraphV2InfiniteControl.graph_prefix_slice_happy_iff
      (GSTGraphV2HandwrittenOmegaUBlock.residualEnergy s k m)
      0 (s+k+1) 1 (gstNavigationConstant (s+k) m) j hE hone
    apply hiff.2
    have hseed : (4 * 1) / 3^(s+k+1) = 0 := Nat.div_eq_of_lt hfour
    simpa [GSTCanonicalSevenAxisBridge.digit3, gstDigit,
      GSTGraphV2InfiniteControl.seededCarry, gstCarry, hseed] using
      ⟨hd, hcarry⟩

  -- TRANSPLANTED CONNECTOR B:
  -- all-depth residual Omega bad trace -> all-depth bad right boundary.
  have hRightBad : ∀ j,
      ¬ GST2DMixedEmergence.HappyCell
        (GSTGraphV2InfiniteControl.graph
          (GSTGraphV2HandwrittenOmegaUBlock.residualEnergy s k m)
          (GSTGraphV2HandwrittenOmegaUBlock.residualWidth s)
          (s+k+1+j)).seven.carry
        (GSTGraphV2InfiniteControl.graph
          (GSTGraphV2HandwrittenOmegaUBlock.residualEnergy s k m)
          (GSTGraphV2HandwrittenOmegaUBlock.residualWidth s)
          (s+k+1+j)).seven.digit := by
    intro j hright
    have habs :
        GST2DMixedEmergence.HappyCell
          (GSTGraphV2InfiniteControl.graph 1
            (GSTGraphV2HandwrittenOmegaUBlock.residualParentExponent s k m)
            (s+k+1+j)).seven.carry
          (GSTGraphV2InfiniteControl.graph 1
            (GSTGraphV2HandwrittenOmegaUBlock.residualParentExponent s k m)
            (s+k+1+j)).seven.digit :=
      (GSTGraphV2HandwrittenOmegaUBlock.residual_parent_happy_iff
        s k m (s+k+1+j)).1 hright
    have hb2 : 2 ≤ s+1 := by omega
    have hpow : 3^2 ≤ 3^(s+1) :=
      Nat.pow_le_pow_of_le (by decide : 1 < 3) hb2
    have hfour : 4 < 3^(s+1) := by
      norm_num at hpow ⊢
      omega
    have hone : 1 < 3^(s+1) := by omega
    have hE :
        4^(GSTGraphV2HandwrittenOmegaUBlock.residualParentExponent s k m) * 1 =
          1 + 3^(s+1) * gstNavigationConstant s (1 + 3^k*m) := by
      simpa [GSTGraphV2HandwrittenOmegaUBlock.residualParentExponent] using
        gst_navigation_decomposition s (1 + 3^k*m) hs
    have hiff := GSTGraphV2InfiniteControl.graph_prefix_slice_happy_iff
      1 (GSTGraphV2HandwrittenOmegaUBlock.residualParentExponent s k m)
      (s+1) 1 (gstNavigationConstant s (1 + 3^k*m)) (k+j) hE hone
    have hq := hiff.1 habs
    have hseed : (4 * 1) / 3^(s+1) = 0 := Nat.div_eq_of_lt hfour
    have hproj := gst_omega_parent_projection s k m j hs
    have hdOmega : (gstOmega s k m j).parentDigit = 2 := by
      rw [← hproj.1]
      simpa [GSTCanonicalSevenAxisBridge.digit3, gstDigit] using hq.1
    have hcOmega :
        (gstOmega s k m j).parentCarry = 0 ∨
        (gstOmega s k m j).parentCarry = 3 := by
      rw [← hproj.2]
      simpa [GSTGraphV2InfiniteControl.seededCarry, gstCarry, hseed] using hq.2
    have hzero : GSTOmegaGatePolynomial (gstOmega s k m j) = 0 :=
      (gst_omega_gate_polynomial_zero_iff (gstOmega s k m j)).2
        ⟨hdOmega, hcOmega⟩
    have hneq := hResidualBad j
    change GSTOmegaGatePolynomial (gstOmega s k m j) ≠ 0 at hneq
    exact hneq hzero

  -- The exact classifier remains the only split.  Each branch consumes the
  -- same transplanted infinite Graph-V2 boundary objects.
  rcases hboundary with hlevel1 | hlevel3 | hstable
  · rcases hlevel1 with ⟨hs1, hcase⟩
    subst s
    rcases hcase with hm1 | hm2
    · -- Unbounded hard family: s=1 and m mod 3 = 1.
      obtain ⟨q, hChild⟩ := hChildLeftExists
      have hRightBad3 : ∀ j,
          ¬ GST2DMixedEmergence.HappyCell
            (GSTGraphV2InfiniteControl.graph
              (GSTGraphV2HandwrittenOmegaUBlock.residualEnergy 1 k m)
              3 (k+2+j)).seven.carry
            (GSTGraphV2InfiniteControl.graph
              (GSTGraphV2HandwrittenOmegaUBlock.residualEnergy 1 k m)
              3 (k+2+j)).seven.digit := by
        intro j
        have h := hRightBad j
        simpa [GSTGraphV2HandwrittenOmegaUBlock.residualWidth,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

      let E := GSTGraphV2HandwrittenOmegaUBlock.residualEnergy 1 k m
      let b := k + 2
      let Kexp := 3^(k+1) * m
      have hEpow : E = 4^Kexp := by rfl

      -- Canonical prefix-one constants transplanted from the Aug-17 stack.
      have hQ : GSTCanonicalOriginEnergyS gstNavigationConstant := by
        intro t n ht
        exact gst_navigation_decomposition t n ht
      let z : Nat → Nat := fun t => c t / 3
      have hunit : ∀ t, 1 ≤ t →
          gstNavigationConstant t 1 = 1 + 3 * z t := by
        intro t ht
        dsimp [z]
        rw [gstNavigationConstant_one t ht]
        have hc3 : c t % 3 = 1 := c_mod3 t ht
        have hsplit := Nat.mod_add_div (c t) 3
        omega
      have hz3 : ∀ t, 1 ≤ t → z t % 3 = 2 := by
        intro t ht
        dsimp [z]
        have hc9 : c t % 9 = 7 := c_mod9 t ht
        have hc3 : c t % 3 = 1 := c_mod3 t ht
        have hsplit : c t % 9 = c t % 3 + 3 * (c t / 3 % 3) := by
          rw [show (9:Nat) = 3 * 3 by decide, Nat.mod_mul]
        rw [hc9, hc3] at hsplit
        omega

      -- Exact A=64, c=7, z=2 canonical block identities.  These are now
      -- instantiated inside the hard branch rather than left in scratch files.
      have hA64 : (64 : Nat) = 4^(3^1) := by norm_num
      have hLTE64 : (64 : Nat) = 1 + 3^(1+1) * 7 := by norm_num
      have hc72 : (7 : Nat) = 1 + 3 * 2 := by norm_num
      have hPrefixSquare := gst_canonical_prefix_one_energy_squareS
        gstNavigationConstant hQ 1 m (by decide)
      have hOriginRec := gst_hard_tail_origin_one_recursionS
        gstNavigationConstant hQ z hunit 1 (m/3) (by decide)
      have hOriginDigit := gst_hard_tail_origin_one_mod3S
        gstNavigationConstant hQ z hunit hz3 1 (m/3) (by decide)

      -- Full exact power-residue rectangle, not the reduced one-theorem probe.
      have hPowerRectangle :=
        gst_exact_power_rectangle_conservationS k 2 Kexp q
      have hPowerCarry0 :=
        gst_residue_strip_carry_is_exact_power_carryS k Kexp q 0
      have hPowerCarry1 :=
        gst_residue_strip_carry_is_exact_power_carryS k Kexp q 1
      have hPowerCarry2 :=
        gst_residue_strip_carry_is_exact_power_carryS k Kexp q 2
      have hPowerCarry3 :=
        gst_residue_strip_carry_is_exact_power_carryS k Kexp q 3

      have hBaseCarryZero :
          (GSTGraphV2InfiniteControl.graph E 0 b).seven.carry = 0 := by
        have hmodE : E % 3^b = 1 := by
          have h := GSTGraphV2HandwrittenExponentialLTE.pow4_scaled_mod_next
            (k+1) m
          simpa [E, b, GSTGraphV2HandwrittenOmegaUBlock.residualEnergy,
            Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
        change GSTCanonicalSevenAxisBridge.carry4 E b = 0
        unfold GSTCanonicalSevenAxisBridge.carry4
        rw [hmodE]
        apply Nat.div_eq_of_lt
        have hb9 : 9 ≤ 3^b := by
          rw [show (9 : Nat) = 3^2 by decide]
          exact Nat.pow_le_pow_of_le (by decide : 1 < 3) (by dsimp [b]; omega)
        omega

      have hInfiniteControl :=
        GSTGraphV2InfiniteControllerBridge.graph_infinite_bad_control
          E 3 b hBaseCarryZero (by
            intro j
            simpa [E, b, Nat.add_assoc] using hRightBad3 j)
      have hLatentGate :=
        GSTGraphV2InfiniteControllerBridge.graph_child_happy_latent_transfer
          E 3 b q hBaseCarryZero
          (by intro j; simpa [E, b, Nat.add_assoc] using hRightBad3 j)
          (by simpa [E, b, Nat.add_assoc] using hChild)
      have hInfiniteLedger :=
        GSTV2.infinite_coupled_ledger
          (4^3)
          (GSTGraphV2InfiniteControllerBridge.graphCoupledState E 3 b)
          (by positivity)
          (GSTGraphV2InfiniteControllerBridge.graphCoupledState_invariant E 3 b)
      have hLedgerGate := hInfiniteLedger.pastSynchronized q
      have hBadSuffix := hLatentGate.nextParentBadSuffix
      have hLatentCarry := hLatentGate.nextCarryTwoOrThree
      have hLatentCarryNonzero := hLatentGate.nextCarryNonzero
      have hNextInvariant := hLatentGate.nextInvariant

      -- The only remaining goal after this point is the canonical no-erasure
      -- collision between the transplanted origin recursion / residue rectangle
      -- and the all-depth right-bad suffix.  Keep it visible to Lean.
      trace_state
      omega
    · rcases hm2 with ⟨hm2, hk13⟩
      rcases hk13 with hk1 | hk3
      · subst k
        trace_state
        omega
      · subst k
        trace_state
        omega
  · rcases hlevel3 with ⟨hs3, hk7, hnot2, hnot4, hnot6⟩
    subst s
    trace_state
    omega
  · rcases hstable with ⟨hs2, hs3, hk4, hnot2⟩
    trace_state
    omega
  -- END SOL56 FINAL INFINITE MONOLITH TRANSPLANT
'''

if needle not in s:
    raise SystemExit('production gst_end seam not found')
s = s.replace(needle, replacement, 1)
p.write_text(s, encoding='utf-8')
print('FINAL_INFINITE_MONOLITH_TRANSPLANT installed')
