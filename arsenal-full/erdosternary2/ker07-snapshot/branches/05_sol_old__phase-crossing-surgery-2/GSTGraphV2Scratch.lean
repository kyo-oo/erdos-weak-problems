/- ======================================================================
/- CHRONOLOGICAL LABEL -- #0480 / 1132
/-    Path         : branches/sol_phase-crossing-surgery-2/GSTGraphV2Scratch.lean
/-    Ref          : origin/sol/phase-crossing-surgery-2
/-    First-commit : 2026-08-16 00:34:53 +0530  (4cd4426)
/-    Last-commit  : 2026-08-16 02:29:37 +0530  (d84b9aa)
/-    Total commits: 8
/- ======================================================================
/- GIT HISTORY (chronological, oldest first)
/- ======================================================================
/- [01/8] 2026-08-16 00:34:53 +0530  4cd4426  (ker07-dev)
/-        Add GST Graph V2 residue classifier scratch
/- [02/8] 2026-08-16 00:39:13 +0530  3867634  (ker07-dev)
/-        Extend GST Graph V2 with closed micro-output phase loop
/- [03/8] 2026-08-16 00:44:06 +0530  1a9706b  (ker07-dev)
/-        Add common-two interpretation to GST Graph V2
/- [04/8] 2026-08-16 00:56:49 +0530  5aedb58  (ker07-dev)
/-        Fix GST Graph V2 common-two tactic overrun
/- [05/8] 2026-08-16 01:17:18 +0530  75dcf6e  (ker07-dev)
/-        Kernelize GST V2 local five-rotation law
/- [06/8] 2026-08-16 01:33:49 +0530  e47d846  (ker07-dev)
/-        Expand GST local five-rotation explicitly for Lean 4.33
/- [07/8] 2026-08-16 02:02:09 +0530  d8279e9  (ker07-dev)
/-        Fix GST Graph V2 bad-trace import
/- [08/8] 2026-08-16 02:29:37 +0530  d84b9aa  (ker07-dev)
/-        model GST V2 as seven-axis three-space graph
/- ====================================================================== -/

import InformationRegenerationScratch
import InformationBadTraceScratch

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

/-!
# GST Graph V2 scratch

V2 does NOT replace the original GST ontology.  It keeps the exact seven
non-dimensional axes

  (x, x', y, y', z, z', n -> n')

and the same three spaces NULL / ALT- / GST+.  The upgrade is that every vertex
may additionally be read through the shared-information, phase-cycle, and
canonical-energy overlays proved in the information modules.

Semantic correction: NULL is a genuine space/realisation, but no absorbing or
terminal axiom is attached to it.  In particular digit-two information in NULL
regenerates to carry two under the exact GST edge law.
-/

inductive GSTSpaceV2S
  | null
  | altMinus
  | gstPlus
  deriving Repr, DecidableEq

def gstSpaceV2S (C : Nat) : GSTSpaceV2S :=
  if C = 0 then .null else if C = 3 then .gstPlus else .altMinus

/-- The original seven axes, represented without collapsing any coordinate. -/
structure GSTSevenAxisVertexV2S where
  x : Nat
  xNext : Nat
  carry : Nat
  space : GSTSpaceV2S
  digit : Nat
  boundary : Nat
  descent : Nat
  nextDescent : Nat
  deriving Repr

/-- Canonical construction of one V2 vertex.  The additional V2 invariants are
projections/overlays on this vertex; they are not replacement dimensions. -/
def gstSevenAxisVertexV2S (R N p : Nat) : GSTSevenAxisVertexV2S where
  x := p
  xNext := p + 1
  carry := gstCarryS R p
  space := gstSpaceV2S (gstCarryS R p)
  digit := gstDigitS R p
  boundary := N - p
  descent := R / 3^p
  nextDescent := R / 3^(p+1)

/-- The V2 overlay retains the new conserved coordinates discovered during the
surgery while the underlying seven-axis vertex remains intact. -/
structure GSTGraphV2OverlayS where
  sharedCarrier : Nat
  affineQuotient : Nat
  highRemainder : Nat
  phase : Nat
  paradoxEnergy : Nat
  deriving Repr

/-- The two residue classes of the shared carrier which realise a parent Happy
Gate for the current child digit r. -/
def GSTParentHappyResidue12S (S r : Nat) : Prop :=
  match r with
  | 0 => S % 12 = 8 ∨ S % 12 = 11
  | 1 => S % 12 = 4 ∨ S % 12 = 7
  | 2 => S % 12 = 0 ∨ S % 12 = 3
  | _ => False

/-- Exact mod-12 compression of the parent gate condition. -/
theorem gst_parent_happy_iff_shared_residue12S
    (S D Z r : Nat)
    (hD : D < 4)
    (hr : r < 3)
    (hS : S = D + 4*Z) :
    (((Z + r) % 3 = 2) ∧ (D = 0 ∨ D = 3)) ↔
      GSTParentHappyResidue12S S r := by
  have hrCases : r = 0 ∨ r = 1 ∨ r = 2 := by omega
  rcases hrCases with h0 | h1 | h2
  · subst r
    simp [GSTParentHappyResidue12S]
    omega
  · subst r
    simp [GSTParentHappyResidue12S]
    omega
  · subst r
    simp [GSTParentHappyResidue12S]
    omega

/-- Parent badness is exactly avoidance of the rotating residue pair. -/
theorem gst_parent_bad_iff_avoids_shared_residue12S
    (S D Z r : Nat)
    (hD : D < 4)
    (hr : r < 3)
    (hS : S = D + 4*Z) :
    GSTBadPairS D ((Z+r) % 3) ↔
      ¬ GSTParentHappyResidue12S S r := by
  unfold GSTBadPairS
  rw [gst_parent_happy_iff_shared_residue12S S D Z r hD hr hS]

/-- At a child digit-two row a bad parent avoids residues 0 and 3 mod 12. -/
theorem gst_parent_bad_at_child_two_residue12S
    (S D Z : Nat)
    (hD : D < 4)
    (hS : S = D + 4*Z)
    (hbad : GSTBadPairS D ((Z+2) % 3)) :
    S % 12 ≠ 0 ∧ S % 12 ≠ 3 := by
  have havoid :=
    (gst_parent_bad_iff_avoids_shared_residue12S S D Z 2 hD (by decide) hS).mp hbad
  simpa [GSTParentHappyResidue12S] using havoid

/-!
The second V2 compression is horizontal. Encode one microscopic multiply-by-4
output word at macro phase p by `Yp = p + 4*Hp`. The canonical macro phase
advance by A becomes an affine recurrence on the Y words themselves.
-/

/-- Phase 0 -> phase 1 on the microscopic output word. -/
theorem gst_phase_micro_output01S
    (A z H0 H1 : Nat)
    (hH1 : H1 = z + A*H0) :
    1 + 4*H1 = (1 + 4*z) + A*(4*H0) := by
  rw [hH1]
  ring

/-- Phase 1 -> phase 2 on the microscopic output word. -/
theorem gst_phase_micro_output12S
    (A N c z H1 H2 : Nat)
    (hA : A = 1 + 3*N*c)
    (hc : c = 1 + 3*z)
    (hH2 : H2 = z + N*c + A*H1) :
    2 + 4*H2 = (1 + 4*z + N*c) + A*(1 + 4*H1) := by
  rw [hH2, hA, hc]
  ring

/-- Phase 2 -> next phase 0 on the microscopic output word. -/
theorem gst_phase_micro_output20S
    (A N c z H2 H0next : Nat)
    (hA : A = 1 + 3*N*c)
    (hc : c = 1 + 3*z)
    (hH0 : H0next = z + 1 + 2*N*c + A*H2) :
    4*H0next = (2 + 4*z + 2*N*c) + A*(2 + 4*H2) := by
  rw [hH0, hA, hc]
  ring

/-- Generic bridge from phase energy to its microscopic output tail. -/
theorem gst_phase_micro_output_energyS
    (E D p H : Nat)
    (hE : E = 1 + p*D + 3*D*H) :
    4*E = 4 + p*D + 3*D*(p + 4*H) := by
  rw [hE]
  ring

/-- Exact microscopic output digit for a seed-retaining wave. -/
theorem gst_seeded_output_digit_exactS
    (seed H q : Nat) :
    gstDigitS (seed + 4*H) q =
      (gstAffineMulCarryS 4 seed H q + gstDigitS H q) % 3 := by
  exact gst_parent_digit_from_informationS 4 seed H q (by decide)

/-- A seeded Happy Gate is exactly a common ternary digit two between the input
word H and its microscopic output word seed+4H. -/
theorem gst_seeded_happy_iff_common_twoS
    (seed H q : Nat)
    (hseed : seed < 4) :
    (gstDigitS H q = 2 ∧
      (gstAffineMulCarryS 4 seed H q = 0 ∨
       gstAffineMulCarryS 4 seed H q = 3)) ↔
    (gstDigitS H q = 2 ∧ gstDigitS (seed + 4*H) q = 2) := by
  have hC : gstAffineMulCarryS 4 seed H q < 4 :=
    gst_affine_carry_lt_multiplierS 4 seed H q (by decide) hseed
  have hout := gst_seeded_output_digit_exactS seed H q
  constructor
  · rintro ⟨hd, h0 | h3⟩
    · refine ⟨hd, ?_⟩
      rw [hout, hd, h0]
    · refine ⟨hd, ?_⟩
      rw [hout, hd, h3]
  · rintro ⟨hd, hout2⟩
    refine ⟨hd, ?_⟩
    rw [hout, hd] at hout2
    omega

/-- A complete seeded bad trace is exactly absence of a common digit two
between H and seed+4H at every ternary height. -/
theorem gst_seeded_bad_iff_no_common_twoS
    (seed H : Nat)
    (hseed : seed < 4) :
    GSTSeededBadTraceS seed H ↔
      ∀ q, ¬ (gstDigitS H q = 2 ∧ gstDigitS (seed + 4*H) q = 2) := by
  constructor
  · intro hbad q hcommon
    have hhappy :=
      (gst_seeded_happy_iff_common_twoS seed H q hseed).mpr hcommon
    exact (hbad q) hhappy
  · intro hno q hhappy
    have hcommon :=
      (gst_seeded_happy_iff_common_twoS seed H q hseed).mp hhappy
    exact hno q hcommon

/-! Local five-rotation realization law. This is a re-coordinate map of one
legal GST cell, not a global GST+/ALT- mirror. -/
def gstLocalRotateS (x : Nat × Nat) : Nat × Nat :=
  ((x.1 + 4*x.2) / 3, (x.1 + 4*x.2) % 3)

/-- Every legal local carry/digit cell returns after five re-coordinatizations.
The two fixed states are `(0,0)` and `(3,2)`; the remaining ten states form two
five-cycles. -/
theorem gst_local_rotate_fiveS
    (C d : Nat) (hC : C < 4) (hd : d < 3) :
    gstLocalRotateS
      (gstLocalRotateS
        (gstLocalRotateS
          (gstLocalRotateS
            (gstLocalRotateS (C,d))))) = (C,d) := by
  have hCc : C = 0 ∨ C = 1 ∨ C = 2 ∨ C = 3 := by omega
  have hdc : d = 0 ∨ d = 1 ∨ d = 2 := by omega
  rcases hCc with h0 | h1 | h2 | h3 <;>
    rcases hdc with d0 | d1 | d2 <;>
    subst C <;> subst d <;> decide
