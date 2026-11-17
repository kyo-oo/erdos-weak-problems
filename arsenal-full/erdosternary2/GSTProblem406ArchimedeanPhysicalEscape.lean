import GSTFourPowerDirectNo22
import GSTFourPowerNo22Magnitude
import GSTFourPowerThirdWave
import GSTFourPowerDirectCreationMaster

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
# Archimedean physical escape into the *original* universal GST hGate

The all-depth absence of a CommonTwo gate forces every positive source
ternary-22 block to disappear (exact binary carry law).  The sharp
Cantor-language magnitude inequality then applies to the **literal**
source 4^K (not a generic shifted controller):

    4^K < 9^m  and  no CommonTwo K
    ==> 8 * 4^K <= 7*(9^m-1).

The contrapositive produces a genuine physical same-row digit-two
witness.  It requires NO prior gate, no axiom, no sample bound and no
sorry. It does not by itself cover every exponent K; its remaining
coverage question is stated explicitly, not claimed proved.
-/

namespace GSTProblem406ArchimedeanPhysicalEscape

open GSTFourPowerDirectExistence

/-- A source without an original physical CommonTwo has the sharp
global magnitude restriction of the no-22 ternary language. -/
theorem no_gate_forces_sharp_magnitude
    (K m : Nat)
    (hBelow : 4^K < 9^m)
    (hBad : ¬ CommonTwo K) :
    8 * 4^K ≤ 7*(9^m-1) := by
  have hNoWord :
      GSTFourPowerNo22Magnitude.No22Ternary (4^K) :=
    GSTFourPowerDirectNo22.no_common_pow4_forbids_all_22 K hBad
  exact GSTFourPowerNo22Magnitude.no22_nine_power_bound
    (4^K) m hBelow hNoWord

/-- A purely numerical *source-specific* inequality establishes the exact
original same-position two in 4^K and 4^(K+1), at some positive position. -/
theorem CommonTwo_of_archimedean_escape
    (K m : Nat)
    (hBelow : 4^K < 9^m)
    (hEscape : 7*(9^m-1) < 8*4^K) :
    CommonTwo K := by
  by_contra hBad
  have hbound := no_gate_forces_sharp_magnitude K m hBelow hBad
  omega

/-- Translate the unconditional physical criterion directly into the
production gate body, using the kernel-verified exact third-wave equivalence. -/
theorem original_thirdWave_of_archimedean_escape
    (K m : Nat)
    (hBelow : 4^K < 9^m)
    (hEscape : 7*(9^m-1) < 8*4^K) :
    GSTFourPowerThirdWave.thirdWave K := by
  exact (GSTFourPowerThirdWave.thirdWave_iff_commonTwo K).2
    (CommonTwo_of_archimedean_escape K m hBelow hEscape)

/-- The same mathematical witness directly inhabits the original physical
creation-certificate type (no abstraction or extra hypothesis). -/
theorem original_creation_certificate_of_archimedean_escape
    (K m : Nat)
    (hBelow : 4^K < 9^m)
    (hEscape : 7*(9^m-1) < 8*4^K) :
    GSTFourPowerOntologicalAdapter.CreationCertificate (4^K) := by
  exact GSTFourPowerDirectCreationMaster.commonTwo_to_creation_certificate K
    (CommonTwo_of_archimedean_escape K m hBelow hEscape)

/-- A single existential Archimedean trigger, independent of any
hGate-shaped provider or oracle. -/
def ArchimedeanEscape (K : Nat) : Prop :=
  ∃ m : Nat, 4^K < 9^m ∧ 7*(9^m-1) < 8*4^K

theorem thirdWave_of_ArchimedeanEscape
    (K : Nat)
    (h : ArchimedeanEscape K) :
    GSTFourPowerThirdWave.thirdWave K := by
  obtain ⟨m, hsize, htop⟩ := h
  exact original_thirdWave_of_archimedean_escape K m hsize htop

/-- All-exponent formulation of what this branch proves. This is
conditional on the *explicit numerical escape condition* and must not
be substituted for the still-open original all-K hGate. -/
theorem original_hGate_body_on_ArchimedeanEscape
    (K : Nat) (_hK : 5 ≤ K) (_hK7 : K ≠ 7)
    (hEscape : ArchimedeanEscape K) :
    GSTFourPowerThirdWave.thirdWave K :=
  thirdWave_of_ArchimedeanEscape K hEscape

/-- A concrete witness of the metric criterion, demonstrating it is
nonvacuous. (The general theorem above is uniform in K and m.) -/
theorem ArchimedeanEscape_nineteen :
    ArchimedeanEscape 19 := by
  refine ⟨12, ?_, ?_⟩ <;> decide

#print axioms no_gate_forces_sharp_magnitude
#print axioms CommonTwo_of_archimedean_escape
#print axioms original_thirdWave_of_archimedean_escape
#print axioms original_creation_certificate_of_archimedean_escape
#print axioms thirdWave_of_ArchimedeanEscape
#print axioms ArchimedeanEscape_nineteen

end GSTProblem406ArchimedeanPhysicalEscape
