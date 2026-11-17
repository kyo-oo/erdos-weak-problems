import GSTGraphV2CanonicalPhaseSteering

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace GSTGraphV2CanonicalSheetTranslation

open GSTCanonicalSevenAxisBridge
open GSTGraphV2InfiniteControl
open GSTGraphV2PerfectPowerBlock
open GSTGraphV2CanonicalRenormalization
open GSTGraphV2CanonicalPhaseSteering
open GSTV2
open GSTU2DEventTransport

/-- Multiplying the sheet energy by an x4 power is literally a horizontal
translation of every physical Graph-V2 observable.  The coordinate labels
`horizontal` and `horizontalNext` themselves translate, so we state the
physical fields rather than falsely identifying the whole seven-axis record. -/
theorem graph_energy_shift_physical
    (E k t p : Nat) :
    (graph (4^k * E) t p).seven.carry =
        (graph E (k+t) p).seven.carry ∧
      (graph (4^k * E) t p).seven.space =
        (graph E (k+t) p).seven.space ∧
      (graph (4^k * E) t p).seven.digit =
        (graph E (k+t) p).seven.digit ∧
      (graph (4^k * E) t p).seven.descent =
        (graph E (k+t) p).seven.descent ∧
      (graph (4^k * E) t p).seven.nextDescent =
        (graph E (k+t) p).seven.nextDescent := by
  have henergy : 4^t * (4^k * E) = 4^(k+t) * E := by
    rw [pow_add]
    ring
  simp only [graph, cell, GSTCanonicalSevenAxisBridge.vertex]
  rw [henergy]
  simp

/-- Consequently Happy/event-eight is invariant under the same literal sheet
translation. -/
theorem graph_energy_shift_happy_iff
    (E k t p : Nat) :
    HappyCell
        (graph (4^k * E) t p).seven.carry
        (graph (4^k * E) t p).seven.digit ↔
      HappyCell
        (graph E (k+t) p).seven.carry
        (graph E (k+t) p).seven.digit := by
  have h := graph_energy_shift_physical E k t p
  rw [h.1, h.2.2.1]

/-- Stripping one ternary origin digit is an exact horizontal translation of
canonical perfect-power energy into the next scale. -/
theorem canonicalEnergy_three_adic_translate
    (s a m : Nat) :
    canonicalEnergy s (a + 3*m) =
      4^(a * 3^(s+1)) * canonicalEnergy (s+1) m := by
  unfold canonicalEnergy
  have hexp :
      3^(s+1) * (a + 3*m) =
        a * 3^(s+1) + 3^((s+1)+1) * m := by
    rw [Nat.pow_succ]
    ring
  rw [hexp, pow_add]

/-- Full physical Graph-V2 translation law for the canonical three-adic
renormalization.  This is the ontological form of the one-trit recurrence. -/
theorem canonical_graph_three_adic_physical
    (s a m t p : Nat) :
    (graph (canonicalEnergy s (a+3*m)) t p).seven.carry =
        (graph (canonicalEnergy (s+1) m) (a*3^(s+1)+t) p).seven.carry ∧
      (graph (canonicalEnergy s (a+3*m)) t p).seven.space =
        (graph (canonicalEnergy (s+1) m) (a*3^(s+1)+t) p).seven.space ∧
      (graph (canonicalEnergy s (a+3*m)) t p).seven.digit =
        (graph (canonicalEnergy (s+1) m) (a*3^(s+1)+t) p).seven.digit ∧
      (graph (canonicalEnergy s (a+3*m)) t p).seven.descent =
        (graph (canonicalEnergy (s+1) m) (a*3^(s+1)+t) p).seven.descent ∧
      (graph (canonicalEnergy s (a+3*m)) t p).seven.nextDescent =
        (graph (canonicalEnergy (s+1) m) (a*3^(s+1)+t) p).seven.nextDescent := by
  rw [canonicalEnergy_three_adic_translate]
  exact graph_energy_shift_physical _ _ _ _

/-- Happy waves themselves transport exactly under canonical one-trit
renormalization. -/
theorem canonical_graph_three_adic_happy_iff
    (s a m t p : Nat) :
    HappyCell
        (graph (canonicalEnergy s (a+3*m)) t p).seven.carry
        (graph (canonicalEnergy s (a+3*m)) t p).seven.digit ↔
      HappyCell
        (graph (canonicalEnergy (s+1) m) (a*3^(s+1)+t) p).seven.carry
        (graph (canonicalEnergy (s+1) m) (a*3^(s+1)+t) p).seven.digit := by
  rw [canonicalEnergy_three_adic_translate]
  exact graph_energy_shift_happy_iff _ _ _ _

/-- The same translation transports an all-depth bad boundary without any
support cutoff. -/
theorem canonical_graph_three_adic_bad_trace_iff
    (s a m t b : Nat) :
    (∀ j, ¬ HappyCell
        (graph (canonicalEnergy s (a+3*m)) t (b+j)).seven.carry
        (graph (canonicalEnergy s (a+3*m)) t (b+j)).seven.digit) ↔
      (∀ j, ¬ HappyCell
        (graph (canonicalEnergy (s+1) m) (a*3^(s+1)+t) (b+j)).seven.carry
        (graph (canonicalEnergy (s+1) m) (a*3^(s+1)+t) (b+j)).seven.digit) := by
  constructor <;> intro h j hHappy
  · exact h j ((canonical_graph_three_adic_happy_iff s a m t (b+j)).mpr hHappy)
  · exact h j ((canonical_graph_three_adic_happy_iff s a m t (b+j)).mp hHappy)

#check canonicalEnergy_three_adic_translate
#check canonical_graph_three_adic_physical
#check canonical_graph_three_adic_happy_iff
#check canonical_graph_three_adic_bad_trace_iff
#print axioms canonical_graph_three_adic_happy_iff

end GSTGraphV2CanonicalSheetTranslation
