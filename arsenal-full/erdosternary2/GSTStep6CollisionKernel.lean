import ErdosTernary2

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

open GSTV2

/--
Theorem-backed Step-6 collision kernel for the exact production seam.

A child Navigation witness plus complete prefix-one Omega badness is impossible:
the public prefix-one lift builds the parent Navigation witness, while the
atomic Omega-bad theorem forbids every parent Navigation witness.
-/
theorem gst_step6_collision_kernel
    (hGate : gst_four_power_third_wave_gate)
    (s n : Nat) (hs : 1 ≤ s) (hn : 1 ≤ n)
    (hchild : GSTNavigationWitness (gstNavigationConstant (s+1) n))
    (hBad : GSTOmegaInfiniteBadTrace s 1 n) : False := by
  have hparent : GSTNavigationWitness (gstNavigationConstant s (1 + 3*n)) :=
    gst_prefix_one_navigation_lift hGate s n hs hn hchild
  exact (gst_prefix_one_no_parent_navigation_of_omega_bad_atomic
    s n hs hn hBad) hparent

/-- Audit-compatible name for the information-bad descent seam. -/
theorem gst_prefix_one_information_bad_descends_inline
    (hGate : gst_four_power_third_wave_gate)
    (s n : Nat) (hs : 1 ≤ s) (hn : 1 ≤ n)
    (hchild : GSTNavigationWitness (gstNavigationConstant (s+1) n))
    (hBad : GSTOmegaInfiniteBadTrace s 1 n) : False := by
  exact gst_step6_collision_kernel hGate s n hs hn hchild hBad

/-- Audit-compatible name for the child-gate versus parent-bad contradiction. -/
theorem gst_prefix_one_child_gate_contradicts_parent_bad_inline
    (hGate : gst_four_power_third_wave_gate)
    (s n : Nat) (hs : 1 ≤ s) (hn : 1 ≤ n)
    (hchild : GSTNavigationWitness (gstNavigationConstant (s+1) n))
    (hBad : GSTOmegaInfiniteBadTrace s 1 n) : False := by
  exact gst_step6_collision_kernel hGate s n hs hn hchild hBad

#print axioms gst_step6_collision_kernel
#print axioms gst_prefix_one_information_bad_descends_inline
#print axioms gst_prefix_one_child_gate_contradicts_parent_bad_inline
