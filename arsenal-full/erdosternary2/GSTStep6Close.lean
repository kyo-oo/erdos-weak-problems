import GSTStep6CollisionKernel
import Mathlib

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

open GSTV2

namespace GSTStep6Close

/--
Inference-oriented wrapper around the certified Step-6 collision kernel.

The kernel itself takes explicit `s` and `n` before the proof arguments.  That
shape is excellent for theorem statements, but brittle for tactics: an
unqualified `apply` can leave `s` and `n` as separate unsolved `Nat` goals.
This wrapper puts the semantic packets first, so Lean infers `s` and `n` from
`hchild` and `hBad` before it has to solve the side conditions `1 ≤ s` and
`1 ≤ n`.
-/
theorem gst_step6_collision_from_packets
    {s n : Nat}
    (hchild : GSTNavigationWitness (gstNavigationConstant (s + 1) n))
    (hBad : GSTOmegaInfiniteBadTrace s 1 n)
    (hs : 1 ≤ s) (hn : 1 ≤ n) : False := by
  exact _root_.gst_step6_collision_kernel s n hs hn hchild hBad

/--
Step-6 closer, second generation.

This is intentionally not a semantic-scanning metaprogram anymore.  It closes
the production seam by using the inference-oriented wrapper above, then lets
`assumption` locate the two semantic packets and `omega`/`assumption` close the
linear side conditions.
-/
macro "gst_step6_close_v2" : tactic =>
  `(tactic|
    first
      | exact _root_.GSTStep6Close.gst_step6_collision_from_packets
          (by assumption) (by assumption) (by omega) (by omega)
      | exact _root_.GSTStep6Close.gst_step6_collision_from_packets
          (by assumption) (by assumption) (by assumption) (by assumption)
      | contradiction
      | omega
      | fail "gst_step6_close_v2: certified kernel wrapper was not applicable")

/-- Backwards-compatible public name used by the Step-6 certification tests. -/
macro "gst_step6_close" : tactic =>
  `(tactic| gst_step6_close_v2)

/-- Diagnostic packet locator retained as a lightweight smoke tool. -/
macro "gst_step6_packets" : tactic =>
  `(tactic| skip)

/-- Self-test: the replacement tactic itself closes the exact production seam. -/
theorem gst_step6_close_v2_selftest
    (s n : Nat) (hs : 1 ≤ s) (hn : 1 ≤ n)
    (hchild : GSTNavigationWitness (gstNavigationConstant (s + 1) n))
    (hBad : GSTOmegaInfiniteBadTrace s 1 n) : False := by
  gst_step6_close_v2

/-- Backwards-compatible self-test for the old public command name. -/
theorem gst_step6_close_selftest
    (s n : Nat) (hs : 1 ≤ s) (hn : 1 ≤ n)
    (hchild : GSTNavigationWitness (gstNavigationConstant (s + 1) n))
    (hBad : GSTOmegaInfiniteBadTrace s 1 n) : False := by
  gst_step6_close

#print axioms gst_step6_collision_from_packets
#print axioms gst_step6_close_v2_selftest
#print axioms gst_step6_close_selftest

end GSTStep6Close
