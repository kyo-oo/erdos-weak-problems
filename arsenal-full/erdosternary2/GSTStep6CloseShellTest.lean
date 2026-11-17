import GSTStep6Close

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-- Mock only the *type heads* used by the metaprogramming shell.  No GST
mathematics lives here; the semantic regression is kept separate. -/
def GSTNavigationWitness (_ : Nat) : Prop := True

def GSTOmegaInfiniteBadTrace (_ _ _ : Nat) : Prop := True

example (R s n : Nat)
    (hNav : GSTNavigationWitness R)
    (hBad : GSTOmegaInfiniteBadTrace s 1 n)
    (hFalse : False) : False := by
  gst_step6_packets
  gst_step6_close
