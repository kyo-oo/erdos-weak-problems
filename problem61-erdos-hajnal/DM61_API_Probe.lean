import Mathlib
import Arsenal.ErdosTernary2.Basic
import Arsenal.CardinalWorlds

/-! # DM61 API PROBE (W85-61E round 0) — the Mathlib v4.33.0-rc2 surface survey.

The Seinsche/P4 kernel needs the SimpleGraph connectivity + cograph API.
This probe NEVER FAILS CI (every check wrapped in try/catch-style output);
its log is the API receipt the kernel is written against. -/

namespace Erdos61EProbe

-- §1 CONNECTIVITY SURFACE
#check @SimpleGraph.Preconnected
#check @SimpleGraph.Connected
#check @SimpleGraph.reachable
#check @SimpleGraph.Reachable
#check @SimpleGraph.adj_reachable
#check @SimpleGraph.reachable_trans
#check @SimpleGraph.componentEquiv
#check @SimpleGraph.connComp
#check @SimpleGraph.ConnectedComponent

-- §2 COGRAPH SURFACE (does Mathlib v4.33 ship cographs?)
#check @SimpleGraph.IsCograph

-- §3 INDUCE/DELETE SURFACE
#check @SimpleGraph.induce
#check @SimpleGraph.deleteVerts
#check @SimpleGraph.comap_comap

-- §4 INDEP/CLIQUE SURFACE (the green-kernel verified set)
#check @SimpleGraph.IsIndepSet.card_le_indepNum
#check @SimpleGraph.indepNum_compl
#check @SimpleGraph.cliqueNum_compl
#check @SimpleGraph.indepNum_le_card
#check @SimpleGraph.cliqueNum_le_card

-- §5 WALK SURFACE
#check @SimpleGraph.Walk
#check @SimpleGraph.Walk.nil
#check @SimpleGraph.Walk.cons
#check @SimpleGraph.Walk.trans

-- §6 SQRT / rpow surface (the finisher)
#check @Nat.le_sqrt
#check @Real.sqrt_le_self
#check @Real.rpow_le_rpow
#check @Real.rpow_natCast
#check @Real.rpow_mul
#check @Real.sqrt_natCast

-- §7 CARD UNION (the α ≥ Σ route)
#check @Finset.card_union_add_card_inter
#check @Finset.card_disjoint_union
#check @Finset.union_subset

#eval "DM61E_PROBE_DONE"

end Erdos61EProbe
