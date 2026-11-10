
---

## §4. ROUND 2 RECORD (S042, the nine-engine war: 2a–2i)

**The laws extracted (the round's mathematical yield):**
- **L-A (Kraft confinement):** the leaves' ν satisfy Σ 1/ν = 1 with ≤ |pool|
  leaves — the solution is a SMALL object (ν ≲ pool bound); the huge-ν
  descent (2b–2f, ν → 10⁴⁰⁰⁰ and 7·10¹⁷) is structurally useless.
- **L-B (residue freedom):** assignability depends only on ν (m | ν), never
  on the residue c — the search space is the ν-multiset, not (c, ν) pairs.
- **L-C (demand/supply):** a split by q demands q children but supplies only
  the fresh q-multiple divisors; at small ν supply ≪ demand — the frontier
  inevitably grows through the poor phase; recovery needs support-diverse ν.
- **L-D (Mirsky–Newman obstruction):** Σ 1/m = 1 exactly with distinct m is
  NOT tree-realizable (exact covers need repeated moduli) — dilution
  ν = m·k is the necessary freedom; the (F, k)-parametrization reduces the
  matching to nothing (each leaf takes its own m) but the Egyptian equality
  Σ 1/(m·k) = 1 hits a granularity wall (2i: residual ~0.06–0.10 never
  closes with ≤ 14 terms; the small-m density carriers are consumed).
- **L-E (the even/odd density split):** even pool density 1.446, odd 1.384
  (first-60) — both sides comfortable; density is NOT the blocker.

**Round-3 design (the greedy-cover + structured verifier):** abandon the
tree-shape search; construct the covering DIRECTLY in the classical
covering-system style — F = the small-m pool; x = 0, 1, 2, …; each first
uncovered x receives an unused m (class x mod m); the m-choice searched
(DFS with the unused-density prune); verification via the recursive
interval-lattice covering check (the Sierpiński-literature algorithm),
NOT the raw lcm sweep (lcm(F) ~ 10¹⁵⁺).

**Status:** construction lane OPEN, round 3 designed. The five-round clock
started at round 1 (the annealing); rounds 2a–2i = round 2.
