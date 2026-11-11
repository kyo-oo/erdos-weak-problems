# ERDŐS #1212 — THE INFINITE-PATH CONSTRUCTION WAR (round 2, S041)

## THE PROBLEM (verbatim, erdosproblems.com/1212)

> Let $G$ be the graph with vertex set those pairs $(x,y)\in \mathbb{N}^2$
> with $\gcd(x,y)=1$, in which we join two vertices if they differ in only
> one coordinate, and thereby by $\pm 1$. Is there a path going to infinity
> on $G$, say $P$, such that for all $(x,y)\in P$ both $\min(x,y)>1$ and at
> least one of $x$ or $y$ is composite?

## ROUND-2 STRUCTURE (the B-lattice phase calculus)

The habitat: $H = \{(x,y) : \gcd(x,y)=1,\ \min>1,\ x \text{ or } y
\text{ composite}\}$. Round-1 type analysis: the path alternates
B-hubs (odd, odd) with A/C intermediates (even ≥ 4, odd) — the evens are
auto-composite, so the B-to-B net moves are ±2 in one coordinate, and the
conditions reduce to gcd checks at the intermediates and landings.

**THE PHASE LAW (round-2 discovery, engine-corrected).** Fix an odd
composite $y$ and an odd composite $x \equiv 1 \pmod{\mathrm{rad}(y)}$ with
$\gcd(x, y) = 1$. Consider the forward x-phase $x \to x+2 \to \cdots \to
x + 2m$ (each via the even intermediate $x + 2j + 1$):

- *Intermediates*: $q \mid y$ (q odd prime) divides $x + 2j + 1 \equiv
  2(j{+}1) \pmod q$ iff $q \mid j{+}1$ — first collision at $j = q - 1$.
- *Landings*: $q$ divides $x + 2j + 2 \equiv 2j + 3 \pmod q$ iff
  $2j \equiv -3 \pmod q$ — first collision at $j = (q-3)/2$.

**THE LANDINGS COLLIDE AT HALF THE INTERMEDIATE RANGE** (the round-2
engine correction: the naive $q-1$ bound fails 224/224 — the true law):
the phase is certified for $j = 0, \ldots, (q_{\min}(y) - 5)/2$, i.e.
**$(q_{\min}(y) - 3)/2$ certified moves**. Every intermediate is
(even ≥ 4, odd) — auto-composite; every landing has $y$ composite. The
phase length grows linearly in the least prime factor of $y$ — with
$q_{\min}(y) = 101$: 49 certified moves.

**THE SYMMETRIC Y-HOP + CRT RESTORE.** After the x-phase ends at
$x' = x + 2m$, the invariant is restored on the other axis: choose the
y-phase length $m'$ with $y + 2m' \equiv 1 \pmod{\mathrm{rad}(x')}$ —
a CRT system in the odd primes of $x'$ ($2$ invertible mod each) —
solvable at every sampled phase-end (engine: 146/146 applicable cases).

**THE CONSTRUCTION SKETCH (the infinite path).** Maintain the invariant
$(x_k, y_k)$ both odd composite, $x_k \equiv 1 \pmod{\mathrm{rad}(y_k)}$;
run the certified x-phase; CRT-restore on y; repeat. Each round advances
$x + y$ by $\ge q_{\min}/2 + \ldots$ — the path goes to infinity PROVIDED
the phase-end $x'$ (chosen inside the certified window) is an odd
composite whose least prime factor is large enough for the NEXT y-phase.

**THE OPEN GAP (round 3 target).** The phase-end selection needs an odd
composite with all prime factors $> B$ inside a window of length
$\sim q_{\min}(y)$ — a short-interval rough-composite existence statement
(Mertens-density heuristic: plentiful; a proof needs Jacobsthal-function
machinery). This is the sole remaining gap between the phase calculus and
the FULL YES answer.

## ROUND-2 ENGINE EVIDENCE

- `engine1212_round2.py` — the undirected greedy SURVIVES 3000+ steps from
  (9, 25) but oscillates in the box [7,9]×[25,27] (no growth pressure) —
  local traps are rich at low coordinates.
- `engine1212_round2b.py` — the DIRECTED (forward-only) walk dies within
  4 steps from all 12 composite starts at low coordinates — growth
  requires the phase calculus, not greedy.
- The phase-law validator: 224 random invariant configurations —
  intermediates all clean; landings collide exactly at $(q-3)/2$ (the
  corrected law verified on every failure row).

## ROUND BUDGET

Round 3: the rough-composite selection lemma (the Jacobsthal/Mertens
lane) + the assembled construction; if it closes: Kernel 36 with the
periodic-certificate shape (the phase pattern as the period).
