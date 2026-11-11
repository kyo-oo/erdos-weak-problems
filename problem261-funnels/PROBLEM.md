# ERDŐS #261 — SUB-QUESTIONS 2 & 3: THE FUNNEL / COALESCENCE STRUCTURE

## THE UNSOLVED PROBLEM (verbatim, erdosproblems.com/261)

> Are there infinitely many $n$ such that there exists some $t \geq 2$ and
> distinct integers $a_1, \ldots, a_t \geq 1$ such that
> $\frac{n}{2^n} = \sum_{k=1}^{t} \frac{a_k}{2^{a_k}}$?
> Is this true for all $n$? Is there a rational $x$ such that
> $x = \sum_{k=1}^{\infty} \frac{a_k}{2^{a_k}}$ has at least $2^{\aleph_0}$
> solutions?

Status: OPEN (sub-Q2: all $n$; sub-Q3: rational $x$ with $2^{\aleph_0}$).

## THE WALK (Kill #2, kernel-green)

Sub-Q2 for a fixed $n$ ⟺ termination of the walk
$v_{N+1} = (2 v_N) \bmod N$ (take iff $2v \geq N$), started at $(N, v) =
(n+1, n)$ (special start $(3,2)$ for $n = 1$).  The ABSOLUTE state space
$\{(N, v) : 0 \leq v\}$ carries one deterministic map
$\varphi(N, v) = (N+1, (2v) \bmod N)$; every walk is an orbit.

## WHAT THIS PACKAGE DELIVERS (the funnel discovery, kernel-green)

1. **THE FUNNEL/C OALESCENCE STRUCTURE** (the discovery): orbits of the walk
   COALESCE — they merge into shared states and die together.  Census
   (exact arithmetic, `funnels.py`, $n \leq 4000$):
   - ALL 4000 walks terminate.
   - The death-modulus distribution has GIANT basins:
     $N = 12231$ absorbs **2578 of 4000 walks (64%)**;
     $N = 4855$: 475; $N = 4993$: 103; $N = 2593$: 101; $N = 4489$: 99;
     $N = 393$: 90; $N = 29753$: 47 (the deep funnel containing
     $n \in [3113, 3329]$) — 25 distinct funnel heads visible.
   - `death_fuel_mono` (Lean, kernel-green): the death modulus is a
     function of the state alone — two orbits meeting at a state share
     their future.  The funnel heads are the shared states.

2. **THE GREEDY-ROOM CENSUS (a negative structural theorem)**: the greedy
   room (last piece $- n$) is UNBOUNDED — max $152125$ at $n = 3817$
   within $n \leq 4000$ (mean $7647$, median $9407$).  The naive
   uniform-room hypothesis behind the Q3 bridge FAILS for the greedy walk:
   the bridge (kernel-green, problem261-q3bridge) needs either non-greedy
   representations with bounded room, or a funnel-based construction.

3. **THE TERMINATION ATTACK ROUTE (mapped)**: every orbit tested terminates
   and the state space is a coalescence tree with enumerable funnel heads.
   The proof program: enumerate the absorbing heads, show every start
   orbit $(n+1, n)$ enters one.  (The coalescence is empirically massive:
   the 12231-funnel alone eats 64% of starts in $[1, 4000]$.)

## OPEN FRONTS (honest labels)

- Sub-Q2 (all $n$): termination verified to $3 \cdot 10^6$ (64-bit C
  engine) + the funnel structure here; the all-$n$ proof remains open.
- Sub-Q3 (rational $x$): the greedy room is unbounded (this package), so
  the bridge fires only via non-greedy bounded-room representations or a
  funnel-based toggle family — both live fronts.

## Files
- `FunnelStructure.lean` — the Lean kernel (core-only, zero sorry):
  the walk, `death_fuel_mono` (coalescence certificate), funnel receipts.
- `DERIVATION.tex` — the complete derivation.
- `funnels.py` — the census battery (exact arithmetic).
