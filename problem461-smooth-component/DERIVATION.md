# ERDŐS–GRAHAM #461 — THE SMOOTH-COMPONENT DISTINCT-VALUE CENSUS (S040, round 1)

## THE PROBLEM (erdosproblems.com/461, ErGra80)

> Let $s_t(n)$ be the $t$-smooth component of $n$ — the product of all
> primes $p < t$ dividing $n$ (with multiplicity). Let $f(n,t)$ count
> the number of distinct possible values for $s_t(m)$ for
> $m\in[n+1,n+t]$. Is it true that $f(n,t)\gg t$ (uniformly, for all
> $t$ and $n$)?

Erdős–Graham report $f(n,t) \gg t/\log t$.

## THE ARSENAL TRANSFER

The #961 smooth-run machinery (Kernel 25 green: the {2,3}-census laws,
Størmer–Pell certification) computes smooth components wholesale; the
sliding-window distinct-counter is the #261 walk-engine pattern.

## THE CENSUS (round 1)

Engine: `engine461_round1.py` — per-$t$ sieve of $s_t$ over
$[1, 2\cdot10^5 + t]$, sliding-window distinct count, $\min_n f(n,t)$
and argmin for every $t \in [2, 120]$.

**THE ~0.57 STABILITY LAW (the round-1 discovery):**
$\min_n f(n,t)/t \in [0.55, 0.62]$ for EVERY $t \in [14, 120]$ —
rock-stable around $0.57$, no decay whatsoever. At $t = 120$:
$\min_n f = 69$ ($0.575 \cdot t$).

**THE ERGRA BEATING:** $f/(t/\log t)$ GROWS monotonically
$0.35 \to 2.75$ on $t \in [2,120]$ — the census says $f(n,t)$ is a
FULL $\gg t$ on this range, a factor $\sim \log t$ above the published
bound. Evidence: the conjecture is TRUE-shaped with constant
$\gtrsim 0.55$.

**THE MINIMIZER CLUSTER LAW:** the argmin $n$ concentrate on a stable
set $\{1281, 1541, 1771, 1892, 2420, 2930, \ldots\}$ — the same
minimizing neighborhoods serve many consecutive $t$. Structure
(round-2 target): these windows END near highly-divisible anchors
(e.g. $2420 + t \approx 2520 = \mathrm{lcm}(1..10)$) — the smooth
components collapse in windows aligned with the highly-composite
lattice.

## HONEST SCOPE

The census is $n \leq 2\cdot10^5$, $t \leq 120$. The $\gg t$ core is
the uniform-in-$n$ statement over ALL $n$ — the census is the evidence
base, not the proof. The kernel lane: the finite tables
(min-window certificates, the $t$-row minimums) + the sliding-window
lemma (the $f$-counter identity) — kernelizable in the K18 pattern.
Round budget: 3–5.
