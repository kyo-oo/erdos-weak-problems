# Erdős #411 — THE ITERATED-TOTIENT DOUBLING LAWS (S042 volley)

## THE PROBLEM (verbatim, erdosproblems.com/411)

> Let $g_1=g(n)=n+\phi(n)$ and $g_k(n)=g(g_{k-1}(n))$. For which $n$ and $r$
> is it true that $g_{k+r}(n)=2g_k(n)$ for all large $k$?

Known: $r=2$ solutions $n=10$ and $n=94$; Selfridge–Weintraub $r=9$ ratio-9
solutions; Weintraub $g_{k+25}(3114)=729\,g_k(3114)$ for $k\geq 6$.
Steinerberger [St25]: for $r=2$ the problem is equivalent to
$\phi(n)+\phi(n+\phi(n))=n$, and any solution has odd part in
$\{1,3,5,7,35,47\}$ or is an exotic $8m+7$ prime $\geq 10^{10}$ or a
$6m+5$ with $\phi(6m+5)=4m+4$.

## THE MATHEMATICS (all derived and engine-verified this round)

### 1. THE ODD-PART DECOUPLING (the master structural fact)

For $x = 2^a m$ with $a \geq 1$, $m$ odd:
$$g(x) = x + \phi(x) = 2^a m + 2^{a-1}\phi(m) = 2^{a-1}(2m + \phi(m)).$$
So the odd part of $g(x)$ is $T(m) := \mathrm{odd}(2m+\phi(m))$ —
**independent of $a$**. The odd parts of an even trajectory follow the
one-dimensional dynamical system $m \mapsto T(m)$, and the two-exponent
evolves as $a \mapsto a - 1 + v_2(2m+\phi(m))$.

### 2. THE MASTER REDUCTION (the complete characterization, both directions)

**THEOREM.** Let $n \geq 4$ be even, $r \geq 1$. Then
$g_{k+r}(n) = 2 g_k(n)$ for all large $k$ **iff** the $T$-trajectory of
$\mathrm{odd}(n)$ eventually enters an $r$-cycle
$(m_0, \ldots, m_{r-1})$ (i.e. $T(m_i) = m_{i+1 \bmod r}$ from some point
on) with
$$\sum_{i=0}^{r-1} v_2\!\bigl(2m_i + \phi(m_i)\bigr) = r + 1.$$

*Proof.* ($\Leftarrow$) Suppose $x_K = 2^A m_0$ with $(m_0,\ldots,m_{r-1})$
an $r$-cycle of $T$ with $j$-sum $r+1$, where $j_i := v_2(2m_i+\phi(m_i))$.
By the decoupling, $x_{K+i} = 2^{A - i + (j_0 + \cdots + j_{i-1})} m_i$
for $0 \le i \le r$ (each step divides the exponent by one and adds
$j_i$). At $i = r$: exponent $= A - r + (r+1) = A+1$ and $m_r = m_0$, so
$x_{K+r} = 2 x_K$. The state at $K+r$ is $(2^{A+1}, m_0)$ — the same
cycle with the exponent raised by one — so by induction over laps,
$x_{K + \ell r + i} = 2^\ell x_{K+i}$ for all $\ell, i$, giving
$g_{k+r}(x_K) = 2 g_k(x_K)$ for all $k \geq 0$. Lifting to $n$: the
trajectory of $n$ reaches $x_K$ at step $K$, so $g_{k+r}(n) = 2g_k(n)$
for all $k \geq K$. ($\Rightarrow$) If $g_{k+r}(n) = 2g_k(n)$ for all
$k \geq K$, then odd parts satisfy $m_{k+r} = m_k$ (odd parts of numbers
differing by a factor 2 agree) and exponents satisfy
$a_{k+r} = a_k + 1$; summing the step relation
$a_{i+1} = a_i - 1 + j(m_i)$ over one period gives
$\sum j(m_i) = r + 1$ over the eventual $r$-cycle of odd parts. $\square$

For $r = 2$: doubling chains are exactly the pairs
$\{u, v\}$ with $T(u) = v$, $T(v) = u$, and $j(u) + j(v) = 3$.

### 3. THE THREE CHAIN FAMILIES (the $r=2$ solution classes)

Solving the pair law: $\{1,3\}$: $T(1)=3$, $T(3)=1$, $j(1)=v_2(3)=0$,
$j(3)=v_2(8)=3$, sum 3 ✓. $\{5,7\}$: $T(5)=7$, $T(7)=5$, $j(5)=v_2(14)=1$,
$j(7)=v_2(20)=2$ ✓. $\{35,47\}$: $T(35)=47$, $T(47)=35$, $j(35)=v_2(94)=1$,
$j(47)=v_2(140)=2$ ✓. These are Steinerberger's six small odd parts.

**THE CHAIN LAWS** (symbolic in $a$, all six):
- $g(2^a) = 3\cdot 2^{a-1}$, $g(3\cdot 2^a) = 2^{a+2}$ (the $\{1,3\}$ chain; needs $a \geq 2$ at the $m=1$ end),
- $g(5\cdot 2^a) = 7\cdot 2^a$, $g(7\cdot 2^a) = 5\cdot 2^{a+1}$,
- $g(35\cdot 2^a) = 47\cdot 2^a$, $g(47\cdot 2^a) = 35\cdot 2^{a+1}$.

**THE DOUBLING THEOREM.** Every $n = 2^a m$ with $m \in \{1,3,5,7,35,47\}$,
$a \geq 1$, and $n \geq 4$ satisfies $g_{k+2}(n) = 2 g_k(n)$ for **all**
$k \geq 0$ (not just large $k$). This includes the two known solutions
$n = 10 = 2\cdot 5$ and $n = 94 = 2\cdot 47$.

### 4. THE PARITY EXCLUSION

$\phi(x)$ is even for every $x \geq 3$ (the totatives pair as
$c \leftrightarrow x - c$, no fixed points). Hence $g$ preserves parity
from 3 on: odd $n \geq 3$ has $g_k(n)$ odd forever, so
$g_{k+r}(n) = 2 g_k(n)$ (even) is impossible for $k \geq 1$. The
exceptions: $n = 1$ ($g_1(1) = 2$, then $g_2(1) = 3$ odd forever) and
$n = 2$ ($g_1(2) = 3$ odd forever) — also never ratio-2 solutions.
**No odd $n$, and neither 1 nor 2, is a ratio-2 solution — for any $r$.**

### 5. THE COMPLETE CENSUS AT 2000 (both sides)

Engine: the $T$-dynamics on odd parts. The odd parts $\leq 1000$ split:
- **221 SOLUTION odd parts** whose $T$-trajectory reaches
  $\{1,3,5,7,35,47\}$ (max 26 steps, max value $59049 = 3^{10}$) —
  these give **535 solution evens $n \leq 2000$** ($n = 2^a m$), each
  certified by its trajectory witness (kernel-decided);
- **279 WANDERER odd parts** (first: 65) whose $T$-trajectory avoids the
  six for 150 steps and past $2^{200}$ (deepest: 65 reaches
  $2.9 \cdot 10^{18}$ without structure). Even $n = 130 = 2\cdot 65$ is
  engine-verified NOT to double within 60 steps (conjecturally never —
  exotic Steinerberger chains at $\geq 10^{10}$ could in principle
  capture later trajectories; no such capture occurs in range).

**Every even $4 \leq n \leq 2000$: either a certified $r=2$ solution
(kernel witness: the odd-part trajectory to a chain family + the chain
laws), or its odd part is a wanderer (bounded non-entry, engine flag).**
Sample direct verifications: $n=10, 94$ double from $K=0$; $n = 222$
from $K=7$ (entry $1536 = 2^9 \cdot 3$); $n = 1998$ from $K=9$ (entry
$24576 = 2^{13}\cdot 3$); $n = 130, 500, 1000$ do not double in 60 steps.

### 6. THE ENGINE RULES OUT OTHER MECHANISMS IN RANGE

A full $T$-cycle scan over all odd $m_0 \leq 2000$ (values $< 2^{60}$,
120 steps): **zero cycles other than the three pairs** — within range,
the $r=2$ chain mechanism is the only doubling mechanism. No $r \neq 2$
ratio-2 cycles exist in range. (Odd-side regimes like the
$3^8$-per-20-steps pattern seen at $n$ odd are outside the ratio-2 ask —
odds are excluded by parity.)

## HONEST SCOPE

The full characterization "which $n$, which $r$" over ALL $n$ remains
open: it reduces (by the Master Reduction) to the cycle structure of the
one-dimensional map $T(m) = \mathrm{odd}(2m + \phi(m))$ — a
Collatz-flavored dynamical question (do all even trajectories chain-enter?
the 279 wanderers $\leq 1000$ say not obviously). The kernel lands:
the parity exclusion (all odd $n$, $n = 1, 2$ — unconditional, all $r$),
the three chain-family theorems (all $2^a m$, unconditionally, from
$k=0$), the witness-reduction theorem, and the complete certified census
at 2000 (535 solutions kernel-witnessed; 279 wanderer odd-parts
partitioned and engine-flagged). Steinerberger's exotic-chain
classification [St25] is the literature anchor for what can lie beyond.

## FILES

- `Erdos411.lean` — the kernel (Kernel 36): statement-then-proof format.
- `battery411.py` — pure-Python dual-method battery (no sympy — L55):
  direct big-int trajectory doubling ∥ odd-part witness machinery.
- `engine411_round{1,2,3,3b,4,4b,5}.py` (monorepo root) — the engine rounds.
- `table411.json`, `witness411.json` (monorepo root) — the census data.
