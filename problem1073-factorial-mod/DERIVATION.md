# ERDŐS #1073 — THE FACTORIAL-MOD COMPOSITE CENSUS (S040 volley, round 1)

## THE PROBLEM (verbatim, erdosproblems.com/1073 — Hardy–Subbarao [HaSu02])

> Let $A(x)$ count the number of composite $u<x$ such that
> $n!+1\equiv 0 \pmod{u}$ for some $n$. Is it true that $A(x)\leq x^{o(1)}$?

The sequence of such $u$ begins $25, 121, 169, 437, \ldots$ (OEIS A256519).

## THE ARSENAL TRANSFER

This is the #1072 (Wilson-pair law, Kernel 22) + #1108 (vp-engine,
Brocard channel, Kernels 13/15/30) + #404 (factorial-sum machinery)
confluence: the factorial-prefix residues mod $u$ are exactly the object
of all three green fronts, and the master condition $u \mid n!+1$ is the
multiplicative twin of the #1108 subset-sum condition.

## THE STRUCTURE LAWS (round 1, engine-proven; L1/L2 kernel-ready)

**L1 — THE GCD LAW.** If $u \mid n!+1$ then $\gcd(u, n!) = 1$, so every
prime $p \mid u$ satisfies $p > n$; i.e. $n < P(u)$, the least prime
factor of $u$. *(Proof: $d = \gcd(u,n!) \mid u$ and $d \mid n!$ would
give $d \mid (n!+1) - n! = 1$.)* The scan window per $u$ is $[1, P(u))$.

**L2 — THE SATURATION LAW.** For $n \geq P(u)$, $P(u) \mid n!$, so
$P(u) \nmid n!+1$, so $u \nmid n!+1$ — the window never re-opens.
(Census confirms: no L1 violation in $10^6$.)

**L3 — THE MASTER LAW.** $u$ is a hit with witness $n$ iff $u \mid n!+1$
with $n < P(u)$. Engine: **131 composite $u < 10^6$**, prefix exactly
A256519 ($25, 121, 169, 437, \ldots$). Verified: all 131 witnesses
satisfy $u \mid n!+1$ by direct big-int division (dual method).

**L4 — THE WILSON-PRIME CHANNEL.** If $p$ is a Wilson prime
($p^2 \mid (p-1)!+1$) then $u = p^2$ is a hit with witness $n = p-1$
(L1 window: $p-1 < p$ ✓). Census: **all three known Wilson primes
appear**: $5^2 = 25$ ($n{=}4$), $13^2 = 169$ ($n{=}12$),
$563^2 = 316969$ ($n{=}562$). The reverse lift also appears:
$47^2 \mid 23!+1$ and $613^2 \mid 229!+1$ with $n < p-1$
(Wilson-quotient lifts, NOT Wilson primes).

**L5 — THE BROCARD CHANNEL.** $n!+1 = m^2$ (Brocard/Brown numbers:
$n = 4, 5, 7$ known) gives hits $u = m^2$: $25 = 4!{+}1$, $121 =
5!{+}1$, $5041 = 7!{+}1$. The #1108 K17/K19 Brocard census (exactly
$\{4,5,7\}$ to depth 22) transfers verbatim.

**L6 — THE CLUSTER LAW (the semiprime layer).** The hits concentrate on
the RICH $n$: $18!+1 = 19 \cdot 23 \cdot 29 \cdot 61 \cdot 67 \cdot
123610951$ — six prime factors $> 18$ — so every product of two of
$\{19,23,29,61,67\}$ is a hit with witness $n=18$ ($437, 551, 667,
1159, 1273, 1403, 1541, 1769, 1943, \ldots$ — **22 hits at $n=18$
alone**). Similarly $16!+1$ (9 hits), $36!+1$ (5), $40!+1 = 41 \cdot 59
\cdot 277 \cdot \ldots$ (4), $23!+1 = 47^2 \cdot 79 \cdot \ldots$ (3).
The hit count decomposes as $A(x) = \sum_{\text{rich } n}
(\text{divisor-pairs of } n!{+}1 \text{ below } x)$ — the $x^{o(1)}$
question is exactly: are the rich $n$ sparse enough?

**L7 — THE WITNESS-UNIQUENESS LAW (empirical, the conjecture layer).**
Every hit $u < 10^6$ has EXACTLY ONE witness $n \in [1, P(u))$ — zero
multi-witness $u$ in the full rescan. *Why non-trivial:* two witnesses
$n_1 < n_2$ would give $(n_1{+}1)\cdots n_2 \equiv 1 \pmod{u}$ — no
obvious obstruction. Conjecture: the witness is unique. Honest scope:
census-verified to $10^6$, NOT proved.

## THE GROWTH TABLE (the $x^{o(1)}$ evidence)

| $x$ | $A(x)$ | $\alpha = \log A/\log x$ |
|---|---|---|
| $10^3$ | 7 | 0.282 |
| $10^4$ | 28 | 0.362 |
| $10^5$ | 60 | 0.356 |
| $3\cdot10^5$ | 84 | 0.351 |
| $10^6$ | 131 | 0.353 |

The exponent is flat $\approx 0.35$ on this range — driven by the rich-$n$
clusters; each cluster's contribution eventually saturates, so
$A(x) = x^{o(1)}$ requires the rich $n$ to have $n!+1$-divisor-pairs
growing sub-polynomially. The census is the evidence base; the
asymptotic core remains open (honest scope).

## THE KERNEL LANE (next round)

- The 131-row census table with witnesses (mod-cascade decides, the
  K18/#1056 pattern: each row = one kernel decide over the window
  $[1, P(u))$).
- L1 + L2 as general theorems (trivial proofs, core-only).
- The Wilson channel: $p$ Wilson prime $\Rightarrow p^2$ hit (kernel:
  the three instances; the general theorem needs only the definition).
- The Brocard instances $4!{+}1 = 25, 5!{+}1 = 121, 7!{+}1 = 5041$
  (K17's channel, re-usable).

## FILES

- `engine1073_round1.py` — the 2·10^5 census + shapes + L1 check.
- `engine1073_round2.py` — the 10^6 census + Wilson layer + master-law
  exhibit + witness histogram + multi-witness hunt.
- `battery1073.py` — the dual-method battery.
- `census1073_1e6.txt` — the full 131-row table.
