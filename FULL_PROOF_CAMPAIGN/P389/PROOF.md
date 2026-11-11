# P389 — Erdős #389: Consecutive-Product Divisibility — FULL PROOF CAMPAIGN

**Agent:** W2-P389. **Status:** ATTACK IN PROGRESS (live document — updated every few minutes).

## §0. VERBATIM TARGET (corpus-erdos #389, extracted from corpus_statements_full.json)

> Is it true that for every $n\geq 1$ there is a $k$ such that
> \[n(n+1)\cdots(n+k-1)\mid (n+k)\cdots (n+2k-1)?\]

- Asked by **Erdős and Straus**. Examples in corpus: $n=2$, $k=5$: $2\cdot3\cdot4\cdot5\cdot6 \mid 7\cdot8\cdot9\cdot10\cdot11$ ($720 \mid 55440$); $n=3$, $k=4$: $3\cdot4\cdot5\cdot6 \mid 7\cdot8\cdot9\cdot10$ ($360 \mid 5040$).
- Minimal $k$ for $1\le n\le 18$ computed by Bhavik Mehta = OEIS **A375071**.
- Corpus status: **open** (unformalized). Tags: number theory.

**NAMED FRONT (THE_LIST §C rank 11):** the **k ≤ n/2 lane** — search/construct $k$ in the
range $k \le n/2$. Rounds budget 4–5.

## §1. CAMPAIGN CONTEXT

- Boost arsenal: `problem394-consecutive-crt/` (CRT soundness + unique-position +
  prime-landing laws; the t_k(n) engine) and `problem396-prod-binomial/`
  (∏(n−i) | C(2n,n), Kummer/carry machinery).
- Law: BOSS's repo maths only, no open cop-outs, numerics = evidence, no `lake build`.

## §2. REFORMULATIONS (derived this session)

Write $P_1 = n(n+1)\cdots(n+k-1) = \frac{(n+k-1)!}{(n-1)!}$ and
$P_2 = (n+k)\cdots(n+2k-1) = \frac{(n+2k-1)!}{(n+k-1)!}$.

**(R1) Binomial form.** $P_1 = k!\binom{n+k-1}{k}$ and $P_2 = k!\binom{n+2k-1}{k}$, hence
$$P_1 \mid P_2 \iff \binom{n+k-1}{k} \;\Big|\; \binom{n+2k-1}{k}.$$
(Verified: n=2,k=5: $\binom65=6 \mid \binom{12}5=792$. n=3,k=4: $\binom64=15 \mid \binom{10}4=210$.)

**(R2) Valuation form.** $P_1 \mid P_2 \iff \forall p:\; 2\,v_p((n+k-1)!) \le v_p((n-1)!) + v_p((n+2k-1)!)$.

**(R3) Count form.** With $N_q(W) = $ # multiples of $q$ in interval $W$ (length $k$):
$v_q$ of a block product $= \sum_{e\ge1} N_{p^e}(W)$. Sufficient (not necessary):
$N_q([n,n+k)) \le N_q([n+k,n+2k))$ for all prime powers $q$. **Shift law:** if $q \mid k$
then $N_q([n,n+k)) = N_q([n+k,n+2k))$ (translate by multiple of $q$).

**(R4) Kummer form.** $v_p\binom{m}{k}$ = # carries adding $k$ and $m-k$ in base $p$. So need:
for all $p$, carries$_p(k, n-1) \le$ carries$_p(k, n+k-1)$.

## §3. ATTACK LOG

- [in progress] See §4–§7 below as they land.

## §4. DATA / EXPERIMENTS

- Directory: `experiments/`. Table of minimal $k$ (cross-check vs A375071), structure of
  $P_2/P_1$, prime-by-prime deficit analysis. PENDING — computing.
