# CHALLENGE FILE — Erdős #142 (the comparator target)

## Source A — erdosproblems.com/142 (verbatim)

> Let $r_k(N)$ be the largest possible size of a subset of $\{1,\ldots,N\}$
> that does not contain any non-trivial $k$-term arithmetic progression.
> Prove an asymptotic formula for $r_k(N)$.

Prize: $10,000. Erdős: "probably unattackable at present", "probably
enormously difficult". Best upper bounds: Kelley–Meka (k=3), Green–Tao
(k=4), Leng–Sah–Sawhney (k≥5). [Er80] asks for the ORDER OF MAGNITUDE and
notes: "we do not even know whether r_k(n)/r_{k+1}(n) → 0 for any k ≥ 3".

## Source B — Google DeepMind formal-conjectures (ErdosProblems/142.lean, verbatim statements)

```
noncomputable abbrev r := Set.IsAPOfLengthFree.maxCard

@[category research open, question value, AMS 11]
theorem erdos_142 (k : ℕ) : (fun N => (r k N : ℝ)) ~[atTop] erdos_142.answer

@[category research open, AMS 11]
theorem erdos_142.variants.lower (k : ℕ) (hk : 1 < k) :
    (fun N => (r k N : ℝ)) =o[atTop] (fun N : ℕ => N / (N : ℝ).log)

@[category research open, question value, AMS 11]
theorem erdos_142.variants.isTheta (k : ℕ) :
    (fun N => (r k N : ℝ)) =Θ[atTop] erdos_142.variants.isTheta.answer

@[category research open, question value, AMS 11]
theorem erdos_142.variants.three :
    (fun N => (r 3 N : ℝ)) ~[atTop] erdos_142.variants.three.answer
```

## The comparator questions (what a solution must answer)

Q1. The asymptotic formula (main) — OPEN (fortress).
Q2. r_k(N) = o_k(N/log N) — OPEN (fortress; Erdős's $5000 side-prize).
Q3. The order of magnitude — OPEN.
Q4. r_3(N) asymptotic — OPEN.
Q5. THE FINITE EXACT FRONTIER: what are the exact values r_k(N), with
    certificates, and what do they say about Erdős's ratio question? —
    DECIDABLE, attacked by this campaign.
