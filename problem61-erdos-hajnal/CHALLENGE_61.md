# CHALLENGE FILE — Erdős #61 (the comparator target)

## Source A — erdosproblems.com/61 (verbatim)

> For any graph $H$ is there some $c=c(H)>0$ such that every graph $G$ on
> $n$ vertices that does not contain $H$ as an induced subgraph contains
> either a complete graph or independent set on $\geq n^c$ vertices?

Corpus context: conjectured by Erdős–Hajnal [ErHa89] (exp(c√log n)); BNSS23
improved to exp(c√(log n log log n)); PROVED for all H on ≤ 5 vertices
(ErHa89, ChSa08, CSSS23, NSS26, substitution closure APS01).

## Source B — Google DeepMind formal-conjectures (ErdosProblems/61.lean, verbatim)

```
def IsErdosHajnalLowerBound {α : Type*} [Fintype α] [DecidableEq α]
  (H : SimpleGraph α) (f : ℕ → ℝ) : Prop :=
  ∀ᶠ n in atTop, ∀ G : SimpleGraph (Fin n),
    (¬∃ g : α ↪ Fin n, H = G.comap g) → G.indepNum ≥ f n ∨ G.cliqueNum ≥ f n

@[category research open, question, AMS 5]
theorem erdos_61 :
    ∀ {α : Type*} [Fintype α] [DecidableEq α] (H : SimpleGraph α),
      ∃ c > (0 : ℝ), IsErdosHajnalLowerBound H (fun n : ℕ => (n : ℝ) ^ c)
```

## The comparator questions

Q1. The full conjecture (all H, polynomial) — OPEN (fortress).
Q2. For WHICH H families does the conjecture hold with complete elementary
    proofs and EXPLICIT constants? — the attackable front.
Q3. What are the finite shadows m(H, n) (min over H-free G of max(ω,α))? —
    census-decidable.
