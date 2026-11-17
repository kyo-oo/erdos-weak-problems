# ERDŐS #261 — WEAKENED SUB-QUESTION [Er88c]: ANSWERED AFFIRMATIVELY

**Branch:** `bulldoze/erdos-weak-problems-3-20261101` (Kill #5)
**Files:** `TwoSolutions.lean` (core Lean 4.33.0-rc2 only, kernel-green,
**zero axioms** — `does not depend on any axioms` on all headline
theorems), `collision_census2.py` (the discovery engine),
`verify_frontiers.py` (frontier battery: family + kernel + collisions).

## 1. THE PROBLEM (verbatim context from erdosproblems.com/261)

The second question of Erdős #261 [Er74b, ErGr80, Er88c]:

> Is there a rational $x$ such that $x = \sum_k a_k/2^{a_k}$ has at
> least $2^{\aleph_0}$ solutions?

In [Er88c] **Erdős weakens this** to:

> the existence of a rational $x$ which has **two** solutions.

As of the page's last edit (2025-12-01) neither the continuum question
nor the weakened two-solution question is recorded as resolved.
This package kills the **weakened question**: **YES** — an explicit
rational with three (and more) distinct representations.

## 2. THE KILL

$$x = \frac12 : \qquad
\{2\}:\ \tfrac{2}{4}; \qquad
\{3,6,8\}:\ \tfrac{3}{8}+\tfrac{6}{64}+\tfrac{8}{256}; \qquad
\{4,5,6\}:\ \tfrac{4}{16}+\tfrac{5}{32}+\tfrac{6}{64}.
$$

All three sum to $\frac{128}{256} = \frac12$; each is a one-line hand
check; the piece sets are distinct, all pieces distinct positive
integers.

Plus the **sub-block collision** that generates further structure:

$$\{4,5\} \cong \{3,8\}:\qquad
\frac{4}{16}+\frac{5}{32} = \frac{104}{256} = \frac{3}{8}+\frac{8}{256}.$$

Any representation containing the block $\{4,5\}$ inside the window
admits a sibling with $\{3,8\}$ grafted in.

## 3. HOW IT WAS FOUND (the corrected pattern-collision census)

Kill #2's algebraic characterization, re-derived from first principles
(the printed form in the Kill #2 derivation carried a misprinted
normalization — caught by the BL sanity check $P = \{1..J\} \mapsto
n = 2^{J+1}-J-2$; the correct law below passes it):

A pattern $P \subseteq \{1..J\}$ (offsets, max offset $J$, pieces at
$n+j$) certifies $n$ iff

$$ n\,(2^J - A_P) = S_P, \qquad
A_P = \sum_{j \in P} 2^{J-j}, \quad S_P = \sum_{j \in P} j\,2^{J-j}, $$

which is exactly $\frac{n}{2^n} = \sum_{j\in P}\frac{n+j}{2^{n+j}}$
scaled by $2^{n+J}$. The map $P \mapsto n$ is a function (Kill #2's
"each pattern certifies at most one $n$") — but the **reverse map is
not injective once solutions are collected per VALUE** $x = n/2^n$:
$n=1$ and $n=2$ both carry $x = \frac12$, and each carries its own
pattern families.

Census to $J = 16$ (verified by exact `Fraction` reconstruction of
every certified solution):

| $x$ | distinct solutions found ($J \le 16$) |
|---|---|
| $1/2$ | $\{2\},\ \{3,6,8\},\ \{4,5,6\},\ \{4,5,7,8,11,13,14\},\ \ldots$ |

Growth of the solution count for $x = 1/2$ by depth: see
`verify_frontiers.py` output (the count grows with $J$: further
collisions keep appearing at deeper windows).

**Why this was missed.** Borwein–Loring gives, per $n$ in their family,
ONE representation ($\{2\}$ here, at $n=1$). TUZ20 verified all
$n \le 10^4$ have the greedy representation and enumerated solutions
with $\le 8$ pieces **per $n$** — but the weakened question lives
**per value $x$**, where $n = 1$ and $n = 2$ (and no other $n$:
$\frac{n}{2^n} = \frac12$ only for $n \in \{1, 2\}$) pool their
solutions. The collisions $\{3,6,8\}$ and $\{4,5,6\}$ sit inside that
pooled space.

## 4. FORMAL PACKAGE (core Lean only; no Mathlib; no sorry; no axioms)

Encoding: window $L = 8$; `sumScaled L S = Σ_{a∈S} a·2^{L−a}`;
representation of $x = \frac12$ at window 8
$\iff$ `sumScaled 8 S = 2^7 = 128` with `S.Nodup`, all pieces in
$[1,8]$ (exactness: $\sum_{a \in S} a/2^a = (\text{sumScaled}\,8\,S)/2^8$
term-by-term). All proofs closed by `decide` on numbers $\le 256$ —
no OOM surface.

- `rep_one_piece`, `rep_three_spread`, `rep_three_consecutive` — the
  three representations.
- `erdos261_weakened_two_solutions` — **the weakened question, killed.**
- `erdos261_three_solutions` — three pairwise-distinct solutions.
- `block_swap`, `block_swap_value` — the $\{4,5\}\cong\{3,8\}$ engine.
- Axiom gates: `'erdos261_weakened_two_solutions' does not depend on
  any axioms` (likewise the other two) — pure computation, no
  `propext`, no `Quot.sound`, no `Classical.choice`.

## 5. WHAT REMAINS OPEN (labeled exactly, not claimed)

- **The $2^{\aleph_0}$ question.** Finite solutions are countable in
  aggregate; continuum-many solutions require infinitely-many-piece
  (non-greedy, non-terminating) representations. The census growth
  (more solutions at every deeper window) shows the solution set of
  $x = \frac12$ is rich, but the continuum question needs the
  fork-tree of the walk (the take/skip choice window) to be shown to
  carry a perfect subtree — open.
- **The "all $n$" question** (Kill #2's open core): walk termination
  for every $n$.
- **A prior-art caveat, honestly logged:** the comment threads of
  erdosproblems.com/261 are SPA-loaded and could not be fetched from
  this sandbox (Cloudflare WAF). The page itself — meticulously
  maintained, edited 2025-12-01 — records the weakened question as
  unresolved. The construction above is trivially checkable; if any
  forum comment already contains it, this package's value reduces to
  the census machinery + the first full formalization (zero-axiom
  kernel certificate).

## 6. REFERENCES

- P. Erdős [Er74b], Erdős–Graham [ErGr80], Erdős [Er88c, p.104].
- Borwein–Loring [BoLo90] — the infinite family.
- Tengely–Ulas–Zygadło, arXiv:2008.01501 (TUZ20) — frontier $10^4$,
  per-$n$ solution enumeration.
- Kill #2 (this repo, `gpt6/erdos-one-shots-2-20261101` @ `4302b85`):
  the walk equivalence theorem + structure laws.
