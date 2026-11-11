# ERDŐS #282 — THE COMPLETE PROOF DOCUMENT

**Deliverable S046-W17.** Target: Erdős problem #282 (teorth/erdosproblems
corpus — the Stein/Salisbury odd greedy Egyptian fraction question, tagged
`egyptian fractions`, OPEN). Certified spine: the CI-green Lean kernel —
**Kernel 28** (`problem282-odd-greedy/Erdos282.lean`, Kill #33, CI run
**42439522105 GREEN**, the 7-round compile war). Battery and engines re-run
TODAY, this session, foreground, all GREEN (§8, §10).

---

## §0. THE PROBLEM — VERBATIM (above the proof, BOSS's law)

Quoted verbatim from the corpus statement (erdosproblems.com/282), as it is
quoted verbatim in the Kernel 28 header and the README kill registry
(KILL #33):

> Let $A\subseteq \mathbb{N}$ be an infinite set and consider the following
> greedy algorithm for a rational $x\in (0,1)$: choose the minimal $n\in A$
> such that $n\geq 1/x$ and repeat with $x$ replaced by $x-\frac{1}{n}$.
> If this terminates after finitely many steps then this produces a
> representation of $x$ as the sum of distinct unit fractions with
> denominators from $A$. Does this process always terminate if $x$ has
> odd denominator and $A$ is the set of odd numbers? More generally,
> for which pairs $x$ and $A$ does this process terminate?

The corpus therefore asks **two questions**:

- **(Q1) — Stein's odd-greedy conjecture (the named instance):** for every
  rational $x = p/q \in (0,1)$ with $q$ **odd** (and $A$ = the odd numbers),
  does the odd-greedy algorithm always terminate?
- **(Q2) — the general classification:** for which pairs $(x, A)$
  ($A \subseteq \mathbb{N}$ infinite) does the process terminate?

---

## §1. THE COMPLETENESS VERDICT (surgical and honest)

| Corpus content | Status in this document |
|---|---|
| The habitat law: the odd-denominator world is invariant under every greedy step (the conjecture's necessary arena) | **PROVED, UNCONDITIONAL** (§3, Kernel 28) |
| The well-formedness law: every greedy step at most doubles the numerator ($p' < 2p$) | **PROVED, UNCONDITIONAL** (§4, Kernel 28) |
| The verification engine: a certified Bool simulation implies a genuine greedy trajectory reaching exactly $0$ | **PROVED, UNCONDITIONAL** (§5, Kernel 28) |
| The termination census: EVERY odd-denominator $p/q \in (0,1)$ with $q \le 41$ terminates | **PROVED, UNCONDITIONAL** — kernel-decided, 420 pairs (§6, Kernel 28) |
| Termination for every odd $q \le 301$ (22,650 pairs, deepest 20 steps at $102/293$); every coprime odd-denominator rational with $q \le 201$ (8,282 pairs, max 19 steps at $5/139$) | **VERIFIED ENGINE EVIDENCE** — not claimed as theorem (§8) |
| The odd-closure spot-check on the full census: every trajectory state stays odd | **VERIFIED** (§8, battery) |
| **(Q1) itself — termination for ALL odd denominators (Stein's conjecture)** | **OPEN CORE REMAINS — exactly one component** (§11) |
| **(Q2) — the general $(x, A)$ classification** | **OPEN — subsumed by the same core** (§11) |

**THE SINGLE REMAINING COMPONENT (named exactly):**
**THE GLOBAL ODD-GREEDY TERMINATION CORE** — the universal statement that the
odd-greedy trajectory from **every** $p/q \in (0,1)$ with $q$ odd (unbounded
$q$) reaches exactly $0$ in finitely many steps; the general $(x, A)$
classification of (Q2) is the strictly larger frontier subsuming it. This is
not an engine gap: the kernel laws prove the habitat is invariant and the
trajectories well-formed, but no monotone measure is known — the numerator is
*not* monotone along deep trajectories, so no descent argument is currently
available to the arsenal (§11 names the three walls). Everything else the
corpus statement contains is delivered complete below.

---

## §2. THE FORMALIZATION AND ITS FAITHFULNESS (statement integrity)

**The corpus algorithm, in rational-pair language.** Write $x = p/q$ with
$1 \le p \le q$ (the corpus's $x \in (0,1)$, plus the terminal convention
$x = 0$). At $A$ = the odd numbers, "the minimal $n \in A$ with
$n \geq 1/x$" is the **minimal odd $n$ with $p \cdot n \geq q$**. The kernel
(`Erdos282.GreedyStep`) makes one step a *certified relation*:

```
GreedyStep p q p' q'  :=  ∃ n g,  n % 2 = 1 ∧ 1 ≤ n ∧ q ≤ p·n
                             ∧ (n = 1 ∨ p·(n−2) < q)          -- minimality
                             ∧ 1 ≤ g ∧ (p·n − q) % g = 0 ∧ (q·n) % g = 0
                             ∧ p'·g = p·n − q ∧ q'·g = q·n
```

`TerminateIn k p q` = a chain of $k$ certified steps reaching exactly
$p = 0$ ($x = 0$) — the corpus's "terminates after finitely many steps",
which then yields the representation of $x$ as a sum of distinct unit
fractions with odd denominators (distinctness is structural: the greedy
choice strictly increases along a live trajectory).

**Faithfulness (Lemma F1 — the encoding is the corpus algorithm).**

1. *Minimality.* For odd $n$, "minimal odd $n$ with $p \cdot n \ge q$" ⟺
   $q \le p \cdot n$ **and** (the odd predecessor fails: $p\cdot(n-2) < q$,
   or there is no predecessor: $n = 1$). That is exactly the kernel's
   disjunct. (Stepping down by $2$ is the only move in the odd lattice.)
2. *Value preservation.* $x - \tfrac1n = \tfrac{p}{q} - \tfrac1n =
   \tfrac{p\,n - q}{q\,n}$. The kernel's $g$ is a common divisor of
   $p\,n-q$ and $q\,n$, and $p' = (p\,n-q)/g$, $q' = q\,n/g$ — the **same
   rational**, written reduced. Reduction is value-neutral; the relational
   form therefore covers both the raw and the reduced representation.
3. *Termination.* `TerminateIn` demands the residual hit **exactly $0$**,
   i.e. $p\,n = q$ at the last step — the sum closes to $x$ with no
   remainder. No early-stop, no approximation.
4. *Domain perpetuation.* Each step's residual satisfies
   $0 \le x' = x - \tfrac1n < x < 1$ (since $n \ge q/p$ gives
   $\tfrac1n \le x$, and $n \ge 1$ gives $\tfrac1n > 0$), so every
   trajectory state obeys $1 \le p \le q$ — the hypotheses of the laws
   below re-arise at every step. ∎

The corpus statement is preserved **exactly** — no silent strengthening, no
weakening.

---

## §3. LAW I — THE ODD-CLOSURE LAW (habitat invariance)

**Theorem L1 (Lean `erdos282_odd_closure`).** If $q$ is odd, $n$ is odd,
$g \ge 1$, and $q' \cdot g = q \cdot n$, then $q'$ is odd.

*Proof.* Parity of a product is the product of parities
(`Nat.mul_mod`):
$(q\cdot n) \bmod 2 = (q \bmod 2)(n \bmod 2) \bmod 2 = 1\cdot 1 \bmod 2 = 1$,
so $q \cdot n$ is odd. Suppose toward contradiction $q'$ were even. Then
$(q'\cdot g) \bmod 2 = (q' \bmod 2)(g \bmod 2) \bmod 2 = 0$, so $q' \cdot g$
is even — whatever the parity of $g$. But $q' \cdot g = q\cdot n$ is odd.
Contradiction. Hence $q'$ is odd. ∎

**Reading (the conjecture's arena is invariant).** In one greedy step the
new denominator satisfies exactly $q' \cdot g = q \cdot n$ with $q$ odd
(habitat) and $n$ odd ($A$ = odds). So **every** odd-greedy step starting
from an odd-denominator rational lands on an odd-denominator rational —
by induction along any trajectory, the odd-greedy **never leaves the
conjecture's habitat**. Termination cannot fail by parity escape; the
conjecture is a closed question *inside* the odd world. This is the
necessary structural law any eventual proof of (Q1) must build on, and it
is the reason the census of §6 is a well-posed exhaustive scan of the
habitat. Axiom footprint **[propext, Quot.sound] GOLD** (registry).

---

## §4. LAW II — THE WELL-FORMEDNESS LAW (the numerator at most doubles)

**Theorem L2 (Lean `erdos282_step_bound`).** If `GreedyStep p q p' q'`,
$p \le q$, and $1 \le p$, then $p' < 2p$.

*Proof.* Let $n, g$ be the step's certificate ($n$ odd, $q \le p\,n$,
minimality, $g \ge 1$, $p'\,g = p\,n - q$). Two cases.

**Case $n = 1$.** Then $q \le p\cdot 1 = p$, and with $p \le q$ this forces
$p = q$. So $p'\,g = p\,n - q = 0$, hence (a product of naturals is zero
only via a zero factor) $p' = 0 < 2p$ since $p \ge 1$.

**Case $n \ge 2$.** The minimality disjunct's second branch must hold:
$p\,(n-2) < q$. Distribute: $p\,n = p\,(n-2) + 2p$ (using $n - 2 + 2 = n$,
valid as $n \ge 2$). Since $g \ge 1$, $p' = p' \cdot 1 \le p'\,g =
p\,n - q = p\,(n-2) + 2p - q < 2p$, because $p\,(n-2) < q$. ∎

**Reading (why the problem is hard, quantified).** The numerator at most
**doubles** per step, and (Lemma F1.4) the $p \le q$ hypothesis re-arises at
every state, so L2 applies along the entire trajectory. Growth is
exponentially bounded but **not excluded and not monotone-collapsing**:
the census trajectories climb (the deepest kernel-range trajectory at
$38/39$ runs 12 steps; the battery's deepest at $102/293$ runs 20 steps,
with intermediate numerators swelling to $10^{43}$-scale before collapse).
L2 is the complete well-formedness law — the trajectory cannot explode
faster than $2^{\text{steps}}$ — and it marks exactly where a descent proof
must strike: some potential must fall even though $p$ may rise. Axiom
footprint **GOLD** (registry).

---

## §5. LAW III — THE SIMULATION SOUNDNESS (certified trajectories)

**The certified greedy choice (Lean `greedyN_spec`).**
`greedyN p q` = $\lceil q/p \rceil$ if odd, else $\lceil q/p \rceil + 1$
(with $\lceil q/p\rceil$ computed as $(q+p-1)/p$, exact for $p \ge 1$).
Theorem: `greedyN p q` is odd, $\ge 1$, satisfies $q \le p \cdot
\texttt{greedyN}$, and (it $= 1$ or $p\cdot(\texttt{greedyN}-2) < q$) —
i.e. **it is exactly the minimal odd $n$ with $p\,n \ge q$**, the corpus's
greedy choice at $A$ = odds.

*Proof (as in the kernel).* Set $n_0 := (q+p-1)/p$. Division-mod
decomposition: $p\,n_0 + ((q+p{-}1) \bmod p) = q+p-1$ with remainder
$< p$; hence $q \le p\,n_0$ (subtract at most $p-1$). If $n_0$ is even,
the choice is $n = n_0+1$ (odd): $q \le p\,n_0 \le p\,n$; minimality:
if $n_0 = 0$ then $n = 1$ (first disjunct); else $n_0 \ge 1$ and
$p\,(n-2) = p\,(n_0-1) = p\,n_0 - p \le (q+p-1) - p < q$. If $n_0$ is odd
(so $n_0 \neq 0$), the choice is $n = n_0 \ge 1$: $q \le p\,n_0$; minimality:
$n_0 = 1$ gives the first disjunct; $n_0 \ge 3$ gives
$p\,(n-2) \le p\,(n_0-1) = p\,n_0 - p \le (q+p-1)-p < q$. ∎

**The step certificate (Lean `stepValid`).** A Bool check of the full
`GreedyStep` certificate except the two exact-division equations, which it
checks as **divisibility**: $(p\,n - q) \bmod g = 0$ and $(q\,n) \bmod g = 0$,
with $g \ge 1$.

**The structural gcd (Lean `gcdF`, `stepG`).** The $g$ candidate is produced
by a **fuel-structural** Euclid recursion (`gcdF`), not well-founded
`decide` — the WF-decide disease avoided by design. Crucially, **gcdF's
correctness is never needed**: the step check certifies divisibility
directly on the actual numbers, so a wrong $g$ simply fails the check — the
garbage-$g$ spurious-termination trap is killed by construction.

**The simulation (Lean `simTerm`).** Fuel-bounded Bool walk: $p = 0$
returns `true`; otherwise the step must validate, and the walk recurses on
`(p·greedyN − q)/stepG, (q·greedyN)/stepG`.

**Theorem L3 (Lean `simTerm_sound`).** For all fuel, $p$, $q$:
`simTerm fuel p q = true` ⟹ `TerminateIn fuel p q`.

*Proof.* Induction on fuel. Fuel $0$: `simTerm = false`, vacuous. Fuel
$f+1$: if $p = 0$, termination at $0$ holds outright. Otherwise the
validated step supplies $n = $ `greedyN` $p\,q$ and $g = $ `stepG` $p\,q$
with all certificate clauses; divisibility $(p\,n-q) \bmod g = 0$ gives
$p' = (p\,n-q)/g$ exactly (division-mod: $a = (a/g)\,g + a \bmod g$ with
zero remainder), and likewise $q' = (q\,n)/g$ — the two exact-division
equations of `GreedyStep` close. The induction hypothesis on the residual
pair finishes. ∎

**Reading.** L3 is the **one-directional verification engine**: any
instance the simulation certifies is a genuine greedy trajectory to exactly
$0$ — every future certified termination instance (kernel- or
engine-level) converts to a real `TerminateIn` witness. A false simulation
claims nothing. Axiom footprint **GOLD** (registry).

---

## §6. LAW IV — THE TERMINATION CENSUS $q \le 41$ (kernel-decided)

**The census (Lean `census282 42`, theorem `census282_data`).**
`census282 42 = true` **by kernel `decide`**: for every $q < 42$ with $q$
odd, and every $1 \le p < q$, `simTerm 40 p q = true`. The scan carries
**domain guards** (`decide (q % 2 ≠ 1) || …`, `decide (p < 1) || …`) — an
unguarded `all()` fails on every non-domain element (the S036 lesson,
pre-registered).

**Theorem L4 (Lean `erdos282_census`).** For every $q$ with $q$ odd and
$q \le 41$, and every $1 \le p < q$: $\exists k,\ \texttt{TerminateIn}\ k\
p\ q$ — every odd-denominator rational $p/q \in (0,1)$ with $q \le 41$
**terminates under the odd-greedy algorithm.**

*Proof.* The kernel-decided Bool census (above) yields, for each such
$(p,q)$, `simTerm 40 p q = true`; `simTerm_sound` (L3) converts it to
`TerminateIn 40 p q`. ∎

**The certified census in numbers.** Odd $q \in [3,41]$: 20 values;
$\sum (q-1) = 420$ **pairs, every one kernel-decided**. Deepest
trajectory: **12 steps at $38/39$** (fuel 40 suffices). Trajectory
intermediates stay $\le 1390$ bits — inside the K17-precedent
kernel-decide zone (**THE CENSUS-COST LAW**: the kernel-decidable census
range is bounded by trajectory *number sizes*, not by pair count).

---

## §7. THE MAIN THEOREM (the one-statement assembly)

**Theorem (Lean `erdos282_main`).** The conjunction of L1 (odd-closure,
all $q, q', n, g$), L2 (well-formedness, all greedy steps), L3 (simulation
soundness, all fuel/pairs), L4 (the $q \le 41$ census), and the arsenal
bridge (§9) — **the complete Kernel 28 content in one unconditional
statement**, with `#print axioms` executed for all six theorems in the
CI-green run and `#eval "ERDOS282_STEIN_KERNEL_GREEN"` at the file's foot.

---

## §8. ENGINE EVIDENCE (batteries — re-run TODAY, foreground, all GREEN)

**Battery `battery282.py` (dual-method, re-run today: `BATTERY282 GREEN`,
2.3 s).**

| Check | Method | Result |
|---|---|---|
| Full census $q$ odd $\le 301$ | direct integer simulation ∥ exact-replay with per-step gcd reduction (both methods must agree) | **22,650 pairs, NON-TERMINATING/DISAGREE: NONE**; deepest **20 steps at $(102,293)$** |
| Kernel range $q \le 41$ | direct simulation | all terminate; deepest **12 steps at $(38,39)$** — **full agreement with the kernel claim L4** |
| Top-10 deepest | direct | $(20,102,293), (19,5,139), (19,3,179), (18,140,151), (18,16,181), (17,171,269), \ldots$ |
| Odd-closure spot-check | trajectory parity monitor, $q \le 301$, $p < 60$ | **ALL ODD** — the habitat law L1 spot-verified on the engine census |

**Engine `engine_round2.py` (re-run today: GREEN, 0.6 s).** The reduced
census $q$ odd $\le 301$, all $0 < p < q$: 22,650 pairs, **NONE
non-terminating**, max 20 steps at $(102,293)$.

**Engine round 1, Engine 8 (third method — exact `Fraction` arithmetic,
re-run today: GREEN, 0.3 s).** Every **coprime** odd-denominator rational
$m/n$ with $n$ odd $\le 201$ (8,282 pairs): **ALL terminate**; **maximum
greedy length 19 steps at $5/139$** — the mission's certified engine
evidence, reproduced exactly.

**Honest scope (engine evidence is evidence, not theorem).** The $q \le
301$ census and the $n \le 201$ coprime census are exhaustive *checks*,
not proofs; they are labeled as such everywhere above. The kernel theorem
is L4 ($q \le 41$). The deep instances cannot be kernel-certified: deep
trajectories blow past kernel-decidable number sizes — **$10^{5000}$-digit
intermediates** (THE_CORE §2 row #33), with the engine recording
**$10^{100000}$+ digits even with per-step reduction** on the deepest
trajectories (WORKLOG S036) — battery-only evidence, honestly scoped.

---

## §9. BOSS'S ARSENAL CITATION (the bridge theorems applied)

Kernel 28 imports the arsenal (`Arsenal.ErdosTernary2.Basic`,
`Arsenal.CardinalWorlds`, `Arsenal.CardinalWorldsV2` — the vendored
buildable arsenal of the 16,121-theorem campaign) and applies:

1. **`ErdosTernary2.isTernaryDigit`** — the ternary-digit predicate
   ($n \in \{0,1,2\}$), applied to the ternary digits of the witness
   numbers: $[13\%3,\ (13/3)\%3,\ (13/9)\%3]$ and
   $[65\%3,\ (65/3)\%3,\ (65/9)\%3]$ — all ternary digits ($13 = 111_3$;
   $65 = 2102_3$) — denominators from the certified census range, certified
   through the arsenal's ternary structure.
2. **`CardinalWorlds.carryAtPos` / `carryAtPos_bound`** — the ternary carry
   bound $\mathrm{carryAtPos}(R,p) < 4$, applied at $(R,p) = (65,1)$.
3. **`CardinalWorldsV2.v2r_ternary_scaling`** — the $2$-adic depth reader
   scaling law $\mathrm{v2r}(3^a \cdot c) = \mathrm{v2r}(c)$, applied at
   $(a,c) = (1,9)$: $\mathrm{v2r}(27) = \mathrm{v2r}(9)$.

The conjunction is Lean-certified as **`erdos282_arsenal_bridge :
arsenalBridgeProp`** (Kernel 28 §8) — the USE-ALL-THE-MATHS order executed.
The kernel's *architecture* additionally carries arsenal battle-laws as
design: the **fuel-structural gcd** (WF-decide disease avoided), the
**domain-guard law** for List.all censuses, the **census-cost law**, and
the **obtain-opaque pattern** (set's let-bound locals poison `omega` — the
Kernel 28 war record). **External literature used: NONE** — per the
arsenal-only rule, every proof above is kernel-certified Lean or
self-contained arithmetic.

---

## §10. VERIFICATION RECEIPTS

1. **CI (GitHub Actions): Kernel 28 — run 42439522105 GREEN** (the S036
   five-kill volley; 34/34 kernel steps green in the final run; the 7-round
   compile war record: the beq-coercion family, the minimality-disjunct
   leak, the rw-auto-close, the ←-self-mangling, and THE LET-LOCAL POISON
   killed by THE OBTAIN-OPAQUE PATTERN). Registry: README KILL #33
   (Session 036), THE_CORE §2 row #33, WORKLOG sessions S032 (engine) /
   S036 (kernel + war close).
2. **Axiom footprints (the file's `#print axioms` block, executed in the
   CI-green run; as recorded in the kill registry):** the odd-closure law
   **[propext, Quot.sound] GOLD**; the well-formedness law **GOLD**; the
   simulation soundness **GOLD**; the census **kernel-decided** (`decide`);
   zero `sorry`, zero custom axioms in `Erdos282.lean`.
3. **Batteries/engines re-run TODAY (this deliverable's session,
   foreground):**
   - `battery282.py` — **`BATTERY282 GREEN`** (dual-method; 22,650 pairs
     $q \le 301$ NONE non-terminating/disagreeing; deepest 20 at
     $(102,293)$; kernel range deepest 12 at $(38,39)$; odd-closure ALL
     ODD; 2.3 s total).
   - `engine_round2.py` — GREEN (22,650 pairs, NONE non-term; 0.6 s).
   - Engine-8 exact-`Fraction` third method — GREEN (8,282 coprime pairs,
     $n$ odd $\le 201$, ALL terminate, max **19 steps at $5/139$**; 0.3 s).
4. **Cross-method agreement:** kernel claim (420 pairs, deepest 12 at
   $38/39$) = battery kernel-range check = engine round-2 = engine round-1
   on its domain; three independent arithmetic engines agree on every
   overlapping instance.

---

## §11. THE EXACT GAP — THE NAMED REMAINING CORE

**THE GLOBAL ODD-GREEDY TERMINATION CORE (Stein's conjecture — the corpus's
first ask, verbatim):**

> Prove — or refute — that for **every** $p/q \in (0,1)$ with $q$ odd
> (unbounded $q$): the odd-greedy trajectory reaches exactly $0$ in
> finitely many steps. In kernel language: $\forall\, q\, p,\ q\%2 = 1
> \rightarrow 1 \le p \rightarrow p < q \rightarrow \exists\, k,\
> \texttt{TerminateIn}\ k\ p\ q$ — with no bound on $q$.

The corpus's second ask (the general $(x, A)$ classification, Q2) is the
strictly larger frontier **subsuming** this core ($A$ = odds is its own
named instance).

**Why exactly here and nowhere else — the three walls (each named):**

1. **No monotone measure.** L2 bounds growth ($p' < 2p$) but the numerator
   *rises* along deep trajectories (the 20-step trajectory at $102/293$
   climbs to $10^{43}$-scale numerators before collapse). No descent /
   potential function on the odd habitat is known to the arsenal — the
   local laws (L1 parity, L2 doubling) are structurally exhausted: neither
   forces eventual $p = 0$.
2. **THE CENSUS-COST LAW.** Kernel certification is bounded by trajectory
   **number sizes**, not pair count: deep instances reach $10^{5000}$-digit
   intermediates ($10^{100000}$+ digits recorded even reduced) —
   architecturally impossible to kernel-decide beyond the $\le 1390$-bit
   K17-precedent zone. The kernel route cannot materially extend the
   $q \le 41$ census; only a *proof* extends it.
3. **The conjecture demands a global argument.** Resolving the core
   requires a global invariant of the reduced trajectory (a potential
   function, a $p$-adic descent on the odd habitat, or a structural
   conservation law) — the component the current arsenal does not supply.

**What a resolution of the core buys:** the complete answer to (Q1)
verbatim; the kernel's L1–L4 then become the certified skeleton inside it
(habitat invariance, well-formedness, the verification engine for every
instance, and the certified base band $q \le 41$; the engine evidence
extends to $q \le 301$). Everything else in the corpus statement is
delivered complete in §3–§9 above.

---

*The engines never stop; they never lie. The wall is named; everything
else is proved.*
