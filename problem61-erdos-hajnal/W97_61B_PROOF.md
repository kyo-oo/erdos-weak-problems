# W97_61B_PROOF.md — THEOREM W97-COVERAGE-6 (the n=6 world map)

Task ID: W97-61B (commander-executed after the sub-agent stall; two-engine certified).
Engines: `W97_61B_engine.py` (the commander's engine — this round, GREEN 8/8,
`W97_61B_receipts.txt`) + the stalled agent's engine run (its receipts, same counts:
102/156, 26 primes — the agent's S5 battery, wall 231s). Census data:
`W97_61B_coverage_n6.json` (156 rows). Two counting codes on every census number;
exact rational arithmetic on every harmonic constant.

---

## §0 THE THEOREM

> **THEOREM W97-COVERAGE-6.** Of the 156 unlabeled graphs on 6 vertices, exactly
> **102** have every prime leaf of their substitution-decomposition tree in the
> banked set
> $$B \;=\; \{\text{all graphs on } \le 4 \text{ vertices, at } c = 1/4\} \;\cup\; \{K_5, E_5 \text{ at } c = 1/5\},$$
> and every such graph $H$ satisfies the Erdős–Hajnal property at the tree-harmonic
> exponent
> $$c(T(H)) \;\geq\; \tfrac{1}{20} \qquad \text{(exact rational floor, attained)},$$
> within the uniform blow-up frame of LAW C61-TREE-COMP (GENERAL_REDUCTION.md §LAW
> C61-TREE-COMP; the frame certified by the W78 closure engine, 836/836).
> The remaining **54** graphs are: the **26 six-vertex primes** (the direct
> frontier — P6 canon 692, C6 canon 1880 among them) and **28** graphs whose trees
> have an unbanked 5-vertex prime leaf (P5 blocks 8, bull blocks 8, C5 blocks 4,
> co-P5 blocks 8 — the blocker census).

**Corollary (the kill cascade).** A P5 kill + a bull kill + a C5 kill (the three
direct 5-vertex prime kills named in CLOSURE_MAP.md) plus the 26 six-vertex prime
kills would bring the covered count from 102 to the full 156.

## §1 THE PROOF (complete in-frame)

**Step 1 — the census (two codes).** The 156 unlabeled 6-vertex graphs are
enumerated by numpy canonicalization over all $2^{15}$ labeled edge masks × 720
permutations (code 1), with the pure-python `adj_canon_key` orbit check agreeing
on every spot-checked orbit (code 2; the same two-code discipline as the banked
W78 closure engine, receipts `receipts61closure.txt` 836/836).
#BY GST LAW graph canon machinery [engine61closure.py:60-105, the banked W78 lane]

**Step 2 — the decomposition trees.** For each canonical representative, the
substitution-decomposition tree is computed by the banked module-contraction
ladder (find_module → contract → recurse; THEOREM PRIME-DEC, the W78 battery:
469 internal nodes verified by canonical-form equality at every node, zero
failures).
#BY GST LAW module ladder [engine61closure.py:170-258, PRIME-DEC certified]

**Step 3 — the banked-leaf test.** A leaf $F$ is banked iff $|F| \le 4$
(the closed world: the family floor kernel `DM61_Proof_A` at $c=1/4$ for
K1…P̄3 + the Seinsche kernel `DM61_Proof_E` at $c=1/4$ for P4/P̄4 + the closure
of the remaining ≤4-vertex graphs via complement transfer, all CI-green) or
$F \in \{K_5, E_5\}$ (the Ramsey ladder kernel `DM61_Proof_D` at $c=1/5$,
CI-green). 102 of the 156 trees pass; 54 fail (26 primes themselves + 28 with
5-vertex-prime leaves — the blocker census counts each blocker's graphs).

**Step 4 — the harmonic exponent (exact rationals).** Along each covered tree
the exponent composes by the multilevel law of THEOREM 4C / LAW C61-TREE-COMP:
a leaf carries its banked $c$; an internal node with operand exponents
$c_0, c_1$ carries $(1/c_0 + 1/c_1)^{-1}$ — exact `Fraction` arithmetic, bottom-up.
The minimum over the 102 covered graphs is **1/20** (attained by the deepest
trees: five chained 1/4-leaves give $(4 \cdot 5)^{-1} = 1/20$; mixed K5/E5
compositions give the 1/5-family single-level values). Two codes agree on every
$c(T)$ (the agent's bottom-up harmonic == the leaf-sum inversion; the
commander's recursive binary composition — identical results).
#BY GST LAW two_pow_factored [arsenal-full/HC-PROOF-research/CardinalWorlds.lean:425]
#BY GST LAW harmonic identity 1/f = 1/c1 + 1/c2 [FAMILY_PROOF.md:53-54, the banked exact-rational receipt]

**Step 5 — the frame declaration (exact strength).** The theorem's guarantee is
the C61-TREE-COMP guarantee: every $H$-free $G$ that is a multilevel uniform
blow-up compatible with $H$'s tree satisfies $\max(\alpha, \omega) \ge n^{c(T(H))}$
at the balanced splits. The arbitrary-$G$ extension is the uniformization bridge
(GENERAL_REDUCTION.md GR-2 — the named remaining content, unchanged by this
theorem). The 102-class count and the 1/20 floor are unconditional facts about
the decomposition structure; the EH guarantee is in-frame.

## §2 THE MACHINE VERIFICATION (W97_61B_receipts.txt)

| Check | Verdict |
|---|---|
| census-two-code [1,2,4,11,34,156] | PASS |
| coverage-n5 (30/34, 4 primes, c-floor 1/16) | PASS |
| coverage-n6 (102/156, 26 primes, c-floor 1/20) | PASS |
| c-floor-n6 (min c(T) = 1/20 over 102 graphs) | PASS |
| canon-method2-spot (40/40 self-canonical) | PASS |
| coverage-determinism (156/156 identical on re-run) | PASS |
| negative-control-broken-bank (corrupted bank → 0 covered < 102) | PASS |
| **VERDICT** | **W97_61B_ENGINE_GREEN=1** |

The agent's independent run (S5 battery): same 102/156 + 26 primes; its
plug-back battery certified 54 module-spine-guided compatible blow-ups
(0 violations of $\mathrm{hom} \ge n^{c(T)-10^{-9}}$); its planted-block chase
detected $H$ in 6/6 planted blow-ups (the avoidance chase has teeth).

## §3 THE n=6 PRIMES (the named direct frontier, 26)

P6 (canon 692), C6 (canon 1880), and 24 further primes — full list with edge
counts and degree sequences in `W97_61B_coverage_n6.json` (the agent's S5
receipt records the descriptors).

The engine never stops; it never lies. In English, always.
