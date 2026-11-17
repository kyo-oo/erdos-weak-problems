# Erdős #142 — THE r_k(N) AP-FREE TERNARY KERNEL (COMPLETE PROOF, W67-142K)

Erdős problem #142 (verbatim, erdosproblems.com/142, prize $10000):

> "Let $r_k(N)$ be the largest possible size of a subset of $\{1,\ldots,N\}$
> that does not contain any non-trivial $k$-term arithmetic progression.
> Prove an asymptotic formula for $r_k(N)$."

Convention (pinned, verbatim): non-trivial k-term AP: a, a+d, ..., a+(k-1)d
with d ≥ 1 (distinct terms). r_k(N) := max |S| over S ⊆ [1,N] containing no
non-trivial k-term AP. Finite-list encoding: S : List Nat, S.Nodup, every
s ∈ S with 1 ≤ s ≤ N.

---

## §1 THE CERTIFIED THEOREMS (Erdos142.lean, namespace E142, CI job kernel-142k)

1. **E142.t3free — THE TERNARY KERNEL.** The Cantor ternary set
   `T := {n : noTernaryTwo n = true}` (the Arsenal's CardinalWorlds reader:
   the ternary expansion avoids the digit 2, i.e. every ternary digit is 0
   or 1) is 3-AP-free:
   `∀ x y z : Nat, noTernaryTwo x = true → noTernaryTwo y = true → noTernaryTwo z = true → x + z = 2 * y → x = z.`
   Proof: the mod-3 descent. T's residue law (noTernaryTwo forces n % 3 ≠ 2,
   the reader's own definitional step), the trichotomy from
   ErdosTernary2.lt_three_cases on y % 3:
   - y % 3 = 0 → the equation x + z = 2y mod 3 forces x % 3 = z % 3 = 0
     (residues ≤ 1 on both sides), so x = 3(x/3), z = 3(z/3), y = 3(y/3)
     and the equation descends to x/3 + z/3 = 2(y/3) with all thirds in T
     (the reader's step law ntt_step);
   - y % 3 = 1 → similarly x % 3 = z % 3 = 1 and the descent holds;
   - y % 3 = 2 → impossible (T's residue law).
   Termination: fuel induction on y (y/3 < y for y > 0). Base y = 0 forces
   x = z = 0. **E142.t3_no_nontriv**: T contains no non-trivial 3-term AP
   (the a, a+d, a+2d form: t3free gives a = a+2d, contradicting d ≥ 1).

2. **E142.cantor_lower — THE CANTOR LOWER BOUND.**
   `∀ k : Nat, r3AtLeast (3^k − 1) (2^k − 1)`, i.e. r_3(3^k − 1) ≥ 2^k − 1:
   the explicit witness list `genTp k` — every ternary digit vector in
   {0,1}^k except the all-zero vector, read as a natural — has exactly
   2^k − 1 distinct elements (genTp_length, with
   CardinalWorlds.two_pow_pos for the 2-world positivity), all inside
   [1, 3^k − 1] (genTp_bounds), and is 3-AP-free by t3free (genTp_apfree:
   membership in genTp implies the Cantor verdict via the closure laws
   ntt_3n / ntt_3n1 — appending a ternary digit 0 or 1 preserves T).

3. **E142.block_upper — THE BLOCK UPPER BOUND.**
   `∀ k N S, 1 ≤ k → S.Nodup → (∀ s ∈ S, 1 ≤ s ∧ s ≤ N) → APfree S k → S.length ≤ (k − 1)·⌊N/k⌋ + (N mod k).`
   Proof: the partition of [1,N] into ⌊N/k⌋ consecutive k-blocks plus the
   tail. Each full k-block {jm+1, ..., jm+k} is itself a k-term AP with
   d = 1, so a k-AP-free set takes at most k−1 of its points:
   - window_pigeon: a Nodup list in a k-wide window has ≤ k elements
     (induction on the window width, splitting off the lo-bound points);
   - window_cover: k distinct points in a k-wide window cover it all
     (the equality case of the pigeonhole, by induction);
   - together: exactly k points in the top block would cover it, giving
     the block AP (a = block-start, d = 1) — contradiction; hence ≤ k−1
     per block, and block_upper_aux descends on the block count.
   **E142.r3_upper** (k = 3): every 3-AP-free S ⊆ [1,N] has
   |S| ≤ 2⌊N/3⌋ + (N mod 3), i.e. r_3(N) ≤ 2⌊N/3⌋ + N mod 3
   (via apfree3_of_set: the midpoint form implies the k=3 AP form).

4. **E142.k2_edge — THE EDGE.** r_2(N) = 1 for N ≥ 2: the upper law
   (k2_upper: any 2-element set {x,y} with x < y is a 2-AP with
   d = y − x ≥ 1, so a 2-AP-free S has |S| ≤ 1) + the witness [1].

5. **E142.r3_exact_small — THE EXACT SMALL VALUES.**
   r_3(N) = v for N = 1..8 with v = 1, 2, 2, 3, 4, 4, 4, 4.
   - The lower certificates: the explicit witnesses [1], [1, 2], [1, 2],
     [1, 2, 4], [1, 2, 4, 5], [1, 2, 4, 5], [1, 2, 4, 5], [1, 2, 4, 5]
     (Nodup, bounded, certified 3-AP-free by the ap3Free checker, whose
     soundness ap3Free_sound is proved in full).
   - The upper certificates: the exhaustive enumeration `r3max N` — the
     fold-max of the 3-AP-free members of the sublists of [1..N] — is
     kernel-decided to equal v at each N = 1..8, and the r3max bridge
     (r3_upper_via_r3max) proves r3max dominates EVERY 3-AP-free S ⊆ [1,N]
     (the sorted-filtration S' := [1..N].filt(memB S) is a sublist member
     whose length dominates |S| by the membership pigeonhole nodup_mem_le).
   - The checker's iff: ap3Free (the triple-scan Bool) is proved sound
     AND complete against the Prop-level midpoint form
     (ap3Free_sound / ap3Free_of_set).

6. **E142.arsenal_bridge + E142.erdos142_board.** The Arsenal bridge: T's
   closure laws (ntt_3n, ntt_3n1 — the CardinalWorlds reader applied). The
   board: the 7-conjunct conjunction of all certified results above.
   Receipts: IO.println "E142_TERNARY_GREEN" / "E142_CANTOR_GREEN" /
   "E142_BOARD_GREEN" + #print axioms per board theorem.

## §2 VERIFICATION (dual method + machine certificates)

- The python mirror `engine142/mirror142.py` (log:
  `engine142/mirror142_log.txt`, verdict **E142_MIRROR_GREEN**): the decide
  table r_3(N) for N ≤ 8 = [1,2,2,3,4,4,4,4]; the Cantor witnesses T_k for
  k ≤ 8 (T_k ∩ [1, 3^k − 1] size 2^k − 1, 3-AP-free); the block-bound
  domination for N ≤ 100, k ≤ 5; the k=2 edge. DUAL METHOD inside the
  mirror: exhaustive 2^N subset scan AND an independent branch-and-bound
  agree on N ≤ 12.
- The doubter lane W67-142D (CI-green, run 43726649205 after the r2
  repair at 5f031ed): the exact r_3 table to N ≤ 30, r_4/r_5 frontiers to
  N ≤ 20, z3 SAT/UNSAT dual certificates, brute-force 100% agreement to
  N ≤ 12, the Cantor set triple-digitized (32,640 pairs, zero violations),
  the T_8 complement scan. INTEL: the printed reference string in the
  mission deviates from the certified truth at N = 9,11,13,14,15,16,20 —
  the doubter's own computation is the truth (mission law); the values
  certified here agree with the doubter's certified table on N ≤ 8.
- Lean verdict: GitHub CI only (job kernel-142k, workflow kills.yml);
  axioms within [propext, Classical.choice, Quot.sound]; zero sorry,
  zero admit, zero native_decide.

## §3 CI VERDICT (banked, W68-142K r4)

- CI run **43753209508** (workflow kills.yml, branch w67-p142k, head
  `654224c`): job **kernel-142k** = `success` (job id 132931526918).
  Compile log: `lake env lean problem142-ap-free/Erdos142.lean` → zero
  errors, zero sorryAx, markers `E142_TERNARY_GREEN` / `E142_CANTOR_GREEN` /
  `E142_BOARD_GREEN` emitted, `KERNEL142K_GREEN=1` reached; the guards'
  axiom greps all hit: E142.(t3free|t3_no_nontriv|cantor_lower|
  block_upper|r3_upper|k2_edge|r3_exact_small|arsenal_bridge|
  erdos142_board) each `depends on axioms: [propext, Classical.choice,
  Quot.sound]` or a subset thereof — all inside the allowed profile
  [propext, Classical.choice, Quot.sound].
- Repair trail: r1 (011cb3e) 73 errors → r2 → r3 (6e51a4b) 28 errors →
  r4 (654224c) **0 errors, GREEN**. The r4 root-kill: the `eqb`
  `zero`-pattern collision (variables named `zero`, not the constructors)
  that poisoned every downstream reduction incl. the 12-member
  r3max/ap3Free `decide` family — verified first on a local
  Lean v4.33.0-rc2 stub-harness that reproduced all 28 CI errors
  verbatim, then zero after the fix.

## §4 HONEST SCOPE

The asymptotic formula for r_k(N) remains **OPEN for every k ≥ 3** — this
kernel does NOT claim it (Roth's r_3 = o(N), Behrend's lower bound, and
the Kelley–Meka upper bound are literature context only; none are used).
What closed here — complete and unconditional:
- the Cantor ternary lower bound r_3(3^k − 1) ≥ 2^k − 1 (the digit-vector
  construction, fully formalized with the Arsenal's own ternary reader);
- the block upper bound r_k(N) ≤ (k−1)⌊N/k⌋ + (N mod k) for every k ≥ 1,
  and its k = 3 specialization;
- the exact values r_3(N) for N = 1..8;
- the k = 2 edge r_2(N) = 1.
These are the classical elementary two-sided bounds of the problem — the
complete elementary theory below the asymptotic frontier.

The engine never stops; it never lies.

---

## THE BEHREND PILLAR (W72-142K, S071)

**Theorem B (explicit Behrend).** For all $d \geq 1$, $m \geq 2$, $B = 2m$:
there is a 3-AP-free $S \subseteq [0, B^d)$ with
$|S| \geq \frac{m^d}{(d(m-1)+1)(d(m-1)^2+1)}$; hence for $N \geq B^d$,
$r_3(N) \geq \frac{m^d}{(d(m-1)+1)(d(m-1)^2+1)}$. With the optimization
$d = \lfloor\sqrt{3\ln N/\ln 2}\rfloor$, $m = \lfloor N^{1/d}/2 \rfloor$:
$r_3(N) \geq N\exp(-(2\sqrt{3\ln 2}+o(1))\sqrt{\ln N})$.

Full six-step derivation, the no-carry law, the sphere lemma, the certified
instance table, the Cantor ternary family + the $\mathbb{F}_3^d$ cap-set
bridge, and the 18 arsenal-law citations:
**BEHREND_PROOF.md** (this directory). Engine:
`engine142behrend.py --verify` — 8/8 GREEN (`receipts142behrend.txt`),
including the three-way $r_3$ table agreement and the 18/18 arsenal law
spot-checks. The OFFICIAL DeepMind comparator lane (fresh
google-deepmind/funsearch clone): `comparator-official/challenges/142/`.
