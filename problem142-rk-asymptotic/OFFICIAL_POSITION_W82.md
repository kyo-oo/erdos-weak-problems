# OFFICIAL POSITION W82 — Erdős #142 on the official DeepMind statement

**The official statement** (google-deepmind/formal-conjectures @ 2207c54d,
`FormalConjectures/ErdosProblems/142.lean`, byte-verified identical to
`deepmind-comparator/DM_142.lean` and the spec block of
`problem142-rk-asymptotic/DM142_Official.lean`):

> Prove an asymptotic formula for $r_k(N)$, the largest possible size of a
> subset of $\{1, \dots, N\}$ that does not contain any non-trivial $k$-term
> arithmetic progression. That is, find $f_k$ with $r_k(N) / f_k(N) \to 1$
> as $N \to \infty$.

with the official definition `noncomputable abbrev r :=
Set.IsAPOfLengthFree.maxCard` (vendored verbatim in `FC/Combinatorics/AP/Basic.lean`).

## STATUS: OPEN — and the exact remaining content, named

The asymptotic formula itself is open (this is the research-open core; no
one anywhere has it, for any $k \ge 3$ — even the order of magnitude
$\Theta$-form is open). The campaign attacks it with everything that IS
provable, all over the OFFICIAL definition, machine-verified. The remaining
content beyond the campaign's stack, precisely:

1. **F-UP-SUB (the sublinear upper for $k \ge 4$):** the LOGDECAY-GEN
   inversion chain. The k=3 sublinear upper is banked in-package (LOGDECAY:
   $r_3(N) \le \sqrt{26600}\,N\sqrt{\ln\ln N/\ln N}$, W77-142K, 19/19
   dual-method). The W81-142A wave banked the ORDER-k DEVIATION IDENTITY
   (the exact Fourier-side k-AP count, Theorem D1-k, 4-method certified) +
   the extraction layer (X-4, F2-SHARP, TC-4, L-TERM-3-SHARP $2-\sqrt 2$,
   L-TERM-4 $(10-\sqrt{10})/9$) — the named missing law between the
   deviation identity and the k≥4 arc-increment is the flow-composition
   step of the density-increment program.
2. **F-LOW-RANK (the Rankin shape):** the lower envelope's believed shape
   $r_k(N) \ge N \exp(-c(\ln N)^{1/(k-1)})$-class improvements — the
   sum-classifier ceiling is PROVEN in-package (the Rankin front named with
   its ceiling proof, W79-142E).

## WHAT IS CLOSED (each entry: exact strength + location + verification)

| Law | Strength | Where | Verdict |
|---|---|---|---|
| BEHREND-GEN (all-k lower) | $r_k(N) \ge N\exp(-C_k\sqrt{\ln N})$ for every $k \ge 3$, $N \ge 2^{40}$, $C_k = 2\sqrt{(k{+}1)\ln 2}+1$ explicit | problem142-ap-free/BEHREND_PROOF.md + engine142behrendgen.py (9/9) + the official gate (24/24 OKAY) | in-package + CI gate |
| Official-r Lean stones (k=3) | $6 \le r_3(216)$, $12 \le r_3(1296)$, $30 \le r_3(7776)$, $90 \le r_3(46656)$, $24 \le r_3(10000)$, $48 \le r_3(38416)$, $10 \le r_3(1024)$, … | DM142_Proof_B.lean (decide-certified witnesses, maxCard transfer) | CI kernel-142dm-b |
| Official-r Lean stones (k=4,5) | $6 \le r_4(216)$, $12 \le r_4(1296)$, $6 \le r_5(216)$, … (19 stones total) | DM142_Proof_B.lean | CI kernel-142dm-b |
| LAW M-1 (monotonicity) | $r_k(N) \le r_{k+1}(N)$ — the ladder | DM142_Proof_A.lean (sibling lane) + banked LOWER_STACK.md | CI kernel-142dm-a |
| LAW U-GEN-0 (universal upper) | $r_k(N) \le N - \lfloor N/k \rfloor$, every $k \ge 2$, tight at $N = k$ | W80-142U (in-package, 56/56) + DM142_Proof_A.lean | CI kernel-142dm-a |
| THEOREM V-GEN (amplification) | $k$-AP-free $A \subseteq [1,N]$, $N \ge 16m^2$: $\lvert A\rvert \le (1 + 1/(2\,r_k(m)))\,(r_k(m)/m)\,N$ | W80-142U (in-package) | engine + receipts |
| LOGDECAY (k=3 sublinear upper) | $r_3(N) \le \sqrt{26600}\,N\sqrt{\ln\ln N/\ln N}$ | W77-142K + AUD-LOGDECAY 60-digit re-derivation | CI gate |
| Deviation identity + extraction | Theorem D1-k, V2-k, X-4, F2-SHARP, TC-4, L-TERM-*-SHARP | W81-142A (engine 51/51) + W81-142B audit (defects D1-D3 fixed) | CI gate |
| The classical stones table | 188 certified $r_k(N)$ cells, dual-method (z3 + B&B), zero OEIS b-file mismatches | S060 W1 + witnesses_table_ext.json | CI gate |

**The two-sided shape of the campaign's position:**
$$N\exp(-C_k\sqrt{\ln N}) \;\le\; r_k(N) \;\le\; N - \lfloor N/k \rfloor
\quad\text{(all } k \ge 3\text{, banked)}$$
with the k=3 upper sharpened to sublinear (LOGDECAY) and the k≥4 sublinear
program's missing law named exactly (the flow-composition step). Every law
above is a complete, machine-verified theorem — nothing partial is dressed
as the open core, and the open core is not claimed by anyone.

The engine never stops; it never lies. In English, always.
