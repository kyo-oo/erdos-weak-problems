# Mathbox — GST Problem 406: exact cofactor-one collision obligation, 2026-10-30

## Fixed target

The requested result is **unchanged**:
\[
\forall K\ge5,\ K\ne7\implies
\exists p\ge1:\quad d_p(4^K)=d_p(4^{K+1})=2.
\]
The kernel-verified result is still conditional on the exact source gate.
No declaration in this branch upgrades that status.

## Three routes tested, and their precise mathematical status

### A. All-length dyadic BAD exclusion (open)

Let \(L_K=\lceil24K/19\rceil\). Already established by strict Lean:
\(4^K<3^{L_K}\) and
\(2^{\lfloor3L_K/2\rfloor+1}\mid4^K\) for every \(K\ge13\).
A *sufficient* all-source theorem would be
\[
\forall L\ge11,\quad 0<R<3^L,\ R\bmod3=1,\
2^{\lfloor3L/2\rfloor+1}\mid R
\quad\Longrightarrow\quad
\exists p\ge1:\ d_p(R)=d_p(4R)=2.
\]
This is not proved. A different, weaker proposed cutoff
\(\lfloor4L/3\rfloor+1\) is FALSE, already refuted and axiom-free
Lean-verified in GSTProblem406BadValuationNoGo.lean.

Independent **finite falsification search**, no sampling:
enumerate all R = m*2^e with \(e=\lfloor3L/2\rfloor+1\),
\(m\ge1\), \(R<3^L\), \(R\bmod3=1\), and test
all digits of R and 4R for their first shared 2.
The loops checked \(L=11,\ldots,260\), with no
counterexample encountered in that finite range. This observation
is NOT the all-length theorem, and cannot close the gate.
The finite computation is not an assumption in any Lean proof.

### B. GST phase / U-telescope forcing a 3-step collision (false without new input)

The original failing source is
GSTInfiniteFourPowerNavigation.lean, theorem
power_three_step_collision, line 176:
linarith cannot get False from
a left Happy cell, an all-depth BAD right rectangle,
local signed phase windows, exact width-three carry conservation,
and the U telescope.

Already STRICT Lean verified on the prior branch:
- GSTProblem406TerminalUBoundary.lean: all \(K\ge13\)
  pure source terminal \(U=-315\);
- all-\(K\) renormalized finite U checksum;
- GSTProblem406TruePowerPhaseMismatch.lean:
  on the actual \(4^8\) to \(4^{11}\) rectangle, child phase \(+2\),
  right phase \(-4\), U derivative \(+518\).
The phase signs and positive defect are compatible: the right
parent acquires a Happy event only later.

A **new exact stronger countermodel** has now been proven in
GSTProblem406PrefixOneDyadicNoGo.lean.

\[
E=4339\cdot 2^{24}=72{,}796{,}340{,}224,\quad
R=64E=4{,}658{,}965{,}774{,}336.
\]
It satisfies:
- \(E\bmod27=1\), hence carries at the source's ternary depth 3
  start with zero (the prefix-one source geometry);
- \(2^{24}\mid E\);
- \(d_3(E)=d_3(4E)=2\), a real child Happy;
- **for every p, no simultaneous 2** occurs in
  \(d_p(64E),d_p(256E)\).

No finite-bound extrapolation is used. The kernel checks all
\(p<30\) with Fin 30 exact arithmetic, then uses
\(64E<3^{30}\) for every remaining height. The source is NOT
a pure power \(4^K\): its odd binary cofactor is 4339.

Strict axiom and kernel CI PASS:
https://github.com/kyo-oo/erdosternary2/actions/runs/41082831276 .

This proves the existing GST local/terminal identities, prefix-one,
and a large fixed dyadic valuation alone cannot yield the
desired width-three collision. It does NOT refute the original theorem.

### C. Exact source / odd cofactor one (unfinished)

The true source \(E=4^K\) has a binary representation with one 1
at position \(2K\), i.e. odd cofactor exactly one. Equivalently
the affine source \(u_K=\mathrm{affineOrbit}(K)\) is a base-four
repunit:
\[
4^K=1+3u_K,\quad u_{K+1}=4u_K+1.
\]
These exact identities and the digit-shift equivalence are already
kernel-verified in GSTFourPowerAffineOrbit.lean.
The original gate can be stated
\[
\forall K\ge8,\quad
\neg\mathrm{BadChannel}(1,u_K).
\]

The currently attempted three-step collision theorem is precisely
the source-specific claim
\[
\begin{aligned}
K\ge8,\quad& \exists p\ge3:
   \mathrm{Happy}(4^K,p)\\
&\Longrightarrow\exists q\ge3:
   \mathrm{Happy}(4^{K+3},q).
\end{aligned}
\]
Together with the verified bases at K=8,9,10 it implies
the universal target by strong induction. Thus the missing
propagation is **the substantive all-K research obligation**,
not an arithmetic-tactic simplification.

To close it one must prove a new inequality / invariant of
the *whole* ternary BAD trajectory from the exact repunit
\(u_K\), or prove the uniform all-source \(3L/2\) zero-exclusion
above. Existing GST local phase equations, U checksum,
prefix-one, and a large 2-power are insufficient; the new
countermodel establishes this rigorously.

## Audit and evidence labels

- Original \(\forall K\ge5,K\ne7\) result: **incomplete / conditional**.
- All-\(K\) physical 24/19 bound: **Lean proved**.
- Physical terminal U and renormalized checksum: **Lean proved**.
- Prefix-one high-valuation width-three no-go: **Lean proved**.
- Universal \(\lfloor3L/2\rfloor\) BAD-valuation exclusion:
  **not proved**, finite falsification only.
- All-\(K\) source-specific three-step collision: **not proved**.
- Production \`hGate\`: **left unchanged**; no false upgrade.

The prior GST source branch and this Mathbox branch preserve all earlier
research; only evidence-backed new files were added.
