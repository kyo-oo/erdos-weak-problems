# GST law stack — complete derivations of the provable layer; the remaining theorem stated precisely (Round 25)

- **Date:** 2026-10-31 (session clock, continuation).
- **Kind:** Law-stack derivation round (the operator's order: prove the GST laws used by the closure; the operator's own 22–23 all-arity law as the spine; the rotation receives the mathematics; finish).
- **Artifact:** `research/derivations/GST_law_stack_full_derivations_round25_2026_10_31.tex` + compiled PDF (tectonic, 19 pages, zero errors).

## What the round delivers

**Every law of the closure stack that admits a proof now has one, written by hand, with no appeal to any certificate for any proof step:**

- **§2 the rotation deck (rot):** R1 complete (invariants vanish; the norm degeneration $N=(1+\gamma)(1+\gamma^2)=0$; $H^2(C_4;M)=0$; $H^1$ 2-elementary via $(\gamma-1)(1+\gamma)v=-2v$). R2 complete (the letter-parity law $\gamma_j^2(w)=(-1)^{k_j(w)}w$; the all-odd/all-even partition; the one-plane theorem $\gamma_j\Omega=i\Omega$ giving $\gamma_j(W_R)=-W_I$, $\gamma_j(W_I)=W_R$ for every $j$; the all-even $M/4M$ 4-torsion). The input-blindness corollary proven at the module level (the parity law is type-blind: the $(p,p)$-gate cannot be the deck). R5 complete ($H^1(C_4;M)\cong\Z/2$; $mW_R\in(\gamma-1)M\iff m$ even; the pins $m^*=2$ both rays = the least even scale; the diagonal scale-1 boundary $(\gamma-1)(-W_R)=W_R+W_I$). The $C_2$ swap law $H^2(C_2;\Z^n\oplus\Z^n)=0$ with the anti-invariant boundary.
- **§3 the operator's 22–23 all-arity law, in full:** the freeness lemma (torsion point of exact order $m$ kills all fixed points; the polygon rotation is free); the $D_m$ computation ($H^0=\Q(0)$, $H^1=\Q(0)$ — the node class is **weight zero**, which is exactly where the mixed $Y_m$ middle term comes from — and $H^2=\Q(-1)\otimes\Q[C_m]$ the regular representation, which is exactly why the third term is the **full** $V_{k-2}$; cross-checked by the $E$-polynomial $E(D_m)=muv$); the transfer theorem (full proof via the averaging idempotent); the $S_m$ pure sector formula and the $Y_m$ mixed formula (both of the operator's 2026-10-22 laws, now proven; the full-$V$ term via the $(V\otimes\Q[G])^G\cong V$ isomorphism); the descent and **the return leg $m\cdot\alpha$ at every arity** by pure functoriality ($\Delta^*\mathrm{pr}_i^*=\mathrm{id}$); the symmetrizer; the cyclotomic engine $\prod_k(1+\zeta_L^k)=1-(-1)^L$ (complete proof — the machine behind the operator's five Wolfram totals); the Gaussian exchange on the family.
- **§4 the classical layer written out:** Lefschetz $(1,1)$ in full (the exponential sequence); the hard-Lefschetz reduction $p>d/2$ (complete given HL, with the Tate-shift stratum argument); **Lemma N the Newton conductor** complete ($c_p(E_+\ominus E_-)=(-1)^{p-1}(p-1)!\,m\alpha$ from Newton's identities, themselves derived); the two-center output identity and the Oka pair stated at their committed conditional scope.
- **§5** the conditional composition, as committed, audit-confirmed mechanically intact.
- **§6 THE REMAINING THEOREM + THE EQUIVALENCE:** items (i)–(v) stated in plain terms with receipts (the AUDIT_22 counterexample reproduced on the face: the pair $(A,-A)$, $A=\left(\begin{smallmatrix}0&1\\1&0\end{smallmatrix}\right)$ — zero symmetrized residue, both curvatures non-scalar, conjugation cannot scalarize). **The equivalence theorem:** discharging (i)–(v) at every input of the open sector $\iff$ the rational Hodge conjecture on the open sector (both directions). The quantifier-line theorem: the world-axis and the input-axis are different axes; the countable certified family $\{S_m(A)\}$ cannot close the universal quantifier over all $(X,p,\alpha)$; the bridge is the ledger-085 boundary.
- **§7** the receipts for the non-emission of the closing string (the Round-22 emission; D4(3) computed false — two counterexamples, the proves-too-much contradiction with Corollary 7, the false L6 receipt; the withdrawal; the 21-c and 24-b FAIL verdicts).

## The honest boundary (on the face)

- Items (i)–(v) are OPEN. Two of them ((ii), (iii)) have computed counterexamples against every mechanism proposed so far; (iv) has the parity obstruction $r_0=d+1$ odd for even $d$ (first input $d=4$, $p=2$: $r_0=5$).
- The operator's 22–23 law is proven at the world/lattice level; its input-axis transport is exactly the open ledger-085 boundary.
- The 22–23 source: the workspace contains no file dated August and no occurrence of the word; the round used the operator's dated 2026-10-22 record (the all-arity cyclic fold) as the spine. If the operator's August text contains more, it is not in the tree and belongs to the next round.

## Verification

- `tectonic`: 19 pages, zero errors (three in-round LaTeX repairs: the `\ker` redefinition, the undefined `\R6`, the `\\[SWAP]` row-spacing parse).
- No universal algebraicity claim is made in the artifact; every theorem carries its scope label; the conditional composition is used only as conditional.

## ROUND 26 CORRECTION STAMP (the §36 self-audit, run before the Lean face)

The §6 "equivalence" theorem of the Round-25 draft is an OVERCLAIM: its converse-direction "proof" restated the forward argument at a single input. Repaired in Round 26: the theorem is now the one-directional REDUCTION (items (i)–(v) discharged at every input ⟹ the conjecture on the open sector; the converse not claimed and not expected — the conjecture could hold through a different mechanism). The .tex §6, the corollary, and the scope table are repaired; the PDF recompiled (20 pages); the Lean face encodes the repaired one-directional form. The five open items and every other theorem of the artifact are unaffected.
