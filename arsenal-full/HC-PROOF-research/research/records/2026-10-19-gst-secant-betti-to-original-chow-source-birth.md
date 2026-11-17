# Mathbox — noncircular ordinary sheaf -> Betti-to-Chow source -> original A

**Date:** 2026-10-19. **Single active objective:** unconditional original-X rational Hodge conjecture. **Fixed route:** native perfect-complex secant geometry / ordinary projective-bundle sheaf / Hilbert period transport / original Weil-fourfold Gysin extraction. **Base commit:** \`96e09d3cc50eec0a4021e4d019ab5440c7c99c75\`.

## Material correction of the source construction

In the first algebraic projective-bundle identity, the fixed source κ was given as an element of CH*(Y)_Q. **That is circular if used to assert algebraicity of κ_B**, the initially Betti-only flat Hodge class. This round added an explicitly NONCIRCULAR theorem whose data include κ_B in Betti cohomology only, never a Chow representative of κ_B on Y.

Let p:P(Q)->Y be the actual projective bundle of relative dimension f=m-1 in the existing Weil-sixfold semiregularity program. Let ζ=c1(O(1)) in rational Chow, and E be the actual ordinary coherent sheaf produced by the deformation step, with true rational Chow Chern character ch_CH(E). The semiregularity/Hodge comparison is the geometric equality
\[
  \operatorname{cl}_{P(Q)}(\operatorname{ch}_{CH}(E))
       =e^{\zeta_B}\,p_B^*\kappa_B,
\]
where κ_B is the required flat rational Betti source character on Y.

Because p_*^B(ζ_B^f)=1 and projection formula holds, define the EXPLICIT algebraic class on Y
\[
 \boxed{C=p_*^{CH}\bigl(\zeta_{CH}^f\,e^{-\zeta_{CH}}
              \operatorname{ch}_{CH}(E)\bigr).}
\]
Canonical Chow/Betti proper Gysin naturality gives
\[
 \begin{aligned}
  \operatorname{cl}_Y(C)
   &=p_*^B\bigl(\zeta_B^f e^{-\zeta_B}
                 e^{\zeta_B}p_B^*\kappa_B\bigr)\\
   &=p_*^B(\zeta_B^f p_B^*\kappa_B)=\kappa_B.
 \end{aligned}
\]
This recovers an algebraic representative of κ_B from the **independently constructed ordinary sheaf**, with no target-cycle selector or surjectivity hypothesis in the theorem. It is a rigorous Betti-to-Chow *construction conditional on the genuine sheaf*, not a theorem that every Betti class has such a sheaf.

## Original fourfold Gysin birth from the same sheaf

For the actual original Weil-type fourfold A and genuine elliptic padding B, set Y=A×B. Let D0=Δ-F1-F2 ∈CH¹(B)_Q, and define the rational graph-Gysin map
\[
  g_{CH}(C)=(p_A)_*\bigl(C_3\cdot p_B^*D_0\bigr)
       \in CH^2(A)_Q,
\]
with its genuine rational Betti counterpart g_B and canonical naturality
\(\operatorname{cl}_A\circ g_{CH}
  =g_B\circ\operatorname{cl}_Y\).

Then
\[
 \boxed{Z_A=g_{CH}\left(
      p_*^{CH}(\zeta_{CH}^f e^{-\zeta_{CH}}
                         \operatorname{ch}_{CH}(E))\right)}
\]
is an actual algebraic source on **original A** with
\(\operatorname{cl}_A(Z_A)=g_B(\kappa_B)\).
The earlier real secant character and graph-difference contraction compute its Weil coordinate:
\[
  W(g_B(\kappa_B))=((d+1)/(2d),0)\ne0,\qquad d>0.
\]
Thus Z_A is NONZERO and produces a second rationally independent algebraic source by genuine CM isogeny action; the previous exact CM Cramer theorem then constructs prescribed rational Weil classes on this A.

The new Lean theorem does **not** assume Z_A or any Chow preimage of κ_B. It assumes the algebraic/Betti projective bundle and graph-Gysin maps together with their standard cycle-class compatibilities, the actual sheaf and its known Betti character, and the geometrically computed fixed secant coefficient.

## Kernel-verified code

Existing file edited IN PLACE: \`GSTWeilFourfoldAuxiliaryExtraction.lean\`.

New proofs:
- \`projectiveBundleChow_extract_fixedChern_character\`: exact projective-bundle projection formula and cancellation (Chow κ version, auxiliary identity only).
- \`projectiveBundleBettiSource_constructChowWitness\`: **noncircular** Betti-only κ_B produces a Chow witness via ordinary sheaf.
- \`projectiveBundleSecantSheaf_birthOnOriginalFourfold\`: same sheaf produces a **nonzero** algebraic source on original A by graph Gysin.
- \`nilpotentChowTwist_inverse_identity\` and \`nilpotentChowTwist_unit\`: finite positive-degree Chern twist \(1+u\), \(u^n=0\), has a CONSTRUCTED inverse \(\sum_{k=0}^{n-1}(-u)^k\), so exponential untwisting needs no externally selected rational inverse.

GitHub CI, using the repository's own pinned Lean without installing Lean locally:
- [Focused Weil seed/transport run 39244582544](https://github.com/kyo-oo/HC-PROOF/actions/runs/39244582544) — **SUCCESS** at \`aa20f3b6e0f230102faa214c10becdb0aecfdca3\`, noncircular Betti-to-Chow witness.
- [Full pinned integration 39244582493](https://github.com/kyo-oo/HC-PROOF/actions/runs/39244582493) — **SUCCESS**, same revision.
- [Focused original-A Gysin 39245098403](https://github.com/kyo-oo/HC-PROOF/actions/runs/39245098403) — **SUCCESS** at \`d875f652c695c45bc38350933c177e7fb50cd88f\`.
- [Full original-A integration 39245098563](https://github.com/kyo-oo/HC-PROOF/actions/runs/39245098563) — **SUCCESS**, same revision.
- First attempted finite nilpotent inverse proof failed only due Lean \`HasDistribNeg\` typeclass simplification recursion. The revised direct \( (-u)^n=(-1)^n u^n=0 \) ring factorization is at \`bdeb25f1b1324d6811cde4e49d8703be27783bca\`: [Focused 39245975087](https://github.com/kyo-oo/HC-PROOF/actions/runs/39245975087) **SUCCESS** and [full 39245975078](https://github.com/kyo-oo/HC-PROOF/actions/runs/39245975078) **SUCCESS**.

## Exact mathematical boundary / next work

The new theorem **proves extraction after the deformed ordinary sheaf is present**. What must be geometrically instantiated for every requested Weil period is the existing source manuscript's projective-germ semiregularity and Hilbert-period transport of the fixed class. The pinned \`openai/math\` source \`301488868beec11bfd897168433b0a64f5258559\`, theorem \`p3sw:projective-germ\`, supplies the intended analytic deformation theorem under full Ext² trace injectivity and rational flat Hodge Chern-character conditions. \`research/records/2026-10-18-weil-all-period-transport-and-original-fourfold.md\` develops their mathematical application and the proper Hilbert-spread proof; those complex-analytic geometric objects are not yet realized as concrete inhabitants of Lean's abstract scheme/Hodge interfaces in this repository.

We must NOT confuse the existence of a twisted/ordinary sheaf at a chosen Weil period with arbitrary Hodge α having a Chow preimage. The sheaf must be independently constructed from the secant geometry and deformation. The all-smooth-projective-X Hodge target is broader even if all Weil fourfold periods are resolved.

**Route status:** substantial noncircular native source-extraction step PROVED and both CI gates green. **Continuing source-construction task:** instantiate the actual coherent sheaf deformation and Hilbert period-spread geometry in Lean for this Weil route, then pursue its extension to arbitrary original X without hidden Hodge-to-Chow selectors.
