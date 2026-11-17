# GST Mathbox — transverse graph ideals: local Koszul Ext and global incidence boundary

- **Date:** 2026-10-20 (IST)
- **Kind:** exact geometric derived-Hom test, separate from source-completeness theorem
- **Program:** construct native algebraic representatives of prescribed primitive Hodge classes on every original smooth projective complex X; this tests the central CM sixfold's proposed coupled source
- **Base checkpoint:** `00f3952830db94994dcc452fde12beb40e6e1f9c`, active `research/gpt6-native-point-primitive-span-20261017`
- **Related:** [64-torsion derived self-Ext audit](2026-10-19-gst-derived-ideal-torsion-ext2-semi-regularity-audit.md), [three-CM incidence networks](2026-10-19-gst-three-cm-operator-short-weil-incidence-source.md), [raw ideal-source first-order Hodge leak](2026-10-20-gst-derived-cm-graph-hodge-variation-obstruction.md)
- **Evidence label:** complete conditional geometric derivation under standard regular-immersion, Koszul, abelian-scheme cohomology and local-to-global Ext facts; **no Lean derived-category instantiation and no independently peer-reviewed scheme proof** in this record
- **Review:** Mathbox-guided self-audit; the numerical binomial ranks are exact, not numerical fitting

## Precisely typed objects

Let A be a complex abelian sixfold and Z0,Z1 two transverse **abelian subthreefolds**, intersecting in a finite nonempty reduced set P (the active Gaussian graph pair has |P|=64). Let I0,I1 be their coherent ideal sheaves on A, and assume their normal bundles have the standard trivial determinant trivializations. The object in this calculation is **RHom_A(I0,I1)**, NOT the more complicated self-RHom of the derived tensor F or the specialized two-divisor incidence W used by the earlier 16-dimensional bridge theorem.

## Local Koszul computation

At each crossing p in P, transversality supplies regular parameters
`R=C[[x1,x2,x3,y1,y2,y3]]`,
`I0=(x1,x2,x3)`, `I1=(y1,y2,y3)`.
The Koszul resolution on the regular x-sequence, together with regularity of x on R/I1, gives

\[
\mathcal Ext^j_A(O_{Z0},O_A) =
\begin{cases}O_{Z0},&j=3,\\0,&j\ne3,\end{cases}
\quad
\mathcal Ext^j_A(O_{Z0},O_{Z1}) =
\begin{cases}O_P,&j=3,\\0,&j\ne3.\end{cases}
\]

Use `0 -> I1 -> O_A -> O_Z1 -> 0`. The j=3 portion of its Ext long exact sequence is

\[
0\longrightarrow \mathcal Ext^3_A(O_{Z0},I1)
\longrightarrow O_{Z0}\longrightarrow O_P\longrightarrow 0.
\]

The middle map is restriction, so the kernel is the **actual ideal of the crossing set inside Z0**:
\[
\mathcal Ext^3_A(O_{Z0},I1)\simeq I_{P/Z0}.
\]
All lower local Ext sheaves vanish. Applying `0 -> I0 -> O_A -> O_Z0 -> 0` then gives
\[
\mathcal Ext^1_A(I0,I1)=0,\qquad
\mathcal Ext^2_A(I0,I1)\simeq I_{P/Z0}.
\]

For the Hom sheaf, `Hom(I0,O_A)=O_A` (codimension three) and multiplication by a local f sends I0 into I1 precisely when f belongs to I1. At a crossing this uses that the x-ideal remains nonzero in the domain R/I1. Thus
\[
\mathcal Hom_A(I0,I1)\simeq I1.
\]

These are genuine local ring calculations, not free vector-space models.

## Global Ext dimensions for actual abelian graphs

The local-to-global spectral sequence
`H^p(A, ExtSheaf^q(I0,I1)) => Ext_A^(p+q)(I0,I1)`
has only q=0 and q=2 in the lowest relevant degrees. Since Z0 is connected projective and P is nonempty, the only global regular functions vanishing on P are zero:
\[
H^0(Z0,I_{P/Z0})=0.
\]
Consequently
\[
Ext^1_A(I0,I1)\simeq H^1(A,I1),\qquad
Ext^2_A(I0,I1)\simeq H^2(A,I1).
\]

Because Z1 is an abelian subthreefold, the restriction `H^1(A,O_A)->H^1(Z1,O_Z1)` is surjective; exterior powers give surjectivity in every degree. The ideal sequence of Z1 therefore yields
\[
\dim H^q(A,I1)=\binom6q-\binom3q \quad (q=1,2).
\]
In particular the exact resulting ranks are
\[
\boxed{\dim Ext^1_A(I0,I1)=6-3=3,\qquad
       \dim Ext^2_A(I0,I1)=15-3=12.}
\]
They do not equal 64 or the earlier 16-dimensional **different incidence-carrier** Ext² spaces.

## What this decides

A **local ordinary one-extension of the two bare graph ideals** has no sheaf-level Ext¹ crossing class: `ExtSheaf¹(I0,I1)=0`. The three global Ext¹ directions are inherited from `H¹(A,I1)`; they are not 64 independent point-incidence couplings. Thus merely asserting that the 64 intersections permit a rich first-order ordinary extension of I0 by I1 is not a valid geometric proof. The previously constructed **Ext² for two-divisor incidence carriers W** is a *different* geometric construction and is not contradicted by this calculation.

This does not prove a no-go for all possible derived or ordinary sheaves with auxiliary supports. It narrows the correct next object: a nontrivial incidence/shifted derived complex with the **pure projected Weil K0 class**, where the Atiyah obstruction is computed in the actual Ext² of that coupled complex.

## Required independent follow-up

Check the local `ExtSheaf^3(O_Z0,I1)` Koszul model and its orientation against the actual closed immersion data in the Lean scheme library; instantiate the local-to-global Ext spectral sequence and the abelian-cohomology restriction map if formal support exists. Test whether the chosen specialized incidence W has global obstruction-cancellation classes, rather than replacing its Ext² by `Ext²(I0,I1)`.

**Not claimed:** a semiregular family, deformation of the raw F (already ruled out by Hodge leakage), a new original-X Hodge representative, or full Hodge surjectivity.
