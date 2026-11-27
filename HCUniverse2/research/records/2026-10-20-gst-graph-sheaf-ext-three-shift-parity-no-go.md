# GST Mathbox — transverse CM graph structure sheaves: Ext³-only crossing and shift-parity constraint

- **Date:** 2026-10-20 (IST)
- **Kind:** geometric derived-category necessary-condition test; no-go for a narrowly specified direct-coupling attempt
- **Extends:** [transverse graph ideal local-to-global Ext](2026-10-20-gst-transverse-graph-ideal-ext-local-to-global.md)
- **Base revision:** `3d0f73f14c056f0d8f01ec5597a42293f8dde064` on `research/gpt6-native-point-primitive-span-20261017`
- **Original goal:** universal original-X primitive rational Hodge cycle construction (still unchanged); this is a central-CM sixfold discriminator
- **Evidence:** standard Koszul regular-sequence derivation under the stated true geometric transversality; degree/parity argument exact; no Lean-derived-category instance or independent peer review claimed

## Genuine geometric input and local calculation

Let A be the original smooth projective CM abelian sixfold and Z0,Z1 ⊂ A two transverse embedded abelian threefold graph subgroups. Their intersection P is a finite reduced scheme of length 64 for the recorded pair of slopes 1 and 2+i.

At a geometric crossing, select regular parameters
`R=C[[x1,x2,x3,y1,y2,y3]]`,
with `O_Z0=R/(x1,x2,x3)` and `O_Z1=R/(y1,y2,y3)`. Because the x-variables form a regular sequence on `R/(y1,y2,y3)`, applying `Hom_R(-,R/(y))` to the x-Koszul free resolution gives the actual local sheaf Ext profile

\[
\mathcal Ext^k_A(\mathcal O_{Z0},\mathcal O_{Z1})=
\begin{cases}
\mathcal O_P, & k=3,\\
0, & k\ne3.
\end{cases}
\]

There are no nontrivial sheaf-level degree-one or degree-two crossing extensions between the **bare graph structure sheaves**. The only nonzero sheaf Ext is the codimension-three transverse intersection packet.

The spectral sequence
`H^p(A, sheafExt^q(O_Z0,O_Z1)) => Ext^(p+q)_A(O_Z0,O_Z1)`
collapses because a finite reduced scheme P has vanishing higher coherent cohomology. Consequently

\[
\operatorname{Ext}^k_A(\mathcal O_{Z0},\mathcal O_{Z1})=
\begin{cases}
H^0(P,\mathcal O_P)\simeq\mathbb C^{64},&k=3,\\
0,&k\ne3.
\end{cases}
\]

This is DIFFERENT from the previous calculation for **ideal-to-ideal** Ext (which has global degrees one and two), and different again from `Ext²_A(O_W,O_Zv)` of the specially constructed two-divisor incidence W whose recorded bridge dimension is 16 per edge.

## Exact parity obstruction for naive signed-summand glue

Represent positive and negative coefficients of the eight graph-source K₀ numerator by even and odd cohomological shifts of their structure sheaves. A differential in a genuine dg/twisted perfect-complex presentation must have cohomological degree +1.

For objects A0 and B0 and shifts p,q, a degree-one morphism from `A0[p]` to `B0[q]` lies in

\[
\operatorname{Hom}^{1}(A_0[p],B_0[q])
\cong\operatorname{Ext}^{,1+q-p}(A_0,B_0).
\]

**Opposite K₀ signs mean p and q have opposite parity**, so q-p is odd and 1+q-p is even. But for two transverse graph structure sheaves all even Ext groups vanish: the sole crossing group is Ext³. Thus no nonzero *direct degree-one differential between these opposite-sign graph structure-sheaf summands* can be obtained from their transverse incidence.

An Ext³ crossing class can be shifted into differential degree +1 only when q-p=2, which preserves (rather than reverses) the K₀ sign.

This argument rules out one simple proposed coupling architecture. It does **not** rule out genuinely nonseparable derived objects, longer complexes with auxiliary incidence sheaves, or a filtered/shifted complex using the already-recorded two-divisor W geometry. In particular, the existing 16-dimensional Ext² incidence carrier can have the parity appropriate to a degree-one differential across opposite K₀ signs.

## Direct next mathematical test

Construct an explicit dg/derived incidence packet with extra sheaf terms W on the SEVEN minimal opposite-sign edges and a differential satisfying (d^2=0), calculate its K₀/Chern correction including auxiliary supports, and verify that the resulting middle character remains in the pure Weil projector image. Then calculate the actual Atiyah/Kodaira–Spencer obstruction on one named nonsplit period tangent. Merely writing down seven separate Ext² classes does not establish that their Yoneda products vanish or that the total object deforms.

**Outcome:** restricted direct-gluing mechanism ruled out under exact transversality; alternative incidence-coupled construction remains open. No result about nonalgebraicity of the Weil class or the full Hodge conjecture is asserted.
