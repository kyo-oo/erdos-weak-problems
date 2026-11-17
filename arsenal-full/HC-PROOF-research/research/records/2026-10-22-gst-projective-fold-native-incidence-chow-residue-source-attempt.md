# GST projective fold original-X source attempt — exact native Chow extraction and incidence geometry

- **Date:** 2026-10-22
- **Kind:** Mathbox research-attempt + proof-audit self-review + Wolfram exact computation
- **Program:** Universal original-X rational Hodge algebraicity
- **Base checkpoint:** `69b088f99e4c41201830baa309c75c4ad4bd014c` on `research/gpt6-native-point-primitive-span-20261017`
- **Exact input:** Every connected smooth projective complex original X, arbitrary integer p, rational (p,p) Hodge alpha, an actual rank r>=2 algebraic bundle E on X
- **Exact target:** Produce a genuine independently constructed `Z_alpha^P in CH^p(P_X(O+E))_Q` with actual canonical Betti class `pi^*alpha`, then return it by a genuine Chow operation to the same original X
- **Nearest route:** The [October 22 projective/Hopf bifurcation and arbitrary-bundle Chow-defect reflection](2026-10-22-gst-arbitrary-bundle-hopf-euler-chow-defect-reflection.md) already established an abstract section return and projective-bundle Hodge defect decomposition. This attempt computes an explicit algebraic Chern-polynomial cycle representing that return, constructs new exact incidence sources from morphisms, and audits the K-theoretic source type.
- **Mechanism:** Actual regular zero section, refined Chow intersection/pushforward, diagonal coincidence loci, rational (1,1) and Hard Lefschetz algebraic sources, topological-versus-algebraic K0 comparison
- **Decisive test:** Explicit coefficient selector must annihilate every positive vertical xi-power, while the constructed independent incidence source must detect a nonambient primitive class without assuming its target Chow preimage
- **Verdict:** **Proved as written for the stated extractor, incidence family, and known codimension cases.** The universal all-X/all-p prescribed source construction remains **incomplete**; the vertical-only and topological-K shortcuts are shown insufficient without a new algebraization mechanism.
- **Route disposition:** Vertical-only source factory closed as insufficient. Target-sensitive non-split incidence/moduli/perfect-complex source continuation remains open.

## Durable mathematical results

### Exact original-X native Chow residue (every X, every E)

Use quotient-line projectivization `P=P_X(O_X⊕E)`, `xi=c1(O_P(1))`, and the canonical section `s:X->P` from the O quotient. The **actual** fundamental cycle of the regular closed zero section is

`R_E = c_r(pi^*E^dual ⊗ O_P(1)) = Σ_(j=0)^r (-1)^j pi^*c_j(E) xi^(r-j) = [s(X)]`.

In the actual Chow ring `xi*R_E=0`, `pi_*(R_E)=1`, and for any `Z in CH^p(P)_Q`,

`pi_*(R_E · Z) = s^*Z in CH^p(X)_Q`.

If the canonical Betti class of `Z` equals `pi^*alpha`, the extracted original-X cycle has **exact** canonical class alpha. This is a strong explicit geometric extraction *conditional only on the existence of an actual upstairs Z*, never an arbitrary surrogate cycle map.

### Actual nonambient incidence source

For any smooth target Y of dimension p and genuine X-morphisms `f,g:X->Y`, the operational Chow pullback of the algebraic diagonal yields the constructed source

`Z_(f,g)^P = (f∘pi,g∘pi)^*[Delta_Y] in CH^p(P)_Q`.

This is actual geometry with correct canonical class and actual original-X Chow return; it needs no selected cycle preimage to define it. It does **not** imply such maps exist for every alpha.

In the all-genus positive test `X=C×C`, `A=C×{point}`, `B={point}×C`, `Delta` diagonal and `D=Delta-A-B`, `h=A+B`, genuine coincidence geometry gives an actual upstairs source for `pi^*cl(D)` with

`D·h=0`, `D²=-2g`, and `det Gram(A,B,Delta)=2g`.

Thus for all genus g>0 the source is a new nonambient primitive direction relative to the polarization-only factory. The genus g=0 test correctly degenerates to zero. This is an independently built incidence representative for that prescribed geometric family, not for every middle Hodge alpha.

### Full all-X actual sources in known codimension ranges

For `p=0,1,d-1,d` (valid ranges) genuine upstairs representatives exist independently of assuming the target Chow preimage: use fundamental/point cycles, Lefschetz (1,1) for divisors, and Hard Lefschetz `h^(d-2):H²(X,Q)≅H^(2d-2)(X,Q)` plus Lefschetz (1,1) for all curve classes. The explicit upstairs cycle is `pi^*(D_beta·H^(d-2))` for p=d-1, where beta is the uniquely computed rational (1,1) preimage of alpha. These are previously established algebraicity cases, not newly solved middle codimensions.

### Topological K0 firewall, exact typed result

For any rational alpha, a rational topological virtual bundle `u_alpha^top` always exists via `ch:KU^0(X)_Q≅H^even(X,Q)`, and its pullback to P always exists. But an actual algebraic `v in K0^alg(P)_Q` with Betti Chern-character component `ch_p(v)=pi^*alpha` exists **iff** alpha is already in the original-X canonical Chow image: this follows from the rational algebraic Chern-character isomorphism and the explicit section pullback. Hodge purity and GAGA alone do not algebraize arbitrary topological K-classes.

## Exact computation and scope

- [Complete mathematical LaTeX derivation](../derivations/GST_projective_fold_native_incidence_and_chow_residue_2026-10-22.tex), including scheme-level zero section, Chern signs, operational Chow, canonical Betti and all-X known codimension constructor.
- [Committed exact Wolfram source](../computations/gst_projective_chow_residue_incidence_2026_10_22.wl), source blob `ce94b1539be7e6e5813d853e90e36ac09b931361`, **fetched verbatim from the commit and re-executed** with WolframLanguageEvaluator: **44/44** Chern/Segre coefficient selectors pass for r=1..8, all k=0..r. Symbolic determinant `2g`, primitive square `-2g`, zero hyperplane pairing; g=0..5 boundary tests return the exact expected integers.
- **Review:** Mathbox proof-audit self-review; no independent new mathematical reviewer.
- **Formal scope:** Mathematical proofs of geometry, **not** formal Lean scheme/Chow/analytification certificates. No Lean files modified, no new GitHub Actions Lean run claimed.
- **First unresolved implication:** For arbitrary original smooth projective X and prescribed middle rational primitive Hodge residual, construct a genuine target-sensitive incidence/moduli/perfect-complex algebraic class on P whose genuine original-X Chow residue has the prescribed canonical Betti class (or a provably nonzero new residual pairing). Projectivity alone cannot establish that input.

**Research conclusion:** The true zero-section extractor is completely explicit and independently constructed incidence sources exist and exhibit real primitive geometry. The uniform middle-codimension source-birth theorem does not follow from the fold, and no surjectivity-shaped assumption was inserted to claim otherwise.
