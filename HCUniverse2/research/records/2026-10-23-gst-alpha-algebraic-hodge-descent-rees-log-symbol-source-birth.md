# Mathbox: prescribed-Hodge-to-algebraic-differential descent, Rees log symbol and original-X cycle-source test

**Date:** 2026-10-23 (Asia/Kolkata). **Branch:** `research/gpt6-native-point-primitive-span-20261017`. **Starting commit:** `1105a56724a99750dcf9aebc5c7e7e0482279ef4`. **Exact owner:** for EVERY original smooth projective complex X, codimension p and rational (p,p) Hodge alpha, construct a true rational original-X Chow cycle with canonical Betti alpha. All established GST whole-dimensional fold/Hodge-purity mathematics accepted as proved INPUT, not simulated or downgraded. No public web; no local Lean installation. Mathbox `research-program`, `research-attempt`, `proof-audit`, `computation-audit` skills read. Self-audited, not an independent expert or Lean kernel certificate.

## 1. NEW unconditional actual algebraic differential geometry constructed FROM every Hodge alpha

[Full mathematical proof source](../derivations/GST_hodge_alpha_algebraic_differential_to_rees_milnor_fold_2026_10_23.tex) created in commit `d81975d35037e99f562ef9d1aad4e932d1f5eb1a`, further strengthened for all-X alpha visibility and primitive pairing in commit `838113da6ec55cd3bf8bb05fda950ec1fe280bce`.

Fix ANY original smooth projective X, integer p>=2, and prescribed rational Hodge alpha of type(p,p). Actual algebraic Hodge-to-de Rham spectral-sequence degeneration and Grothendieck algebraic de Rham comparison give alpha in the image of `H^(2p)(X,Omega_X^(>=p))`. On ANY finite affine Zariski cover {U_i}, all finite intersections are affine since X is separated. Therefore one may actually choose a FINITE algebraic Cech-de Rham cocycle `omega_alpha^{a,b}(U_i0...ia) in Gamma(U_i0...ia,Omega_X^b)`, with a+b=2p,b>=p, satisfying the TRUE algebraic differential equation `(delta+(-1)^a d) omega_alpha=0` and canonical full de Rham/Betti class alpha. **No algebraic codim-p Chow class, global algebraic K0 source or special center appears as a premise.** This is a genuine new algebraic differential object, not a cycle and not an asserted Hodge-to-Chow selection.

## 2. SAME nonlinear dimensional fold gives a UNIVERSAL algebraic logarithmic/K-symbol boundary

For any regular center Z with local equations z1,...,zp, true Rees deformation chart z_i=t u_i gives `dlog(z_i)=dlog(t)+dlog(u_i)`. Exterior antisymmetry gives the exact ALL-p formula

`wedge_i dlog(z_i) = wedge_i dlog(u_i) + dlog(t) wedge sum_j (-1)^(j-1) wedge_(i ne j) dlog(u_i)`.

The coefficient of dlog t is the actual algebraic logarithmic residue along the fold divisor t=0, with explicit alternating signs. Under the usual local Milnor K-symbol map `{z1,...,zp}-> wedge_i dlog(z_i)`, successive valuation residues of the regular parameter symbol have terminal multiplicity 1 at the genuine center. The SAME center's original-X Chow class is recovered from exceptional Rees self-intersection: `(-1)^(p-1)b_*[E]^p=[Z] in CH^p(X)`. This fully translates geometry, differential-algebra, local K-theory residue and actual algebraic Chow into one equation set for EVERY actual regular center.

[Wolfram code](../computations/gst_hodge_rees_log_wedge_all_rank_2026_10_23.wl) committed `bb4bdd5c17eb7f8fe4a54b52e8c9aebf81443c7`, blob `6c606ea1ca38cad3a09966976bb985fec705d70d`. Independently expanded the exterior algebra as antisymmetric indexed basis, NOT commuting polynomials, for p=1..12 with 2^p terms per case (through 4096). All **12/12** ranks passed, all alternating residue signs correct, no failures; general all-p theorem proved by explicit wedge expansion.

## 3. Actual arbitrary-X alpha-center visibility and primitive pairing

For ANY smooth center i:Z→X with normal projection pi:N_(Z/X)→Z, the true original-X Hodge class under the actual algebraic normal fold restricts EXACTLY as `alpha|N=pi^*(i^*alpha)` under canonical algebraic de Rham and Betti comparisons. If dimC Z<p, then i^*alpha=0 for EVERY degree-2p class, so the born normal world, regardless of added projective dimensions, has zero NATURAL inherited alpha. Moreover for any genuine beta∈CH^(p-c)(Z) with p<=d/2, the exact paired period is `int_X alpha cl(i_*beta) h^(d-2p)=int_Z i^*alpha cl(beta) h_Z^(d-2p)`. Hence no center with i^*alpha=0 can supply such an alpha-detecting native period.

If alpha is NONZERO rational primitive (p,p), `h^(d-2p+1)alpha=0`, and every actual pure ample-power fold cycle z=c h^p has primitive pairing exactly `int_X alpha z h^(d-2p)=c int_X alpha h^(d-p)=0`. Hodge--Riemann gives a strictly nonzero self-pairing for alpha. Thus folding more fixed hyperplane complete intersections cannot produce that higher primitive direction; genuine new algebraic center data are mathematically needed. This does not rule out a different nonabelian GST source construction.

## 4. Executed first independent attempt to make a general source FROM alpha

Construct actual finite algebraic differential data omega_alpha as in Section 1. Attempt to use that alpha-dependent algebraic form as a varying polynomial section s_alpha of ONE fixed algebraic vector bundle V on X, take its regular zero scheme Z_alpha, and perform an ACTUAL Rees fold at that zero locus. This yields a REAL algebraic scheme but its TRUE CHOW class is `[Z(s_alpha)]=c_top^CH(V)` for EVERY choice of alpha; in nonregular cases the localized refined top Chern class still pushes to c_top(V). Thus **proved as written** that this specific straightforward alpha-dependent graph/zero-section algebraization does not create variable primitive target periods. Its Chern/K0 source class was fixed before alpha was supplied. This is a counterexample to THAT construction's claimed universality, not a refutation of Hodge or GST and not evidence all nonabelian constructions fail.

## Classification / continuation

**Proved as written** under standard projective algebraic Hodge-to-de Rham degeneration, Milnor residue and Chow intersection theorems: (1) every original rational Hodge alpha gives FINITE true algebraic differential descent data, (2) the same Rees dimensional fold generates explicit all-p dlog boundary and local residue multiplicities for a genuine regular center, (3) original alpha visibility and native primitive coupling formulas, (4) fixed-bundle alpha-section route produces alpha-INDEPENDENT Chow class.

**Not derived:** a new algebraic ideal/bundle/K-theory residue built FROM the filtered omega_alpha that can realize an arbitrary unsupported higher primitive alpha through the true original-X cycle-class map. That is the first precisely specified unproved implication; the old split Rees fold theorem already covers centers once they exist. **New direction offered by this attempt:** search for a polynomial/Quillen K-theoretic descent construction whose ALGEBRAIC BUNDLE CLASS changes with alpha, rather than moving a section inside a previously fixed bundle. Do not relabel the algebraic differential cocycle itself a codim-p Chow cycle. No Lean source edits or CI claims in this pass.

