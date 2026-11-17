# GST prescribed-alpha polynomial spectral worlds: algebraic source test, quantitative gap and nonlinear eigenline square

- **Date:** 2026-10-24 IST
- **Kind:** Mathbox sustained research-program checkpoint, independent mathematical attempt, precise construction and source-type audit
- **Base checkpoint:** `0d4e7f2fe3442ba292878e74d5cbb8e911096efa`, active `research/gpt6-native-point-primitive-span-20261017`
- **Immutable target:** For EVERY original smooth projective complex X, integer p and prescribed rational (p,p) alpha, construct an ACTUAL Z_alpha in CH^p(X)_Q with canonical cl_X^can(Z_alpha)=alpha; no assumed algebraic witness, Gram full rank or fictitious Stage2G canonical identification
- **Project guidance:** AGENTS.md, ACTIVE_HODGE_PROOF_PLAN.md, Oct 22–24 signed antideck/normalization/flag-fold records and Oct 23 all-target holomorphic Chern spectral theorem
- **Executed skills:** Mathbox research-program, research-attempt, proof-audit and computation-audit. No public internet, no local Lean

## Route 1: construct ACTUAL alpha-dependent finite algebraic worlds without a supplied Chow source

For ANY original X,p,alpha (the proof works for all rational even cohomology classes, Hodge or not), let q:J->X be the genuine smooth affine Jouanolou fold. The previous target-sensitive K_top/Oka–Grauert/Cartan construction produces finite holomorphic idempotents P_+,P_- on the Stein J with ch_p(P_+−P_-)=m q*alpha. Choose a compact finite-cycle carrier K subset J^an containing supports of a basis of H_{2p}(J,Q); H^{2p}(J,Q)->H^{2p}(K,Q) is injective.

Embed affine J as a closed algebraic subset of C^M. By Cartan B each holomorphic entry extends to an entire C^M function; approximate the entire entries by Taylor polynomials, restricted to J. This constructs finite REGULAR ALGEBRAIC matrices Q_(alpha,epsilon) of the same sizes, uniformly approximating P± on K with polynomial algebraic idempotency defect ||Q²−Q||_K->0. Their monic polynomial characteristic equations define ACTUAL finite FLAT spectral covers
    T_(alpha,epsilon)=Spec_J(O_J[lambda]/det(lambda I−Q_(alpha,epsilon))).
For epsilon sufficiently small, on an analytic neighborhood of K the exact Riesz projector onto eigenvalues within |lambda−1|=1/2 is holomorphic and homotopic on K to P±, and its degree-2p Chern character difference equals m(q*alpha)|_K.

This is a genuine prescribed-alpha algebraic polynomial SCHEME construction plus topologically verified LOCAL eigenbundle; it does not itself produce an original-X Chow source with class alpha. All Hodge types and even non-Hodge alpha admit such approximate polynomial data.

**Proof:** [Updated October 23 source derivation](../derivations/GST_alpha_deligne_integral_fold_kgersten_source_birth_2026_10_23.tex), commit `603adda1851b8ddf799dea23b264894846f9e10f`.

## Route 2: exact universal obstruction to the NATURAL whole-spectral return

For ANY commutative smooth affine coordinate ring R and ANY regular Q in Mat_N(R), put A=R[lambda]/chi_Q and let M=coker_A(lambda I−Q), the ACTUAL coherent eigenmodule of the finite characteristic spectral cover pi:T->J. The universal R[lambda] module presentation with lambda acting as Q identifies M with the ACTUAL original free R-module R^N after restriction of scalars:
    pi_* M ≅ O_J^N
as algebraic vector bundles, no approximation or Hodge assumption. Hence for EVERY p>=1,
    ch_p^CH(pi_*M)=0  in CH^p(J)_Q.
This rules out precisely the full unsplit spectral eigenmodule pushforward as a higher-primitive CHOW source. It leaves component selection, nonlinear anti-anti products, and genuine twists untouched.

**Proof:** same derivation; commit `6aa34ad15ce29e398832143882854b8ddfced639`.

## Route 3: concrete original-GST two-sheet monodromy and quantitative spectral-gap obstruction

On TRUE Q={xy+z²=1}, choose Q_eps=[[1,eps*x],[eps*y,0]]. It is an actual regular polynomial matrix converging on any compact core K to diag(1,0), with exact defect Q_eps²−Q_eps=eps²xy I, and characteristic discriminant D_eps(z)=1+4eps²(1−z²). For every positive epsilon its field extension is NONSPLIT quadratic (D has simple zeros, so is nonsquare in C(x,z)). Its regular eigenline sheets exist on the finite etale double-world t²=D, but there is NO nontrivial rational algebraic idempotent commuting with Q_eps on the original Q, because its field-theoretic centralizer is a field.

The deck exchanges E+ and E−, so the ACTUAL anti-class pushes to zero in K0(Q°). The two branch fibers on Q are irreducible PRINCIPAL divisors z=±sqrt(1+1/(4eps²)), each with CH^1 class zero. They escape every finite compact core as eps->0. Thus genuine spectral double-world branching plus epsilon-small polynomial defect does not imply a target-matched nonzero original-X Chow class.

Quantitatively, for any all-target holomorphic P± with compact norm M=max||2P±−I||_K, if a REGULAR ALGEBRAIC pair of idempotents R± were within delta=1/(2 max(1,M)) of P± on K, the explicit conjugating matrices U=RP+(I−R)(I−P) would be invertible and identify topological bundles on K; injection of H^{2p}(J)->H^{2p}(K) would imply that alpha already has an ACTUAL original-X Chow preimage. The contrapositive is a POSITIVE norm gap for nonalgebraic rational classes, despite arbitrarily good polynomial near-idempotents. Along any continuous spectral matrix homotopy the 0/1-cluster Chern class is constant while the contour remains gapped on K; different classes require gap closure somewhere on the CORE, not merely branch creation at infinity.

**Proof:** same derivation, commit `603adda1851b8ddf799dea23b264894846f9e10f`.

## Route 4: ACTUAL nonlinear anti-eigenline-square source on arbitrary original X

For ANY smooth projective original X of dimension>=2, q:J->X and ANY regular 2x2 matrix Q on J with nonzero nonsquare discriminant, take its actual quadratic spectral double-cover, normalize and equivariantly resolve to a smooth algebraic Y->J. Over etale locus the two genuine algebraic rank-one eigenline modules L+,L- are deck exchanged. Extend the line bundles to resolution, equivariantly conjugate, form Delta=[L+]−[L−] in algebraic K0(Y). The genuine proper linear G-theory pushforward vanishes identically: pi_*Delta=0, but the NONLINEAR virtual tensor square Delta^2 is deck invariant and gives a genuine original-X codimension-2 algebraic cycle
    Z_Q=(q*)^−1 ch_2^CH(pi_*(Delta^2)) ∈ CH²(X)_Q .
By actual GRR and rank/ch1 zero of the square,
    q*Z_Q = pi_*(c1(L+)−c1(L−))²    in CH²(J)_Q.
This is an ACTUAL algebraic source constructor from polynomial double-world geometry on EVERY original X, no inserted Hodge-Chow witness. It does NOT show the source has prescribed alpha or positive residual coupling. On the special true Q base, CH²(Q)=CH²(P1)=0, so every such quadratic source on Q itself vanishes (a precise base-vs-world check).

**Proof:** same existing math file commit `e151eb881e098cdf2f2260ea2de2d537a8f6d82b`; external inputs: equivariant characteristic-zero resolution, coherent G0/K0 for smooth schemes, proper GRR, Jouanolou homotopy invariance, topological rational Chern comparison. Self-review only.

## Reproducible exact computation

[Saved and fetched verbatim exact Wolfram test file](../computations/gst_alpha_spectral_cover_source_audit_2026_10_24.wl) commit `237b6919448048c6749a765629b69058673d5153`, observed source blob `d6ab112ca78c1f5d48c0f9dae3fc570b641ed976`. The fetched source was EXECUTED in Wolfram evaluator. Five named assertions all TRUE: generic 2x2 Cayley-Hamilton, polynomial idempotent defect, spectral two-world involution square, deck exchange, and ch₂ of virtual anti-eigenline square. Exact output: characteristic polynomial lambda²−lambda−eps²xy, epsilon=1/10 discriminant (26−z²)/25, and ch₂ coefficient (a−b)². No floating point, sampling inference or fake Hodge certification. These checks support the explicit finite symbolic claims; the uniform all-X theorems are established by their mathematics, not tested case count.

## Strongest result, audit, disposition

**Proved mathematical constructions (self-reviewed, named geometric theorem dependencies):** arbitrary-alpha actual polynomial spectral cover with local topological Chern information on a finite cohomology-detecting compact core; exact free full spectral pushforward; no-rational-sheet obstruction on the explicit Q spectral cover; quantitative no-exact-projector gap for nonalgebraic classes; real all-X quadratic original CH² source and GRR formula.

**First unresolved original target implication:** From a prescribed arbitrary higher-primitive Hodge alpha, produce a CH-producing algebraic component/twist/nonlinear eigenline construction whose TRUE canonical original-X Betti class is alpha, without assuming an algebraic source or a full-rank residual coupling. The polynomial world does not force it; neither zero discriminant nor approximate topological projector gives that implication alone.

**Scope:** The construction is not a full proof or counterexample to the classical rational Hodge conjecture. Nor does the Q no-go obstruct different original varieties and different world-bearing geometric operations. Do not rerun the exact full-spectral-free or small-gap algebraization route unchanged; genuine nonlinear twisting with alpha-sensitive canonical period remains OPEN.

**Repository state:** LaTeX first, existing derivation edited surgically; one computation .wl added and executed; no Lean source changed and no new GitHub Actions/Lean kernel success is asserted. This is Mathbox-assisted author self-review, not independent external referee.
