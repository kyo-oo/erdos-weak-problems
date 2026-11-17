# Mathbox — universal spectral curvature certificate on actual GST affine fold, and exact nonalgebraic gauge test

- **Date:** 2026-10-23 IST
- **Kind:** research-attempt, program checkpoint, proof-audit self-review and exact computation-audit
- **Program/claim IDs:** prose project (no .mathbox ledger registered for this attempt)
- **Base checkpoint:** 8da972dd349902609f772d02de5fdaaf8a077200
- **Actual research input:** arbitrary smooth projective complex original X, p>=1 and arbitrary fixed rational (p,p) Hodge alpha in H^(2p)(X,Q). The proved curvature result in fact works for every rational degree-2p class regardless of Hodge type.
- **Exact goal:** independently construct Z_alpha in CH^p(X)_Q, and prove cl_X^can(Z_alpha)=alpha, without assuming algebraic source, full rank, or a type-changing map.
- **Nearest prior exact theorem:** arbitrary alpha has finite holomorphic involutions on the true Stein affine Jouanolou fold. Genuine regular algebraic involutions return original Chow. The attempt attacks the *alpha-dependent source differential equation itself*, not another finite source-span compiler.
- **Changed operation:** derive an actual algebraic target differential form on the SAME fold, select finite target-dependent holomorphic projector source, and SOLVE the complete global nonlinear curvature-vs-target equation with a genuine holomorphic transgression. Adversarially test whether this actual solution is algebraic by an explicit transcendental gauge of the known nonzero algebraic spectral source.

## 1. Uniform direct construction, proof, and exact source types

Choose true smooth affine Jouanolou q:J->X. Grothendieck affine algebraic de Rham comparison produces a GLOBAL CLOSED REGULAR ALGEBRAIC differential 2p-form eta_alpha with actual de Rham image q*alpha. It is an algebraic differential, NOT itself a Chow cycle.

The rational topological Chern character identifies K_top^0(X) tensor Q with H^even(X,Q). Choose the virtual K-class of total Chern character alpha in degree 2p, clear an integer m, pull to J. Oka-Grauert realizes the two finite topological bundles as holomorphic vector bundles on the Stein space J^an. Holomorphic finite global generation plus coherent H1=0 gives FINITE GLOBAL HOLOMORPHIC matrices A_+, A_- with A²=I by splitting free presentations. Their Grassmann projector normalized differential curvatures have de Rham difference m q*alpha.

Since J^an is Stein, the analytic de Rham complex of GLOBAL HOLOMORPHIC forms computes H^*(J,C): analytic Poincare lemma and Cartan B. The difference of those two closed holomorphic 2p-forms and m eta_alpha is globally exact, proving the LITERAL nonlinear form equation:

    [Tr(A_+(dA_+)^(2p))-Tr(A_-(dA_-)^(2p))]
          / [(2 pi i)^p 2^(2p+1) p!]
     - m eta_alpha = d B_alpha,

with GLOBAL HOLOMORPHIC (2p-1)-form B_alpha. NO original codimension-p Chow source is assumed. Mathematical proof is all-X/all-p, and not an extrapolation from a computation. See [full mathematics](../derivations/GST_alpha_deligne_integral_fold_kgersten_source_birth_2026_10_23.tex), commit e87f030db9a1ad34ea3bd7d6946862021b12520a.

## 2. Exact analytic-vs-algebraic source test on true Jouanolou P1 fold

Let Q={xy+z²=1}, P=1/2[[1+z,x],[y,1-z]], G=[[1,0],[exp(z),1]], P'=G P G^-1, A'=2P'-I.

- P and P' are both actual global holomorphic idempotents, and A'=2P'-I is a global holomorphic involution; P is REGULAR ALGEBRAIC, but P' is NOT regular algebraic.
- Over the actual embedded affine line x=1, y=1-z², the (2,1) entry of P' is (1-z²)/2+z exp(z)-exp(2z)/2, not a polynomial, so P' cannot be regular algebraic.
- Their image line bundles are holomorphically isomorphic. The Chern period is the SAME nonzero value -1: the original P is q*O_P1(-1).
- On chart x!=0, with y=(1-z²)/x, direct calculation gives C(P)=-1/(2x) dx^dz and C(P')=(-1/(2x)+exp(z)/2) dx^dz, where C(P)=Tr(P dP wedge dP).
- Thus C(P')-C(P)=d((x exp(z)/2) dz), an EXACT global holomorphic transgression which is not algebraic.

This is a genuine test of simultaneous folding: a nonzero rational Hodge (1,1) class and fixed affine geometry permit holomorphic source matrices with correct curvature and periods but TRANSCENDENTAL entries, so an arbitrary holomorphic representative is not forced to be an algebraic projector just by Hodge type. It does not rule out an alternative regular algebraic representative; P provides one in this very example.

The exact [Wolfram script](../computations/gst_all_x_spectral_fold_gauge_transgression_2026_10_23.wl) was CREATED at df39538d014761efa097b249f4fb7150ac630bce, then FETCHED unchanged by content blob 69f26cdb065111d9bd9d0f431feab7bb377f82f7 and EXECUTED VERBATIM with Wolfram evaluator: eight named assertions all TRUE, full combined verdict TRUE, exact coefficients printed. No floating point input or finite-range generalization. Author's symbolic check is independent of a Lean kernel theorem but is NOT an independent mathematical referee.

## 3. The source-birth verdict under binding AGENTS.md

- **Attempt outcome:** PROVED the unconditional all-X all-alpha *analytic nonlinear curvature/transgression equation* with a regular algebraic target differential. PROVED an exact nonregular gauge counterexample for automatic promotion of a CHERN-MATCHED chosen holomorphic matrix to regular algebraic.
- **Strongest surviving claim:** genuine SAME FOLD geometry supplies both a regular algebraic global differential form of alpha and finite holomorphic spectral projectors whose differential Chern form matches it up to an EXPLICITLY EXISTING holomorphic primitive. All original X, all degrees 2p>0.
- **Type status:** A_+ and A_- are HOLOMORPHIC, and B is HOLOMORPHIC; eta_alpha is REGULAR ALGEBRAIC. No original-X CH^p source follows from this theorem in general. Its proof does not use the (p,p) property, which is an adversarial check against calling it a Hodge-to-Chow result.
- **First remaining nontrivial implication:** construct from the prescribed (p,p) class alpha a REGULAR ALGEBRAIC source with correct canonical Betti class, not just a global algebraic form plus holomorphic projector. Ordinary curve/divisor channels from 9653c4d already supply this; unrestricted higher primitive source is not supplied by (34).
- **Mathematical audit:** all-X quantified, actual affine scheme vs Stein analytification, K_top vs K_alg, closed form vs Chow, cohomology vs literal differential equation and Chern normalization checked in the paper. Standard external leaves: Grothendieck algebraic de Rham, topological rational Chern-character isomorphism, Oka-Grauert on Stein, Cartan finite generation/coherent vanishing, analytic de Rham. Self-review only, no outside literature audit.
- **CI:** no Lean file edited, no new GitHub Actions compiler check claimed, no sorry or axiom introduced.
- **Route disposition:** holomorphic differential-source stage completed; continuation remains OPEN for a distinct algebraic source-birth mechanism, not a restatement that an arbitrary holomorphic matrix can be algebraized. The explicit gauge counterexample defeats automatic regularity of a *chosen* solution only, not existence of a different algebraic solution for a Hodge target.

