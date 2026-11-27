# GST all-codimension nonlinear flag birth, genuine nonambient codimension-three test, and null-Hodge curvature obstruction

- **Date:** 2026-10-24 IST
- **Kind:** Mathbox sustained research-program, three source/obstruction attempts, proof self-audit and exact symbolic calculations
- **Program and claim:** Immutable full classical rational Hodge on the ORIGINAL X: given ANY smooth projective X, any codim p and a SPECIFIED rational Hodge (p,p) alpha, independently construct a genuine CH^p(X)_Q Z_alpha with cl_X^can(Z_alpha)=alpha
- **Exact starting branch checkpoint:** `15934b5d5a9f07606e0ece6c1e8ac48e29838376`, branch `research/gpt6-native-point-primitive-span-20261017`
- **Read sources:** Active AGENTS.md and execution plan, 2026-10-23 root-cause record, 2026-10-22 signed two-divisor antideck source theorem, 2026-10-24 all-p normalization spectral Chow source, 2026-10-24 simultaneous curvature/discriminant source
- **Instructions:** No public internet, no local Lean, math-first latex edits to existing files, no unsupported source generators or surrogate cycle-class map
- **Mathbox workflow:** research-program, research-attempt, proof-audit, computation-audit; author self-review and Wolfram exact symbolic checks

## 1. Positive mechanism: a LOWER-DIMENSIONAL FLAG permits independently signed algebraic Chow components in EVERY codimension

For EVERY smooth projective original X of dimension d and 2<=p<=d, start from a real smooth projective codim-(p−2) complete-intersection FLAG i:Y->X. Let D1,D2 be ACTUAL integral Cartier divisors on Y with reduced pure codim-two intersection C=union_j C_j. The old October 22 theorem can be applied DIRECTLY TO Y (which has dimension d−p+2>=2), producing a finite branched double cover and anti-invariant divisors Delta1,Delta2 with independent generic sheet signs eps_j.

**Exact ORIGINAL-X source, no assumed target Chow witness:**

    F_eps=i_*f_*(Delta1.Delta2)=2 sum_j eps_j [C_j] in CH^p(X)_Q.

For any distinguished component C_k choose eps_k=+1 and all other eps_j=−1; then

    [C_k]=1/4 F_eps + 1/2 i_*([D1][D2]) in CH^p(X)_Q.

The second independent algebraic mechanism is normalization of C's reduced components and sign idempotents. Since X is smooth, pushforward of each normalization structure sheaf is a coherent K0(X) class of leading Chern character [C_j]; hence the signed spectral K0 source satisfies

    ch_p^CH(Xi_eps)=sum_j eps_j[C_j]=F_eps/2

in genuine original-X Chow. This holds even if D1,D2 on Y are NOT restrictions of original-X global Cartier divisors. Canonical Betti naturality is inherited from the scheme proper pushforwards and actual Chern class comparison, NOT Stage2G substitution.

For a prescribed rational primitive residual r in H^{2p}(X,Q), 2p<=d, let lambda_j=(-1)^p integral_X r cl(C_j) h^(d−2p). Choose eps_j=sign(lambda_j) (the original conductor construction genuinely realizes it). Its exact maximum is 2sum_j|lambda_j|; source target dependence and original-X pairing are real. This maximum may be zero, so the new theorem does NOT silently assume all classes are detected.

**Source proof:** [Updated original October 22 nonlinear antideck derivation](../derivations/GST_nonlinear_antideck_chow_source_birth_2026-10-22.tex), positive commit `92d8b2d85e45a6f1dd10236c416961920eeaf0e9` and important normalization-proof correction `efe5927351b8c46deb804bf55c30ac1856f8cc80`.

## 2. Strict sharp genuine projective fivefold test: original pairwise intersections integral, folded codimension-three primitive Chow source NONZERO

Take X=Q4 x P1, with Q4={x0 y0+x1 y1+x2 y2=0} subset P5, P1=[u:v]. Construct ACTUAL integral Cartier divisors W1=(y1=0), W2=(u y2+v x1=0), W3=(v=0). All pairwise intersections W1∩W2, W1∩W3, W2∩W3 are INTEGRAL: W1/W2 with W3 are rank-four integral quadrics; W1∩W2 is the irreducible Rees graph of the rational map [x1:−y2] on the integral quadric threefold W1|Q4. Its ideal (x1,y2) is codim two and regular, so the one-equation projective graph is the actual integral blowup.

The FULL triple intersection is nevertheless the REDUCED UNION of the genuine ruling planes P_A and P_B, each at [u:v]=[1:0]. The flag Y=W3=Q4 is smooth; the original antideck construction on Y gives the ACTUAL signed original-X class

    F=2([P_B x {pt}]-[P_A x {pt}])!=0 in CH^3(Q4 x P1)_Q.

By projective-bundle formula the difference lies in the CH^2(Q4)*[pt] direct summand, and is NOT divisor-generated; its canonical Betti class is nonzero. This is a direct codimension-three example showing the LOWER-DIMENSIONAL flag avoids the earlier pairwise-integral multiworld NO-GO: the former NO-GO assumes splitting of all roots on the ORIGINAL divisors, whereas our double-cover roots only need to split on the final flag.

**Source proof:** same existing Oct22 derivation; commit `d096d86f1081304bfd4d5488f3db9eabaad74879`.

**Independent Wolfram exact check:** quadratic form ranks after y1=0 and y2=0 are both 4; genuine Q4 ruling-plane middle-intersection Gram diag(1,1), difference r has square 2 and signed source S=2r has square 8 and pairing r*S=4; specialization y1=y2=0 yields x0*y0, precisely two reduced components. Exact returned output `{{4,4,2,8,4}, x0*y0, True}`. The general irreducibility/Chow proof is mathematical, not supplied by a finite symbolic rank test.

## 3. Independent adversarial source test: even the ZERO class produces the SAME born Chow components

On the same true Jouanolou Q, let Omega=Tr(P dP wedge dP), a GLOBAL nowhere-vanishing algebraic two-form with nonzero normalized rational spectral Chern period. Construct ACTUAL closed REGULAR algebraic forms:

    eta_nonzero=(z²−1)Omega,   [eta_nonzero]=−(2/3)[Omega]!=0,
    eta_zero=(z²−1)(1−5z²)Omega
            =d(((z−z³)/2) x dy),   [eta_zero]=0.

The identity is literal in the GLOBAL algebraic de Rham complex. Both ZERO SCHEMES contain THE SAME FOUR irreducible multiplicity-one lines over z=±1, each with an ACTUAL nonzero Chow class ±q*h. Thus a target-independent inference from existence of nonzero born zero-divisor components to canonical Betti equality with the input alpha is FALSE even when the algebraic two-form represents alpha perfectly. The geometry is real and useful; the missing link is the actual class-to-component coupling.

**Source proof:** [Updated October 23 spectral/Deligne–Gersten derivation](../derivations/GST_alpha_deligne_integral_fold_kgersten_source_birth_2026_10_23.tex); exact global primitive commit `d9a4f6140b0e69787a4d5783fdc92e4d95459320`.

**Independent Wolfram exact tests:** derivative of B in the actual affine chart x!=0 equals f(z)Omega with f=−1+6z²−5z⁴, the two zero-fiber factors at z=±1 are checked, and the exact 1-form chart identity returned TRUE. The check is of differential formulas, not a proof of an all-X conjecture.

## 4. Precise implications for the full all-X higher-primitive Hodge target

The all-p flag construction is a genuine NEW, original-X algebraic geometry source birth. Its outputs have correctly proven canonical cycle classes. It bypasses the previously proven obstruction for ALL-on-X pairwise-integral simultaneous covers by changing geometry to an intermediate smooth flag. It is an actual improvement of the GST source mechanism, not another formal equivalence.

The nonzero codimension-three Q4 x P1 test checks that this upgrade can create NONAMBIENT algebraic source classes at genuine original-X middle geometry (though that particular class is degree six in a fivefold and not a middle-degree primitive of the total fivefold; its quadric ruling component is primitive on Q4). It is not an unrestricted source theorem.

The zero-class differential demonstrates why merely folding a GLOBAL ALGEBRAIC differential and taking its zero components cannot be used to certify any arbitrary prescribed alpha. The genuine open research route is to supply a noncircular geometric forcing law for alpha-dependent flags/components that has nonzero canonical pairing with any prescribed missing primitive class and then assemble a cycle with exact canonical class. This is not assumed or relabeled a proved theorem.

- **Verdict:** proved as written for the precise flag-fold/normalization and null-form source tests, subject to the previously proven signed-cover theorem and named standard algebraic geometry; **incomplete** for unrestricted all-X rational Hodge algebraicity.
- **Original universal goal:** NOT completed or disproved.
- **Review:** Mathbox author self-audit; no independent referee or Lean kernel certificate.
- **Lean/CI:** No Lean files modified, no new GitHub Actions execution claimed.
- **Route continuation:** Open for genuine alpha-selected flag construction, or a different new source constructor if incidence periods vanish; do not rerun naive component-zero-locus inference or original-ambient only multiple-square-root signs.
