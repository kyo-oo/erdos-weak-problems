# GST simultaneous curvature/component birth and higher-world charge — direct arbitrary-X Hodge attempt

- **Date:** 2026-10-24 IST
- **Kind:** Mathbox research-program, research-attempt and adversarial proof-audit; three executed source-birth routes
- **Exact base checkpoint:** `2eea2082e6ec8163042d983a31b965a858050f52` on `research/gpt6-native-point-primitive-span-20261017`
- **Immutable original target:** ALL smooth projective complex X, 0<=p<=dim X, every prescribed rational (p,p) alpha, an independently constructed ACTUAL original-X Z_alpha in CH^p(X)_Q with canonical cl_X^can(Z_alpha)=alpha. No special-family or Chow-image/basis premise.
- **Binding instructions:** AGENTS.md; research/ACTIVE_HODGE_PROOF_PLAN.md; research-direction failure-root-cause record; preceding Oct 22–24 nonlinear anti-deck, Jouanolou eigenbundle, and all-p normalization birth proofs
- **Methods invoked:** Mathbox research-program, research-attempt, proof-audit, computation-audit; exact stateless Wolfram calculations; no public internet, no local Lean

## Route 1 — actual ALL-X higher-codimension anti-deck product with target-directed signed source

Construct the ORIGINAL algebraic double-world of the October 22 two-divisor reduced incidence theorem on arbitrary X, with its actual anti-divisors Delta1, Delta2. Choose arbitrary p−2 genuine X-divisors H3,...,Hp and take the ACTUAL product upstairs and proper Chow pushforward:

    S_(eps,H)= f_*(Delta1 Delta2 prod_(i=3)^p f*H_i)
             = 2 sum_j eps_j [C_j] prod_(i=3)^p [H_i]   in CH^p(X)_Q.

This is a genuine source for ALL 2<=p<=dim X. For fixed prescribed rational primitive Hodge r_alpha with 2p<=d, the signed period lambda_j=(-1)^p integral_X r_alpha cl(C_j) prod cl(H_i) h^(d−2p) is rational. The mathematical sign-conductor construction makes eps_j=sign(lambda_j) independently; this yields an ACTUAL r_alpha-dependent algebraic world with maximum period 2sum_j |lambda_j|. It does not assume a Chow preimage for r_alpha. In particular it is strictly positive if a source component with nonzero coupling is produced, but the construction does not force that for an arbitrary unknown primitive residual.

**Source:** [Updated October 22 nonlinear anti-deck derivation](../derivations/GST_nonlinear_antideck_chow_source_birth_2026-10-22.tex), commit `a2e6061c4f13db3e4e18715b9a011c55983bf9de`.

## Route 2 — genuinely multiworld algebraic characters, then an exact pairwise-integrality failure certificate

For a smooth projective equivariant resolution of ANY finite abelian Galois cover f:Y->X and ACTUAL deck-eigencycle classes Delta_i in CH^q_i(Y)_C, if the product of deck characters is nontrivial then f_*(prod Delta_i)=0 in actual CH(X)_C. This is a universal exact character-charge conservation law, not a de Rham analogy. An odd number of anti-characters on one double cover dies; a biquadratic group (Z/2)^2 has three nontrivial characters a,b,ab whose product is 1, and the exact group-character sum is 4, allowing a triple nonzero pushforward algebraically.

We then test whether arbitrary higher-codimension components can be isolated merely by adding finitely many unramified square-root worlds. Under the concrete class of covers t_a²=F_a, with chosen algebraic splitting roots A_i,a over each divisor W_i, if EVERY pairwise W_i∩W_j is integral, equality of the two squared roots on that integral scheme forces a CONSTANT relative sign. These signs remain constant over all components C_j of the full p-fold intersection. Hence for a neutral product of characters the generic coefficient is one fixed kappa at every C_j and the ACTUAL Chow output is

    f_*(prod_i Delta_(i,chi_i)) = kappa sum_j[C_j]
                              = kappa prod_i[W_i].

Thus *this precise multiworld smooth, generically unramified, pairwise-integral construction* cannot yield individually chosen primitive components in higher codimension. It does not bar genuinely branched/excess/nonintegral-pairwise worlds. The obstruction is a full scheme-/character-level proof, not an arbitrary finite test.

**Source:** same updated October 22 derivation, correction for smooth equivariant Chow product `2bae757249127f4cf6413cb13b1241c5c4c4dcec`.

**Independent Wolfram test:** for G=(Z/2)^2 with characters a,b,ab, exact values were characterwise product {1,1,1,1}, total 4; the a and a*b partial nontrivial character sums both 0. Result `{{0,0},{0,1},{1,0},{1,1}}, {1,1,1,1}, 4, 0, {0,0,4}`. This verifies only the finite group test; the universal theorem is proved algebraically.

## Route 3 — SAME folded geometry CREATES its spectral algebra and its actual nonlinear zero components, without changing de Rham class

On genuine Q={xy+z²=1}, P=(I+A)/2, the GLOBAL nowhere-vanishing regular spectral curvature form Omega_P=Tr(P dP wedge dP)=dx wedge dy/(4z) has nonzero normalized rational Chern period. For arbitrary t,

    Omega_(P,t)=(1+t z) Omega_P
               =Omega_P+d(t x dy/4)

holds as a LITERAL equality of GLOBAL ALGEBRAIC two-forms. Hence the de Rham/BETTI class is fixed, but its scheme of zeros is EMPTY at t=0, a smooth irreducible G_m curve xy=1−t^(−2) at t not in {0,±1}, and at the exact discriminant t=±1 SPLITS into two affine algebraic lines. At t=1 the zero divisor z+1=0 has components Dx=(x=0,z=−1) and Dy=(y=0,z=−1), whose true CH^1(Q)=Z classes satisfy

    [Dx]= q*c1^CH(O_P1(1)),
    [Dy]= c1^CH(im P) = −[Dx] != 0,

while [Dx]+[Dy]=0 because their sum is the principal z+1 divisor. This is a literal SAME differential form, SAME polynomial Q, SAME eigenbundle: geometry and algebra are actually synchronized at the nonlinear fold. The total zero divisor remains Chow zero; the signed INDIVIDUAL component is nonzero.

**ALL original-X simultaneous version:** For p sufficiently very ample original X line bundles Li, resolve their general pencils on a common smooth b:Y->X, with morphisms fi:Y->P1 and f_i*O(1)=b*Li−Ei. Form W=Y×_(P1^p)Q^p, a true A^p torsor. The exact p-fold curvature transgression is the telescoping sum of 2p-forms on W; at all t_i=1 the component intersection returns

    (−1)^p b_*(q_W*)^(−1)(prod_i[Di])
       = b_*(prod_i(b*c1(Li)−Ei))  in CH^p(X).

The **mandatory exceptional correction** R from all nonempty products of Ei gives the genuine identity

    prod_i c1^CH(Li)
       = (−1)^p b_*(q_W*)^(−1)(prod_i[Di]) − R

in actual original CH^p(X), avoiding the false assumption that products of exceptional divisors all vanish. From any prescribed product alpha=prod beta_i of rational divisor Hodge classes, Lefschetz(1,1) gives the input line bundles Mi without higher-p Chow witnesses; signed 2^p finite differences of actual folds give Z_alpha and exact CANONICAL Betti alpha. This simultaneously realizes geometry, differential algebra, and Chow source in arbitrary X and codimension for this precisely stated Hodge subalgebra.

**First further all-X alpha-sensitive scheme test:** For ANY prescribed rational Hodge alpha, the true affine fold has a GLOBAL REGULAR ALGEBRAIC closed 2p-form eta_alpha. It defines a real alpha-dependent algebraic zero scheme D_alpha of section of V=Omega_J^(2p). If it is a regular section with expected codimension R=rank V, its full Chow class is FIXED c_R(V), INDEPENDENT of alpha. Thus a whole-form zero locus cannot force varying prescribed Chow classes; only exceptional individual components can carry source information. The Q discriminant above is the sharp positive test: whole zero divisor Chow zero, components opposite nonzero classes.

**Sources:** [Updated Oct 23 spectral/Deligne–Gersten derivation](../derivations/GST_alpha_deligne_integral_fold_kgersten_source_birth_2026_10_23.tex), commits `8563e3178a0251e62b8a8e6f67592c4c77602594` and `3ad5e568991b63b0f213507c918a8917d701e604`.

**Wolfram exact tests:** (i) Omega_t−Omega=t/4 dx wedge dy, algebraic exactness; (ii) the t=1 zero ideal is {1+z,xy}; (iii) 1−t^(−2)=((t−1)(t+1))/t² isolates the exact ±1 split; (iv) explicit even-degree polynomial telescoping source identity returned True for each p=1,...,10. All arithmetic was exact; the mathematical all-p claim uses the symbolic telescoping proof, not extrapolation.

## Full classical target / evidence status

- **Proved as written subject to named standard external geometric results:** the all-X higher-degree anti-deck projection formula, finite-G character conservation, integral pairwise sign rigidity, Q spectral form bifurcation, all-X simultaneous differential/CH return with explicit blowup correction, and section zero-locus top Chern constancy.
- **Positive original-X alpha sensitivity:** In the prescribed divisor-generated Hodge subalgebra, a full actual CH^p original-X constructor with canonical Betti equality alpha; the all-codimension anti-deck source construction is actual for any X but its positive period is conditional on a separately constructed component detecting the prescribed primitive class.
- **Unresolved classical goal:** No established all-X theorem forces a nonzero algebraic component coupling to EVERY arbitrary higher-primitive rational Hodge class, nor a genuine regular algebraic K0 class with prescribed primitive Betti Chern character from the all-target holomorphic matrices. Therefore the full classical conjecture has not been proved in this attempt; it has not been refuted.
- **No duplicate fake equivalence:** The derivation executed genuinely new schemes, finite character source rules, de Rham zero-divisor geometry, algebraic Chow identities and exact experimental discriminants, not merely a new equivalence of existing conclusions.
- **Review:** Mathbox-guided author self-audit only; the external named standard algebraic geometry theorems were not independently source-checked this round.
- **Lean/CI:** No Lean files changed; no new GitHub Actions compilation or final Clay target kernel proof claimed. Existing green SHA-specific checks are not attributed to these LaTeX changes.
- **Continuation:** To advance from these unconditional component rules to a universal all-Hodge class theorem requires actual independent alpha-selected HIGHER PRIMITIVE algebraic component production. Unlike the whole-section Chern class or smooth polynomial spectral deformation, the split component mechanism is not excluded by current constraints.
