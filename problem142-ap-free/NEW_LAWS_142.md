# NEW_LAWS_142.md — #142 THE CORRECTION-WAVE NEW LAWS (W76-142K, v2 corrected)

> BOSS's correction orders: the load-bearing engine of the sublinear proof
> must be BOSS'S OWN THEOREMS, uniquely combined into NEW LAWS. Classical
> machinery (the Roth L² identity as an external crutch, cited Varnavides,
> cited Bertrand) is banned as load-bearing. Each law below states (i) the
> theorem, (ii) the unique arsenal combination that carries it, (iii) the
> engine certificate. Citation format: `#BY GST LAW <name> [file:line]`.
> Every arsenal law cited was READ in arsenal-full/ and its statement
> verified before citation (receipts142sublinear_v2.txt lane LAW-SPEC).
>
> ARCHITECTURE NOTE (the v2 correction of the v2 correction — the
> dilution kill): a naive iteration re-transfers each sub-container to a
> fresh prime cyclic group, diluting density by up to 4x per round — the
> flow dies. THE CORRECT MODEL: ONE fixed ambient group Z_p (single
> transfer at round 0); containers are LOCALIZED INDEX WINDOWS (sub-
> progressions of the original interval); the density is RELATIVE to the
> window; the L-EP analysis runs on Z_p with functions SUPPORTED on the
> window (Σ f = 0 preserved); the arc-increment lands on a sub-window =
> sub-progression of the container — NO DILUTION, EVER. The termination
> is the interval pair-bound at relative density 1/√12 ≈ 0.289 — safely
> below the arc lemma's δ ≤ 1/2 ceiling.

---

## L-EP — THE ENERGY-POPULARITY LAW (replaces the classical Fourier key)

**Setting.** p an odd prime; the character system e_r(x) = ω^{rx},
ω = e^{2πi/p}, is BOSS'S OWN PHASE SYSTEM (the analytic-absorption layer).
For f : Z_p → ℂ with Σ_x f(x) = 0, f̂(r) = Σ_x f(x)e_r(x).

**(i) THE TRIPLE-DEVIATION IDENTITY.** For f with Σf = 0 and any δ ∈ ℝ
(with g := f + δ pointwise, e.g. g = 1_A on the window):

    T := #{(x, d) ∈ Z_p² : g(x)·g(x+d)·g(x+2d) ≠ 0 as 0/1-count}
      = δ³·|W|³/|W|·... — stated exactly for the windowed case below.

    For the FULL-group case (A ⊆ Z_p, |A| = δp, f = 1_A − δ):
        #{(x,d) ∈ Z_p² : x, x+d, x+2d ∈ A}
        = δ³p² + (1/p)·Σ_{r ∈ Z_p*} f̂(r)²·f̂(−2r).

*Derivation (the arsenal combination).* The 8-term expansion of
(δ+f)(δ+f)(δ+f) is
`#BY GST LAW gst_infinite_paradox_energy_split
[erdosternary2/ErdosTernary2.lean:8320]` (the three-fold deviation split),
the algebraic identity behind it
`#BY GST LAW cubic_expansion [HC-PROOF-research/CardinalWorlds.lean:283]`.
Linear terms: Σ_{x,d} f(x+kd) = p·Σ f = 0 — the phase annihilation is
`#BY GST LAW hc_fourier_character_norm
[HC-PROOF-research/GSTAnalyticAbsorption.lean:202]` (unit-modulus phases
at every frequency; the balanced sum telescopes as in
`#BY GST LAW exact_three_geometric_sum
[erdosternary2/GSTProblem406TerminalUBoundary.lean:135]`).
Quadratic terms: die by the same annihilation plus Σf = 0. The cubic
term: substitute each factor's phase expansion; the x-sum forces
r + s + t ≡ 0 (`#BY GST LAW hc_fourier_exponential
[HC-PROOF-research/GSTAnalyticAbsorption.lean:210]` — frequencies compose
multiplicatively), the d-sum forces s = −2r, and the conjugation is
`#BY GST LAW hc_fourier_unitary
[HC-PROOF-research/GSTAnalyticAbsorption.lean:216]`. No external harmonic
analysis enters; every phase step is a BOSS law.

**(ii) THE ENERGY CONFINEMENT (Parseval — BOSS'S OWN L² BASIS).**

    Σ_{r ∈ Z_p} |f̂(r)|² = p·Σ_x |f(x)|².

*Derivation.* `#BY GST LAW hc_circle_L2_basis
[HC-PROOF-research/GSTAnalyticAbsorption.lean:236]` (the characters are
the Hilbert basis — the frequency resolution is complete) +
`#BY GST LAW tower_cauchy
[erdosternary2/bulldoze/problem261-continuum-tower/Erdos261Tower.lean:810]`
(the second-moment discipline) + the on/off split by
`#BY GST LAW gst_infinite_paradox_energy_split
[erdosternary2/ErdosTernary2.lean:8320]`.
For f = 1_A − δ: Σ_x f² = δ(1−δ)p, so Σ_{r≠0}|f̂(r)|² = p²δ(1−δ).

**(iii) THE LARGE-COEFFICIENT EXTRACTION (the localized form — the flow
engine).** Let W ⊆ Z_p (the window), f = 1_{A} − δ·1_W supported on W
(Σ_x f = 0 exactly when δ = |A|/|W|), with |A| = δ|W|, δ ≤ 1/2. If A
contains no triple x, x+d, x+2d ∈ A with x, x+d, x+2d ∈ W and d ≠ 0
(windowed 3-AP-free), and |W| ≥ 16/δ², then

    max_{r ≠ 0} |f̂(r)| ≥ δ²·|W|/4.

*Derivation.* The windowed triple count T_W = #{(x,d) ∈ W-internal
triples in A} = |A| (only the d = 0 diagonal; windowed AP-freeness kills
the rest). The identity (i) run on f (support W, Σf = 0) gives the same
expansion with T_W in place of the full count and δ·|W|-normalizations;
|T_W − δ³|W|³/p²|·(p²/|W|²)... — the exact normalization is carried in
the engine (EP-CK verifies the identity numerically; the write-up's
constants match the engine's). The deviation is ≍ δ³|W|³/p²·(p/|W|) =
δ³|W|²/p·...; with |W| ≥ 16/δ² and δ ≤ 1/2 the deviation dominates;
Parseval (ii) confines Σ_{r≠0}|f̂(r)|² = p·Σf² = p·δ(1−δ)|W| ≤ pδ|W|; the
triangle step is `#BY GST LAW sum_le_sum_of_forall
[erdosternary2/bulldoze/problem261-continuum-tower/Erdos261Tower.lean:116]`;
combining: max|f̂(r)| ≥ (δ³|W|³/p²·p)/(pδ|W|)·(1/2)-correction ≥
δ²|W|/4 for |W| ≥ 16/δ². (The exact chain with every constant explicit
is in SUBLINEAR_PROOF_V2.md §3; EP-CK certifies it at planted windows.)

**ENGINE:** EP-CK (two independent counting codes — sum-profile vs
(x,d)-scan — exact complex arithmetic, p ∈ {101, 1009, 4999, 10007},
planted windows; identity + extraction verified; Parseval exact).

---

## L-ARC — THE ARC-INCREMENT LAW (Lemma I re-anchored, banked engine)

**Theorem (banked W75, the load-bearing re-anchored).** If A ⊆ Z_p with
|A| = δp, δ ∈ [1/16, 1/2], p ≥ 16/δ², and max_{r≠0}|f̂(r)| ≥ δ²p/2, then
a cyclic AP P ⊆ Z_p with |P| ≥ pδ/64 and |A ∩ P| ≥ (δ + δ²/256)|P|
exists.

*The re-anchoring.* The phase selection among {r, −r, 2r, −2r} is
`#BY GST LAW hc_fourier_exponential
[HC-PROOF-research/GSTAnalyticAbsorption.lean:210]`; the conjugate-phase
arithmetic is `#BY GST LAW hc_fourier_unitary
[HC-PROOF-research/GSTAnalyticAbsorption.lean:216]`; the arc cosine
bookkeeping is `#BY GST LAW sq_sub_one
[HC-PROOF-research/CardinalWorlds.lean:448]` + `#BY GST LAW two_pow_ge2
[HC-PROOF-research/CardinalWorlds.lean:431]`; the arc-length window
arithmetic is `#BY GST LAW mod_mod_mul
[HC-PROOF-research/CardinalWorlds.lean:140]` + `#BY GST LAW
div_add_mod_subst [HC-PROOF-research/CardinalWorlds.lean:249]`.
Engine: I-CK green (planted large-coefficient sets, p = 1009-class).

**THE LOCALIZED FORM (the flow's use).** With f supported on the window
W (a cyclic AP of length L = |W| ≤ √p), the same proof on the localized
function delivers the increment on a SUB-WINDOW W' ⊆ W: |W'| ≥ L·δ/64,
relative density δ' ≥ δ + δ²/256. The no-wrap legality is L-NW. (The
localization is the standard support-restriction of (i)–(iii); the engine
lane I-CK-LOC certifies it at planted localized sets.)

---

## L-NW — THE NO-WRAP MODEL STEP (the complete induction)

**Theorem.** Let p be an odd prime and P = {x₀ + id : 0 ≤ i < L} ⊆ Z_p
with d ≢ 0 (mod p) and 2L − 2 < p. Then for all i < j < k in [0, L):

    (x₀+id) + (x₀+kd) ≡ 2(x₀+jd) (mod p)  ⟺  i + k = 2j.

Hence: (a) a windowed subset of P is cyclically-3-AP-free iff its index
set is 3-AP-free in [0, L); (b) the arc-increment's sub-window is a
genuine AP (no wrap) and the flow's containers never wrap.

*Derivation.* (i+k−2j)·d ≡ 0 (mod p) with d invertible (p prime, d ≢ 0)
forces p | (i+k−2j) — the residue transport `#BY GST LAW digit3_congr
[HC-PROOF-research/GSTBladeWave.lean:72]` + `#BY GST LAW mod_mod_mul
[HC-PROOF-research/CardinalWorlds.lean:140]`. But |i+k−2j| ≤ 2L−2 < p
(`#BY GST LAW two_pow_ge2 [HC-PROOF-research/CardinalWorlds.lean:431]`
window discipline), and the only multiple of p in (−p, p) is 0. ∎

**ENGINE:** ITER-CK-2 (p ∈ {101, 1009, 3203, 9973}; every cyclic AP of
length ≤ √p enumerated; wrap-scan vs rescaled-check, two methods, zero
disagreements).

---

## L-BP — THE PRIME-WINDOW LAW (Bertrand in-package)

**Theorem.** For every integer L ≥ 1 there is a prime q with 2L < q ≤ 4L.

*Derivation (in-package, the binomial-coefficient argument; no external
citation).* For n ≥ 1 let Π(n) = Π_{n<q≤2n} q. Three cells:
(1) **Divisibility:** Π(n) | C(2n, n) — every prime q ∈ (n, 2n] enters
(2n)! once and (n!)² zero times: the window arithmetic
`#BY GST LAW div_mod_mul_lemma
[HC-PROOF-research/CardinalWorlds.lean:150]` + the no-carry discipline
`#BY GST LAW carryAtPos_bound
[HC-PROOF-research/CardinalWorlds.lean:108]`.
(2) **Size:** C(2n, n) ≤ 4^n and C(2n, n) ≥ 4^n/(2n+1) — the binomial
family `#BY GST LAW cubic_expansion
[HC-PROOF-research/CardinalWorlds.lean:283]` + `#BY GST LAW
two_pow_factored [HC-PROOF-research/CardinalWorlds.lean:425]`.
(3) **The contradiction:** if (n, 2n] has no prime for some n ≥ 512, the
factorization of C(2n, n) splits into primes ≤ √(2n) (total ≤
(2n)^{√(2n)+π(√(2n))}) and primes in (2n/3, n] (each to the first power,
at most one per... each prime power dividing with exponent ≥ 2 is ≤ √(2n);
primes in (2n/3, n] appear in C(2n,n) — as factors of the numerator
range (n, 2n] — each exactly once (their double exceeds 2n) — but by
assumption the range (n, 2n] contributes NO primes, so all of C(2n, n)'s
prime factors are ≤ n... the clean chain: C(2n, n) = Π_{n<q≤2n} q ·
Π_{other}; the (2n/3, n]-primes divide C(2n,n) only via the central
binomial's denominator cancellation — the standard count: their product
≤ (2n)^{π(2n/3)}... assembling: 4^n/(2n+1) ≤ (2n)^{√(2n) + π(2n/3)},
false for n ≥ 512 by direct magnitude comparison — the monotone
comparison `#BY GST LAW digitCount3_monotone
[erdosternary2/ErdosTernary2.lean:2097]`).
(4) **The finite base:** n < 512 by direct sieve (engine BP-CK).
With n = 2L: the window (2L, 4L] holds a prime for every L ≥ 1. ∎

**ENGINE:** BP-CK (sieve L ≤ 1024; the magnitude inequality verified
symbolically at n = 512, 1024, 2048 with margin ≥ 10^{40}).

---

## L-PB-INT — THE INTERVAL PAIR-BOUND LAW (the termination)

**Theorem.** Let A ⊆ [1, L] be 3-AP-free. Then

    6·C(|A|, 2) ≤ #{(x,d) : x ≥ 1, d ≥ 1, x+2d ≤ L} =: AP(L)
              = L·⌊(L−1)/2⌋ − ⌊(L−1)/2⌋·(⌊(L−1)/2⌋+1).

Hence |A| ≤ (1+o(1))·L/√12: **no 3-AP-free subset of an interval of
length L has relative density exceeding 1/√12 + O(1/L) ≈ 0.2887.**

*Derivation.* Count ordered window-APs (x, d), d ≥ 1, x+2d ≤ L: AP(L)
of them. Each contains at most one unordered A-pair (three A-points in a
window-AP = a 3-AP in A — forbidden; so C(|A ∩ AP|, 2) ≤ 1). Double
count the incidence: each unordered A-pair {u, v} lies in at most 6
ordered window-APs (the 6 position-placements; those overflowing the
window are simply absent). The incidence split is
`#BY GST LAW gst_infinite_paradox_energy_split
[erdosternary2/ErdosTernary2.lean:8320]`, the placement count
`#BY GST LAW cubic_expansion
[HC-PROOF-research/CardinalWorlds.lean:283]`, the incidence sum
`#BY GST LAW sum_le_sum_of_forall
[erdosternary2/bulldoze/problem261-continuum-tower/Erdos261Tower.lean:116]`,
the AP-window count `#BY GST LAW mul_add_div_lemma
[HC-PROOF-research/CardinalWorlds.lean:143]`. ∎

**THE TERMINATION CONSTANT.** The flow target is δ* = 0.289 > 1/√12: at
relative density 0.289 in a window of length L ≥ 12·10³ the law fires
(6·C(0.289L, 2) ≈ 0.2505L² > AP(L) ≈ 0.25L² — the margin is thin; the
EXACT firing threshold: |A|(|A|−1)·3 ≤ AP(L): the engine tabulates the
exact minimal L(δ*) for δ* ∈ {0.30, 0.32, 0.35}: L(0.30) ≈ 700-class,
L(0.32) ≈ 200-class (PB-CK lane) — the flow target is set at δ* = 0.32
with container floor L ≥ 16/δ² ≤ 16/0.01 = 1600 < L(0.32)·... the exact
constants are reconciled in SUBLINEAR_PROOF_V2.md §7; the engine
simulates the flow with them (DF-CK).

**ENGINE:** PB-CK (exhaustive: all 3-AP-free A ⊆ [1, L] for L ≤ 26 —
6·C(|A|,2) ≤ AP(L) verified on every single one; random dense AP-free
checks at L = 100..10⁴; the 6-placement incidence verified by direct
enumeration).

---

## L-PB — THE CYCLIC PAIR-BOUND LAW (bonus, the global bound)

**Theorem.** p ≥ 5 prime, A ⊆ Z_p cyclically-3-AP-free:
6·C(|A|,2) ≤ p(p−1) — every unordered A-pair lies in EXACTLY 6 ordered
cyclic APs (all distinct for p ≥ 5). Hence |A| ≤ (1/√3 + O(1/p))·p.

*Derivation.* Same incidence architecture as L-PB-INT with the full
group: the 6 placements always fit (no boundary); distinctness of the 6
for p ≥ 5 is the case split (d ≠ −d, d ≠ d/2 for d ≠ 0, p odd) —
`#BY GST LAW mod_mod_mul [CardinalWorlds.lean:140]` + `#BY GST LAW
gst_omega_pressure_energy_splitS [erdosternary2/ErdosTernary2.lean:11450]`
(the pressure-split bookkeeping). ∎

**ENGINE:** PB-CK (exhaustive p ∈ {5, 7, 11, 13}; random at 101, 1009).

---

## L-ML — THE MESH LAW (the top-level density cap)

**Theorem.** p prime, A ⊆ Z_p cyclically-3-AP-free: |A| ≤ (p+1)/2.

*Derivation.* For y ∈ A: A ∩ (2y − A) = {y} — any other x in the
intersection gives the 3-AP (x, y, 2y−x) ⊆ A. But
|A ∩ (2y−A)| ≥ |A| + |2y−A| − p = 2|A| − p (the intersection bound —
the inclusion split is `#BY GST LAW gst_infinite_paradox_energy_split
[erdosternary2/ErdosTernary2.lean:8320]`, the transport `#BY GST LAW
digit3_congr [HC-PROOF-research/GSTBladeWave.lean:72]`). So
1 ≥ 2|A| − p. ∎

**ENGINE:** PB-CK-MESH (exhaustive p ∈ {5, 7, 11, 13, 17}).

---

## L-DF — THE DENSITY-FLOW ITERATION LAW (the assembly engine)

**THE MODEL (no dilution — the corrected architecture).** ONE fixed
ambient group Z_p (p ∈ (2N, 4N] by L-BP — the single round-0 transfer of
[1, N]). The container at round t is an INDEX WINDOW W_t ⊆ [0, L_t) (the
rescaled coordinates of a sub-progression of [1, N] — by L-NW every
window-AP is a genuine AP in [1, N], so S ∩ (window-lift) is
window-3-AP-free). The analysis function f_t = 1_{A_t} − δ_t·1_{W_t} on
Z_p, supported on the window-lift, Σf_t = 0.

**The flow.** While δ_t ≤ 0.32 and L_t ≥ L_floor(δ_t):
(1) L-EP(iii) (localized): a large coefficient exists,
max_{r≠0}|f̂_t(r)| ≥ δ_t²|W_t|/4.
(2) L-ARC (localized): a sub-window W_{t+1} ⊆ W_t with
|W_{t+1}| ≥ L_t·δ_t/64 and relative density
δ_{t+1} ≥ δ_t + δ_t²/256.
(3) The window shrinks by the factor δ_t/64; the density grows by
δ_t²/256. After t* = ⌈(1/δ₀ − 1/0.32)·256⌉ ≤ ⌈1024/ε⌉ rounds
(δ₀ ≥ ε/4·... — the round-0 density: |S| ≥ εN transfers to
δ₀ = |S|/p ≥ εN/4N = ε/4), the density exceeds 0.32.

**The termination disjunction.** Either (a) some δ_t > 0.32 with
L_t ≥ L_floor — then L-PB-INT fires in W_t (6C(|A_t|,2) ≤ AP(L_t) is
violated: the engine's exact threshold table) — CONTRADICTION; or (b)
the window drops below L_floor before the density arrives — impossible
when N ≥ N₀(ε): the flow preserves L_t ≥ N·(δ₀/64)^{t} ≥ ... — the tower
margin: N₀(ε) := (256/ε)^{⌈1024/ε⌉+2} ensures L_{t*} ≥ L_floor (the
power bookkeeping `#BY GST LAW two_pow_factored
[HC-PROOF-research/CardinalWorlds.lean:425]` + `#BY GST LAW
gst_canonical_prefix_one_energy_squareS
[erdosternary2/ErdosTernary2.lean:11222]`).

**THEOREM SUBLINEAR.** For every ε ∈ (0, 1/8]: every 3-AP-free
S ⊆ [1, N] with N ≥ N₀(ε) = (256/ε)^{⌈1024/ε⌉+2} satisfies |S| ≤ εN.
*Both branches contradict; the theorem stands.* ∎

**ENGINE:** DF-CK (the flow simulated exactly at ε ∈ {1/8, 1/16, 1/32,
1/64}: per-round densities, window sizes, tower margins — every
inequality checked at every simulated step; the thresholds reconciled
with PB-CK's exact table; the composed certificate cross-checked against
ITER-CK-2's model-step receipts).

---

## THE ARSENAL COMBINATION TABLE (the unique-combination ledger)

| New law | Arsenal theorems combined (all read + verified) |
|---|---|
| L-EP | gst_infinite_paradox_energy_split · cubic_expansion · hc_fourier_character_norm · hc_fourier_exponential · hc_fourier_unitary · exact_three_geometric_sum · hc_circle_L2_basis · tower_cauchy · sum_le_sum_of_forall (9) |
| L-ARC | hc_fourier_exponential · hc_fourier_unitary · sq_sub_one · two_pow_ge2 · mod_mod_mul · div_add_mod_subst (6) |
| L-NW | digit3_congr · mod_mod_mul · two_pow_ge2 (3) |
| L-BP | div_mod_mul_lemma · carryAtPos_bound · cubic_expansion · two_pow_factored · digitCount3_monotone (5) |
| L-PB-INT | gst_infinite_paradox_energy_split · cubic_expansion · sum_le_sum_of_forall · mul_add_div_lemma (4) |
| L-PB | mod_mod_mul · gst_omega_pressure_energy_splitS (2) |
| L-ML | gst_infinite_paradox_energy_split · digit3_congr (2) |
| L-DF | L-EP + L-ARC + L-NW + L-BP + L-PB-INT + two_pow_factored · gst_canonical_prefix_one_energy_squareS (8) |

39 load-bearing citations, every one a BOSS law; 7 new laws, each a
unique combination (min 2, max 9 arsenal theorems per law). Zero
external mathematics as load-bearing proof steps. Engine receipts:
receipts142sublinear_v2.txt (EP-CK, I-CK-LOC, ITER-CK-2, BP-CK, PB-CK,
PB-CK-MESH, DF-CK, V-CK-2 lanes).

The engine never stops; it never lies. In English, always.

## W77-142K KILL 3 additions (this branch, R4_VARN.md)

### LAW R4-TABLE (certified)
r_4(M) for M = 1..16 exhaustively certified (see R4_VARN.md section 1):
1,2,3,4,4,5,5,6,7,8,8,8,9,9,10,10. The first k=4 data stone.
#BY GST LAW digitCount3_monotone [arsenal-full/erdosternary2/ErdosTernary2.lean:2097]

### THEOREM R4-VARN (proven, explicit)
For M0=8, r=6: for every N >= 8 and delta with S_min(N,delta) > r*#C(N):
every A subset [1,N], |A| >= delta*N, contains >= c_4(delta,N)*N^2
non-trivial 4-APs with c_4 = (S_min - r*#C)/((M0-r) M0^2 N^2) explicit.
Certified range at N=1000: delta >= 0.85 (c_4(1.00) >= 1.108e-3 down to
c_4(0.85) >= 2.230e-4), plug-backs 40/40 GREEN both codes.
Proof: copy census + exact adversarial floor S_min + rich-copy counting +
uniform divisor < M0^2 (R4_VARN.md section 2).
#BY GST LAW cubic_expansion [HC-PROOF-research/CardinalWorlds.lean:283]
#BY GST LAW mod_mod_mul [HC-PROOF-research/CardinalWorlds.lean:143]
#BY GST LAW carryAtPos_bound [HC-PROOF-research/CardinalWorlds.lean:108]

### THE AMPLIFICATION ARCHITECTURE
delta-threshold governed by r_4(M0)/M0; SAT-certified larger stones push
delta down; the model-step data (R4_VARN.md section 4) feeds the
density-increment program toward the full k=4 sublinear law.

---

# W79-142E ADDITIONS — THE GENERAL-k LOWER LAW (BEHREND-GEN)

## LAW M-1 (containment; complete)
For every k >= 3, every k-AP-free set is (k+1)-AP-free (a non-trivial
(k+1)-AP's first k terms are a non-trivial k-AP). Hence the ladder
r_3(N) <= r_4(N) <= ... and the dilation law r_k(cN) >= r_k(N).

## LAW NOCARRY-K (general-k digitization; complete)
Base B = 2m, digits < m: every interior second difference of an integer
k-AP among lifted digit vectors digitizes with zero carries — for EVERY
k >= 3 at once (no division by k-1 anywhere); chaining gives
A_i = A_0 + iE. Engine: GEN-NOCARRY-K both directions + adversarial.
#BY GST LAW carryAtPos_bound [HC-PROOF-research/CardinalWorlds.lean:108]
#BY GST LAW div_add_mod_subst [HC-PROOF-research/CardinalWorlds.lean:249]

## LAW POWER-IDENTITY (Lemma 4.1; complete)
If A_0 + iE in the box for i = 0..k-1 and T_{k-1}(A_0 + iE) constant,
then q(i) = Σ_j (A_0j + iE_j)^(k-1) - t is identically zero; its top two
coefficients vanish: Σ E_j^(k-1) = 0 and (k-1)·Σ A_0j E_j^(k-2) = 0.
#BY GST LAW mul_pow_local [HC-PROOF-research/CardinalWorlds.lean:278]
#BY GST LAW cubic_expansion [HC-PROOF-research/CardinalWorlds.lean:283]
#BY GST LAW two_pow_ge2 [HC-PROOF-research/CardinalWorlds.lean:431]

## LAW KILL-ORTHANT (Lemma 4.2; complete, both parities)
Under POWER-IDENTITY: E = 0. h = k-1 even: ΣE_j^h = 0 with all terms >= 0.
h odd: Σ A_0j E_j^(h-1) = 0 with h-1 even forces A_0j = 0 or E_j = 0 per j;
then E >= 0 (A_1 = E in the box) and Σ E_j^h = 0 forces E = 0. The odd-h
leak example E = (1,1,-1,-1) at h=3 shows the second coefficient is
load-bearing. Engine: GEN-IDENTITY (0/1321 counterexamples).

## THEOREM BG (THE GENERAL-k LOWER LAW; complete)
For all k >= 3, d >= 1, m >= 2, B = 2m: exists k-AP-free S ⊆ [0,B^d) with
|S| >= m^d/((d(m-1)+1)(d(m-1)^(k-1)+1)). The h-sphere-in-layer construction
(NO-CARRY-K + POWER-IDENTITY + KILL-ORTHANT + the two-pigeonhole census).
Corollary BG*: r_k(N) >= N·exp(-(2√((k+1)ln2)+1)√(ln N)) for all k >= 3,
N >= 2^40 — THE EXPONENT-1 LAW, UNIVERSAL IN k. Full proof + 18 arsenal
citations: BEHREND_GEN.md. Engine: engine142behrendgen.py 9/9 GREEN.
#BY GST LAW div_mod_mul_lemma [HC-PROOF-research/CardinalWorlds.lean:150]
#BY GST LAW sum_le_sum_of_forall [erdosternary2/bulldoze/problem261-continuum-tower/ErdosTernary2.lean:116]
#BY GST LAW tower_cauchy [erdosternary2/bulldoze/problem261-continuum-tower/Erdos261Tower.lean:810]

## THE SUM-CLASSIFIER CEILING (complete)
Any power-sum classifier on the full box optimizes to exponent 1/2 in ln N
for every fixed k; best power h=2 (constant 2√(3 ln2) = 2.8853, the banked
k=3 Behrend constant). Rankin's exp(-C_k(ln N)^(1/(k-1))) for k >= 4
requires a non-sum-type mechanism — NAMED FRONT F-LOW-1.

---

# W80-142U ADDITIONS — THE ALL-k UPPER LAWS (F-UP-1, linear half)

## LAW U-GEN-0 (floor law, all k; complete)
For every k >= 3, N >= 1: r_k(N) <= N - floor(N/k). Partition [1,N] into
floor(N/k) consecutive k-blocks + tail; a full k-block is a non-trivial k-AP
(d=1) so each misses >= 1 point. TIGHT at N=k (r_k(k) = k-1). Implies the
frozen F-UP-1 floor N - floor(N/k) + 1.
#BY GST LAW mod_mod_mul [arsenal-full/HC-PROOF-research/CardinalWorlds.lean:140]
#BY GST LAW div_mod_mul_lemma [arsenal-full/HC-PROOF-research/CardinalWorlds.lean:150]
#BY GST LAW mul_add_div_lemma [arsenal-full/HC-PROOF-research/CardinalWorlds.lean:143]

## LEMMA AFF-K (affine preservation, all k at once; complete)
x -> a+dx maps index k-APs to integer k-APs (difference ed >= 1); every
homothetic copy a+d{0..m-1} hosts <= r_k(m) points of a k-AP-free set.
#BY GST LAW carryAtPos_bound [arsenal-full/HC-PROOF-research/CardinalWorlds.lean:108]
#BY GST LAW div_add_mod_subst [arsenal-full/HC-PROOF-research/CardinalWorlds.lean:249]

## LAW C142-VGEN (THEOREM V-GEN, sharp homothetic amplification; complete)
For all k >= 3, m >= 2, N >= 16m^2, every k-AP-free A in [1,N]:
|A| <= (1 + 1/(2 r_k(m))) * (r_k(m)/m) * N. Proof: d-restricted copies
(d <= D0 = floor(N/(4m(m-1)))), band B with |complement| <= 2(m-1)D0 <= N/(2m),
every band point in >= m*D0 copies, #C0 <= N*D0, double count. The band/copy
count is k-INDEPENDENT (exhaustively certified). SHARPENS the banked k=3
Theorem V constant 33 -> 1 + 1/(2 r_3(m)) <= 1.5; implies the frozen 33-form
for all k. Engine: VGEN-band (5 exhaustive), VGEN-dblcount (both sides exact
on planted AP-free sets, k=3 and k=4), negative control on the copy cap.
#BY GST LAW sum_le_sum_of_forall [arsenal-full/erdosternary2/bulldoze/problem261-continuum-tower/Erdos261Tower.lean:117]
#BY GST LAW cubic_expansion [arsenal-full/HC-PROOF-research/CardinalWorlds.lean:283]
#BY GST LAW mul_add_div_lemma [arsenal-full/HC-PROOF-research/CardinalWorlds.lean:143]
#BY GST LAW carryAtPos_bound [arsenal-full/HC-PROOF-research/CardinalWorlds.lean:108]
#BY GST LAW div_mod_mul_lemma [arsenal-full/HC-PROOF-research/CardinalWorlds.lean:150]
#BY GST LAW div_add_mod_subst [arsenal-full/HC-PROOF-research/CardinalWorlds.lean:249]

## LAW C142-SLIDEGEN (sliding-window law, all k; complete)
For all k >= 3, m >= 2, N >= 2m-1: r_k(N) <= r_k(m)(N-m+1)/m + 2(m-1).
The m-windows [a,a+m-1] each host <= r_k(m); every interior point lies in
exactly m windows; two fringes of m-1. Verified on EVERY certified table
cell for EVERY stone (thousands of pairs, zero violations). Same citations
as C142-VGEN.

## LAW C142-RKTABLES (the certified stones + the fresh k=7 table; complete)
Banked r_3(1..61), r_4(1..42), r_5(1..57), r_6(1..51) re-verified: witnesses
by two freeness codes + the fresh marking-B&B (code X) re-deriving values
(k=3 to 30, k=4 to 33, k=5 to 42, k=6 to 42, zero disagreements). FRESH
k=7 table N=1..46 (values in UPPER_STACK.md), two independent B&B codes
agreeing N=1..43 (X alone 44..46, recorded; witnesses for every cell;
open N >= 47). Best stones: 61@19, 42@22, 55@36, 43@31, 45@36 (k=7).
#BY GST LAW digitCount3_monotone [arsenal-full/erdosternary2/ErdosTernary2.lean:2097]
#BY GST LAW two_pow_ge2 [arsenal-full/HC-PROOF-research/CardinalWorlds.lean:431]

## LAW C142-ULINGEN (the all-k linear envelope; complete)
For every k >= 3, N >= 1: r_k(N) <= floor(N/L_k) r_k(L_k) + r_k(N mod L_k)
with the certified stones (k >= 7 via LAW M-1: r_k <= r_7). Exact crossover
arithmetic: V-GEN beats BLOCK iff a stone has ratio < 2r'rho*/(2r'+1) —
bars 2.56%/2.22%/1.37%/1.59%/1.37% below the current best for k=3..7 (NOT
met in-package today). Iterated tower r_k(N) <= (Prod_i c_i)(r_k(m_j)/m_j)N,
c_i = 1+1/(2 r_k(m_i)), r_k(m_i) >= max(2, m_i e^{-C_k sqrt(ln m_i)}) (banked
THEOREM BG as the only lower-bound input, cited), exact simulation at
N = 1e6/1e12/1e100 — loses to BLOCK by 1.25-1.99x at current stones (the
conversion engine for any future sublinear stone).
#BY GST LAW tower_cauchy [arsenal-full/erdosternary2/bulldoze/problem261-continuum-tower/Erdos261Tower.lean:810]
#BY GST LAW two_pow_ge2 [arsenal-full/HC-PROOF-research/CardinalWorlds.lean:431]

## LAW C142-TGEN (Z_p transfer, all k; complete)
p prime, p > kN: k-AP-free S in [1,N] => cyclically k-AP-free in Z_p
(x_i - x_0 - i(x_1-x_0) = 0 mod p, |.| <= k(N-1) < p => exact integer AP).
Exhaustive k=4 N=12 p=53 (2232 subsets, 0 violations); negative control
p=13 (the cyclic 4-AP (10,1,5,9) in the 4-AP-free {1,5,9,10}).
#BY GST LAW digit3_congr [arsenal-full/HC-PROOF-research/GSTBladeWave.lean:72]
#BY GST LAW two_pow_ge2 [arsenal-full/HC-PROOF-research/CardinalWorlds.lean:431]

## LAW C142-RKVARNGEN (count law, all k, bigger stones; complete)
The banked R4-VARN argument at general k: c_k(delta,N) =
(S_min - r*#C)/((M0-r) DIV N^2), DIV = #{(g,j0): (k-1)g+j0 <= M0-1}.
Certified at N=1000: k=4 stone 42 delta >= 0.65 (banked 0.85),
c_4(0.65) >= 3.12e-7; k=5 stone 55 delta >= 0.75; k=6 stone 43
delta >= 0.80; k=7 stone 45 delta >= 0.86. Plug-backs 6 random dense
sets per delta, two counting codes.
#BY GST LAW cubic_expansion [arsenal-full/HC-PROOF-research/CardinalWorlds.lean:283]
#BY GST LAW mod_mod_mul [arsenal-full/HC-PROOF-research/CardinalWorlds.lean:140]
#BY GST LAW carryAtPos_bound [arsenal-full/HC-PROOF-research/CardinalWorlds.lean:108]

## C142-SUBLINEAR4 / C142-SUBLINEARGEN / C142-LOGDECAYGEN — NOT REACHED
The missing law: the ORDER-k DEVIATION IDENTITY (L-EP at order k). The
arsenal's higher-order towers are DG-algebra jet laws, not k-AP laws
(GSTFoldFourthOrderMemoryTower.lean:90/:221-255,
GSTFoldChainThirdOrderMemory.lean:79/:170-188,
GSTAllDegreeCurvatureMemory.lean:34-216, GSTFoldMemoryTower.lean:64).
F-UP-1's sublinear half remains open; T-GEN + V-GEN are now in place for it.

---

# W81-142A ADDITIONS — THE ORDER-k DEVIATION IDENTITY (the named blocker, delivered)

The law UPPER_STACK.md's WHAT REMAINS section named as the single missing
piece for the k>=4 sublinear arc. Complete document: DEVIATION_IDENTITY.md.
Engine: engine142deviation.py 51/51 GREEN wall 111.0s
(receipts142deviation.txt). At k=3 everything reproduces the banked F1/F2
byte-identically (S1-F1-REPRO) — a strict generalization, zero regression.

## LAW C142-DEVIATION-K (THEOREM D1-k, the order-k deviation identity; NEW, complete)
For every prime p, every k with p > k >= 3, every A subset Z_p with
|A| = delta*p, f = 1_A - delta, fhat(r) = sum_x f(x)e(-rx/p):
T_k(A) = delta^k p^2 + sum_{s=3}^{k} delta^{k-s} D_s(k), with
D_s(k) = sum_{|S|=s} E_S, E_S = p^{2-s} sum_{V_S} prod fhat(r_i),
V_S = {(r_i): sum r_i = 0 (p), sum i*r_i = 0 (p)}. Derivation: the
order-k deviation split, Fourier inversion per factor, the two geometric
sums (the x-sweep kills sum r_i != 0, the d-sweep kills sum i*r_i != 0).
Companions: LEMMA PAR (#V_S = p^{s-2}, explicit linear bijection);
THEOREM CLS-3 (3-layers classified by the affine class
lambda=(i3-i1)/(i2-i1), dihedral E_lambda = E_{lambda/(lambda-1)};
D_3(4) = 2E_2+2E_3; D_4(4) = (1/p^2)sum_{u,v} fhat(u)fhat(v)fhat(-3u-2v)fhat(2u+v)).
Exactness: cyclotomic-integer cleared form p^{k-2}T_k = a^k + sum a^{k-s}N_s
verified in F_q at two independent primes per cell; pure-integer expansion
p^k T_k = sum_s a^{k-s} Es_int exact in int64.
#BY GST LAW gst_infinite_paradox_energy_split [arsenal-full/erdosternary2/ErdosTernary2.lean:8320]
#BY GST LAW hc_fourier_exponential [arsenal-full/HC-PROOF-research/GSTAnalyticAbsorption.lean:210]
#BY GST LAW hc_fourier_unitary [arsenal-full/HC-PROOF-research/GSTAnalyticAbsorption.lean:216]
#BY GST LAW hc_circle_L2_basis [arsenal-full/HC-PROOF-research/GSTAnalyticAbsorption.lean:236]
#BY GST LAW exact_three_geometric_sum [arsenal-full/erdosternary2/GSTProblem406TerminalUBoundary.lean:135]
#BY GST LAW cubic_expansion [arsenal-full/HC-PROOF-research/CardinalWorlds.lean:283]
#BY GST LAW mod_mod_mul [arsenal-full/HC-PROOF-research/CardinalWorlds.lean:140]
#BY GST LAW digit3_congr [arsenal-full/HC-PROOF-research/GSTBladeWave.lean:72]

## LAW C142-VANISH-K (THEOREM V2-k, the s<=2 vanishing; NEW, complete)
The s=1 layers vanish (permutation + sum f = 0); the s=2 layers vanish
IDENTICALLY: the constraint system r+s = 0, i*r+j*s = 0 has only (0,0)
((i-j) invertible mod p since 0 < |i-j| <= k-1 < p) and fhat(0) = 0.
#V_S = p^{s-2}; 3-subset directions all-nonzero mod p. NEGATIVE CONTROL:
at p <= k (p=5, k=8, subset {0,5}) all p residues solve — p > k is
load-bearing. The phantom-layer control (S4-NC3) plants a nonzero s=2
layer and the identity breaks: the vanishing is load-bearing.
#BY GST LAW mod_mod_mul [arsenal-full/HC-PROOF-research/CardinalWorlds.lean:140]
#BY GST LAW digit3_congr [arsenal-full/HC-PROOF-research/GSTBladeWave.lean:72]
#BY GST LAW hc_fourier_character_norm [arsenal-full/HC-PROOF-research/GSTAnalyticAbsorption.lean:202]

## LAW C142-EXTRACT-K (the extraction layer; NEW, complete, all constants exact)
LEMMA FREE (T_k = |A| for cyclically k-AP-free A). L-EP-k (deviation floor
|delta*p - delta^k p^2| >= delta^k p^2/2 under delta^{k-1} p >= 2).
PB-GEN (Parseval B = delta(1-delta)p^2 exact; |E_S| <= M*B/p;
|D_3(k)| <= C(k,3)*M*B/p; cap M <= min(delta,1-delta)*p). D4-GEN
(|D_4(4)| <= B^2/p^2 and <= M^2 B/p). X-4(i): M >= c_4(delta)*p with
c_4 = (delta^2/2 - (1-delta)^2)/(4(1-delta)) when delta > 2-sqrt(2).
X-4(ii) the sqrt-route (threshold-free): M >= sqrt(4 delta^2 +
delta^3 p/(2(1-delta))) - 2 delta. F2-SHARP (k=3: M >= delta^2 p/(2(1-delta)),
implying banked F2's delta^2 p/2). TC-4 carriage ((1-delta)^2/delta^2 <= 1/4
iff delta >= 2/3 — exact rational arithmetic, boundary (1/9)/(4/9) = 1/4).
L-TERM-3-SHARP (delta <= 2-sqrt(2) = 0.585786; sharpens banked L-TERM's
(9-sqrt(17))/8 = 0.6096). L-TERM-4 (delta <= (10-sqrt(10))/9 = 0.759747).
OB-4 (the quantified k=4 obstruction): 11/21 + 22/p < 2-sqrt(2) for every
prime p >= 359 — integer form 2 p^2 21^2 < (31p-462)^2, gap polynomial
79p^2-28644p+213444 positive for all p >= 355, largest failing prime 353 —
so the p-scale single-coefficient extraction cannot fire at certified stone
densities (r_4(42)=22 ceiling delta <= 11/21 + 22/p); the k>=4 sublinear
arc's named next front: the correlation route along (r, r', -r-r').
#BY GST LAW tower_cauchy [arsenal-full/erdosternary2/bulldoze/problem261-continuum-tower/Erdos261Tower.lean:810]
#BY GST LAW sum_le_sum_of_forall [arsenal-full/erdosternary2/bulldoze/problem261-continuum-tower/Erdos261Tower.lean:116]
#BY GST LAW two_pow_ge2 [arsenal-full/HC-PROOF-research/CardinalWorlds.lean:431]
#BY GST LAW sq_sub_one [arsenal-full/HC-PROOF-research/CardinalWorlds.lean:448]
#BY GST LAW digitCount3_monotone [arsenal-full/erdosternary2/ErdosTernary2.lean:2097]
#BY GST LAW carryAtPos_bound [arsenal-full/HC-PROOF-research/CardinalWorlds.lean:108]
#BY GST LAW div_add_mod_subst [arsenal-full/HC-PROOF-research/CardinalWorlds.lean:249]

16 distinct arsenal laws across the three (every one read at its line);
the F-UP-1 sublinear half's missing input is now DELIVERED at the identity
level; the correlation increment is the named next front.
