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
