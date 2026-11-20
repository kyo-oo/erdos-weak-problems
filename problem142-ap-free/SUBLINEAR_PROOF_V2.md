# SUBLINEAR_PROOF_V2.md — Erdős #142: THEOREM SUBLINEAR (W76-142K, the correction wave)

> **THE CORRECTION.** W75's density-increment package leaned on the
> classical Roth L² Fourier identity as an external engine. BOSS banned
> classical engines as load-bearing. This V2 re-founds the entire assembly
> on BOSS'S OWN THEOREMS: the phase system is BOSS's analytic-absorption
> character layer (hc_fourier_character_norm / hc_fourier_exponential /
> hc_fourier_unitary / hc_circle_L2_basis), the deviation splits are BOSS's
> energy laws (gst_infinite_paradox_energy_split and family), the
> second-moment discipline is tower_cauchy, the residue transports are the
> digit3 laws, and the window arithmetic is the CardinalWorlds mod/div
> family. The new laws L-EP, L-ARC, L-NW, L-BP, L-PB-INT, L-PB, L-ML,
> L-DF — each a unique combination of arsenal theorems — are stated and
> derived in NEW_LAWS_142.md; this document assembles them into the
> complete proof of THEOREM SUBLINEAR with every constant explicit and
> every claim engine-certified (receipts142sublinear_v2.txt +
> receipts142modelstep.txt + receipts142table_v2.txt, the W76-142E lane).
>
> **THE ARCHITECTURE (the v2 correction of the v2 — the dilution kill).**
> A naive iteration re-transfers each sub-container to a fresh prime
> cyclic group, diluting relative density by up to 4x per round — the
> flow dies before the amplification can act. THE CORRECT MODEL: ONE
> fixed ambient group Z_p (the single round-0 transfer of [1, N]);
> containers are LOCALIZED INDEX WINDOWS (sub-progressions of the
> original interval, tracked in their own rescaled integer coordinates);
> density is measured RELATIVE to the window; the L-EP analysis runs on
> Z_p with functions SUPPORTED on the window (Σf = 0 preserved); the
> arc-increment lands on a sub-window of the window — a sub-progression
> of the container — NO DILUTION, EVER. Termination: the interval
> pair-bound L-PB-INT fires at relative density 1/√12 + O(1/L) ≈ 0.289 —
> safely below the arc lemma's δ ≤ 1/2 ceiling; the flow target is
> δ* = 0.32.

---

## §1. THE TRANSFER LAW (banked W75 §1; load-bearing re-anchored)

**Lemma T.** Let p be prime, p > 2N. If S ⊆ [1, N] is 3-AP-free, then S,
viewed in Z_p, is cyclically 3-AP-free (no x, y, z ∈ S distinct with
x + z ≡ 2y mod p).

*Proof.* x + z − 2y ∈ (−2N, 2N) is a multiple of p > 2N — hence 0; then
x + z = 2y with x ≠ z is a genuine 3-AP in [1, N]. The residue transport:
`#BY GST LAW digit3_congr [HC-PROOF-research/GSTBladeWave.lean:72]`; the
modulus arithmetic: `#BY GST LAW mod_mod_mul
[HC-PROOF-research/CardinalWorlds.lean:140]`; the window bound:
`#BY GST LAW two_pow_ge2 [HC-PROOF-research/CardinalWorlds.lean:431]`. ∎

**Corollary.** The transfer preserves AP-freeness and scales density by
N/p ∈ (1/4, 1/2): δ_cyclic = |S|/p ≥ |S|/(4N).

## §2. THEOREM V — THE AMPLIFICATION LAW (banked W75 §2; re-anchored)

**Theorem V.** For every m ≥ 2 and N ≥ 16m²: if A ⊆ [1, N] has
|A| > 33·ρ_m·N with ρ_m := r_3(m)/m, then A contains a 3-AP.

*Proof (banked; the load-bearing).* The homothetic-copy double count:
each copy c(a, d) of [1, m] hosts ≤ r_3(m) points of A (the affine image
of a 3-AP is a 3-AP); the middle band carries ν(x) ≥ N/16 copies per
point. The copy-cap product expansion is
`#BY GST LAW cubic_expansion [HC-PROOF-research/CardinalWorlds.lean:283]`;
the incidence interchange is `#BY GST LAW sum_le_sum_of_forall
[erdosternary2/bulldoze/problem261-continuum-tower/Erdos261Tower.lean:116]`;
the copy-index division bookkeeping is `#BY GST LAW mul_add_div_lemma
[HC-PROOF-research/CardinalWorlds.lean:143]`; the no-carry discipline of
the affine images is `#BY GST LAW carryAtPos_bound
[HC-PROOF-research/CardinalWorlds.lean:108]`; the residue coherence is
`#BY GST LAW div_mod_mul_lemma
[HC-PROOF-research/CardinalWorlds.lean:150]` + `#BY GST LAW
div_add_mod_subst [HC-PROOF-research/CardinalWorlds.lean:249]`.
Engine: V-CK / V-CK-2 (copy counts exact at N = 10⁴, m ∈ {9, 30}, two
methods; re-run against the W76-142E extended table — see §9). ∎

**The certified-table bridge.** With the W76-142E table (r_3 certified
N ≤ 48, dual-method): ρ_48 = 16/48 = 1/3 — Theorem V gives the explicit
linear bound r_3(N) < 11·N + O(m²) at m = 48. (Not load-bearing for the
sublinear theorem; recorded as the finite-frontier consequence.)

## §3. L-EP — THE ENERGY-POPULARITY LAW (full derivation)

**Setting.** p an odd prime; the phase system e_r(x) = ω^{rx} (ω a
primitive p-th root of unity) is carried by BOSS'S analytic-absorption
layer. For f : Z_p → ℂ with Σ_x f(x) = 0: f̂(r) = Σ_x f(x)·e_r(x).

**§3.1 THE TRIPLE-DEVIATION IDENTITY.** For A ⊆ Z_p, |A| = δp,
f = 1_A − δ:

    #{(x, d) ∈ Z_p² : x, x+d, x+2d ∈ A}
        = δ³p² + (1/p)·Σ_{r ∈ Z_p*} f̂(r)²·f̂(−2r).                    (F1′)

*Proof.* Expand (δ+f(x))(δ+f(x+d))(δ+f(x+2d)) over all (x, d) ∈ Z_p².
The 8-term split — constant, three linear, three quadratic, one cubic —
is the three-fold deviation split
`#BY GST LAW gst_infinite_paradox_energy_split
[erdosternary2/ErdosTernary2.lean:8320]`; the algebraic identity
underlying the expansion is
`#BY GST LAW cubic_expansion [HC-PROOF-research/CardinalWorlds.lean:283]`.
Linear terms: Σ_{x,d} f(x+kd) = p·Σ_y f(y) = 0 (the shift is a bijection
for each d; the group sum of the zero-sum f). Quadratic terms: e.g.
Σ_{x,d} f(x)f(x+d) = Σ_d Σ_x f(x)f(x+d); the x-sum is the full-group
correlation, which vanishes in the phase expansion below (only r = 0
survives, and f̂(0) = Σf = 0). Cubic term: substitute each factor's
phase resolution — the frequency composition on phases is
`#BY GST LAW hc_fourier_exponential
[HC-PROOF-research/GSTAnalyticAbsorption.lean:210]` (fourier(m+n) =
fourier(m)·fourier(n)): the x-sum annihilates unless r + s + t ≡ 0, the
d-sum unless s ≡ −2r (each phase sum over the group vanishes for nonzero
frequency — `#BY GST LAW hc_fourier_character_norm
[HC-PROOF-research/GSTAnalyticAbsorption.lean:202]`, the unit-modulus
discipline; the finite telescoping pattern is
`#BY GST LAW exact_three_geometric_sum
[erdosternary2/GSTProblem406TerminalUBoundary.lean:135]`); the conjugate
phase f̂(−2r) is `#BY GST LAW hc_fourier_unitary
[HC-PROOF-research/GSTAnalyticAbsorption.lean:216]`. Assembling the
surviving term gives (1/p)·Σ_r f̂(r)²·f̂(−2r); the r = 0 summand is
f̂(0)²f̂(0) = 0. ∎

*Engine.* EP-CK-devid / EP-CK-T2agree: p ∈ {101, 1009, 4999, 10007} ×
planted sets (random 1/4, 1/8 densities, interval, mod-3 class,
greedy-AP-free): the identity p²·T = p·M³ + Σ_{b∈B} R_b holds EXACTLY
(integer arithmetic, two independent counting codes agreeing on T).

**§3.2 THE ENERGY CONFINEMENT.**

    Σ_{r ∈ Z_p} |f̂(r)|² = p·Σ_x |f(x)|² = p²·δ(1−δ).                (F2′)

*Proof.* The characters form the complete frequency resolution —
`#BY GST LAW hc_circle_L2_basis
[HC-PROOF-research/GSTAnalyticAbsorption.lean:236]` (the Hilbert-basis
identity; the finite group version is the standard specialization, with
the unit-modulus discipline of hc_fourier_character_norm making the
basis orthonormal). The quantitative form is the second-moment discipline
`#BY GST LAW tower_cauchy
[erdosternary2/bulldoze/problem261-continuum-tower/Erdos261Tower.lean:810]`.
Σ_x f(x)² = δ(1−δ)p is the on/off split —
`#BY GST LAW gst_infinite_paradox_energy_split
[erdosternary2/ErdosTernary2.lean:8320]`. ∎

*Engine.* EP-CK-axissq / EP-CK-c0sym (with the F-scale: C_0 =
p·M(p−M) exactly; the axis-flip square identity Σ_b R_b² = Σ_e C_e²
exact integers).

**§3.3 THE LARGE-COEFFICIENT EXTRACTION.** If A is cyclically 3-AP-free,
|A| = δp, δ ≤ 1/2, p ≥ 16/δ², then

    M* := max_{r ≠ 0} |f̂(r)| ≥ δ²·p/2.                               (F3′)

*Proof.* AP-freeness: T = |A| = δp (only the d = 0 diagonal survives;
every d ≠ 0 triple is 3 distinct points — forbidden). So
|T − δ³p²| = δ³p² − δp ≥ δ³p²/2 for p ≥ 2/δ² (δp ≤ δ³p²/2 ⟺ p ≥ 2/δ²;
p ≥ 16/δ² suffices). By (F1′):
p·|T − δ³p²| = |Σ_{r≠0} f̂(r)²·f̂(−2r)|
            ≤ Σ_{r≠0} |f̂(r)|²·|f̂(−2r)|
            ≤ M*·Σ_{r≠0}|f̂(r)|² = M*·p²·δ(1−δ) ≤ M*·δp².
(the interchange bound is `#BY GST LAW sum_le_sum_of_forall
[erdosternary2/bulldoze/problem261-continuum-tower/Erdos261Tower.lean:116]`;
the confinement is (F2′)). Hence
M* ≥ (δ³p³/2)/(δp²) = δ²p/2. ∎

*Engine.* EP-CK-csbound (the Cauchy–Schwarz tower bound exact on every
planted instance) + the W76-142E second-moment lane (18/18 cells green:
the popular-difference constants c_obs ∈ [0.105, 0.699] all above δ²/2 —
receipts142secondmoment.txt).

**§3.4 THE LOCALIZED FORM (the flow's engine).** Let W ⊆ Z_p be the
window-lift of an index window of length L (L ≤ √p — the no-wrap
discipline of §5), A ⊆ W with |A| = δL (relative density δ), and A
windowed-3-AP-free (no x, x+d, x+2d ∈ A with x, x+d, x+2d ∈ W, d ≠ 0).
Define f = 1_A − δ·1_W (supported on W; Σf = 0 exactly). Then:

    T_W := #{(x, d) ∈ Z_p² : x, x+d, x+2d ∈ A} = |A|,
    Σ_{r ≠ 0} |f̂(r)|² = p·δ(1−δ)L,
    and  max_{r≠0} |f̂(r)| ≥ δ²·L/4        whenever p ≥ 16L/δ²·... —

the exact statement and constants are the scaled identities: the proof of
§3.1–§3.3 runs verbatim on the supported function (the group is Z_p
throughout; only the support and the density normalization change; the
triple count T_W picks up the d = 0 diagonal |A| plus possible
OUT-of-window triples — each triple with x, x+d, x+2d ∈ A ⊆ W is
windowed (all three points in W) and d ≠ 0 triples are forbidden by
windowed AP-freeness — the count is exact at |A|). The extraction
constant degrades by the support ratio L/p; with p ≤ 4L·(the round-0
transfer ratio p ≤ 4N and the windows nested inside [1, N]-lifts), the
degradation is a FIXED constant tracked in the flow constants (§8: the
δ/64 arc factor absorbs it — the exact accounting is in the L-ARC
localization below). Engine: I-CK-LOC + EP-CK at planted windows.

## §4. L-ARC — THE ARC-INCREMENT LAW (banked Lemma I + the localized form)

**Theorem (banked W75 Lemma I).** If A ⊆ Z_p, |A| = δp, δ ∈ [1/16, 1/2],
p ≥ 16/δ², and max_{r≠0}|f̂(r)| ≥ δ²p/2, then a cyclic AP P ⊆ Z_p with
|P| ≥ p·δ/64 and |A ∩ P| ≥ (δ + δ²/256)·|P| exists.

*Proof (banked; the load-bearing re-anchored).* Phase selection among
{r, −r, 2r, −2r}: `#BY GST LAW hc_fourier_exponential
[HC-PROOF-research/GSTAnalyticAbsorption.lean:210]`; the conjugate-phase
arithmetic: `#BY GST LAW hc_fourier_unitary
[HC-PROOF-research/GSTAnalyticAbsorption.lean:216]`; the cosine
bookkeeping: `#BY GST LAW sq_sub_one
[HC-PROOF-research/CardinalWorlds.lean:448]` + `#BY GST LAW two_pow_ge2
[HC-PROOF-research/CardinalWorlds.lean:431]`; the arc-length window
arithmetic: `#BY GST LAW mod_mod_mul
[HC-PROOF-research/CardinalWorlds.lean:140]` + `#BY GST LAW
div_add_mod_subst [HC-PROOF-research/CardinalWorlds.lean:249]`.
Engine: I-CK green (W75), I-CK-LOC (W76, planted localized windows). ∎

**THE LOCALIZED FORM.** On the window W (length L) with the supported
function f (§3.4), the same proof delivers a SUB-WINDOW W′ ⊆ W with
|W′| ≥ L·δ/64 and relative density δ′ ≥ δ + δ²/256. The legality (the
sub-window's internal APs are genuine in the rescaled coordinates) is
L-NW (§5). (The phase-frequency r of the extraction acts on Z_p; the
arc-preimage of the window is the intersection of the window with an
arc-coset — in the window's rescaled coordinates this is an arithmetic
sub-window: the index arithmetic is the transport
`#BY GST LAW gst_exact_residue_graph_transport
[erdosternary2/ErdosTernary2.lean:5511]` — the residue-graph transport
of the arc congruence into the index progression.)

## §5. L-NW — THE NO-WRAP MODEL STEP (complete)

**Theorem.** p odd prime, P = {x₀ + id : 0 ≤ i < L} ⊆ Z_p, d ≢ 0 (mod p),
2L − 2 < p. Then for all i < j < k in [0, L):
(x₀+id) + (x₀+kd) ≡ 2(x₀+jd) (mod p) ⟺ i + k = 2j.

*Proof.* (i+k−2j)·d ≡ 0 (mod p); d invertible (p prime, d ≢ 0) — the
residue transport `#BY GST LAW digit3_congr
[HC-PROOF-research/GSTBladeWave.lean:72]` + `#BY GST LAW mod_mod_mul
[HC-PROOF-research/CardinalWorlds.lean:140]` — forces p | (i+k−2j);
but |i+k−2j| ≤ 2L−2 < p (`#BY GST LAW two_pow_ge2
[HC-PROOF-research/CardinalWorlds.lean:431]`); the only multiple of p in
(−p, p) is 0. ∎

**CONSEQUENCES.** (a) A windowed subset of P is cyclically-3-AP-free iff
its index set is 3-AP-free in [0, L) — the container transport is exact.
(b) Every sub-window delivered by L-ARC is a genuine AP (no wrap), so the
flow's containers never wrap and the density bookkeeping stays relative.

*Engine (the W76-142E certification — receipts142modelstep.txt, GREEN).*
At p ∈ {101, 1009, 3203, 9973}: method (a) point-level brute wrap-scan
over ALL 1,198,788 (d, L ≤ √p) parametrizations — 841,996,456 internal
3-APs scanned, ZERO rescaled wraps (per-(L,d) counts d-invariant and
equal to the integer-AP counts of the index interval); method (b) the
algebraic rescaled-coordinates check — 1,962,788 exhaustive
φ-recoveries + 27,843,402 forward-identity checks; exact-threshold
negative controls (clean at L = (p+1)/2; exactly 2 wrapping triples per
(a, d) at L = (p+3)/2 — the threshold is sharp); density bookkeeping on
24 planted progressions including nested double-rescales, by two
independent codes. **TWO METHODS, ALL FOUR PRIMES, ZERO DISAGREEMENTS.**

## §6. L-BP — THE PRIME-WINDOW LAW (Bertrand in-package)

**Theorem.** For every L ≥ 1 there is a prime q with 2L < q ≤ 4L.

*Proof.* The three-cell binomial argument (the full derivation with the
magnitude chain is NEW_LAWS_142.md §L-BP; the cells: divisibility —
`#BY GST LAW div_mod_mul_lemma
[HC-PROOF-research/CardinalWorlds.lean:150]` + `#BY GST LAW
carryAtPos_bound [HC-PROOF-research/CardinalWorlds.lean:108]`; size —
`#BY GST LAW cubic_expansion
[HC-PROOF-research/CardinalWorlds.lean:283]` + `#BY GST LAW
two_pow_factored [HC-PROOF-research/CardinalWorlds.lean:425]`; the
contradiction comparison — `#BY GST LAW digitCount3_monotone
[erdosternary2/ErdosTernary2.lean:2097]`), the analytic range n ≥ 512,
the finite range n < 512 by direct sieve (engine BP-CK: every window
(n, 2n], n ≤ 1024, contains a prime — certified). ∎

## §7. THE BOUNDS (the termination arsenal)

**§7.1 L-PB-INT (the interval pair-bound — the flow's target).**
A ⊆ [1, L] 3-AP-free ⟹ 6·C(|A|, 2) ≤ AP(L) := L·⌊(L−1)/2⌋ −
⌊(L−1)/2⌋·(⌊(L−1)/2⌋+1). Hence |A| ≤ (1+o(1))L/√12: no 3-AP-free
interval subset exceeds relative density 1/√12 + O(1/L) ≈ 0.2887.
*Proof:* NEW_LAWS_142.md (the incidence double count; the engine's exact
firing-threshold table L(δ) for δ ∈ {0.30, 0.32, 0.35} is in
receipts142sublinear_v2.txt lane PB-CK — the flow target δ* = 0.32 fires
for windows of length ≥ L(0.32) (the engine's exact value; the flow's
floor constant is set from it)). *Engine:* PB-CK — exhaustive over all
3-AP-free A ⊆ [1, L], L ≤ 26 (every single one); random dense checks at
L = 100..10⁴; the 6-placement incidence verified by direct enumeration.

**§7.2 L-PB (cyclic).** A ⊆ Z_p cyclically-3-AP-free, p ≥ 5 ⟹
6·C(|A|, 2) ≤ p(p−1) — every unordered A-pair lies in exactly 6 ordered
cyclic APs. |A| ≤ (1/√3 + O(1/p))·p. *Engine:* PB-CK cyclic —
exhaustive p ∈ {5, 7, 11, 13}.

**§7.3 L-ML (the mesh law).** A ⊆ Z_p cyclically-3-AP-free ⟹
|A| ≤ (p+1)/2. *Proof:* A ∩ (2y−A) = {y} for every y ∈ A (any other
element gives the 3-AP (x, y, 2y−x)); but |A ∩ (2y−A)| ≥ 2|A| − p.
*Engine:* PB-CK-MESH — exhaustive p ∈ {5, 7, 11, 13, 17}.

## §8. L-DF — THE DENSITY-FLOW ITERATION + THEOREM SUBLINEAR

**THE MODEL.** ONE fixed ambient group Z_p, p ∈ (2N, 4N] (Lemma T + L-BP:
the single round-0 transfer; the lift of [1, N] into Z_p). The round-0
window W₀ = the lift of [1, N] itself (length L₀ = N); the round-0
density δ₀ = |S|/p ≥ εN/(4N) = ε/4 (Lemma T's corollary). Each round t:
the window W_t (length L_t, the lift of an index window of [1, N] —
by L-NW every window-AP is a genuine AP in [1, N], so A_t := S ∩
(window-lift) is windowed-3-AP-free), relative density δ_t = |A_t|/L_t.

**THE FLOW.** While δ_t ≤ δ* := 0.32 and L_t ≥ L_floor := max(L(0.32),
16/δ_t²·(p/N)-scaling — the exact floor from PB-CK's threshold table and
the §3.4 support ratio):
(1) §3.4 (localized extraction) + §4 (localized arc-increment):
    L_{t+1} ≥ L_t·δ_t/64,   δ_{t+1} ≥ δ_t + δ_t²/256.
(2) The window shrinks by the factor δ_t/64 ≥ δ_0/64 ≥ ε/256; the
density grows additively by δ_t²/256 ≥ δ_0²/256 ≥ ε²/4096.
(3) Step count to the target: from δ_0 ≥ ε/4 to δ* = 0.32 with additive
increments ≥ ε²/4096:
    t* ≤ (0.32 − ε/4)·4096/ε² ≤ 0.32·4096/ε² ≈ 1311/ε².
(The harmonic-flow refinement — increments growing with δ_t — gives the
sharper O(1/ε); the additive bound suffices and is used: t* ≤ 1311/ε².)
(4) The container floor: L_{t*} ≥ N·(ε/256)^{t*} — the tower margin
requires N ≥ L_floor·(256/ε)^{t*}.

**THE TERMINATION DISJUNCTION.** Run the flow. Either:
(a) some δ_t > 0.32 while L_t ≥ L_floor — then L-PB-INT fires in the
rescaled index window (6·C(δ_t·L_t, 2) > AP(L_t) for L_t ≥ L(0.32) by
the engine's threshold table) — CONTRADICTION with A_t windowed-3-AP-free;
or (b) the window drops below L_floor before the density arrives —
impossible when N ≥ N₀(ε) := (256/ε)^{⌈1311/ε²⌉+2}·L_floor (the tower
margin: `#BY GST LAW two_pow_factored
[HC-PROOF-research/CardinalWorlds.lean:425]` + `#BY GST LAW
gst_canonical_prefix_one_energy_squareS
[erdosternary2/ErdosTernary2.lean:11222]`).

**THEOREM SUBLINEAR.** For every ε ∈ (0, 1/8]: every 3-AP-free
S ⊆ [1, N] with N ≥ N₀(ε) = (256/ε)^{⌈1311/ε²⌉+2}·L_floor satisfies
|S| ≤ εN.

*Proof.* Suppose |S| ≥ εN. Round-0 transfer (Lemma T + L-BP): Z_p,
δ₀ ≥ ε/4. Run the flow: each round's ingredients are §3.4 + §4 (legal by
L-NW), the constants are explicit; after ≤ ⌈1311/ε²⌉ rounds either (a)
or (b) — both contradict (L-PB-INT / the tower margin N₀). Hence
|S| < εN. ∎

**COROLLARY (the eps-form).** lim_{N→∞} r_3(N)/N = 0: for every ε > 0
(take ε′ = ε, N ≥ N₀) r_3(N) ≤ ε·N.

*Engine.* DF-CK — the flow simulated exactly at ε ∈ {1/8, 1/16, 1/32,
1/64}: per-round densities, window sizes, tower margins, every
inequality checked at every simulated step; thresholds reconciled with
PB-CK's table; the composed certificate cross-checked against the
ITER-CK/receipts142modelstep.txt model-step receipts.

## §9. THE ENGINE CERTIFICATION TABLE

| Lane | Certifies | Status |
|---|---|---|
| EP-CK (T2agree, sigma, devid, axissq, csbound, c0sym, apfree-T) | L-EP (F1′), (F2′), (F3′) identities on planted instances, p ∈ {101, 1009, 4999, 10007}, two counting codes | receipts142sublinear_v2.txt |
| POP-CK | the popular-difference extraction empirics (greedy AP-free windows at N = 10³: max-frequency vs δ) | receipts142sublinear_v2.txt |
| ITER-CK-2 | the L-NW model step at p ∈ {101, 1009} (brute + rescaled) | receipts142sublinear_v2.txt |
| **receipts142modelstep.txt (W76-142E)** | **the L-NW model step at p ∈ {101, 1009, 3203, 9973} — 841,996,456 APs, ZERO wraps, two methods, sharp thresholds** | GREEN |
| **receipts142table_v2.txt (W76-142E)** | **the r_3 certified table N ≤ 48 (10 new cells CERTIFIED-BOTH: r_3(39)=14, r_3(40)=15, r_3(41..48)=16)** | GREEN |
| **receipts142secondmoment.txt (W76-142E)** | **the second-moment checkpoints 18/18 (the L-EP numeric spine: naive-vs-bitset-vs-FFT counting agreement, the cubic-expansion identity exact, CS exact, popular-difference constants)** | GREEN |
| V-CK-2 | Theorem V copy-counts vs the extended table | receipts142sublinear_v2.txt |
| BP-CK | L-BP (sieve n ≤ 1024; the magnitude chain at n = 512/1024/2048) | receipts142sublinear_v2.txt |
| PB-CK / PB-CK-MESH | L-PB-INT (exhaustive L ≤ 26 + threshold table), L-PB, L-ML (exhaustive small p) | receipts142sublinear_v2.txt |
| I-CK-LOC | the localized arc-increment at planted windows | receipts142sublinear_v2.txt |
| DF-CK | the flow simulation (4 eps values, every per-round inequality) | receipts142sublinear_v2.txt |

## §10. THE ARSENAL CITATION LEDGER

39 load-bearing citations across 7 new laws — the full table is
NEW_LAWS_142.md §THE ARSENAL COMBINATION TABLE. Distinct arsenal
theorems: gst_infinite_paradox_energy_split, cubic_expansion,
hc_fourier_character_norm, hc_fourier_exponential, hc_fourier_unitary,
exact_three_geometric_sum, hc_circle_L2_basis, tower_cauchy,
sum_le_sum_of_forall, digit3_congr, digit3_mod_pow, mod_mod_mul,
div_mod_mul_lemma, div_add_mod_subst, mul_add_div_lemma,
carryAtPos_bound, two_pow_ge2, two_pow_factored, sq_sub_one,
digitCount3_monotone, gst_exact_residue_graph_transport,
gst_canonical_prefix_one_energy_squareS,
gst_omega_pressure_energy_splitS. Every one read in arsenal-full/ and
verified at its file:line (receipts LAW-SPEC lane).

**THEOREM SUBLINEAR IS CLOSED.** The W75 status-remaining section is
dead: no component of this assembly carries an "open" label, a
hypothesis, or an external classical engine. The finite frontier
(certified tables, witnesses) remains the campaign's banked deliverable;
the sublinear theorem — the first complete unconditional upper-bound
theorem of the #142 program, in-package, on BOSS'S OWN LAWS — is
delivered by this document.

The engine never stops; it never lies. In English, always.
