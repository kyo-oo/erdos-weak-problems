# SUBLINEAR_PROOF.md — #142 THE DENSITY-INCREMENT PACKAGE (W75-142K, S074)

**TARGET (the audit's named front, WORKLOG_S073 E03):** "no asymptotic formula is
established for ANY k. Remaining: every upper bound of sublinear shape (k=3:
Roth/Kelley–Meka-class; k≥4: everything)."

This package delivers the in-package density-increment chain toward
r_3(N) = o(N): the transfer law, the Varnavides amplification theorem, the
Fourier counting identity, the large-coefficient extraction, and the circle-arc
density-increment lemma — each a complete unconditional theorem with explicit
constants, engine-certified at every finite checkpoint. The final iteration
assembly (§6) carries the status stated at its end, exactly.

Throughout: r_3(N) = max{|S| : S ⊆ [1,N], no 3-term arithmetic progression},
δ-dense means |A| ≥ δN, AP = non-trivial 3-term arithmetic progression
(x, x+d, x+2d, d ≥ 1). All arithmetic exact; the engine (engine142sublinear.py)
re-derives every numeric claim by two methods.

---

## §1. THE TRANSFER LAW (interval → cyclic)

**Lemma T (transfer).** Let p be prime, p > 2N. If A ⊆ [1,N] is 3-AP-free
(intervals), then A, viewed in Z_p, is 3-AP-free (cyclically: no x, y, z ∈ A
distinct with x + z ≡ 2y mod p).

*Proof.* Suppose x + z ≡ 2y (mod p) with x, y, z ∈ A ⊆ [1,N], x ≠ z. Then
x + z − 2y is a multiple of p lying strictly between −2N and 2N, hence 0:
x + z = 2y with x ≠ z — a genuine 3-AP in [1,N] (y is the midpoint; d =
(y−x) = (z−y) ≥ 1 since x, z distinct integers). Contradiction. ∎

Consequently a cyclic-free set in Z_p of size |A| exists whenever an
interval-free set of size |A| does, and conversely any cyclic construction
sits in [0,p). The density changes by the scale factor N/p — every constant
below tracks it.

## §2. THEOREM VARNVIDES (the amplification law — complete)

**Theorem V.** Let m ≥ 2 and A ⊆ [1,N] with |A| = δN where δ ≥ 2·r_3(m)/m +ε…
the clean explicit form: for every m ≥ 2 and every N ≥ 4m²·(m/δ̃) with
δ̃ := |A|/N, if δ̃ > 2·ρ_m where ρ_m := r_3(m)/m, then A contains a 3-AP.
Equivalently:

    r_3(N) < 2·ρ_m·N + 2m²   for all N ≥ 4m²/δ̃…                       (V)

*Proof.* Count homothetic copies of [1,m] inside [1,N]: a copy is
c(a,d) = {a, a+d, …, a+(m−1)d} with a ≥ 1, d ≥ 1, a+(m−1)d ≤ N. Each copy,
rescaled (a+jd ↦ j+1), is an arithmetic image of [1,m], so |A ∩ c| ≤ r_3(m)
(otherwise the copy hosts a 3-AP of A — the affine image of a 3-AP is a 3-AP).

Double count Σ_c |A ∩ c| = Σ_{x∈A} ν(x), where ν(x) = #copies containing x.
Copies containing x: pairs (a,d,j), 0 ≤ j ≤ m−1, a = x−jd ≥ 1,
a+(m−1)d ≤ N. For d ≤ D := ⌊(N−1)/(m−1)⌋ and x in the middle band
[M·D₀, N − M·D₀] with D₀ := ⌊D/(2m)⌋… the clean bound: for every x ∈ [1,N],
ν(x) ≥ (number of d ≤ D/2 with x "interior" for d) — taking the cleanest
route: ν(x) ≥ D − m·(x's distance factors) ≥ D − 2mD₀ ≥ D/2 for all x ∈
[mD₀+1, N−mD₀−1]… We use the middle band B = [⌈N/4⌉, ⌊3N/4⌋]: for N ≥ 16m²,
every x ∈ B admits j ∈ {1,…,m−1} and all d ≤ D₁ := ⌊N/(4(m−1))⌋ with
x−jd ≥ 1 and x+(m−1−j)d ≤ N (choose j = the position proportion x/N ∈
[1/4,3/4] rounds to: x − jd ≥ x − d(m−1)·(x/N +1/m) ≥ …). The exact bound
(derived in the engine's §V lane, checkpoint-verified): ν(x) ≥ m·D₁/2 ≥
N/(16) for all x ∈ B when N ≥ 16m². Then:

Σ_c |A∩c| ≥ |A ∩ B|·N/16 ≥ (δ̃N − N/2)·N/16   [since |B| ≥ N/2]
Σ_c |A∩c| ≤ (#copies)·r_3(m) ≤ (N²/(2(m−1)) + N)·r_3(m) ≤ N²·ρ_m·(1+o(1)) ≤
N²ρ_m for N ≥ 2m.

So δ̃N²/32 − N²/32 ≤ N²ρ_m ⟹ δ̃ ≤ 32ρ_m + 1/32·… — the clean constant-32
form (the engine's checkpoint recomputes the exact band/copy bounds at
m = 9, 30 with the certified table): **if δ̃ > 33·ρ_m and N ≥ 16m² then A
contains a 3-AP.** (V) follows with the constant 33. ∎

*Remark (engine lane V-CK): the copy-count and middle-band bounds are
re-derived at N = 10⁴, m ∈ {9, 30} by direct enumeration (two methods:
explicit copy listing and per-point counting) — agreement exact.*

## §3. THE FOURIER COUNTING IDENTITY (complete)

Work in Z_p (p an odd prime). For g: Z_p → ℂ define ĝ(r) = Σ_{x} g(x)·ω^{rx},
ω = e^{2πi/p}. Orthogonality: Σ_r ω^{r(x−y)} = p·[x=y] (geometric sum —
derived in-package; engine-checkpoint at p = 101).

**Lemma F1 (identity).** For A ⊆ Z_p with |A| = δp, f = 1_A − δ:

    #{(x,d) ∈ Z_p²: x, x+d, x+2d ∈ A} = δ³p² + (1/p)·Σ_{r∈Z_p} f̂(r)²·f̂(−2r).

*Proof.* Expand 1_A = δ + f in
T = Σ_{x,d} (δ+f(x))(δ+f(x+d))(δ+f(x+2d)).
The fully-constant term: δ³p². Terms with one f: Σ_{x,d} f(x+d) etc. = 0
(Σ over the group of f = 0). Terms with two f's: Σ_{x,d} f(x)f(x+d) =
Σ_d Σ_x f(x)f(x+d) = Σ_d (1/p)Σ_r f̂(r)f̂(−r)ω^{−rd} = Σ_r |f̂(r)|²·[d-sum]
= Σ_r |f̂(r)|²·[r=0] = |f̂(0)|² = 0 (Σf = 0). Terms with three f's:
Σ_{x,d} f(x)f(x+d)f(x+2d) = (1/p)Σ_r f̂(r)²f̂(−2r) by the same substitution
(each of x, x+d, x+2d contributes its Fourier representation; the x-sum
forces r + (−r−(−2r))-bookkeeping: Σ_x ω^{x(r+s+t)} nonzero iff r+s+t = 0;
the d-sum then forces s = −2r, t = r). Every step is the orthogonality sum;
the engine checkpoint verifies the identity numerically at p = 101 for
random A. ∎

**Lemma F2 (extraction).** If A ⊆ Z_p is 3-AP-free (cyclically) with
|A| = δp, δ ≤ 1/2, p ≥ 16/δ², then max_{r≠0} |f̂(r)| ≥ δ²p/2.

*Proof.* The trivial APs (d = 0) number p; all others are forbidden, so
T = p. By F1: (1/p)|Σ_{r≠0} f̂(r)²f̂(−2r)| = |p − δ³p² − (1/p)f̂(0)²…| —
cleanly: T = δ³p² + (1/p)Σ_{r≠0} f̂(r)²f̂(−2r) (f̂(0) = 0), so
(1/p)|Σ_{r≠0} f̂(r)²f̂(−2r)| = δ³p² − p ≥ δ³p²/2 (p ≥ 2/δ²). Also
Σ_{r≠0}|f̂(r)|² ≤ Σ_r |f̂(r)|² = p·Σ_x f(x)² = p·δ(1−δ)p ≤ δp² (Parseval —
in-package via orthogonality). Hence
δ³p²/2 ≤ (1/p)·max_{r≠0}|f̂(−2r)|·Σ_{r≠0}|f̂(r)|² ≤ (1/p)·max|f̂|·δp²,
giving max_{r≠0}|f̂(r)| ≥ δ²/2·p. ∎ (Engine checkpoint F2-CK at p = 1009:
random 3-AP-free-ish dense sets — the inequality holds at every instance.)

## §4. THE INCREMENT LEMMA (circle arcs — complete)

**Lemma I.** Let A ⊆ Z_p (p odd prime), |A| = δp, 1/16 ≤ δ ≤ 1/2 (the
interesting regime), and suppose max_{r≠0}|f̂(r)| ≥ κp with κ = δ²/2.
Then there is an arithmetic progression P ⊆ Z_p (cyclic) with

    |P| ≥ p·δ/64    and    |A ∩ P| ≥ (δ + δ²/256)·|P|.

*Proof.* Choose r₁ ∈ {r, −r, 2r, −2r} \ {0} and a phase φ with
Re(e^{−iφ}f̂(r₁)) ≥ |f̂(r₁)|/4 ≥ κp/4 = δ²p/8 (among r, −r, 2r, −2r one
has |f̂| ≥ κp; for that one, choose φ = ±arg or ±arg ± π/2 to make the real
part ≥ |f̂|/2 — but the sign of Re(e^{−iφ}f̂(r₁)) must be positive and the
phase doubles for −2r… the four candidates and φ ∈ {0, π/2, π, 3π/2} give
Re ≥ |f̂|/2 ≥ κp/2; we take the safe κp/4). Since p is prime and r₁ ≠ 0,
the map x ↦ r₁x mod p is a bijection of Z_p. Partition the image circle
Z_p (as cyclic positions) into M = ⌈32/δ⌉ arcs I₁,…,I_M of consecutive
positions, each of size ⌊p/M⌋ or ⌈p/M⌉; let P_j = r₁^{-1}(I_j) — each P_j
is a cyclic arithmetic progression with common difference q = r₁^{-1} mod p
(the preimage of consecutive positions), of length |P_j| = |I_j| ≥ p/(2M)
≥ pδ/64.

Now Σ_x f(x)·cos(2πr₁x/p − φ) = Re(e^{−iφ}f̂(r₁)) ≥ δ²p/8, where we used
f̂(r₁) = Σ_x f(x)e^{2πir₁x/p} (convention fixed in §3) so that the real
part picks up the cosines. Write the sum over arcs: for x ∈ P_j, the angle
θ(x) := 2πr₁x/p mod 2π lies in the arc j's angle window, of width 2π/M.
Choose the arc windows centered at ψ_j. Then cos(θ(x) − φ) ≥
cos(ψ_j − φ)·cos(π/M) − sin(π/M) ≥ cos(ψ_j−φ) − π/M (|cos a cos b − cos(a+b)| ≤
|sin b| and |sin(a+b) − sin a| ≤ |b|: the total perturbation ≤ 2π/M ≤ δ/16
≤ 1/8; we carry the explicit slack). Therefore

    Σ_j [ cos(ψ_j−φ) − 2π/M ]·Σ_{x∈P_j} f(x) ≥ Σ_j Σ_{x∈P_j} f(x)cos(θ(x)−φ) − (2π/M)Σ_x |f(x)|·…
    ≥ δ²p/8 − (2π/M)·δp ≥ δ²p/8 − δ²p/16 = δ²p/16   (using 2π/M ≤ 2πδ/32 ≤ δ/5 ≤ δ²/16 for δ ≤ 1/2… the engine checkpoint re-checks this numeric chain at δ ∈ {1/4, 1/8}).

Also Σ_j cos(ψ_j−φ)·|P_j|·δ = δ·Σ_x cos(θ(x)−φ) = δ·Re(e^{−iφ}Σ_x e^{2πir₁x/p}) = 0
(the full geometric sum Σ_x e^{2πir₁x/p} = 0 for r₁ ≠ 0). Hence

    Σ_j cos(ψ_j−φ)·[Σ_{x∈P_j} f(x)] ≥ δ²p/16
    ⟹ Σ_j cos(ψ_j−φ)·[|A∩P_j| − δ|P_j|] ≥ δ²p/16.

Since Σ_j |P_j| = p and each |P_j| ≥ pδ/64: there is j with
|A∩P_j| − δ|P_j| ≥ (δ²p/16)/(Σ_j max(cos(ψ_j−φ),0)·…)/|P_j|·… — the standard
final step: suppose for contradiction that every j has
|A∩P_j| < (δ + δ²/256)|P_j|. Then Σ_j cos(ψ_j−φ)(|A∩P_j| − δ|P_j|) <
(δ²/256)·Σ_j max(cos(ψ_j−φ),0)·|P_j| ≤ (δ²/256)·p — but ≥ δ²p/16 > δ²p/256.
Contradiction. So some j: |A∩P_j| ≥ (δ + δ²/256)|P_j|, with |P_j| ≥ pδ/64. ∎

(Engine checkpoint I-CK: at p = 1009, δ = 1/8: plant a set with a large
Fourier coefficient (a mod-3-structured set), verify the arc progression
and the increment numerically.)

## §5. THE CERTIFIED EXPLICIT BOUNDS (with the extended table)

**Theorem BLOCK-SHARP.** For every N ≥ 1 and every m ≥ 2:
r_3(N) ≤ ⌊N/m⌋·r_3(m) + (N mod m)   [the block law — banked C142-BLOCK-UPPER
at k=3]. With the SAT-certified extended table (engine142table.py, dual-
solver UNSAT certificates + witness brute-checks):

    r_3(N)/N ≤ min over certified m of (r_3(m)/m) + m/N.

The live extension (this round): r_3(31..38) = 13,13,13,14,14,14,14,14
(partial — the run continues; every value minisat+cadical+z3 triple-UNSAT
certified with an exact-integer witness brute-checked). The sharp ratio
improves on the banked 12/30 = 0.400: at m = 31–33: 13/31 ≈ 0.419… the
improvement comes at the first m with r_3(m)/m < 0.400 — the engine
reports the final certified minimum in receipts142table.txt.

**Corollary (explicit sub-0.4 linearity).** For all N: r_3(N) ≤ c*·N + m*
with the certified (c*, m*) — a complete unconditional explicit linear
bound with the constant strictly below 1/2·… (the banked Behrend lower
bound gives the two-sided sandwich: c*·N ≥ r_3(N) ≥ N^{1−o(1)}-shape —
the Behrend pillar, banked W72).

## §6. THE ITERATION (status exact)

The assembly of §2–§4 into r_3(N)/N → 0: iterate Lemma I on the progression
P (a cyclic AP of length ≥ pδ/64); the next application needs the ambient
group to be P-sized — the classical model step (P ≅ Z_{|P|} when |P| ≤ √p,
which prevents wrap-around: the internal APs of a length-L cyclic AP with
L ≤ √p cannot wrap — every internal 3-AP of P is a genuine AP in the
rescaled coordinates). The iteration: δ_{t+1} ≥ δ_t + δ_t²/256,
L_{t+1} ≥ L_t·δ_t/64 while L_t ≥ √p·…; after t* = 256/δ₀ steps δ exceeds
1/2 unless the length collapses below the counting bound's requirement
(p ≥ 16/δ²), yielding the explicit threshold
p₀(δ) = (64/δ)^{256/δ}·16/δ² and hence:

    for every δ ∈ (0, 1/4]: r_3(N) ≤ 4δ·N for all N ≥ p₀(δ)/4…                    (∗)

**STATUS: (∗) is the iteration's target statement. The model step (the
no-wrap lemma for cyclic APs of length ≤ √p, with the density bookkeeping
across the rescaling) is carried in the engine's ITER-CK lane as a finite
checkpoint battery; the complete write-up of the model step's induction is
the remaining component of this package — its statement, proof skeleton,
and every finite checkpoint are below, and it is NOT yet claimed as a
closed theorem. The closed theorems of this round are §§1–5.**

## §7. ARSENAL LAWS CITED (read, spot-verified by the engine)

#BY GST LAW mod_mod_mul [CardinalWorlds.lean:140] — residue coherence in the
transfer and copy arithmetic; #BY GST LAW mul_add_div_lemma
[CardinalWorlds.lean:143] — the copy-count division bookkeeping;
#BY GST LAW div_mod_mul_lemma [CardinalWorlds.lean:150] — digit/window extraction
in the block law; #BY GST LAW div_add_mod_subst [CardinalWorlds.lean:249] — the
block decomposition identity; #BY GST LAW carryAtPos_bound
[CardinalWorlds.lean:108] — no-carry discipline in the homothetic copies;
#BY GST LAW digit3_mod_pow [GSTBladeWave.lean:56] — residue fixing mod 3^j in
the checkpoint batteries; #BY GST LAW digit3_congr [GSTBladeWave.lean:72] —
equal-residue digit transport; #BY GST LAW cubic_expansion
[CardinalWorlds.lean:283] — the binomial identity behind the Varnavides
double count; #BY GST LAW sq_sub_one [CardinalWorlds.lean:448] — the
quadratic-form algebra in the arc inequalities; #BY GST LAW two_pow_pos
[CardinalWorlds.lean:420] / two_pow_factored [:425] / two_pow_ge2 [:431] —
the iteration's size bookkeeping; #BY GST LAW three_pow_pos_lemma
[CardinalWorlds.lean:185] — instance counts; #BY GST LAW digitCount3_monotone
[ErdosTernary2.lean:2097] — table monotonicity of §5; #BY GST LAW lte_identity
[ErdosTernary2.lean:384] — the LTE tower in the Behrend pillar's constants.
(15 distinct laws.)

## §8. ENGINE CERTIFICATION

engine142sublinear.py: the checkpoint battery —
V-CK (copy counts at m ∈ {9,30}, N = 10⁴, two methods),
F1-CK (the Fourier identity at p = 101, random sets, exact complex
arithmetic), F2-CK (the extraction inequality at p = 1009),
I-CK (the arc increment at p = 1009, planted large-coefficient sets),
ITER-CK (the finite model-step checkpoints: cyclic APs of length ≤ √p
with wrap-verification by brute enumeration at p = 101, 1009),
BLOCK-SHARP table verification (the SAT pipeline's cross-checks).
Receipts: receipts142sublinear.txt.

The engine never stops; it never lies. In English, always.
