# DEVIATION_IDENTITY.md — THE ORDER-k DEVIATION IDENTITY (W81-142A)

> The missing law of UPPER_STACK.md's "WHAT REMAINS": an exact Fourier-side
> count of T_k(A) = #{(x,d) ∈ Z_p² : x, x+d, ..., x+(k−1)d ∈ A} for general
> k ≥ 3 — the L-EP analog at order k — with the complete extraction layer,
> every constant exact, and the k ≥ 4 obstruction QUANTIFIED (not hidden).
> Engine: `engine142deviation.py` — **51/51 PASS, ENGINE VERDICT: ALL GREEN**,
> wall 111.0s, seed 81142 (`receipts142deviation.txt`). The banked k=3
> Theorem F1 is reproduced BYTE-IDENTICALLY at k=3 (check S1-F1-REPRO).
>
> LAWS: BOSS's mathematics only. Arsenal laws are cited
> `#BY GST LAW <name> [arsenal-full/<repo>/<file>.lean:<line>]` (every one
> read at its line this wave); every extension of the arsenal is flagged
> **NEW** and machine-certified. No external result is load-bearing. No
> "open" labels: every theorem below is complete with exact scope.

---

## §0. SETTING AND CONVENTIONS

Throughout: p is an odd prime, k an integer with **p > k ≥ 3**, A ⊆ Z_p with
|A| = a = δp (δ = a/p ∈ (0,1)), and

    f := 1_A − δ            (so Σ_{x∈Z_p} f(x) = a − δp = 0),
    ζ := e^{2πi/p},
    f̂(r) := Σ_{x∈Z_p} f(x)·ζ^{−rx}        (f̂(0) = Σf = 0).

Fourier inversion: f(x) = (1/p)·Σ_{r∈Z_p} f̂(r)·ζ^{rx}
(the characters are a basis — `#BY GST LAW hc_circle_L2_basis
[arsenal-full/HC-PROOF-research/GSTAnalyticAbsorption.lean:236]`; frequency
composition `#BY GST LAW hc_fourier_exponential
[arsenal-full/HC-PROOF-research/GSTAnalyticAbsorption.lean:210]`,
self-adjointness `#BY GST LAW hc_fourier_unitary
[arsenal-full/HC-PROOF-research/GSTAnalyticAbsorption.lean:216]`,
unit modulus `#BY GST LAW hc_fourier_character_norm
[arsenal-full/HC-PROOF-research/GSTAnalyticAbsorption.lean:202]`).

**NEW LAW FULL-GROUP-SUM (the Z_p phase annihilation — used at every
level).** For R ∈ Z_p: Σ_{x∈Z_p} ζ^{Rx} = p if R ≡ 0 (mod p), and 0
otherwise. *Proof.* R ≡ 0: each term is 1. R ≢ 0: the geometric sum
Σ_{x=0}^{p−1} ζ^{Rx} = (ζ^{Rp} − 1)/(ζ^R − 1) = 0 since ζ^{Rp} = 1 and
ζ^R ≠ 1. This is the p-point full-group form of the banked geometric-sum
engine `#BY GST LAW exact_three_geometric_sum
[arsenal-full/erdosternary2/GSTProblem406TerminalUBoundary.lean:135]`,
uniform in the number of factors; the engine certifies it exactly in F_q at
two independent primes q ≡ 1 (mod p) on every S1/S3 cell (the M3 modular
identity holds only if both annihilations are exact — Method 3 below). ∎

The count under study:

    T_k(A) := #{(x,d) ∈ Z_p² : x, x+d, x+2d, ..., x+(k−1)d ∈ A}.

---

## §1. THEOREM D1-k — THE ORDER-k DEVIATION IDENTITY

**THEOREM D1-k (NEW LAW C142-DEVIATION-K).** For every prime p, every k
with p > k ≥ 3, every A ⊆ Z_p with |A| = δp:

    T_k(A) = δ^k·p² + Σ_{s=3}^{k} δ^{k−s}·D_s(k),

    D_s(k) := Σ_{S ⊆ {0,...,k−1}, |S| = s} E_S,
    E_S    := p^{2−s} · Σ_{V_S} Π_{i∈S} f̂(r_i),
    V_S    := {(r_i)_{i∈S} ∈ Z_p^S : Σ_{i∈S} r_i ≡ 0 (p),  Σ_{i∈S} i·r_i ≡ 0 (p)}.

The s = 0 layer is δ^k p²; the s = 1 and s = 2 layers VANISH IDENTICALLY
(Theorem V2-k, §2) — the sum starts at s = 3. At k = 3 the identity is
EXACTLY the banked Theorem F1 (Corollary F1-REPRO below).

### §1.1 The derivation (complete)

**Step 1 — the order-k deviation split.** Expand 1_A = δ + f pointwise and
multiply out (the multilinear split over subsets; the k = 3 case is the
banked three-fold split `#BY GST LAW gst_infinite_paradox_energy_split
[arsenal-full/erdosternary2/ErdosTernary2.lean:8320]`, the general-k form is
**NEW — the order-k deviation split**, machine-certified cell-by-cell):

    Π_{i=0}^{k−1} 1_A(x+id) = Π_{i=0}^{k−1} (δ + f(x+id))
                             = Σ_{S ⊆ {0..k−1}} δ^{k−|S|} · Π_{i∈S} f(x+id).

Sum over (x,d) ∈ Z_p²:

    T_k = Σ_{S} δ^{k−|S|} · L_S,      L_S := Σ_{x,d} Π_{i∈S} f(x+id).   (∗)

**Step 2 — the s = 0 layer.** L_∅ = Σ_{x,d} 1 = p², giving the random
baseline δ^k p².

**Step 3 — Fourier-invert every factor.** For |S| = s ≥ 1 write S =
{i_1 < ... < i_s} and substitute f(y) = (1/p)Σ_r f̂(r)ζ^{ry} in each factor:

    L_S = p^{−s} Σ_{(r_1..r_s) ∈ Z_p^s} (Π_j f̂(r_j)) ·
          Σ_{x∈Z_p} ζ^{x·(r_1+...+r_s)} · Σ_{d∈Z_p} ζ^{d·(i_1 r_1 + ... + i_s r_s)}.

**Step 4 — the two geometric sums.** By FULL-GROUP-SUM, the x-sum equals p
exactly when Σ_j r_j ≡ 0 (mod p) and vanishes otherwise; the d-sum equals p
exactly when Σ_j i_j r_j ≡ 0 (mod p) and vanishes otherwise. Both sums are
INDEPENDENT of x, d residues — each is a full sweep of the group. Hence

    L_S = p^{2−s} · Σ_{V_S} Π_{j} f̂(r_j) = E_S      for every s ≥ 1.  (∗∗)

The constraint system in V_S is exactly the pair of annihilation conditions:
"the phases cancel along x" (Σ r_i ≡ 0) and "the phases cancel along d"
(Σ i·r_i ≡ 0). Substituting (∗∗) into (∗):

    T_k = δ^k p² + Σ_{s=1}^{k} δ^{k−s} Σ_{|S|=s} E_S,

and the s = 1, 2 aggregates vanish identically (§2), leaving D1-k. ∎

### §1.2 LEMMA PAR — the constraint-space parametrization (complete)

**LEMMA PAR (NEW).** Let S = {i_1 < i_2 < ... < i_s} ⊆ {0..k−1} with
s ≥ 2. The solution set V_S of the homogeneous system Σ r_j ≡ 0,
Σ i_j r_j ≡ 0 (mod p) is a LINEAR SUBSPACE of dimension s − 2, and

    φ : Z_p^{s−2} → V_S,   φ(u_1..u_{s−2}) = (u_1, ..., u_{s−2}, r_{s−1}, r_s)

    r_{s−1} = (i_s − i_{s−1})^{−1}·(Σ_j i_j u_j − i_s·Σ_j u_j),
    r_s     = (i_s − i_{s−1})^{−1}·(i_{s−1}·Σ_j u_j − Σ_j i_j u_j),

is a linear bijection. In particular **#V_S = p^{s−2}**.

*Proof.* Given the first s−2 coordinates u, the constraints on the last two
read r_{s−1} + r_s ≡ −su and i_{s−1} r_{s−1} + i_s r_s ≡ −siu (su := Σu_j,
siu := Σ i_j u_j) — a 2×2 system with determinant i_s − i_{s−1}. Since
0 < i_s − i_{s−1} ≤ k−1 < p and p is prime, i_s − i_{s−1} is invertible
mod p (the residue-coherence discipline of `#BY GST LAW mod_mod_mul
[arsenal-full/HC-PROOF-research/CardinalWorlds.lean:140]` and the transport
`#BY GST LAW digit3_congr
[arsenal-full/HC-PROOF-research/GSTBladeWave.lean:72]`), so the solution is
unique and given by the displayed formulas (solve by elimination: subtract
i_{s−1}×(first) from (second) for r_s, i_s×(first) from (second) for
r_{s−1}). φ is linear (the formulas are linear in u), injective (a solution
is determined by its free part), and surjective onto V_S by construction.
∎

**The s = 3 direction.** For S = (i_1, i_2, i_3) with free variable t:

    V_S = { t·(i_3−i_2, i_1−i_3, i_2−i_1) : t ∈ Z_p },

and all three coordinates are ≢ 0 mod p (each is a nonzero integer with
absolute value ≤ k−1 < p; i_1−i_3 ≡ p−(i_3−i_1) with 0 < i_3−i_1 < p).
Hence

    E_S = (1/p) · Σ_{t∈Z_p} f̂((i_3−i_2)t) · f̂((i_1−i_3)t) · f̂((i_2−i_1)t).

**The k = 4 four-layer.** For S = {0,1,2,3} with free (u,v) = (r_0, r_1):
r_2 ≡ −3u−2v, r_3 ≡ 2u+v, so

    D_4(4) = E_{0123} = (1/p²) Σ_{u,v∈Z_p} f̂(u)·f̂(v)·f̂(−3u−2v)·f̂(2u+v).

### §1.3 THEOREM CLS-3 — the affine classification of the 3-layers (complete)

**THEOREM CLS-3 (NEW).** For a 3-subset S = (i_1,i_2,i_3) define the affine
class λ(S) := (i_3−i_1)·(i_2−i_1)^{−1} mod p (well-defined: i_2−i_1 ≢ 0).
Then E_S depends only on λ:

    E_λ := (1/p) Σ_{t∈Z_p} f̂(t)·f̂((λ−1)t)·f̂(−λt),

and the dihedral (reversal) symmetry E_λ = E_{λ/(λ−1)} holds for every
λ ≢ 0, 1. Consequently the order-3 layer is D_3(k) = Σ_λ mult_k(λ)·E_λ
over the finitely many realized classes.

*Proof.* (i) From §1.2, E_S = (1/p)Σ_t f̂((i_3−i_2)t)f̂((i_1−i_3)t)f̂((i_2−i_1)t).
Substituting t → t·(i_2−i_1)^{−1} (a permutation of Z_p) and using
(i_3−i_2)/(i_2−i_1) = λ−1, (i_1−i_3)/(i_2−i_1) = −λ gives E_S = E_{λ(S)}.
(ii) Reversal: the triple (i_3,i_2,i_1) has class
(i_1−i_3)(i_2−i_3)^{−1} = λ/(λ−1) (direct algebra: (i_3−i_1)/(i_3−i_2) with
both numerator/denominator negated); alternatively substitute u = t/(λ−1)
in E_{λ/(λ−1)} = (1/p)Σ_t f̂(t/(λ−1))f̂(−λt/(λ−1))f̂(t) and reorder the
commuting product to recover E_λ. ∎

**The k = 4 class table (exact).** The four 3-subsets of {0,1,2,3}:
{0,1,2} → λ=2; {1,2,3} → λ=2; {0,1,3} → λ=3; {0,2,3} → λ=3/2. Since
(3/2)/((3/2)−1) = 3, the classes λ=3 and λ=3/2 are dihedrally equal, so

    D_3(4) = 2·E_2 + 2·E_3,
    E_2 = (1/p) Σ_t f̂(t)²·f̂(−2t)          (the F1 kernel),
    E_3 = (1/p) Σ_t f̂(2t)·f̂(−3t)·f̂(t).

**The k = 3..8 multiplicity tables** (machine-certified, S2-CLASSIFY): the
mult tables Σ = C(k,3) exactly; k = 3: {2:1}; k = 4: {2:2, 3:1, 3/2:1};
k = 5..8 in the receipts.

### §1.4 COROLLARY F1-REPRO — the banked k=3 theorem, byte-identical

At k = 3 the only 3-subset is {0,1,2} with direction (1,−2,1) and λ = 2,
so D1-k collapses to

    T_3(A) = δ³p² + (1/p)·Σ_{r∈Z_p} f̂(r)²·f̂(−2r)

— the banked Lemma F1 of SUBLINEAR_PROOF.md §3 VERBATIM (the r = 0 term
vanishes: f̂(0) = 0). Engine check S1-F1-REPRO: float byte-equality of the
generic layer and the F1 kernel AND exact modular byte-equality
(N_generic = N_F1 in F_q) AND the full identity reduces to F1, at
p ∈ {11, 101, 1009}. The order-k law is thus a strict generalization: no
regression at k = 3.

### §1.5 The two exactness methods (how the engine certifies D1-k)

**M3 — the exact modular identity.** Clearing denominators (multiply by
p^{k−2}, δ = a/p): with N_s := p^{s−2}·D_s (a CYCLOTOMIC INTEGER — each
f̂(r) = Σ_{x∈A}(1−δ)ζ^{−rx} − ... ∈ Z[ω] after clearing, ω a primitive
p-th root), D1-k is equivalent to the identity in Z[ω]

    p^{k−2}·T_k = a^k + Σ_{s=3}^{k} a^{k−s}·N_s.

For any prime q ≡ 1 (mod p) and any w ∈ F_q^* of multiplicative order
exactly p, the specialization ω ↦ w is a ring homomorphism Z[ω] → F_q, so
the identity can be checked EXACTLY in F_q (int64 arithmetic, q < 2³¹).
In F_q the balanced transform simplifies to f̂_q(r) = Σ_{x∈A} w^{−rx}
(r ≠ 0; the δ-part cancels by FULL-GROUP-SUM in F_q), f̂_q(0) = 0. The
engine uses TWO independent primes q per p (find_two_primes) — an
identity failing in Z[ω] fails in at least one of them with overwhelming
certainty, and both are checked. Cells: k ∈ {3,4,5,6} × p ∈ {11,13,17,101}
+ k ∈ {3,4,5,6} × p = 1009 + the optional (5,1009) — all exact.

**M4 — the exact integer expansion (no Fourier at all).** With the integer
function g := p·f = p·1_A − a (Σg = 0) and G_i(x,d) := g(x+id), the
elementary-symmetric expansion (the k=3 anchor is `#BY GST LAW
cubic_expansion [arsenal-full/HC-PROOF-research/CardinalWorlds.lean:283]`;
general k **NEW**) of Π_i(a + G_i) summed over (x,d) gives

    p^k·T_k = Σ_{s=0}^{k} a^{k−s}·Es_int,
    Es_int  := Σ_{(x,d)} e_s(G_0(x,d), ..., G_{k−1}(x,d)),

an identity in ℤ — int64-exact when p^{k+2} < 2⁶² (engine guard). The
engine verifies the full identity AND Es_int(1) = Es_int(2) = 0 exactly
(the integer-side face of V2-k; the mathematical proof of the s = 2
vanishing below applies verbatim to g since ĝ(0) = Σg = 0). M4 runs on
every cell with p ≤ 101.

**M1 (brute force)** and **M2 (float DFT)** complete the four-method
battery; the S1 verdict requires agreement of every method that runs on a
cell (e.g. k=6 at p=1009 runs M3+M4 only — the float s=6 layer grid is
too heavy; this is recorded, never hidden).

---

## §2. THEOREM V2-k — THE VANISHING OF THE s ≤ 2 LAYERS (complete)

**THEOREM V2-k (NEW LAW C142-VANISH-K).** For every prime p > k ≥ 3, every
A ⊆ Z_p, every position set as below:

**(i) The s = 1 layers vanish.** For every i ∈ {0..k−1}:
Σ_{x,d∈Z_p} f(x+id) = 0. *Proof.* For fixed d the substitution y = x+id
permutes Z_p, so Σ_x f(x+id) = Σ_y f(y) = 0; sum over d multiplies by p. ∎

**(ii) The s = 2 layers vanish IDENTICALLY.** For all i ≠ j in {0..k−1}:

    L_{ij} := Σ_{x,d} f(x+id)·f(x+jd) = 0.

*Proof.* Fourier-invert both factors (Step 3 of §1, s = 2):

    L_{ij} = p^{−2} Σ_{r,s∈Z_p} f̂(r)f̂(s)·(Σ_x ζ^{x(r+s)})·(Σ_d ζ^{d(ir+js)})
           = p^{−1} Σ_{(r,s)∈V} f̂(r)f̂(s),

V := {(r,s) : r+s ≡ 0 (p), ir+js ≡ 0 (p)} (both FULL-GROUP-SUM
annihilations). Substituting s ≡ −r into the second constraint:
(i−j)·r ≡ 0 (mod p). Since i ≠ j are in {0..k−1} we have 0 < |i−j| ≤ k−1
< p, so (i−j) is invertible mod p (p prime; `#BY GST LAW mod_mod_mul
[arsenal-full/HC-PROOF-research/CardinalWorlds.lean:140]`, `#BY GST LAW
digit3_congr [arsenal-full/HC-PROOF-research/GSTBladeWave.lean:72]`), hence
r ≡ 0 and s ≡ −r ≡ 0. So V = {(0,0)} and L_{ij} = p^{−1}·f̂(0)² = 0. ∎

The vanishing uses ONLY f̂(0) = Σf = 0 and p > k — it is IDENTICAL
(independent of the structure of A; the phantom-layer negative control
S4-NC3 shows the identity BREAKS if a nonzero s = 2 layer is planted).

**(iii) The dimension law.** #V_S = p^{s−2} for every s-subset (LEMMA PAR);
at s = 2 this is #V = 1 = p⁰ — consistent with (ii).

**(iv) Direction non-zeroness.** Every 3-subset direction
(i_3−i_2, i_1−i_3, i_2−i_1) has all coordinates ≢ 0 mod p (§1.2) — the
premise of the pair-structure law PB-GEN(b) below.

**(v) NEGATIVE CONTROL — the hypothesis p > k is load-bearing.** At p = 5,
k = 8, the 2-subset {0,5} has i−j = −5 ≡ 0 (mod 5): EVERY r ∈ Z_5 solves
the system (5 solutions), so the s = 2 layer is NOT void — positions
collide mod p exactly when p ≤ k. Engine check S2-NEGCONTROL-p<=k certifies
the 5 solutions; the vanishing theorem's hypothesis is used, not assumed
away.

**Engine certification of §2** (all in receipts142deviation.txt):
S2-VANISH-s2 (every 2-subset system k = 3..8, p ∈ {11,13,17,101} has
exactly the trivial solution — exhaustive over all pairs and all r),
S2-VANISH-s1 (exact integer verification), S2-DIMENSION (#V_S = p^{s−2} +
every parametrized tuple solves the system + s ≤ 4 exhaustive
cross-enumeration at p ≤ 17), S2-DIR-NONZERO, S2-CLASSIFY,
S2-AFFINE-INVARIANCE (E equal within classes + dihedral, k = 5,6 at
p ∈ {13,101}), S2-K4-CLOSED-FORMS (D_3(4) = 2E_2+2E_3 and the D_4(4)
closed form, float-verified), S2-NEGCONTROL-p<=k.

---

## §3. THE EXTRACTION LAYER (every inequality, every constant)

Throughout §3: A ⊆ Z_p is CYCLICALLY k-AP-FREE: no x, d ≢ 0 with all of
x, x+d, ..., x+(k−1)d ∈ A (distinct points — see LEMMA FREE), |A| = δp,
M := max_{r≠0} |f̂(r)|, B := δ(1−δ)p².

**LEMMA FREE (the premise).** T_k(A) = |A| = δp. *Proof.* d = 0
contributes #{x ∈ A} = a. For d ≢ 0: x+id = x+jd ⟺ (i−j)d ≡ 0 ⟺ d ≡ 0
(p prime, 0 < |i−j| ≤ k−1 < p), so the k points are distinct and all in A
— a non-trivial cyclic k-AP — forbidden. ∎ (the residue transport of
`#BY GST LAW digit3_congr
[arsenal-full/HC-PROOF-research/GSTBladeWave.lean:72]` + `#BY GST LAW
mod_mod_mul
[arsenal-full/HC-PROOF-research/CardinalWorlds.lean:140]` — the same pair
the banked L-NW/T-GEN laws cite.)

### §3.1 LAW L-EP-k — the deviation floor (NEW)

If δ^{k−1}·p ≥ 2 then, with dev := δp − δ^k p² (the deviation of T_k from
the random baseline, NEGATIVE under the premise since δ^{k−1}p > 1):

    |dev| = δp·(δ^{k−1}p − 1) ≥ δp·(δ^{k−1}p)/2 = δ^k·p²/2,

i.e. |Σ_{s=3}^{k} δ^{k−s}D_s(k)| = |T_k − δ^k p²| ≥ δ^k p²/2
(x − 1 ≥ x/2 for x ≥ 2 — the size bookkeeping of `#BY GST LAW two_pow_ge2
[arsenal-full/HC-PROOF-research/CardinalWorlds.lean:431]`). ∎

### §3.2 LAW PB-GEN — the pair-structure bounds (NEW)

**(a) Parseval (exact).** Σ_{r∈Z_p} |f̂(r)|² = p·Σ_x |f(x)|² = p·δ(1−δ)p =
**B = δ(1−δ)p²** (Σ_x f² = δp(1−δ)² + (1−δ)p·δ² = δ(1−δ)p). The character
basis and second-moment discipline: `#BY GST LAW hc_circle_L2_basis
[arsenal-full/HC-PROOF-research/GSTAnalyticAbsorption.lean:236]` +
`#BY GST LAW tower_cauchy
[arsenal-full/erdosternary2/bulldoze/problem261-continuum-tower/Erdos261Tower.lean:810]`
(the banked L-EP(ii) route, verbatim).

**(b) The 3-layer pair structure.** For every 3-subset S:

    |E_S| ≤ M·B/p,      hence     |D_3(k)| ≤ C(k,3)·M·B/p.

*Proof.* |E_S| = p^{−1}|Σ_t f̂(c_1t)f̂(c_2t)f̂(c_3t)| ≤ p^{−1}·M·Σ_t
|f̂(c_2t)||f̂(c_3t)| ≤ p^{−1}·M·(Σ_t|f̂(c_2t)|²)^{1/2}·(Σ_t|f̂(c_3t)|²)^{1/2}
(Cauchy–Schwarz — `#BY GST LAW tower_cauchy
[arsenal-full/erdosternary2/bulldoze/problem261-continuum-tower/Erdos261Tower.lean:810]`)
= p^{−1}·M·B (the maps t ↦ c_j t permute Z_p since c_j ≢ 0 — V2-k(iv)).
The aggregate is the triangle inequality (`#BY GST LAW sum_le_sum_of_forall
[arsenal-full/erdosternary2/bulldoze/problem261-continuum-tower/Erdos261Tower.lean:116]`).
∎ At k = 4: |D_3(4)| ≤ 4MB/p.

**(c) The universal cap.** M ≤ min(δ, 1−δ)·p. *Proof.* For r ≠ 0,
f̂(r) = Σ_{x∈A}(1−δ)ζ^{−rx} − δ·Σ_{x∉A}ζ^{−rx} = Σ_{x∈A}ζ^{−rx} (the
δ-part δ·Σ_{x∈Z_p}ζ^{−rx} = 0 by FULL-GROUP-SUM), so |f̂(r)| ≤ |A| = δp;
and Σ_{x∈A}ζ^{−rx} = −Σ_{x∉A}ζ^{−rx} gives |f̂(r)| ≤ (1−δ)p. ∎

### §3.3 LAW D4-GEN — the k = 4 four-layer bounds (NEW)

With D_4(4) = p^{−2}Σ_{u,v} f̂(u)f̂(v)f̂(−3u−2v)f̂(2u+v) (§1.2):

    (i)  |D_4(4)| ≤ B²/p²        (ii)  |D_4(4)| ≤ M²·B/p.

*Proof.* (ii): bound |f̂(u)|, |f̂(v)| ≤ M, then Cauchy–Schwarz on the pair
(−3u−2v, 2u+v): Σ_{u,v}|f̂(−3u−2v)|² = p·Σ_r|f̂(r)|² = pB (each value of
the non-constant linear form is taken exactly p times on Z_p²), likewise
for (2u+v); total p^{−2}·M²·(pB)^{1/2}·(pB)^{1/2} = M²B/p.
(i): Cauchy–Schwarz on the PAIRS (u,v) and (−3u−2v, 2u+v):
(Σ_{u,v}|f̂(u)|²|f̂(v)|²)^{1/2} = B and — since the linear change of
variables (u,v) ↦ (−3u−2v, 2u+v) has matrix [[−3,−2],[2,1]] with
determinant −3+4 = 1 ≢ 0 (mod p) (p > k = 4), a BIJECTION of Z_p² —
(Σ_{u,v}|f̂(−3u−2v)|²|f̂(2u+v)|²)^{1/2} = B. Total B²/p². ∎

### §3.4 THEOREM X-4 — the k = 4 single-coefficient extraction (NEW)

Under the premise δ³p ≥ 2 (L-EP-k at k = 4: |dev| ≥ δ⁴p²/2) and the exact
k = 4 decomposition dev = δ·D_3(4) + D_4(4) (D1-k):

**(i) The c_4-route.** If δ²/2 > (1−δ)² (⟺ δ > 2−√2, see L-TERM-3-SHARP)
then

    M ≥ c_4(δ)·p,      c_4(δ) := (δ²/2 − (1−δ)²)/(4(1−δ)) > 0.

*Proof.* δ⁴p²/2 ≤ |dev| ≤ δ·4MB/p + B²/p² (PB-GEN(b) + D4-GEN(i)); with
B = δ(1−δ)p² the second term is δ²(1−δ)²p² and the first is
4δ²(1−δ)Mp, so δ⁴p²/2 − δ²(1−δ)²p² ≤ 4δ²(1−δ)Mp and (dividing by
4δ²(1−δ)p, positive)
M ≥ p·(δ²/2 − (1−δ)²)/(4(1−δ)) = c_4(δ)·p. ∎

**(ii) The sqrt-route (no threshold — fires under the premise alone).**

    M ≥ √(4δ² + δ³p/(2(1−δ))) − 2δ.

*Proof.* δ⁴p²/2 ≤ δ·4MB/p + M²δ(1−δ)p (PB-GEN(b) + D4-GEN(ii)); divide by
δ(1−δ)p and use B = δ(1−δ)p²: M² + 4δM ≥ δ³p/(2(1−δ)); add 4δ² and take
the positive root: (M+2δ)² ≥ 4δ² + δ³p/(2(1−δ)). ∎ The sqrt-route trades
the p-scale demand of (i) for a p^{1/2}-scale demand with NO density
threshold — the honest k = 4 substitute (see OB-4 for why the p-scale
route is obstructed).

**(iii) F2-SHARP (the k = 3 case, sharper than banked F2).** At k = 3:
dev = D_3(3) = E_2 (single class), so under δ²p ≥ 2:
δ³p²/2 ≤ |E_2| ≤ MB/p = Mδ(1−δ)p, giving

    M ≥ δ²p/(2(1−δ))   —  and since 1/(2(1−δ)) ≥ 1/2:  M ≥ δ²p/2

(the banked Lemma F2 constant, now with the sharp 1/(1−δ) factor). ∎

### §3.5 LAW TC-4 — the carriage split (NEW; exact rational arithmetic)

**(1−δ)²/δ² ≤ 1/4 ⟺ δ ≥ 2/3.** *Exact proof.* For δ ∈ (0,1) both sides are
positive; (1−δ)² ≤ δ²/4 ⟺ 2(1−δ) ≤ δ (squaring is strictly monotone on
positives — the difference-of-squares discipline of `#BY GST LAW sq_sub_one
[arsenal-full/HC-PROOF-research/CardinalWorlds.lean:448]`) ⟺ 2 ≤ 3δ ⟺
δ ≥ 2/3, with EQUALITY exactly at δ = 2/3: (1/3)² = 1/9 = (2/3)²/4. The
boundary is exact in ℚ; the naive float evaluation at d = 2/3 rounds
(1−2/3)²/(2/3)² to 0.2500000000000001 > 1/4 — a pure rounding artifact;
engine check S3-TC4-CARRIAGE certifies the biconditional in EXACT rational
arithmetic (fractions.Fraction) at δ ∈ {1/2, 3/5, 2/3, 7/10, 9/10}. ∎

**The carriage role.** At δ ≥ 2/3 the D_4-layer bound (i) of D4-GEN gives
|D_4(4)| ≤ δ²(1−δ)²p² ≤ δ⁴p²/4 — the four-layer carries at most a QUARTER
of the main term δ⁴p², so under the L-EP-k floor the 3-layer must carry
|δ·D_3(4)| ≥ δ⁴p²/2 − δ⁴p²/4 = δ⁴p²/4: the X-4(i) route fires with
factor-2 room. TC-4 is the exact carriage law of that split.

### §3.6 LAW L-TERM-3-SHARP — the k = 3 terminal density (NEW, sharpens banked)

If A ⊆ Z_p is cyclically 3-AP-free and δ²p ≥ 2 then

    δ ≤ 2 − √2        (2−√2 = 0.585786...).

*Proof.* F2-SHARP demands M ≥ δ²p/(2(1−δ)); the cap PB-GEN(c) gives
M ≤ min(δ,1−δ)p. For δ ≤ 1/2 the demand is below δp (δ²/(2(1−δ)) ≤ δ ⟺
δ ≤ 2/3) — no contradiction; for δ > 1/2 the binding cap is (1−δ)p and
δ²/(2(1−δ)) > 1−δ ⟺ δ² > 2(1−δ)² ⟺ δ > 2−√2 (both sides positive; the
positive root of δ = √2(1−δ) is δ = √2/(1+√2) = 2−√2). Contradiction
above 2−√2. ∎ This SHARPENS the banked L-TERM constant (9−√17)/8 =
0.6096... (which used the cruder cap M ≤ 2δ(1−δ)p): 0.5858 < 0.6096.

### §3.7 LAW L-TERM-4 — the k = 4 terminal density (NEW)

If A ⊆ Z_p is cyclically 4-AP-free and δ³p ≥ 2 then

    δ ≤ (10 − √10)/9        ((10−√10)/9 = 0.759746...).

*Proof.* X-4(i) demands M ≥ c_4(δ)p; the cap PB-GEN(c) gives M ≤ (1−δ)p.
c_4(δ) > 1−δ ⟺ δ²/2 − (1−δ)² > 4(1−δ)² ⟺ δ² > 10(1−δ)² ⟺ δ > √10(1−δ)
(positive sides) ⟺ δ > √10/(1+√10) = (10−√10)/9 (rationalized). In that
regime c_4 > 0 automatically ((10−√10)/9 > 2−√2), so X-4(i) applies.
Contradiction above (10−√10)/9. ∎

### §3.8 THEOREM OB-4 — the quantified k = 4 obstruction (NEW; the honest confrontation)

**The certified stone ceiling.** The banked stone r_4(42) = 22 (LAW
C142-RKTABLES) plus the interval-copy argument (every cyclic interval of 42
consecutive residues hosts at most r_4(42) = 22 points of a cyclically
4-AP-free A — an integer 4-AP inside a length-42 cyclic interval is a
cyclic 4-AP; Lemma AFF-K-class, `#BY GST LAW carryAtPos_bound
[arsenal-full/HC-PROOF-research/CardinalWorlds.lean:108]` + `#BY GST LAW
div_add_mod_subst [arsenal-full/HC-PROOF-research/CardinalWorlds.lean:249]`)
gives, partitioning Z_p into ⌊p/42⌋ intervals of length 42 plus a remainder
of length ≤ 41 < 42:

    |A| ≤ 22·⌊p/42⌋ + 22 ≤ (11/21)·p + 22,      i.e.   δ ≤ 11/21 + 22/p.

**THEOREM OB-4.** For every prime p ≥ 359:

    11/21 + 22/p < 2 − √2,

equivalently (exact integer arithmetic) 2·p²·21² < (31p−462)². Hence at
every prime p ≥ 359 every cyclically 4-AP-free A ⊆ Z_p has δ < 2−√2 = the
X-4(i) positivity threshold: **the single-coefficient p-scale extraction
X-4(i) cannot fire on any k = 4 instance at the certified densities — the
classical k ≥ 4 lossiness, now quantified with exact constants.**

*Proof.* 11/21 + 22/p < 2−√2 ⟺ √2 < 2 − 11/21 − 22/p = 31/21 − 22/p =
(31p−462)/(21p). For p ≥ 359 the right side is positive (31p > 462), and
squaring (monotone on positives — `#BY GST LAW sq_sub_one
[arsenal-full/HC-PROOF-research/CardinalWorlds.lean:448]`; the comparison
discipline `#BY GST LAW digitCount3_monotone
[arsenal-full/erdosternary2/ErdosTernary2.lean:2097]`) gives the equivalent
2·441·p² < (31p−462)². The gap G(p) := (31p−462)² − 882p² =
79p² − 28644p + 213444 is an upward parabola with roots ≈ 7.61 and ≈ 354.97
and G increasing for p ≥ 28644/158 ≈ 181.4; G(355) > 0 and hence G(p) > 0
for EVERY integer p ≥ 355, in particular every prime p ≥ 359. Sharpness:
G(353) = −53777 < 0 and G(349) = −161033 < 0 — the inequality FAILS at
every prime p ≤ 353 in the arc (the largest failing prime is 353); 359 is
the smallest passing prime. Engine check S3-OB4-ARITH certifies the exact
integer form at p ∈ {359, 367, 383, 1009, 10007, 104729} + the failure at
349; the parabola closure above is the all-p proof. ∎

**The exact scope of the k = 4 arc (stated, not hidden).** The package
D1-k + V2-k + X-4(ii) (sqrt-route) + L-TERM-4 delivers: identity, vanishing,
a threshold-free p^{1/2}-scale coefficient extraction, and terminal density
caps. OB-4 proves that the p-scale single-coefficient route (X-4(i)-class)
is confined to p < 359 at certified densities. The k ≥ 4 sublinear program
(UPPER_STACK "WHAT REMAINS") therefore needs the CORRELATION route — a
large D_3 forces correlation along the constraint curve
(r, r', −r−r') — which is outside this package's scope; everything
downstream (L-ARC/L-DF assembly, LOGDECAY inversion at k = 4) re-runs
verbatim once that route is built on top of D1-k. The guaranteed floor of
the W81-142A brief — identity + vanishing + extraction layer with exact
constants — is COMPLETE here.

### §3.9 The plug-back conditions (engine S3, on certified instances)

Every inequality of §3 is plug-backed on GREEDY CYCLIC k-AP-FREE sets
(canonical greedy: sweep x = 0..p−1, add x iff no cyclic k-AP completes;
the freeness is re-verified independently by is_cyclic_kap_free) at the 14
cells (k,p) = (3,{11,13,17,101,1009}), (4,{11,13,17,101,1009}),
(5,{11,13,17,101}). Per cell the engine certifies: freeness premise
(T_k = |A|), the identity (float + both modular primes), the deviation
decomposition Σδ^{k−s}D_s = δp − δ^k p², the L-EP-k floor (when the premise
δ^{k−1}p ≥ 2 holds), the pair-structure bounds (per-layer and aggregate),
Parseval exactly, the cap, and — at k = 4 — both D4-GEN bounds, X-4(i)
(whenever c_4 > 0), X-4(ii) (whenever the premise holds), L-TERM-4; at
k = 3 — F2-SHARP, the banked F2 form, L-TERM-3-SHARP. Measured greedy
cells (δ, T_k = |A|, M): (3,1009): δ=0.0634, M=44.9; (4,1009): δ=0.1397,
M=66.3 (X-4(ii) demand 1.02 — holds with 65× room); (5,101): δ=0.3960,
M=17.8. The premise δ^{k−1}p ≥ 2 is the binding constraint on the small
cells (e.g. (4,11): δ³p = 1.79 < 2 — vacuous cells recorded, never hidden).

---

## §4. THE ENGINE CERTIFICATION TABLE — 51/51 ALL GREEN

`engine142deviation.py --verify` (deterministic, seed 81142, budget 330s,
wall 111.0s; receipts rewritten in full at every run):

| # | Check | Certifies | Verdict |
|---|---|---|---|
| 1–3 | S1-IDENTITY k=3 p=11/13/17 | D1-k by M1+M2+M3(2 primes)+M4, 6 sets/cell | PASS |
| 4–6 | S1-IDENTITY k=4 p=11/13/17 | same, 4 methods | PASS |
| 7–9 | S1-IDENTITY k=5 p=11/13/17 | same | PASS |
| 10–12 | S1-IDENTITY k=6 p=11/13/17 | same | PASS |
| 13–15 | S1-IDENTITY k=3/4/5 p=101 | same, 4 sets/cell | PASS |
| 16 | S1-IDENTITY k=6 p=101 | M3+M4 (float s=6 skipped, recorded) | PASS |
| 17–18 | S1-IDENTITY k=3/4 p=1009 | M1+M2+M3 | PASS |
| 19 | S1-OPT k=5 p=1009 | optional cell, M3 at q=10091: exact | PASS |
| 20 | S1-F1-REPRO | k=3 layer ≡ banked F1 kernel, float+modular byte-equality | PASS |
| 21 | S2-VANISH-s2 | every 2-subset system (k=3..8, p∈{11,13,17,101}) trivial only | PASS |
| 22 | S2-VANISH-s1 | s=1 vanishing exact in ℤ | PASS |
| 23 | S2-DIMENSION | #V_S = p^{s−2}; parametrized tuples solve; s≤4 exhaustive | PASS |
| 24 | S2-DIR-NONZERO | 3-subset directions all-nonzero mod p | PASS |
| 25 | S2-CLASSIFY | λ-mult tables k=3..8 exact; k=4 = {2:2, 3:1, 3/2:1} | PASS |
| 26 | S2-AFFINE-INVARIANCE | E equal per class + dihedral E_λ = E_{λ/(λ−1)} | PASS |
| 27 | S2-K4-CLOSED-FORMS | D_3(4) = 2E_2+2E_3; D_4(4) closed form | PASS |
| 28 | S2-NEGCONTROL-p<=k | p=5,k=8: 2-subset {0,5} has 5 solutions — hypothesis load-bearing | PASS |
| 29–33 | S3-GREEDY k=3 p=11/13/17/101/1009 | premise + identity + extraction plug-backs | PASS |
| 34–38 | S3-GREEDY k=4 p=11/13/17/101/1009 | + D4-GEN, X-4(i)/(ii), L-TERM-4 plug-backs | PASS |
| 39–42 | S3-GREEDY k=5 p=11/13/17/101 | premise + identity + extraction plug-backs | PASS |
| 43 | S3-OB4-ARITH | 2p²21² < (31p−462)² exact at 6 primes; FAILS at 349 | PASS |
| 44 | S3-C4-SIGN | c_4(δ) > 0 ⟺ δ > 2−√2 (8-point grid) | PASS |
| 45 | S3-TERM-CONSTS | (10−√10)/9 = 0.759746927; 2−√2 = 0.585786438 | PASS |
| 46 | S3-TC4-CARRIAGE | (1−δ)²/δ² ≤ 1/4 ⟺ δ ≥ 2/3 — EXACT rationals, δ=2/3 boundary exact | PASS |
| 47 | S4-NC1-SIGN-CORRUPT | f̂(−2t)→f̂(+2t) breaks the identity — DETECTED | PASS |
| 48 | S4-NC2-MULTIPLICITY | 2E_2+1E_3 corrupt multiplicities — DETECTED | PASS |
| 49 | S4-NC3-PHANTOM-LAYER | planted s=2 layer breaks identity — V2-k load-bearing | PASS |
| 50 | S4-NC4-PLANTED-AP | planted 4-AP: T_4=19 > |A|=9 — premise checker DETECTS | PASS |
| 51 | S4-NC5-PREMISE-REFUSES | non-free dense set: T_4 ≠ |A| — L-EP-k premise refuses | PASS |

**CHECKS: 51/51 passed. WALL: 111.0s. ENGINE VERDICT: ALL GREEN.**

The S3-TC4-CARRIAGE line is certified in EXACT rational arithmetic
(Fraction): the law (1−δ)²/δ² ≤ 1/4 ⟺ δ ≥ 2/3 is TRUE at the boundary
δ = 2/3 ((1/9)/(4/9) = 1/4 exactly); the original float check evaluated
the boundary as 0.2500000000000001 > 1/4 and failed — a rounding artifact,
not mathematics. The fix (W81-142A-F) changed ONLY the arithmetic to exact
rationals; the biconditional, the law, and every other check are untouched.

### Arsenal laws cited (read at their lines this wave)

    #BY GST LAW hc_fourier_character_norm [arsenal-full/HC-PROOF-research/GSTAnalyticAbsorption.lean:202]
    #BY GST LAW hc_fourier_exponential     [arsenal-full/HC-PROOF-research/GSTAnalyticAbsorption.lean:210]
    #BY GST LAW hc_fourier_unitary         [arsenal-full/HC-PROOF-research/GSTAnalyticAbsorption.lean:216]
    #BY GST LAW hc_circle_L2_basis         [arsenal-full/HC-PROOF-research/GSTAnalyticAbsorption.lean:236]
    #BY GST LAW gst_infinite_paradox_energy_split [arsenal-full/erdosternary2/ErdosTernary2.lean:8320]
    #BY GST LAW exact_three_geometric_sum  [arsenal-full/erdosternary2/GSTProblem406TerminalUBoundary.lean:135]
    #BY GST LAW cubic_expansion            [arsenal-full/HC-PROOF-research/CardinalWorlds.lean:283]
    #BY GST LAW tower_cauchy               [arsenal-full/erdosternary2/bulldoze/problem261-continuum-tower/Erdos261Tower.lean:810]
    #BY GST LAW sum_le_sum_of_forall       [arsenal-full/erdosternary2/bulldoze/problem261-continuum-tower/Erdos261Tower.lean:116]
    #BY GST LAW digit3_congr               [arsenal-full/HC-PROOF-research/GSTBladeWave.lean:72]
    #BY GST LAW mod_mod_mul                [arsenal-full/HC-PROOF-research/CardinalWorlds.lean:140]
    #BY GST LAW carryAtPos_bound           [arsenal-full/HC-PROOF-research/CardinalWorlds.lean:108]
    #BY GST LAW div_add_mod_subst          [arsenal-full/HC-PROOF-research/CardinalWorlds.lean:249]
    #BY GST LAW sq_sub_one                 [arsenal-full/HC-PROOF-research/CardinalWorlds.lean:448]
    #BY GST LAW two_pow_ge2                [arsenal-full/HC-PROOF-research/CardinalWorlds.lean:431]
    #BY GST LAW digitCount3_monotone       [arsenal-full/erdosternary2/ErdosTernary2.lean:2097]

(16 distinct laws, every one read at its exact line in arsenal-full/ before
citation.) NEW laws created by this document (all machine-certified by
engine142deviation.py, 51/51): **FULL-GROUP-SUM** (§0), **the order-k
deviation split** (§1.1), **LEMMA PAR** (§1.2), **THEOREM CLS-3** (§1.3),
**THEOREM V2-k** (§2), **L-EP-k** (§3.1), **PB-GEN** (§3.2), **D4-GEN**
(§3.3), **THEOREM X-4** (§3.4), **F2-SHARP** (§3.4iii), **TC-4** (§3.5),
**L-TERM-3-SHARP** (§3.6), **L-TERM-4** (§3.7), **OB-4** (§3.8) — ledger
entries in NEW_LAWS_142.md; claims C142-DEVIATION-K, C142-VANISH-K,
C142-EXTRACT-K in NEW_CLAIMS.md and the comparator solution ledger.

*The engine never stops; it never lies. In English, always.*
