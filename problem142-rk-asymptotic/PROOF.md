# PROOF.md — Erdős Problem #142: the attacker mathematics

**Wave 1 · Task 1-a · Sub-agent W1-A1 (ATTACKER).**
**Wave 71 · Task 4-e · Sub-agent W71-142K (KILLER lane): §3B added — the
Behrend theorem lands (complete six-step proof, explicit constants).**
Repo: `/home/z/erdos-weak-problems` (branch `campaign`, HEAD `fa4a160`).
Directory: `problem142-rk-asymptotic/`.

---

## §0. TARGET AND HONESTY LABEL

**Target (verbatim, corpus page `/tmp/ep142.html`):**
> "Let $r_k(N)$ be the largest possible size of a subset of $\{1,\ldots,N\}$
> that does not contain any non-trivial $k$-term arithmetic progression.
> Prove an asymptotic formula for $r_k(N)$."

Corpus state: Erdős — "probably unattackable at present" (Er97c), "probably
enormously difficult", $10000 prize (Er81). Best upper bounds: Kelley–Meka
(k=3), Green–Tao (k=4), Leng–Sah–Sawhney (k≥5). An asymptotic formula is out
of reach even for k=3.

**SELECTION HONESTY LAW (binding).** The full asymptotic formula is OPEN and is
NOT proven here. What this file proves, unconditionally and in full rigor, is
the strongest complete package on the assigned Cardinal-Worlds-native front:

1. **Theorem A** — the Cantor-verdict 3-AP-free law (two independent complete
   proofs: the no-carry digit identity, and the digit-window descent), plus its
   all-order extension (k-AP-free for every k ≥ 3).
2. **Theorem B** — the lower-bound law: `r_3(N) ≥ N^{log_3 2}` for infinitely
   many N (N = 3^m, and N = 3^m − 1), and complete monotone interpolation for
   ALL N ≥ 1 (two forms, constants 1/2 and 2^{log_3 2 − 1}).
3. **Theorem C** — the prime-world strip law (digit-restriction families over
   prime bases), with the exact k = 4 and k = 5 frontier laws the task
   assigned, and the exponent optimization table.
4. **Theorem D** — the no-carry column law (base 2k−3, digits {0,…,k−2},
   any k ≥ 3, no primality needed).
5. **Theorem E** — the base-4 wall: a complete NEGATIVE theorem (every
   3-element base-4 digit family provably contains a non-trivial 4-AP —
   the naive "base k, drop one digit" pattern dies at k = 4).
6. **Theorems F, G, H** — the structure of the Cantor family: exact gap law,
   two-sided counting law, and the 6-world factorization
   `#{n < 6^j : Cantor} = 2^j · #{n < 2^j : Cantor}` (the Arsenal product law
   `6^j = 2^j·3^j` manifesting in the counting function).
7. **Exact census** — r_3(N) for N ≤ 62, r_4(N) for N ≤ 36, r_5(N) for
   N ≤ 30, by exhaustive branch-and-bound, cross-verified by Z3 Optimize,
   by cold-start re-derivation, and by pure subset enumeration (N ≤ 18).
8. **Theorem 3B.7 (the Behrend theorem, §3B)** — the sphere construction,
   complete and self-contained in six steps with EXPLICIT constants:
   r_3(N) ≥ N·e^{−6√(ln N)} for every N ≥ 16 (master base-2 form:
   r_3(N) ≥ N/(u·2^{1+4u}) with u = ⌊√(log₂ N)⌋; and the same bound for
   r_k(N) for every k ≥ 3). The explicit witness families are
   machine-certified (§6.8, engine142behrend.py + receipts142behrend.txt).

**Everything below is unconditional. Classical literature is cited only as
context (§10); no external black-box theorem is used in any proof.** All
machine claims carry the two-method protocol (§6, receipts in this directory).

**Notation.** k ≥ 3 fixed throughout; α := log_3 2 = ln 2 / ln 3 ≈ 0.63093.
A *k-term arithmetic progression* (k-AP) is a list (x_0, x_1, …, x_{k−1}) with
x_t = x_0 + t·d for a common d ≥ 0; it is **non-trivial** iff d > 0 (iff the
terms are pairwise distinct). A set S is *k-AP-free* if it contains no
non-trivial k-AP (equivalently: no k distinct elements in AP). r_k(N) := max
{|S| : S ⊆ {1,…,N}, S k-AP-free}.

---

## §1. PRELIMINARIES — digits, representations, elementary laws

Throughout, b ≥ 2 is an integer base. For n ∈ ℕ and p ≥ 0:

    digit_p(n) := (n div b^p) mod b        (the base-b digit of n at position p)

— this is exactly the Arsenal ternary reader `gstDigit R p := R / 3^p % 3`
(CardinalWorlds §11), used here at general base b.

### Lemma 1.1 (existence of digits).
For every n ≥ 0 there exist m ≥ 0 and d_0,…,d_{m−1} ∈ {0,…,b−1} with
n = Σ_{p<m} d_p b^p (empty sum = 0).

**Proof.** Strong induction on n. If n < b take m = 1, d_0 = n. If n ≥ b,
write n = b·q + r with q = n div b, r = n mod b ∈ {0,…,b−1} (Euclidean
division). Then q ≥ 1 and b·q ≤ n, so q ≤ n/2 < n. By the induction
hypothesis q = Σ_{p<t} e_p b^p with e_p ∈ {0,…,b−1}; then n = Σ_{p<t} e_p
b^{p+1} + r is a representation with digits (r, e_0, e_1, …, e_{t−1}). ∎

### Lemma 1.2 (uniqueness of digits).
If Σ_{p<m} d_p b^p = Σ_{p<m'} e_p b^p with all d_p, e_p ∈ {0,…,b−1}, then
d_p = e_p for all p (after padding the shorter list with zeros).

**Proof.** Induction on M := max(m, m'); pad both lists to length M with
zeros (padding does not change the value). If M = 0 both sides are 0 and
there is nothing to prove. Otherwise reduce the identity modulo b: since
b ≡ 0 (mod b), d_0 ≡ e_0 (mod b), and both lie in {0,…,b−1}, so d_0 = e_0.
Subtract and divide by b (both sides of the remainder are divisible by b):
Σ_{p<M−1} d_{p+1} b^p = Σ_{p<M−1} e_{p+1} b^p. The induction hypothesis
gives d_{p+1} = e_{p+1} for all p < M−1. ∎

### Lemma 1.3 (the reader is the representation).
For every n ≥ 0: n = Σ_{p≥0} digit_p(n)·b^p, a finite sum; and if
n = Σ d_p b^p is any representation with digits in {0,…,b−1}, then
d_p = digit_p(n) for every p.

**Proof.** First, n = Σ_p digit_p(n) b^p: induction on n. n < b: digit_0(n) = n
and digit_p(n) = 0 for p ≥ 1 (n div b = 0). n ≥ b: n = b·q + r, q = n div b <
n, r = n mod b = digit_0(n); by induction q = Σ_p digit_p(q) b^p, and
digit_p(n) = digit_{p−1}(q) for p ≥ 1 by Lemma 1.4 below (whose proof uses
only Euclidean division, not this lemma); hence
n = b·Σ_p digit_p(q) b^p + r = Σ_{p≥1} digit_{p−1}(q) b^p + r. Second, given
any representation, Lemma 1.2 applied to it and to the reader representation
(which Lemma 1.1 guarantees exists for the same n) forces coefficient
equality. ∎

### Lemma 1.4 (digit shift law).
For all n ≥ 0, p ≥ 0: digit_p(n div b) = digit_{p+1}(n).
Equivalently (n div b) div b^p = n div b^{p+1}.

**Proof.** Write n = b^{p+1}·Q + R with 0 ≤ R < b^{p+1} (Euclidean division;
n div b^{p+1} = Q). Also n = b·q + r with q = n div b, r = n mod b. Since
r ≡ n ≡ R (mod b), R − r = b·s for an integer s, and 0 ≤ R − r < b^{p+1} gives
0 ≤ s < b^p. Then b·q = n − r = b^{p+1}Q + (R − r) = b^{p+1}Q + b·s, so
q = b^p·Q + s with 0 ≤ s < b^p: hence q div b^p = Q, i.e.
(n div b) div b^p = n div b^{p+1}. Reducing mod b: digit_p(n div b) =
((n div b) div b^p) mod b = (n div b^{p+1}) mod b = digit_{p+1}(n). ∎

(Arsenal cognate: `CardinalWorlds.div_mod_mul_lemma` proves the companion
digit-extraction law `(n % (a*b)) / a = (n / a) % b`; `CardinalWorldsV2`
builds the exact reader duality on it.)

### Lemma 1.5 (no-carry digit-sum law).
Let x, y ≥ 0. If digit_p(x) + digit_p(y) ≤ b−1 for every p, then
digit_p(x + y) = digit_p(x) + digit_p(y) for every p. In particular, if
2·digit_p(y) ≤ b−1 for every p, then digit_p(2y) = 2·digit_p(y).

**Proof.** By Lemma 1.3, x = Σ digit_p(x) b^p and y = Σ digit_p(y) b^p, so
x + y = Σ (digit_p(x) + digit_p(y)) b^p — and each coefficient lies in
{0,…,b−1} by hypothesis, with finitely many nonzero. This is a valid
representation of x+y; by Lemma 1.3 its coefficients are the reader values
digit_p(x+y). ∎

### Lemma 1.6 (units digit of the AP terms).
If x ≡ x′ (mod b) with u := x mod b, then x div b = x′ div b and
digit_p(x div b) = digit_{p+1}(x) for all p (Lemma 1.4).

### Lemma 1.7 (a k-AP contains a 3-AP).
Every k-term AP with k ≥ 3 contains a non-trivial 3-term AP; hence every
3-AP-free set is k-AP-free for every k ≥ 3.

**Proof.** The first three terms x_0, x_1, x_2 = x_0 + d, x_0 + 2d are a 3-AP;
it is non-trivial exactly when d ≠ 0, which is exactly when the k-AP is
non-trivial. ∎

### Lemma 1.8 (translation invariance).
For S ⊆ ℤ and t ∈ ℤ: S is k-AP-free iff S + t := {s + t : s ∈ S} is.
**Proof.** x ↦ x + t is a bijection and (x_0,…,x_{k−1}) is a k-AP iff
(x_0 + t, …, x_{k−1} + t) is (common difference unchanged). ∎

### Lemma 1.9 (monotonicity).
r_k(N) ≤ r_k(N+1) for all N ≥ 1, and r_k is unchanged if {1,…,N} is replaced
by any translate {i,…,j} of length N (Lemma 1.8 applied to max-size sets).

### Lemma 1.10 (suffix bound — soundness of the census pruning).
Any k-AP-free subset of {i,…,N} has at most r_k(N−i+1) elements.

**Proof.** Translate by −(i−1) into {1,…,N−i+1}; the translate is k-AP-free
(Lemma 1.8) so its size is ≤ r_k(N−i+1). ∎

### Lemma 1.11 (scaling by 2 preserves AP-freeness; digit-doubling).
If every digit d of a digit family satisfies 2d ≤ b−1, then the map
n = Σ d_p b^p ↦ 2n = Σ (2d_p) b^p is a bijection from the family onto the
family with digit set 2D := {2d : d ∈ D} (Lemma 1.5: no carries), and
S is k-AP-free iff 2S is (x ↦ 2x sends k-APs with difference d to k-APs with
difference 2d, and conversely on the image). ∎
(Example: base 6, D = {0,2,4} equals 2×(base 6, D = {0,1,2}) — see §4 Ex. 4.4.)

### Arsenal alignment of §1.
The ternary instance (b = 3) of digit_p is `CardinalWorlds.gstDigit`;
`ErdosTernary2.lt_three_cases` and `ternary_digit_lt_three` are the digit-range
trichotomy at base 3; `isTernaryDigit` and its `zero/one/two/three` lemmas are
the recognizer; `empty_foldr_repr_zero`, `single_digit_value`,
`two_digit_value` are the fold-based value chain (the Lean-side semantics of
Σ d_p 3^p); `div_mod_mul_lemma`, `mul_add_div_lemma`, `mod_mod_mul` are the
div/mod skeleton used by the shift/extraction laws; `noTernaryTwo` /
`hasTernaryTwo` / `no_two_false_iff_digit_witness` / `hasTernaryTwo_of_digit`
are the verdict-scan duality used in §2.

---

## §2. THEOREM A — the Cantor-verdict AP-free law

For m ≥ 0 define the **Cantor family of depth m** (the 3-world of the
Cardinal Worlds):

    C_m := { n ∈ ℕ : n < 3^m and every ternary digit of n lies in {0,1} }.

This is exactly the family cut out by the Arsenal Cantor verdict:
noTernaryTwo n = true ⟺ no ternary digit of n equals 2 ⟺ all ternary digits
of n lie in {0,1} (the equivalence of the verdict and the digit statement is
the Arsenal duality `has_two_iff_no_two_false` + `no_two_false_iff_digit_witness`;
in V2 form: `has_two_iff_first_signature`). So C_m = {n < 3^m : noTernaryTwo n}.

**Fact A.0 (size and max).** |C_m| = 2^m and max C_m = (3^m − 1)/2, with the
maximum attained only by the all-ones number 1 + 3 + … + 3^{m−1}.

*Proof.* The map ε ∈ {0,1}^m ↦ Σ_{p<m} ε_p 3^p is a bijection onto C_m by
Lemmas 1.1/1.3 (every element of C_m has its m digit positions in {0,1}; every
ε gives a valid representation of an n < 3^m; Lemma 1.2 makes both directions
unique). Hence |C_m| = 2^m. The value Σ ε_p 3^p is maximized, and uniquely so,
by ε = (1,…,1), giving (3^m − 1)/(3−1) = (3^m−1)/2. ∎

### Theorem A (Cantor-verdict 3-AP-free law).
Let x, y, z ∈ ℕ with x + z = 2y. If all ternary digits of x, of y, and of z
lie in {0,1} (noTernaryTwo x = noTernaryTwo y = noTernaryTwo z = true), then
x = y = z. Consequently, for every m, C_m contains no non-trivial 3-term
arithmetic progression.

**Proof 1 (the no-carry digit identity).**
Write ξ_p := digit_p(x), υ_p := digit_p(y), ζ_p := digit_p(z) (base 3; Lemma
1.3). Each of ξ_p, υ_p, ζ_p ∈ {0,1}, so:

* ξ_p + ζ_p ∈ {0,1,2} ≤ 2 = b−1 for every p, and 2υ_p ∈ {0,2} ≤ 2 for
  every p. **No carries occur**, in the exact sense of Lemma 1.5:

      digit_p(x + z) = ξ_p + ζ_p   and   digit_p(2y) = 2υ_p    for every p.

* The identity x + z = 2y says the two numbers are equal; by Lemma 1.2
  (uniqueness of the ternary representation) their digit sequences are
  identical position by position:

      ξ_p + ζ_p = 2υ_p        for every p ≥ 0.                                (†)

* Fix p. Equation (†) says the sum ξ_p + ζ_p is even. Since ξ_p, ζ_p ∈ {0,1},
  the only odd sum is 0 + 1 = 1; hence ξ_p = ζ_p. Then (†) reads
  2ξ_p = 2υ_p, i.e. ξ_p = υ_p. So ξ_p = υ_p = ζ_p for every p.

* All ternary digits agree; by Lemma 1.3 (the reader is the representation)
  x = y = z. ∎

Every step is explicit: representation existence (1.1), reader = value (1.3),
no-carry digit arithmetic (1.5), uniqueness (1.2), and the final digit solve.
There is no gap and no circularity: Lemmas 1.1–1.5 depend only on Euclidean
division.

**Proof 2 (the digit-window descent — the Lean-kernel proof).**
Induction on y (strong, on the natural order). If y = 0 then x + z = 0 with
x, z ≥ 0 forces x = z = 0 = y. Suppose y > 0. Look at position 0 and reduce
x + z = 2y modulo 3. With ξ_0, υ_0, ζ_0 ∈ {0,1}:

    ξ_0 + ζ_0 ≡ 2υ_0   (mod 3),   ξ_0 + ζ_0 ∈ {0,1,2},  2υ_0 ∈ {0,2}.

* If (ξ_0, ζ_0) = (0,0): 2υ_0 ≡ 0 (mod 3) with 2υ_0 ∈ {0,2} forces υ_0 = 0
  (2 is not 0 mod 3).
* If (ξ_0, ζ_0) = (1,1): 2υ_0 ≡ 2 (mod 3) forces υ_0 = 1 (0 is not 2 mod 3).
* If {ξ_0, ζ_0} = {0,1}: ξ_0 + ζ_0 = 1 ≡ 2υ_0 (mod 3) — impossible, since
  2υ_0 ∈ {0,2} is congruent to 0 or 2 mod 3, never to 1.

So ξ_0 = υ_0 = ζ_0 =: u ∈ {0,1}, and writing x = 3q_x + u, y = 3q_y + u,
z = 3q_z + u (Euclidean division), the equation x + z = 2y becomes
3(q_x + q_z) + 2u = 3·2q_y + 2u, i.e. **q_x + q_z = 2q_y** — the equation
descends to the quotients. The quotients still have all ternary digits in
{0,1} (Lemma 1.4: digit_p(n div 3) = digit_{p+1}(n)), and q_y = y div 3 < y
(y > 0, base 3). By the induction hypothesis q_x = q_y = q_z. Reassembling
n = 3(n div 3) + n mod 3 gives x = y = z. ∎

(Proof 2 is formalized, statement-for-statement, in
`problem142-rk-asymptotic/AuditKernel142.lean` — `noTernaryTwo_ap3_free` —
written by the Wave-1 doubter agent against the Arsenal readers; it is an
UNCOMPILED kernel draft whose verifier of record is the repo CI.)

### Corollary A.2 (all orders).
C_m is k-AP-free for EVERY k ≥ 3. **Proof.** Lemma 1.7 + Theorem A. ∎

### Corollary A.3 (machine receipts).
Theorem A is machine-verified by three independent engines: exhaustive AP
scans of C_m for m ≤ 12 (census2.py E1: 0 non-trivial 3-APs; 0 k-APs for
k = 3..12), two Z3 encodings (digit-sum and div/mod reader encodings) proving
UNSAT for m ≤ 8 (verify_z3.py Z1), and all-order pair scans for k = 3..8,
m ≤ 7 (census.py C). See §6.

---

## §3. THEOREM B — the lower-bound law (infinitely many N; ALL N)

### Theorem B.1 (the two-fold covering — the bridge 3 = 1 + 2).
C_m + C_m = {c + c′ : c, c′ ∈ C_m} = {0, 1, …, 3^m − 1}.

**Proof.** ⊆: each c ≤ (3^m−1)/2 so sums are ≤ 3^m − 1. ⊇: let n < 3^m with
ternary digits ν_p ∈ {0,1,2} (Lemma 1.3). Define ε_p := ⌈ν_p/2⌉ ∈ {0,1} and
ε′_p := ν_p − ε_p ∈ {0,1} (digit-wise: 0 → (0,0), 1 → (1,0), 2 → (1,1)). Then
c := Σ ε_p 3^p ∈ C_m, c′ := Σ ε′_p 3^p ∈ C_m, and ε_p + ε′_p = ν_p ≤ 2, so
Lemma 1.5 gives digit_p(c + c′) = ν_p for every p; hence c + c′ = n by
Lemma 1.3. ∎

This is the Cardinal-Worlds bridge `3 = 1 + 2` in digit form: **every
ternary digit 2 splits into two Cantor digits 1 + 1, with no carries** — the
mixed world is the sum of the two pure worlds. (Machine: census.py [C1],
m ≤ 7.)

### Theorem B.2 (the infinitely-many-N law).
For every m ≥ 1:

    r_3(3^m − 1) ≥ 2^m   and   r_3(3^m) ≥ 2^m,

and consequently r_3(N) ≥ N^α for the infinitely many N = 3^m − 1 (and
N = 3^m), since 2^m = (3^m)^α ≥ (3^m − 1)^α.

**Proof.** Consider C_m + 1 = {c + 1 : c ∈ C_m}. By Theorem A and Lemma 1.8 it
is 3-AP-free; its size is 2^m (Fact A.0). Its elements lie in
{1, …, (3^m − 1)/2 + 1}. For m ≥ 1, (3^m−1)/2 + 1 ≤ 3^m − 1 (equivalent to
3^m ≥ 3), so C_m + 1 ⊆ {1,…,3^m − 1} ⊆ {1,…,3^m}, giving both bounds.
Finally (3^m)^α = 3^{mα} = 3^{m·log_3 2} = 2^m and (3^m−1)^α ≤ (3^m)^α. ∎

### Theorem B.3 (monotone interpolation — ALL N ≥ 1, complete derivation).
(i) For every N ≥ 1:   r_3(N) ≥ 2^{⌊log_3 N⌋} > N^α / 2.
(ii) Sharper (half-interval law): for every N ≥ 1,

    r_3(N) ≥ 2^{t(N)} − 1,  where  t(N) := max{m ≥ 0 : (3^m − 1)/2 ≤ N}
                          = ⌊log_3 (2N + 1)⌋,

    hence  r_3(N) ≥ (2N+1)^α / 2 − 1 ≥ (2N)^α/2 − 1 = 2^{α−1} N^α − 1
                     (2^{α−1} ≈ 0.774).

**Proof.** (i) Let m := ⌊log_3 N⌋, so 3^m ≤ N. By Lemma 1.9 (monotonicity)
and Theorem B.2, r_3(N) ≥ r_3(3^m) ≥ 2^m. Since 3^m > N/3,
2^m = (3^m)^α > (N/3)^α = N^α / 3^α = N^α/2 (using 3^α = 3^{log_3 2} = 2). ∎

(ii) C_m \ {0} ⊆ {1, 2, …, (3^m − 1)/2} is 3-AP-free of size 2^m − 1
(Theorem A); if (3^m−1)/2 ≤ N this set lives inside {1,…,N}, so
r_3(N) ≥ 2^m − 1. Maximizing over admissible m gives m = t(N), and
t(N) = ⌊log_3(2N+1)⌋ because (3^m −1)/2 ≤ N ⟺ 3^m ≤ 2N+1 ⟺ m ≤ log_3(2N+1)
(the last step since m is an integer). For the constant: 3^{t} ≤ 2N+1, so

    2^t = (3^t)^α ≥ ((2N+1)/3)^α = (2N+1)^α / 3^α = (2N+1)^α / 2,

using 3^{t+1} ≥ 2N+1 (definition of the floor) and 3^α = 2. Hence
r_3(N) ≥ 2^t − 1 ≥ (2N+1)^α/2 − 1 ≥ (2N)^α/2 − 1 = 2^{α−1}N^α − 1. ∎

**Sharpness receipts (machine, §6):** r_3(N) ≥ 2^{⌊log_3 N⌋} holds with room
to spare on the whole table N ≤ 62; and at the half-interval points
N = (3^m−1)/2 the census gives EQUALITY r_3(N) = 2^m − 1 for m = 1,2,3,4
(N = 1, 4, 13, 40) — the Cantor construction is OPTIMAL there (for those N;
the general statement is open). At the other special points, r_3(3^m −1) ≥ 2^m
is confirmed (r_3(2)=2, r_3(8)=4, r_3(26)=11) and r_3(9) = 5 > 4 = 2^2 shows
Cantor is NOT optimal at N = 3^2 (already {1,2,4,8,9} beats it).

**Honest remark.** The constants 1/2 and 2^{α−1} are construction constants of
the Cantor frame, not the truth: the true liminf of r_3(N)/N^α is open. The
Cantor power law is now COMPLETED from below by the Behrend theorem of §3B:
the sphere construction proved there gives r_3(N) ≥ N·e^{−6√(ln N)} for all
N ≥ 16 — a bound that eventually dominates every power N^{1−ε} (and is
itself dominated by the Cantor bound below N ≈ 10^{115}; see the honest
remark closing §3B). Nothing in §3 depends on any classical result.

---

## §3B. THE BEHREND THEOREM — the sphere construction, complete and self-contained

The Cantor frame of §3 delivers the power bound r_3(N) ≥ N^α/2
(α = log₃ 2 ≈ 0.6309). Behrend's 1946 idea delivers exponentially more:
a lower bound of the form N·e^{−C√(ln N)}. This section proves that bound
FROM SCRATCH, in six steps, with every constant explicit. Nothing external is
used: STEP 1 is pure algebra (Lagrange's identity, with both equality cases
spelled out); STEP 2 is the no-carry digit law of §1 transplanted to base
B = 2m — the general-B instance of the law whose base-3 instance (backed by
the Arsenal `carryAtPos` family) proved Theorem A; STEPs 3–6 are bookkeeping
and an explicit rational constant conversion anchored on two Taylor exhibits.
The final constants are **C = 6, N₀ = 16**.

### THEOREM 3B.7 (Behrend 1946, self-contained, explicit constants).

**(i) Master form (base 2, integer-exact).** For every integer N ≥ 16, with

    u := ⌊√(log₂ N)⌋   (so u ≥ 2),

    r_3(N) ≥ N / (u · 2^(1+4u)).

**(ii) Exponential form.** For every integer N ≥ 16:

    r_3(N) ≥ N · e^(−6·√(ln N)).

**(iii) Explicit witness.** The proof yields a machine-generatable 3-AP-free
family W_N ⊆ [1, N] with |W_N| ≥ N·e^(−6√(ln N)) (Corollary 3B.9).

The six steps follow. Throughout, d ≥ 1 and m ≥ 2 are integers,

    D := {0, 1, …, m−1}^d  (the digit cube),   Q(x) := x₁² + … + x_d²,

and for an integer V ≥ 0 the **level set** (sphere when V is a square)

    S_V := { x ∈ D : Q(x) = V }.

---

### STEP 1 (Lemma 3B.1). Every level set of the square form is midpoint-free.

**Lemma 3B.1.** Let x, y, z ∈ D with x + z = 2y (componentwise) and
Q(x) = Q(y) = Q(z). Then x = y = z. Consequently, for every V, the level set
S_V contains no three DISTINCT elements p, q, r with p + r = 2q.

**Proof.** From x + z = 2y we get y = (x+z)/2 componentwise (x + z is even in
every coordinate). Write |w| := √Q(w) (Euclidean norm) and ⟨x,z⟩ := Σ x_i z_i.
The proof is the chain

    Q(y) = |y|² = |x+z|²/4  ≤  ((|x|+|z|)/2)²  ≤  (Q(x)+Q(z))/2  =  Q(x),     (1)

with BOTH inequalities' equality cases analyzed; equality throughout forces
x = z, hence y = x.

**Inequality (1a) — the triangle inequality, with equality case.**
|x+z| ≤ |x| + |z|. Both sides are ≥ 0; squaring, this is equivalent to
Q(x) + 2⟨x,z⟩ + Q(z) ≤ Q(x) + 2|x||z| + Q(z), i.e. ⟨x,z⟩ ≤ |x||z| —
Cauchy–Schwarz. The algebraic proof is Lagrange's identity

    Q(x)·Q(z) − ⟨x,z⟩² = Σ_{1≤i<j≤d} (x_i z_j − x_j z_i)²  ≥ 0,             (2)

a sum of integer squares. Equality in (2) holds iff every 2×2 minor
x_i z_j − x_j z_i vanishes, iff (x, z) are linearly dependent (if x ≠ 0 and
z ≠ 0: z = λx for λ := z_1/x_1, all coordinates agreeing). If z = λx then
|x+z| = |1+λ|·|x| and |x|+|z| = (1+|λ|)·|x| (x ≠ 0), which are equal iff
1+λ = 1+|λ| iff λ ≥ 0. So **equality in (1a) iff z = λx for some λ ≥ 0**
(the degenerate cases x = 0 or z = 0 are included: 0 = 0·x).

**Inequality (1b) — QM–AM, with equality case.**
(|x|+|z|)/2 ≤ √((Q(x)+Q(z))/2). With a := |x| = √Q(x), b := |z| = √Q(z) this
is (a+b)² ≤ 2(a²+b²), i.e. (a−b)² ≥ 0 — equality **iff a = b, i.e. Q(x) = Q(z)**.

**End of chain.** Suppose Q(y) = Q(x) = Q(z) =: V.
* If V = 0: |x|² = 0, so x = 0; likewise z = 0; then y = (x+z)/2 = 0. Done.
* If V > 0: x ≠ 0 and z ≠ 0. Equality in (1b) gives |x| = |z| = √V. Equality
  in (1a) gives z = λx with λ ≥ 0, hence √V = |z| = λ|x| = λ√V, so λ = 1,
  i.e. **z = x**. Then y = (x+z)/2 = x. Done.

In both cases x = y = z. For the second statement: if p, q, r ∈ S_V are
distinct with p + r = 2q, the first statement (x = p, y = q, z = r — all on
the level V) forces p = q = r, a contradiction. ∎

*Geometric reading:* the midpoint of a chord of a sphere lies strictly inside
the sphere unless the chord is degenerate — strict convexity of w ↦ |w|²,
proved above by bare algebra (identity (2)), no black boxes.

---

### STEP 2 (Lemma 3B.2). The digit map at base B = 2m — injectivity and the no-carry pullback.

Let **B := 2m** and define the digit map

    φ : D → ℕ,   φ(x) := Σ_{i=1}^{d} x_i · B^(i−1)

(x_i is the base-B digit of φ(x) at position i−1).

**Lemma 3B.2.**
(i) φ is injective on D, and φ(D) ⊆ [0, B^d − 1].
(ii) (No-carry pullback.) If x, y, z ∈ D satisfy the INTEGER identity
φ(x) + φ(z) = 2φ(y), then x + z = 2y componentwise.

**Proof.** (i) Each x_i lies in {0,…,m−1} ⊆ {0,…,B−1}, so
φ(x) = Σ_{i=1}^d x_i B^{i−1} is a valid base-B representation of φ(x)
(Lemmas 1.1/1.3 read at base B), and by uniqueness of digits (Lemma 1.2 at
base B) the vector x is recovered from φ(x) as its digit sequence:
x_i = digit_{i−1}(φ(x)). Hence φ is injective. Moreover
φ(x) ≤ (m−1)·(1 + B + … + B^{d−1}) = (m−1)(B^d − 1)/(B − 1) ≤ B^d − 1
(since m − 1 ≤ B − 1 = 2m − 1).

(ii) Expand the identity:

    Σ_{i=1}^{d} (x_i + z_i − 2y_i) · B^(i−1) = 0.                            (3)

Set c_i := x_i + z_i − 2y_i. Since 0 ≤ x_i, y_i, z_i ≤ m−1,

    −2(m−1) ≤ c_i ≤ 2(m−1) = B − 2,   i.e.   −B < c_i < B.                   (4)

Induction on the number j of positions. *Claim:* for every j ≥ 0 and every
integer tuple (c_1, …, c_j) with property (4), the identity
Σ_{i=1}^{j} c_i B^{i−1} = 0 forces c_i = 0 for all i. j = 0: vacuous
(empty sum). j ≥ 1: reduce (3) modulo B — every term with i ≥ 2 is a multiple
of B — obtaining c_1 ≡ 0 (mod B). By (4), −B < c_1 < B, and the only multiple
of B in the open interval (−B, B) is 0; hence c_1 = 0. The remaining identity
Σ_{i=2}^{j} c_i B^{i−1} = 0 divides by B to give Σ_{i'=1}^{j−1} c_{i'+1}
B^{i'−1} = 0, and the shifted tuple still satisfies (4). The induction
hypothesis closes the claim. With j = d, (3) gives c_i = 0 for all i, i.e.
x_i + z_i = 2y_i for every i. ∎

**This is the no-carry digit law of §1, read as a pullback.** At base B,
digit sums x_i + z_i reach at most 2(m−1) = B−2 < B and 2y_i ≤ B−2 < B: the
identity φ(x) + φ(z) = 2φ(y), read position by position, never crosses a
multiple of B — "no carries" — so the digit sequences agree coordinate by
coordinate. The Arsenal proved the base-3 instance of exactly this discipline
(the `carryAtPos` family: `carryAtPos_bound`, `carryAtPos_one_mod3_0/1/2`, and
V2's `carryAtPos_one_exact` — the carry into position 1 is the units residue
itself; Theorem A Proof 1 is the base-3 verdict form). Behrend needs the law
at base B = 2m; Lemma 3B.2(ii) is that general-B law, proved above from
scratch (Euclidean reduction + induction on positions), with the Arsenal
base-3 law as the anchor instance.

**The hypothesis is load-bearing (negative control).** At base B′ := 2m − 2
one has 2(m−1) = B′, and a carry DOES occur: take m = 3 (digits {0,1,2}),
B′ = 4, d = 2, x = (0,1), y = (2,0), z = (0,0). Then
φ′(x) + φ′(z) = (0·1 + 1·4) + 0 = 4 = 2·(2·1 + 0·4) = 2φ′(y), but
x + z = (0,1) ≠ (4,0) = 2y: the pullback FAILS at B = 2m−2. The strict
inequality 2(m−1) < B is exactly what (4) needs. (Machine-certified: §6.8,
engine part C-NEG.) Any base B ≥ 2m−1 satisfies (4) (2(m−1) ≤ B−1 < B); we
use Behrend's classical B = 2m.

---

### STEP 3 (Proposition 3B.3). The integer image of a level set is 3-AP-free.

**Proposition 3B.3.** Fix d ≥ 1, m ≥ 2, B = 2m. For every V ≥ 0:

    A_V := φ(S_V) ⊆ [0, B^d − 1]

contains no non-trivial 3-term arithmetic progression, and neither does its
translate A_V + 1 = {a + 1 : a ∈ A_V} ⊆ [1, B^d]. Consequently

    r_3(B^d) ≥ |S_V|   for every V ≥ 0.

**Proof.** A non-trivial 3-term AP (p, p+δ, p+2δ) with δ ≥ 1 consists of
three DISTINCT integers a := p < b := p+δ < c := p+2δ with a + c = 2b.
Suppose a, b, c ∈ A_V. Since A_V = φ(S_V), write a = φ(x), b = φ(y), c = φ(z)
with x, y, z ∈ S_V — uniquely, by Lemma 3B.2(i). The identity a + c = 2b
reads φ(x) + φ(z) = 2φ(y); by Lemma 3B.2(ii), x + z = 2y componentwise; by
Lemma 3B.1 (x, y, z lie on the common level S_V), x = y = z; by injectivity
a = b = c — contradicting distinctness. So A_V is 3-AP-free. The translate
A_V + 1 is 3-AP-free by Lemma 1.8 (translation invariance), and
A_V + 1 ⊆ [1, B^d] because max φ(D) ≤ B^d − 1 (Lemma 3B.2(i)). Finally
|A_V + 1| = |A_V| = |S_V| (translation is a bijection), so the 3-AP-free set
A_V + 1 witnesses r_3(B^d) ≥ |S_V|. ∎

---

### STEP 4 (Lemma 3B.4). Some level is large (pigeonhole).

**Lemma 3B.4.**

    max_V |S_V| ≥ m^d / (d·(m−1)² + 1)   and, since |S_V| is integral,
    max_V |S_V| ≥ ⌈ m^d / (d·(m−1)² + 1) ⌉ ≥ m^d / (d·m²).

**Proof.** The cube D has m^d points and is the disjoint union of its
non-empty level sets S_V. For x ∈ D, 0 ≤ Q(x) ≤ d·(m−1)² (each coordinate
contributes at most (m−1)²), so V takes at most d(m−1)² + 1 integer values.
By the pigeonhole principle some V₀ ∈ [0, d(m−1)²] has
|S_{V₀}| ≥ m^d/(d(m−1)² + 1); integrality promotes this to the ceiling.
Finally d·m² − d(m−1)² − 1 = d(2m−1) − 1 ≥ 1·3 − 1 = 2 > 0 (using m ≥ 2,
d ≥ 1), so d(m−1)² + 1 ≤ d·m². ∎

---

### STEP 5 (Theorem 3B.5). Parameter choice — the master bound, base 2.

**Theorem 3B.5 (master bound).** Let L ≥ 4 be real, N := 2^L, and

    u := ⌊√L⌋,    m := 2^u,    d := ⌊ L/(1+u) ⌋,    N′ := (2m)^d.

Then:
(i) (2m)^d ≤ N (the construction fits inside [1, N]);
(ii) N′ · 2^(1+u) > N (the floor in d costs at most the factor 2^(1+u));
(iii) d ≤ u;
(iv) r_3(N) ≥ N′/(2^d · d · m²) ≥ N/(u · 2^(1+4u)).

In particular, for every INTEGER N ≥ 16 (so L = log₂ N ≥ 4 and
u = ⌊√(log₂ N)⌋ ≥ 2):

    r_3(N) ≥ N / (u · 2^(1+4u)).

**Proof.** First, the parameters are admissible: u = ⌊√L⌋ ≥ ⌊√4⌋ = 2 ≥ 1, so
m = 2^u ≥ 4 ≥ 2; and 1 + u ≤ 1 + √L ≤ 1 + L/2 ≤ L (using L ≥ 4 for √L ≤ L/2
and L ≥ 2 for the rest), so d = ⌊L/(1+u)⌋ ≥ 1.

(i) d(1+u) ≤ L by the definition of the floor, and
(2m)^d = (2^(1+u))^d = 2^(d(1+u)) ≤ 2^L = N.

(ii) d + 1 > L/(1+u) (floor), so (d+1)(1+u) > L, so
(2m)^(d+1) = 2^((d+1)(1+u)) > 2^L = N, i.e. N′ · 2^(1+u) > N.

(iii) √L < u + 1 (floor), so d ≤ L/(1+u) < L/√L = √L < u + 1; d is an
integer, so d ≤ u.

(iv) Chain the previous steps (all inequalities explicit):

    r_3(N) ≥ r_3(N′)                        [monotonicity, Lemma 1.9; N′ ≤ N by (i)]
           ≥ max_V |S_V|                    [Proposition 3B.3 at (d, m)]
           ≥ m^d / (d·m²)                   [Lemma 3B.4]
           = N′ / (2^d · d · m²)            [m^d = N′/2^d since N′ = (2m)^d]
           > N / (2^(1+u) · 2^d · d · m²)   [by (ii): N′ > N/2^(1+u)]
           ≥ N / (2^(1+u) · 2^u · u · 2^(2u))   [by (iii): 2^d ≤ 2^u, d ≤ u; m² = 2^(2u)]
           = N / (u · 2^(1+4u)).

The final statement is the specialization L := log₂ N (a real ≥ 4 for every
integer N ≥ 16). ∎

---

### STEP 6 (Lemma 3B.6 + Theorem 3B.7). The exponential form: C = 6, N₀ = 16.

The master bound is integer-exact but stated with base-2 exponentials. The
conversion to the form N·e^(−C√(ln N)) is a finite rational computation,
anchored on two Taylor exhibits. First the toolbox.

**Lemma 3B.6 (analytic toolbox; every item elementary).** Let ln denote the
natural logarithm (ln x := ∫₁^x dt/t for x > 0) and exp(x) := e^x :=
Σ_{k≥0} x^k/k! (absolutely convergent for all real x).

(T1) ln and exp are strictly increasing. For ln: the integrand 1/t is > 0.
For exp: exp(x)·exp(−x) = exp(0) = 1 (term-wise product of the absolutely
convergent series), so exp(x) > 0 for all real x, and
exp′(x) = Σ_{k≥1} x^{k−1}/(k−1)! = exp(x) > 0 (term-wise differentiation of
the uniformly-on-compacts convergent series).

(T2) For v ≥ 0: ln(1+v) = ∫₀^v dt/(1+t) ≤ ∫₀^v dt = v.

(T3) **ln 2 < 25/36.** Every partial sum of the positive series for e^x is a
strict lower bound: e^(25/36) > Σ_{k=0}^{8} (25/36)^k/k! =
45557920388276909/22749430293725184, and
45557920388276909 > 2·22749430293725184 = 45498860587450368
(excess 59059800826541). So e^(25/36) > 2, and (T1) gives ln 2 < 25/36.

(T4) **ln 2 > 9/13.** Taylor's theorem with Lagrange remainder at order 7:
e^x = Σ_{k≤7} x^k/k! + e^ξ·x^8/8! for some ξ ∈ (0, x). For x = 9/13 < 1,
e^ξ < e < 3 (e = Σ 1/k! < 1 + 1 + Σ_{k≥2} 2^(−(k−1)) = 3, since k! ≥ 2^(k−1)
for k ≥ 1 — induction). Hence
e^(9/13) < Σ_{k=0}^{7} (9/13)^k/k! + 3·(9/13)^8/8! = 7302823230379/3654473630080,
and 7302823230379 < 2·3654473630080 = 7308947260160 (deficit 6124029781).
So e^(9/13) < 2, and (T1) gives ln 2 > 9/13.

(T5) For real x: 2^x := e^(x·ln 2) (definition of the general power). Hence
N = 2^L gives t = ln N = L·ln 2, i.e. L = t/ln 2.

(T6) For s ≥ 3/2: (8/3)s − ln s ≥ 7/2. Proof: for 3/2 ≤ s₁ < s₂,
ln s₂ − ln s₁ = ln(1 + (s₂−s₁)/s₁) ≤ (s₂−s₁)/s₁ ≤ (2/3)(s₂−s₁) < (8/3)(s₂−s₁)
(by T2 and s₁ ≥ 3/2), so h(s) := (8/3)s − ln s is strictly increasing on
[3/2, ∞); and h(3/2) = 4 − ln(3/2) = 4 − ln(1 + 1/2) ≥ 4 − 1/2 = 7/2 (T2).

All fractions above are exact integer arithmetic; the two exhibits (T3), (T4)
are re-verified by machine in §6.8 (engine part D). ∎

**Theorem 3B.7 (Behrend, exponential form).** For every integer N ≥ 16:

    r_3(N) ≥ N · e^(−6·√(ln N)).

**Proof.** By Theorem 3B.5, r_3(N) ≥ N/(u·2^(1+4u)) with u = ⌊√(log₂ N)⌋.
Since u ≤ √L (L := log₂ N) and t ↦ t·2^(1+4t) is increasing for t ≥ 0
(both factors positive increasing),

    r_3(N) ≥ N / (√L · 2^(1+4√L)).                                            (5)

It remains to show √L·2^(1+4√L) ≤ e^(6√t) with t := ln N ≥ ln 16. Take logs
(T1) and substitute L = t/ln 2 (T5):

    ln(√L · 2^(1+4√L)) = ½ ln L + (1 + 4√L)·ln 2
                        = 4√(ln 2)·√t + ½ ln t + ln 2 + ½ ln(1/ln 2).        (6)

(Indeed √L = √t/√(ln 2), so 4√L·ln 2 = 4√(ln 2)·√t; and
½ ln L = ½ ln t − ½ ln(ln 2).) Bound each term of (6) from above:

* 4√(ln 2) ≤ 4·√(25/36) = 10/3    (T3);
* ln 2 ≤ 25/36                      (T3);
* ½ ln(1/ln 2) ≤ ½ ln(13/9) = ½ ln(1 + 4/9) ≤ 2/9    (T4, then T2).

So

    ln(√L·2^(1+4√L)) ≤ (10/3)√t + ½ ln t + 25/36 + 2/9 = (10/3)√t + ½ ln t + 11/12.   (7)

Now s := √t ≥ √(ln 16) = 2√(ln 2) > 2·√(9/16) = 3/2 (T4 gives
ln 2 > 9/13 > 9/16). By (T6): (8/3)√t − ½ ln t ≥ 7/2 > 11/12, i.e.

    ½ ln t + 11/12 ≤ (8/3)√t.                                                 (8)

Combining (7) and (8):

    ln(√L·2^(1+4√L)) ≤ (10/3)√t + (8/3)√t = 6√t,

i.e. √L·2^(1+4√L) ≤ e^(6√t). With (5):

    r_3(N) ≥ N/e^(6√t) = N·e^(−6√(ln N)). ∎

**Remark (the true shape of the constant).** The construction's intrinsic
exponent is 4√(ln 2) ≈ 3.3302 (plus a ½ ln ln N term and the floor losses);
the theorem's C = 6 absorbs every loss with room. Sharpening C toward
4√(ln 2) + ε is possible with more careful rounding; the asymptotically
optimal Behrend–Elkin-type constant is not pursued here — the claim is
exactly what is proved: (C, N₀) = (6, 16).

### Corollary 3B.8 (all orders k ≥ 3).

For every k ≥ 3 and every integer N ≥ 16:

    r_k(N) ≥ N · e^(−6·√(ln N)).

**Proof.** The witness set of Theorem 3B.7 is 3-AP-free, hence k-AP-free for
every k ≥ 3 by Lemma 1.7 (every k-AP with k ≥ 3 contains a non-trivial 3-AP:
its first three terms), and it is a subset of [1, N]. ∎

### Corollary 3B.9 (the explicit witness family; machine certificates).

For N ≥ 16 let u = ⌊√(log₂ N)⌋, m = 2^u, d = ⌊log_{2m} N⌋ (these are exactly
the STEP 5 parameters, computable in pure integer arithmetic: u is the largest
integer with 2^(u²) ≤ N, d the largest with (2m)^d ≤ N), and let

    V* := a value of Q on {0,…,m−1}^d with the LARGEST level set
          (computable by finite enumeration; Lemma 3B.4 guarantees
          |S_{V*}| ≥ m^d/(d(m−1)²+1)).

Then

    W_N := { φ(x) + 1 : x ∈ {0,…,m−1}^d, Q(x) = V* } ⊆ [1, (2m)^d] ⊆ [1, N]

is 3-AP-free with |W_N| = |S_{V*}| ≥ m^d/(d(m−1)²+1) ≥ N·e^(−6√(ln N)).
The engine `engine142behrend.py` (§6.8) generates W_N for the grid
d ∈ {2,3,4}, m ∈ {3,4,5,6} and certifies it by two independent detectors.

**Honest remark (the two constructions are complementary, not redundant).**
Compare the Cantor bound N^{log₃ 2} of §3 with the Behrend bound
N·e^(−6√(ln N)): their ratio is N^{log₃ 2 − 1}·e^(6√(ln N)) =
exp(−0.36907·ln N + 6√(ln N)), which exceeds 1 until √(ln N) = 16.26, i.e.
N ≈ 10^115. Below that astronomical threshold the CANTOR family is the larger
construction at equal N (e.g. at N = 3^9 = 19683 Cantor gives 512 points,
while the largest grid Behrend instance, (d,m) = (4,6), gives 48 points in
[1, 20736]); above it Behrend dominates every fixed power. Both are kept:
Cantor for the exact-equality phenomenology (§6.7), Behrend for the
asymptotic. The true order of r_3(N) remains unknown from below between
N^{0.63} and N·e^{−O(√(ln N))} — no construction known beats Behrend's shape.

---

## §4. THEOREMS C, D, E — the digit-restriction front (k = 4, 5)

Fix b ≥ 2, a digit set D ⊆ {0,…,b−1}, and k ≥ 3. The **digit family** of
depth m (padded semantics — every position p < m is constrained):

    F_m(b, D) := { n ∈ [0, b^m) : digit_p(n) ∈ D for every p < m }.

*Semantics note.* If 0 ∈ D this is the set of numbers < b^m whose base-b
representation has all digits in D. If 0 ∉ D it is the set of numbers with
EXACTLY m digits (i.e. in [b^{m−1}, b^m)) all in D — leading zeros are not
allowed because the slot p = m−1 must carry a digit of D. The two readings
coincide iff 0 ∈ D. The distinction is real: in base 3, D = {1,2}, the
padded family of depth 2 is {4,5,7,8} (11,12,21,22 in ternary) and is 3-AP-free
(Theorem C), while the union over all lengths contains the 3-AP (1, 4, 7)
(1 = 1₃, 4 = 11₃, 7 = 21₃) and is not. In general, for every base b the
representation-union family of D = {1,…,b−1} contains the b-term AP
(1, 1+b, 1+2b, …, 1+(b−1)b) (each term has units digit 1 and one higher
digit in {1,…,b−1}). All theorems below use the padded semantics; every
r_k(N) claim uses the translate F_m + 1 ⊆ {1,…,b^m} or F_m ∩ [1, N].

### Theorem C (the prime-world strip law).

**C.1 (the strip induction — any base).** Call D **(b,k)-admissible** if

    (†)  for every residue a ∈ {0,…,b−1} and every step δ ∈ {1,…,b−1},
         the orbit { a + t·δ (mod b) : t = 0, 1, …, k−1 }  is NOT ⊆ D.

If D is (b,k)-admissible, then F_m(b, D) is k-AP-free for every m ≥ 0.

**Proof.** We prove by induction on m the statement

    P(m):  every k-AP (x_0, x_1, …, x_{k−1}) = (x_0 + t·d)_{t<k} contained
           in F_m satisfies b^m | d.

P(0): F_0 = {0}; a k-AP inside a one-point set must have d = 0, and b^0 = 1
divides 0. ∎(base)

P(m) ⟹ P(m+1): take a k-AP in F_{m+1}, terms x_t = x_0 + t·d, with
d ≥ 0 (the terms are indexed increasingly; non-trivial means d > 0).
*Step 1 — the units digit wall.* Suppose b ∤ d. Put a := x_0 mod b and
δ := d mod b ∈ {1,…,b−1}. Then x_t mod b = (a + tδ) mod b for every t, and
since x_t ∈ F_{m+1}, its position-0 digit lies in D. So the whole orbit
{a + tδ mod b : t < k} ⊆ D — contradicting (†). Hence b | d.
*Step 2 — the strip.* b | d makes all terms congruent mod b; let
u := x_0 mod b ∈ D (x_0 ∈ F_{m+1}). Set y_t := (x_t − u)/b = x_t div b.
By Lemma 1.4 (shift law) the digits of y_t at positions p < m are the digits
of x_t at positions p+1 < m+1 — all in D; and y_t < b^m (since
x_t < b^{m+1}). So (y_t) is a k-AP inside F_m with common difference d/b.
By P(m), b^m | (d/b), i.e. b^{m+1} | d. This proves P(m+1). ∎(induction)

*Conclusion.* Let a non-trivial k-AP live in F_m. By P(m), b^m | d, so
d ≥ b^m. But x_{k−1} − x_0 = (k−1)d ≥ 2b^m (k ≥ 3), while both terms lie in
[0, b^m), so x_{k−1} − x_0 ≤ b^m − 1 < 2b^m. Contradiction. ∎

**C.2 (prime bases — the admissibility dichotomy).** Let p be prime.
(i) If k ≥ p: D is (p,k)-admissible ⟺ D ⊊ {0,…,p−1} (proper subset).
(ii) If 3 ≤ k ≤ p: D is (p,k)-admissible ⟺ D contains no cyclic k-term AP
    {a, a+δ, …, a+(k−1)δ} with δ ≢ 0 (mod p). In particular every D with
    |D| ≤ k−1 is (p,k)-admissible.

**Proof.** For δ ≢ 0 (mod p) the step is invertible in ℤ/p, so
t ↦ a + tδ is injective on any window of length ≤ p.
(i) If k ≥ p, the window t ∈ {0,…,k−1} contains a full residue system
{0,…,p−1} (translate by a), so the orbit is ALL of ℤ/p; it is ⊆ D iff
D = ℤ/p. So admissible ⟺ D proper.
(ii) If k ≤ p the orbit has exactly the k distinct elements
a, a+δ, …, a+(k−1)δ; (†) fails exactly when some such k-tuple lies inside D.
If |D| ≤ k−1 it cannot contain k distinct orbit elements. ∎

**C.3 (the k = 4 assigned front).** The naive pattern — base k, digits
{0,…,k−1} minus one value — **dies at k = 4**: see Theorem E (base 4 is
composite; every 3-element digit family provably contains a non-trivial
4-AP). The correct prime-world analogue at k = 4 is base 5 (5 ≥ 4 prime):

* Every 3-element D ⊆ {0,…,4} is (5,4)-admissible. [Every 4-subset of ℤ/5
  is a cyclic 4-AP: its complement is a single residue r, and
  {r+1, r+2, r+3, r+4} = ℤ/5∖{r} is the δ = 1 orbit through a = r+1. Hence a
  3-element set contains no orbit and is admissible by C.2(ii).] So
  **F_m(5, D) is 4-AP-free for every |D| ≤ 3, e.g. D = {0,1,2}**, and

      r_4(5^m) ≥ 3^m = (5^m)^{log_5 3},   log_5 3 ≈ 0.6826,

  with monotone interpolation r_4(N) ≥ 3^{⌊log_5 N⌋} ≥ N^{log_5 3}/3 for
  all N ≥ 1 (the proof of Theorem B.3(i) verbatim with (3, 2, α) replaced
  by (5, 3, log_5 3)).
* No 4-element D works in base 5: each of the five 4-subsets of ℤ/5 is
  itself a cyclic 4-AP (shown above), so admissibility fails; the census
  (§6, SP4) exhibits an explicit non-trivial 4-AP inside each of the five
  families (e.g. D = {0,2,3,4} contains 3, 10, 17, 24).

*Better exponents from larger primes (machine-certified).* The exact
admissibility condition C.2(ii) for k ≤ p is "no cyclic 4-AP inside D", and
the maximal sizes m(p,4) are computed exactly by exhaustive enumeration
(§6 [F] + SP7): m(5,4) = 3, m(7,4) = 4, m(11,4) = 6, m(13,4) = 6,
m(17,4) = 8, m(19,4) = 8. Each value is a FINITE certificate (all
(p−1)·p orbit checks), so e.g. with D = {0,1,2,4,5,7} ⊆ ℤ/11 (no cyclic
4-AP; certificate §6):

      r_4(11^m) ≥ 6^m = (11^m)^{log_11 6},  log_11 6 ≈ 0.7475,

and similarly r_4(7^m) ≥ 4^m (log_7 4 ≈ 0.7124). Among the verified primes
the best k = 4 digit exponent is **log_11 6 ≈ 0.7475**. (Pushing p → ∞ along
Behrend-type digit sets is the classical route — §10 context; not pursued:
our claim is only what is certified here.)

**C.4 (the k = 5 assigned front).** Base 5 = k is prime, so by C.2(i) EVERY
proper digit subset D ⊊ ℤ/5 is (5,5)-admissible. In particular **all five
"digits {0,1,2,3,4} minus one value" families are 5-AP-free** (the assigned
pattern works at k = 5 — it only dies at k = 4), and the best of them,
|D| = 4 (e.g. D = {0,1,2,3}), gives

      r_5(5^m) ≥ 4^m = (5^m)^{log_5 4},   log_5 4 ≈ 0.8614,

with interpolation r_5(N) ≥ 4^{⌊log_5 N⌋} ≥ N^{log_5 4}/4 for all N ≥ 1.
For the larger primes the exact maxima are m(7,5) = 4, m(11,5) = 6,
m(13,5) = 7, m(17,5) = 9, m(19,5) = 10 (§6): the exponents
log_7 4 ≈ 0.712, log_11 6 ≈ 0.747, log_13 7 ≈ 0.763, log_17 9 ≈ 0.780,
log_19 10 ≈ 0.783 are ALL beaten by log_5 4 ≈ 0.8614. So at k = 5 the
smallest admissible prime (p = k = 5, digits {0,1,2,3}) is the winner of the
digit front. (Machine: all five proper 4-element base-5 families verified
5-AP-free, m ≤ 3 exhaustive, §6 SP4; census.py [D] verifies
(5,{0,1,2,3},5) to m ≤ 4 and (5,{1,2,3,4},5) to m ≤ 4.)

**C.5 (the general law, every k ≥ 3).** For every prime p and every
(p,k)-admissible D (e.g. any D with |D| ≤ min(k−1, p−1)):

      r_k(p^m) ≥ |D|^m = (p^m)^{log_p |D|},    r_k(p^m − 1) ≥ |D|^m − [0 ∈ D],

(the translate F_m + 1 ⊆ {1,…,b^m} needs max F_m + 1 ≤ b^m, true since
max F_m ≤ b^m − 1; if 0 ∉ D no element is 0 and F_m ∩ [1, b^m−1] = F_m), and
by monotone interpolation, for every N ≥ 1,

      r_k(N) ≥ |D|^{⌊log_p N⌋} ≥ N^{log_p |D|} / |D|.

**Proof.** C.1 + Fact-A.0-style counting (|F_m| = |D|^m by the bijection
ε ∈ D^m ↦ Σ ε_p b^p of Lemmas 1.1–1.3) + the argument of Theorem B.3(i)
mutatis mutandis (p^m > N/p ⟹ |D|^m = (p^m)^{log_p |D|} > (N/p)^{log_p |D|}
= N^{log_p |D|}/|D|). ∎

**C.6 (what is NOT claimed).** The converse of C.1 — "family k-AP-free ⟹ D
admissible" — is OPEN in general (a non-admissible D may still be rescued by
carries; see Ex. 4.4). For prime bases and k ≤ p, every non-admissible D
TESTED (bases 5, 7, 11, 13, k = 3, 4, 5, all digit sets) was found to contain
an explicit non-trivial k-AP (§6 E2/E4/E5 receipts) — evidence, not theorem.
Necessity IS provable in the two extremal cases: D = ℤ/p always contains the
k-AP 0, 1, …, k−1 (all single digits, k ≤ p; and for k > p all numbers
qualify), and D = ℤ/b likewise for any b.

### Theorem D (the no-carry column law — no primality needed).
Let k ≥ 3, B := 2k − 3, D := {0, 1, …, k−2}. Then F_m(B, D) is k-AP-free
for every m. Hence r_k(B^m) ≥ (k−1)^m = (B^m)^{log_B (k−1)}, exponent
log_{2k−3}(k−1).

**Proof.** Let (x_0, …, x_{k−1}) = (x_0 + t·d)_{t<k} be a k-AP in F_m, d ≥ 0.
For every i with 0 ≤ i ≤ k−3 the integer identity
x_i + x_{i+2} = 2x_{i+1} holds (both sides equal 2x_0 + (2i+2)d). Read it in
digits: for every position p, digit_p(x_i) + digit_p(x_{i+2}) ≤ 2(k−2) =
2k−4 = B−1 and 2·digit_p(x_{i+1}) ≤ 2k−4 = B−1, so Lemma 1.5 (no carries)
applied to BOTH sides of x_i + x_{i+2} = 2x_{i+1} gives, position by
position (Lemma 1.2 uniqueness):

    digit_p(x_i) + digit_p(x_{i+2}) = 2·digit_p(x_{i+1})     ∀p, ∀i ≤ k−3.

Fix p and write c_i := digit_p(x_i) ∈ {0,…,k−2}. The column (c_0, …, c_{k−1})
satisfies c_i + c_{i+2} = 2c_{i+1} for i ≤ k−3, hence (induction on i:
c_{i+2} = 2c_{i+1} − c_i) it is a rational AP: c_i = c_0 + i·δ with
δ := c_1 − c_0 ∈ ℤ. Now c_{k−1} − c_0 = (k−1)δ and |c_{k−1} − c_0| ≤ k−2,
so (k−1)|δ| ≤ k−2 < k−1, forcing δ = 0: the column is CONSTANT. This holds
for every p, so all k terms have identical digit sequences, hence
x_0 = x_{k−1} (Lemma 1.3), i.e. d = 0: the AP is trivial. ∎

**Remarks.**
* k = 4: B = 5, D = {0,1,2} — coincides with the prime-world winner C.3.
* k = 5: B = 7, D = {0,1,2,3} (exponent log_7 4 ≈ 0.712) is strictly weaker
  than the prime-world C.4 (log_5 4 ≈ 0.861). For k = 6, B = 9 is
  composite and Theorem D is the ONLY one of the two laws that applies
  (log_9 5 ≈ 0.732 < the prime-world log_5 4 ≈ 0.861 from p = 5 ≤ k).
* The mechanism is independent of C (no base stripping; digit columns of a
  k-AP in a carry-free family are rational APs), and it also explains the
  composite-base rescues below.

### Theorem E (the base-4 wall — a complete negative theorem).
For EVERY D ⊆ {0,1,2,3} with |D| ≥ 3, the family ∪_m F_m(4, D) contains a
non-trivial 4-term AP — indeed one inside [1, 15]. Explicitly (each witness
has constant difference and every element's base-4 digits lie in D):

    D ⊇ {0,1,2} :  2, 4, 6, 8        (2 = 2₄,  4 = 10₄, 6 = 12₄, 8 = 20₄)
    D ⊇ {0,1,3} :  1, 3, 5, 7        (1 = 1₄,  3 = 3₄,  5 = 11₄, 7 = 13₄)
    D ⊇ {0,2,3} :  8, 10, 12, 14     (8 = 20₄, 10 = 22₄, 12 = 30₄, 14 = 32₄)
    D ⊇ {1,2,3} :  1, 3, 5, 7        (digits 1, 3, 11, 13₄)
    D = {1,3} (size 2) : 1, 3, 5, 7  (the size-2 exception).

Since the four 3-element subsets are exactly {0,1,2}, {0,1,3}, {0,2,3},
{1,2,3} and every 4-element D contains one of them, this covers all
|D| ≥ 3. **Proof by exhibition** (a displayed AP with checked digits IS a
proof of non-freeness). ∎

Consequences: (a) the task's naive pattern "base k, digits {0,…,k−1} minus
one value" provably FAILS at k = 4 (it succeeds at k = 3 — Cantor — and at
k = 5 — C.4); (b) the maximal 4-AP-free base-4 digit families have size 2,
with the further exception {1,3} failing (census2.py E4 scans all 15
nonempty D ⊆ ℤ/4 under both semantics, m ≤ 6: the k=4-free ones are exactly
{0},{1},{2},{3},{0,1},{0,2},{0,3},{1,2},{2,3}).

**The composite-base dichotomy (cross-lane receipt).** The Wave-1 doubter
engine census2.py E9 proves the same wall for EVERY composite k: a closed-
form k-AP witness (difference g = k/p, p = smallest prime factor) inside
EVERY exclusion family Z_k∖{c}, machine-certified on all 3417 (k,c) pairs
for composite k ≤ 64 plus k ∈ {81,100,121,125,169,243,1000} (E9a), with an
independent search-engine cross-check at m = 2 (E9b). Theorem E is the
k = 4 instance with fully explicit hand-checked witnesses. The complementary
E9c receipt confirms Theorem C.2(i) at the prime bases k = 7 (m ≤ 3), 11, 13
(m ≤ 2): 10/11 and 12/13 exclusion families are k-AP-free — the single
failures are the c = 0 families under REPRESENTATION semantics, exactly the
leading-zero artifact documented in the semantics note above (the padded
families are all k-AP-free, as Theorem C.2(i) proves).

**Example 4.4 (admissibility is sufficient, NOT necessary — composite
rescue).** Base 6, D = {0,2,4}: the orbit δ = 2 through a = 0 is
{0,2,4,0,2,4} ⊆ D, so D is NOT (6,6)-admissible — yet F_m(6, {0,2,4}) IS
6-AP-free for all m. Two-step reason: (1) D₀ := {0,1,2} IS (6,6)-admissible:
its orbits are — δ = 1 or δ = 5: all six residues; δ = 2 or δ = 4: a coset
{0,2,4} or {1,3,5} of the subgroup {0,2,4}, neither inside D₀; δ = 3: a
pair {a, a+3}, and the pairs {0,3},{1,4},{2,5} all leave D₀ — so (†) holds
and F_m(6, D₀) is 6-AP-free by Theorem C.1; (2) {0,2,4} = 2·{0,1,2} digit-wise
with 2d ≤ 5 = b−1 for every d ∈ D₀, so Lemma 1.11 maps F_m(6, D₀)
bijectively onto F_m(6, {0,2,4}), preserving AP-freeness. (Machine:
census.py [D2], m ≤ 3.) ∎

---

## §5. THEOREMS F, G, H — gap, counting, and 6-world structure

### Theorem F (self-similarity and the exact gap law).
C_m = C_{m−1} ∪ (3^{m−1} + C_{m−1}) (disjoint union) for m ≥ 1, and the gap
multiset of C_m (differences of consecutive elements) is exactly

    G(C_m) = { (3^j + 1)/2  with multiplicity 2^{m−1−j} : j = 0, 1, …, m−1 }.

In particular C_m has 2^m − 1 gaps, its largest gap is (3^{m−1}+1)/2 and its
smallest is 1.

**Proof.** Every n < 3^m has digit_{m−1}(n) ∈ {0,1} if it is in C_m. Splitting
n = ε·3^{m−1} + r with ε = digit_{m−1}(n) ∈ {0,1} and r = n mod 3^{m−1}
(Lemma 1.4/1.3): the remaining digits are those of r, so r ∈ C_{m−1}
iff n ∈ C_m, giving C_m = C_{m−1} ∪ (3^{m−1} + C_{m−1}); disjoint because
max C_{m−1} = (3^{m−1}−1)/2 < 3^{m−1} ≤ min of the shifted block (whose min
is 3^{m−1}). The junction gap — from max C_{m−1} = (3^{m−1}−1)/2 up to
3^{m−1} — equals 3^{m−1} − (3^{m−1}−1)/2 = (3^{m−1}+1)/2; the internal gaps
of each block are G(C_{m−1}). Induction on m: m = 1: C_1 = {0,1}, one gap of
(3^0+1)/2 = 1, multiplicity 2^0 = 1 ✓. m → m+1: G(C_{m+1}) =
G(C_m) ⊎ G(C_m) ⊎ {(3^m+1)/2} = {(3^j+1)/2 mult 2·2^{m−1−j}} ⊎ {(3^m+1)/2
mult 1} ✓. Total count: Σ_j 2^{m−1−j} = 2^m − 1 ✓. ∎

### Theorem G (two-sided counting law).
For every m ≥ 1 and every x with 1 ≤ x ≤ 3^m:

    2^{⌊log_3 x⌋}   ≤   |C_m ∩ [0, x)|   ≤   2 · x^α ,      α = log_3 2.

**Proof.** Let t := ⌊log_3 x⌋, so 3^t ≤ x < 3^{t+1} and t ≤ m−1.
*Lower:* C_t ⊆ C_m (an element < 3^t < 3^m with digits in {0,1} has zeros in
positions t..m−1, still in {0,1} — formally digit_p = 0 there, valid), and
C_t ⊆ [0, (3^t−1)/2] ⊆ [0, x) (since (3^t−1)/2 < 3^t ≤ x). So
|C_m ∩ [0,x)| ≥ |C_t| = 2^t.
*Upper:* C_m ∩ [0, x) ⊆ C_m ∩ [0, 3^{t+1}) = C_{t+1} (an element of C_m
below 3^{t+1} has zeros above position t), of size 2^{t+1} = 2·2^t ≤ 2·x^α
because x ≥ 3^t ⟹ x^α ≥ (3^t)^α = 2^t. ∎

Both bounds are sharp up to constants: at x = 3^t the count is exactly
2^t = x^α. (Machine: census.py [G] recursion vs direct count, M < 3000;
verify.py §7 digit-DP third method, M < 4000; spotcheck SP9 exact sweep
x ≤ 3^m, m ≤ 8.)

### Theorem H (the 6-world factorization law).
For every j ≥ 1:

    #{ n < 6^j : ternary digits of n all in {0,1} }  =  2^j · g(2^j),

where g(X) := #{ n < X : ternary digits of n all in {0,1} }.

**Proof.** The Arsenal packet law `gst_three_world_factor_rawS`:
6^j = 2^j · 3^j (also `gst_three_world_mixed_factor_exactS`,
`CardinalWorldsV2.packet_mixed_reconstruct`). Split every n < 6^j by the
3-world cut at 3^j: n = A·3^j + B with A := n div 3^j and
B := n mod 3^j. Since 6^j = 2^j·3^j < 3^{2j}, A < 3^j and B < 3^j; the ternary
digits of n are those of A (positions ≥ j) and of B (positions < j), so n has
all digits in {0,1} iff A ∈ C_j and B ∈ C_j (Lemma 1.4: shifting).
Now the 2-world enters: for (A, B) ∈ C_j × C_j,

    A·3^j + B < 6^j = 2^j·3^j  ⟺  A < 2^j − B/3^j  ⟺  A ≤ 2^j − 1,

because B/3^j ∈ [0, 1): A ≤ 2^j − 1 gives n ≤ (2^j−1)3^j + (3^j − 1) =
6^j − 1; A ≥ 2^j gives n ≥ 6^j. Therefore

    #{n < 6^j : Cantor} = #{A ∈ C_j : A ≤ 2^j − 1} · |C_j|
                        = g(2^j) · 2^j,

using that {A < 2^j with Cantor digits} = {A ∈ C_j : A < 2^j} (2^j < 3^j).
∎

**Corollary H.2 (the 6-world lower bound chain).**
r_3(6^j − 1) ≥ g(6^j) − 1 ≥ 2^{j + ⌊jα⌋} − 1 ≥ (6^j)^α/2 − 1, and the constant
1/2 is the SAME as the pure 3-world interpolation B.3(i) — the identity

    2^{j(1+α)} = (6^j)^α     (exact, since 1 + α = α·log_2 6 ⟺ log_2 3 + 1
                              = log_2 6, true),

shows the mixed world sits exactly on the Cantor exponent line: no gain, but
the factorization 2^j · g(2^j) is itself the structural content — the
counting function of the 3-world at mixed 6^j-points factorizes through the
2-world cut 2^j, exactly as the exponential packet does
(6^j = 2^j · 3^j).

**Proof of the chain.** g(6^j) counts n ∈ [1, 6^j) with Cantor digits, all in
{1,…,6^j−1}, forming a 3-AP-free set (Theorem A), so
r_3(6^j − 1) ≥ g(6^j) − 1 (the −1 removes n = 0 from the count, which is not
in {1,…,6^j−1}). By Theorem H, g(6^j) = 2^j·g(2^j) ≥ 2^j·2^{⌊log_3 2^j⌋}
(Theorem G lower bound at x = 2^j) = 2^{j+⌊jα⌋} ≥ 2^{j(1+α)−1} = (6^j)^α/2
(the floor costs at most a factor 2; then the exact identity above). ∎

(Machine: census.py [G] 6-world block, j ≤ 12, exact equality
tot = 2^j·A(2^j) and the inequality chain; verify.py §9, j ≤ 12; spotcheck
SP10, j ≤ 8. All three agree.)

---

## §6. EXACT-VALUE CENSUS AND THE MACHINE PROTOCOL

### 6.1 The verification law (binding).
Every machine claim in this file has ≥ 2 independent implementations agreeing;
numerics are evidence, never proof, EXCEPT where the domain is certified
exhaustive (all subset enumerations, all orbit checks, all m ≤ M scans) —
those are finite certificates and are proofs of exactly what they check.

### 6.2 Exact r_3(N), N ≤ 62 (method A: branch-and-bound).
Engine: `census.py` `rk_table(3, 62)`. Soundness of every pruning rule:
* **Suffix bound** (Lemma 1.10): at element i with c chosen and suffix
  {i,…,N} remaining, prune if c + r[N−i+1] ≤ best.
* **Take bound**: after taking i, at most r[N−i] more can be chosen.
* **Forbidden propagation (k = 3)**: when i is chosen, every z = 2i − a
  (a ∈ chosen) would complete a 3-AP and is barred while i is in the stack —
  an exact mirror of the constraint, restored on backtrack.
* **Warm lower bounds**: best is initialized to max(r[N−1], (k−1)^{⌊log_p N⌋})
  with p = smallest prime ≥ k — both are genuine constructions (monotonicity;
  the prime-world family C.5 shifted into {1,…,N}), so `best` is always an
  achievable value; the search only needs to beat it.
The engine reports (fresh run, this round):

    r_3(1..62) =
     1  2  2  3  4  4  4  4  5  5   (N=1..10)
     6  6  7  8  8  8  8  8  8  9   (N=11..20)
     9  9  9 10 10 11 11 11 11 12   (N=21..30)
    12 13 13 13 13 14 14 14 14 15   (N=31..40)
    16 16 16 16 16 16 16 16 16 16   (N=41..50)
    17 17 17 18 18 18 18 19 19 19   (N=51..60)
    19 19                            (N=61..62)

### 6.3 Second and third methods.
* **Method B (Z3, `verify.py` §1–§3 + `spotcheck.py` SP2):** Z3 Optimize
  over Booleans v_0..v_{N−1} with a clause ¬(all of a, a+d, …, a+(k−1)d) for
  every k-AP in {0,…,N−1} ([0,N−1] is a translate of {1,…,N}, Lemma 1.8).
  Full agreement with method A for every N ≤ 45 (r_3), N ≤ 28 (r_4), N ≤ 22
  (r_5); spotcheck SP2 extends the Z3 agreement to r_3 N ≤ 62, r_4 N ≤ 36,
  r_5 N ≤ 30 — the FULL range of the method-A tables. Every Z3 optimum is
  accompanied by its witness set, re-verified AP-free by an independent
  scanner.
* **Method C (pure subset enumeration, `spotcheck.py` SP1):** r_3(N) for
  N ≤ 18 by enumerating subsets of {1,…,N} downward — agrees with 6.2.
* **Cold start (`census.py` [A]):** the B&B re-run without warm bounds for
  N ≤ 30 — agrees.
* **Literature anchor:** the corpus-known prefix [1,2,2,3,4,4,4,4,5]
  (N = 1..9) agrees.

### 6.4 Exact r_4, r_5 (same protocol).
Fresh method-A tables (this round):

    r_4(1..36) = 1 2 3 3 4 5 5 6 7 8 8 8 9 9 10 10 11 11 12 12 13 13 14
                  14 15 15 16 17 17 18 18 18 19 20 20 20
    r_5(1..30) = 1 2 3 4 4 5 6 7 8 8 9 10 11 12 12 13 14 15 16 16 16 16
                  16 17 18 18 19 20 21 21

Z3 (method B) agrees on the overlapping ranges N ≤ 28 (r_4) and N ≤ 22 (r_5)
(verify.py §3), and spotcheck SP2 extends the Z3 agreement through
r_4(36) and r_5(30) — the full table range. Notable: r_4(25) = 15 ≥ 3^2
(the C.3 construction at m = 2) and r_5(25) = 18 ≥ 4^2 = 16 (the C.4
construction at m = 2) — both constructions confirmed inside the exact
table, with room.

### 6.5 Digit-family census (the assigned fronts (a)/(b)).
* **[D] Theorem-C battery** (`census.py`): all (b, D, k) instances listed
  there (base 3 {0,1} for k = 3,4,5,8; base 3 {0,2}; exactly-m-digit {1,2};
  base 5 {0,1,2} & {1,2,3} for k = 4; base 5 {0,1,2,3} & {1,2,3,4} for k = 5;
  base 7 {0,…,4} for k = 6; base 7 {0,…,5} for k = 7; base 11 {0,…,6} for
  k = 8; base 13 {0,…,10} for k = 12) — every instance: cyclically
  admissible, family k-AP-free (pair scan), |family| = |D|^m. Second methods:
  `verify.py` §4 (difference-window scan) + §5 (bitmask shift-AND cyclic
  check) + `spotcheck.py` SP5/SP6 (fresh window scans incl. the
  non-contiguous D = {0,1,3} ⊆ ℤ/5 and D = {0,1,2,4} ⊆ ℤ/7,
  D = {0,1,2,4,5,7} ⊆ ℤ/11).
* **[E] Base-k wall sweep:** for every k = 3..12: no (k−1)-element digit set
  in base k is cyclically k-AP-free when k is composite (all C(k,k−1) sets
  fail), while for prime k all of them are — the dichotomy of C.2. Full
  max-size table for bases ≤ 9 included in the receipts.
* **[F] m(p,k) exact walls** (max cyclic-k-AP-free |D| in ℤ/p, exhaustive):
  k = 3: m(3)=2, m(5)=2, m(7)=3, m(11)=4, m(13)=4;
  k = 4: m(5)=3, m(7)=4, m(11)=6, m(13)=6, m(17)=8, m(19)=8;
  k = 5: m(5)=4, m(7)=4, m(11)=6, m(13)=7, m(17)=9, m(19)=10.
  (Values for p ≤ 13 re-verified by three engines: census [F] DFS, verify §6
  brute masks, spotcheck SP7 full 2^p enumeration. Values at p ∈ {17, 19}:
  census [F] DFS + verify §5-style bitmask check; SP7 covers p ≤ 13.)
* **[E4/E5 composite audits]** (`census2.py`): full classification of base-4
  digit families under both semantics (Theorem E witnesses; the {1,3}
  exception); base-5 / base-6 family sweeps.
* **Random-instance theorem tests** (`verify.py` §10): 400 random
  (b, D, k, m ≤ 2) instances with b ≤ 9, k ∈ 3..7: on all 217 instances where
  Theorem C applies (D admissible), the family was k-AP-free with |D|^m
  elements — 217/217.

### 6.6 Structure receipts (front (c)).
Gap law (Theorem F): census [H] m ≤ 8; verify §8 (block self-similarity);
spotcheck SP8. Two-fold covering (B.1): census [C1] m ≤ 7; SP8 m ≤ 6.
Counting law (Theorem G): census [G] (recursion vs direct, M < 3000), verify
§7 (digit-DP, third method, M < 4000), SP9 (exact sweep, all x ≤ 3^m,
m ≤ 8). 6-world factorization (Theorem H): census [G] j ≤ 12 (equality
tot = 2^j·A(2^j)), verify §9 j ≤ 12, SP10 j ≤ 8.

### 6.7 Lower-bound consistency (front: the exact table vs the theorems).
All of the following were checked against the exact table (census [I]):
r_3(3^m) ≥ 2^m and r_3(3^m − 1) ≥ 2^m (m ≤ 3 within the table);
r_3(N) ≥ 2^{⌊log_3 N⌋} for all N ≤ 62; r_3(N) > N^α/2 for all N ≤ 62;
r_3(N) ≥ 2^{⌊log_3(2N+1)⌋} − 1 for all N ≤ 62; EQUALITY
r_3((3^m−1)/2) = 2^m − 1 for m = 1..4; r_4(5^m) ≥ 3^m (m ≤ 2);
r_5(5^2) ≥ 3^2 … and r_5(25) = 18 ≥ 16 = 4^2 (the C.4 construction).

### 6.8 The Behrend battery (§3B; engine `engine142behrend.py`, receipts
`receipts142behrend.txt` — pure python3, exact integer arithmetic +
`fractions.Fraction`; every part two-method, per §6.1).
* **[A] SPHERE-FREENESS (STEP 1+2+3).** Grid d ∈ {2,3,4}, m ∈ {3,4,5,6}:
  ALL non-empty level sets S_V of Q over {0,…,m−1}^d verified 3-AP-free by
  TWO independent detectors — (i) the full pair-midpoint scan on the lattice
  points (all pairs x ≠ z: componentwise parity + membership), (ii) the
  (a,δ)-scan on the integer image φ(S_V) (every pair of image points a < b
  with δ = b−a tests a+2δ for membership; equivalent to the literal (a,δ)
  double loop because an AP a, a+δ, a+2δ ∈ S needs its first two terms in
  S). Zero non-trivial 3-APs everywhere; the two methods agree 100%.
* **[B] SIZE LAW (STEP 4).** Per (d,m): max_V |S_V| reported and the exact
  integer inequality max_V|S_V|·(d(m−1)²+1) ≥ m^d verified (ratios 2.0–5.7);
  plus the partition identity Σ_V |S_V| = m^d and the value-range check
  #levels ≤ d(m−1)²+1.
* **[C] DIGIT MAP (STEP 2).** Per (d,m): φ injective on the FULL cube
  (|φ(D)| = m^d); the no-carry pullback verified EXHAUSTIVELY — every pair
  (a,c) ∈ φ(D)² with a+c even and b = (a+c)/2 ∈ φ(D) (i.e. EVERY integer
  triple with a+c = 2b inside the image) pulls back to componentwise
  x+z = 2y via the base-B digit reader — plus ≥ 10^5 random triples per
  (d,m) and random-integer hits; **negative control**: at the wrong base
  B′ = 2m−2 the pullback fails (exhibit of §3B STEP 2: 0, 2, 4 with
  preimages (0,0), (2,0), (0,1) — a carry occurs).
* **[D] EXPLICIT CONSTANT CHAIN (STEP 5+6).** The two Taylor exhibits of
  Lemma 3B.6 re-verified in exact rational arithmetic (e^{25/36} > 2 via the
  positive partial sum; e^{9/13} < 2 via the order-7 sum + 3x^8/8!
  remainder). For e = 10..60 (N = 2^e) AND all N in [16, 4096] AND decades
  10^6..10^18 AND N = 2^e for e = 4..60: the construction's guaranteed size
  g = ⌈m^d/(d(m−1)²+1)⌉ computed with the explicit integer rounding chain
  (u = max{u : 2^{u²} ≤ N}, m = 2^u, d = max{d : (2m)^d ≤ N}), and BOTH
  bounds verified: the master integer inequality N < g·u·2^{1+4u} (Theorem
  3B.5, exact integers) and the exponential claim g ≥ N·e^{−6√(ln N)}
  (Theorem 3B.7) — the latter by a certified rational LOWER bound E ≤
  e^{6√(ln N)} (Taylor partial sum at a rational ρ ≤ √(ln N) from ln N ≥
  ⌊log₂ N⌋·9/13), checking N·E.denominator ≤ g·E.numerator exactly.
  100% pass; slack factors 10^3–10^8.
* **[E] SUBSETS OF [1,N] (STEP 3/6 shift).** Per grid (d,m): the shifted
  best-level family W = φ(S_{V*})+1 re-verified 3-AP-free under the pinned
  comparator convention (a ≥ 1, δ ≥ 1), W ⊆ [1, (2m)^d], hence
  r_3((2m)^d) ≥ |S_{V*}| (new machine-witnessed data points, e.g.
  r_3(20736) ≥ 48 at (4,6)); consistency: every |W| ≤ (k−1)⌊N/k⌋+(N mod k)
  (the certified BLOCK-UPPER envelope, k = 3).

---

## §7. WHAT IS PROVEN AND WHAT REMAINS OPEN

**Proven, unconditionally, in full rigor (this file):** Theorems A, B.1, B.2,
B.3, C.1–C.5, D, E, F, G, H (+ H.2), **3B.1, 3B.2, 3B.3, 3B.4, 3B.5, 3B.6,
3B.7 (+ 3B.8, 3B.9) — the Behrend theorem r_3(N) ≥ N·e^{−6√(ln N)} for all
N ≥ 16, with the master base-2 form and the all-k corollary**, with every
lemma spelled out; the finite certificates of §6 (exact values, witnesses,
m(p,k) walls, the Behrend battery §6.8).

**Open (not touched by this file, honestly):**
1. THE TARGET: an asymptotic formula for r_k(N) — open for every k ≥ 3,
   including k = 3. Not even the order of magnitude is known (corpus: Er80,
   Va99); unknown whether r_k(n)/r_{k+1}(n) → 0 for any k ≥ 3.
2. The exact converse of Theorem C at prime bases (non-admissible ⟹ real
   k-AP exists): open in general; machine-confirmed on all tested instances.
3. The exact characterization of k-AP-killing digit sets at composite bases
   (admissibility is sufficient not necessary — Ex. 4.4).
4. r_3((3^m−1)/2) = 2^m − 1 beyond m ≤ 4; the growth of r_3(3^m) − 2^m;
   the true liminf of r_3(N)/N^α (construction constants 1/2 and
   2^{α−1} here; the Behrend theorem §3B is now PROVEN in this file — the
   remaining gap below is any N·e^{−o(√(ln N))} construction, the
   Behrend–Elkin frontier; not attempted here).
5. Exact r_3(N) beyond N = 62 (and r_4 beyond 36, r_5 beyond 30) — purely
   computational frontier, no mathematical claim.

---

## §8. ARSENAL USAGE (exact inventory)

| Arsenal notion (file) | where used here |
|---|---|
| `ErdosTernary2.lt_three_cases`, `ternary_digit_lt_three` | §1 digit trichotomy at base 3 (the {0,1,2} range behind Lemmas 1.1–1.5) |
| `ErdosTernary2.isTernaryDigit` (+ zero/one/two/three) | §1 digit recognizer; §2 the Cantor digit predicate |
| `ErdosTernary2.empty_foldr_repr_zero`, `single_digit_value`, `two_digit_value` (fold-based value chain) | §1 Lemmas 1.1/1.3 — the Lean-side semantics of Σ d_p 3^p |
| `CardinalWorlds.noTernaryTwo` / `hasTernaryTwo` (§1 readers) | §2: C_m is EXACTLY the noTernaryTwo family; the verdict/scan duality |
| `CardinalWorlds.has_two_iff_no_two_false`, `no_two_false_digit_witness`, `hasTernaryTwo_of_digit`, `hasTernaryTwo_first_pos` (+ V2 `has_two_iff_first_signature`, `no_two_false_iff_digit_witness`) | §2 Theorem A statement equivalence (verdict ⟺ digit-2 witness) |
| `CardinalWorlds.gstDigit` (§11 reader `R / 3^p % 3`) | §1: digit_p at base 3 (generalized to base b in Lemma 1.3–1.5) |
| `CardinalWorlds.div_mod_mul_lemma`, `mul_add_div_lemma`, `mod_mod_mul`, `three_pow_pos_lemma` | §1 Lemma 1.4 (shift law) skeleton — the digit extraction/div laws |
| `CardinalWorlds.noTernaryTwo_div`, `ternaryLog3`, `ternaryLog3_lt_of_lt_pow` | §2 Proof 2 descent machinery (strip below 3^m) |
| `CardinalWorlds.carryAtPos` + `carryAtPos_one_mod3_0/1/2`, V2 `carryAtPos_one_exact`, `first_carry_two_iff` | §2: the carry discipline at position 1 = the units digit — the "no carry" step of Proof 1/2; **§3B STEP 2: the base-3 anchor instance of the no-carry pullback that Lemma 3B.2 generalizes to base B = 2m (the CARRY LAW FAMILY connection — see ARSENAL_USAGE.md)** |
| `CardinalWorlds` §12 three-world packet: `gstBinaryWorldFactorS` (2^j), `gstTernaryWorldFactorS` (3^j), `gstMixedWorldFactorS` (6^j), `gst_three_world_factor_rawS` (6^j = 2^j·3^j), `gst_three_world_mixed_factor_exactS`, `gstThreeWorldPacket_add`, `gst_handwritten_three_world_joined_prefix_closedS` (5·Σ 2^j3^j = 6^K −1) | §5 Theorem H (the packet law is the engine of the factorization); §3 B.1 (bridge 3 = 1+2); the 6-world window 6^j = 2^j·3^j |
| `CardinalWorldsV2.packet_mixed_reconstruct`, `packet_add`, `v2r_ternary_scaling` (dyadic scaling law) | §5 H (mixed = binary × ternary at every depth); the 2-world cut g(2^j) |
| `CardinalWorlds` header: THE BRIDGE `3 = 1 + 2`, the 2-world/3-world/6-world doctrine | §3 B.1; §4 (prime worlds); §5 H — the whole architecture |

Campaign law compliance: no external black-box theorem is USED in any proof
above; classical results appear ONLY in §10 as labelled context.

---

## §9. LEAN KERNELS (uncompiled drafts; CI is the verifier of record)

* `AuditKernel142.lean` (Wave-1 doubter lane): the Lean-native kernel of
  Theorem A Proof 2 (`noTernaryTwo_ap3_free`,
  `cantor_family_no_nontrivial_ap3`) over the Arsenal readers.
* `Erdos142.lean` (this round, attacker lane — NEW): kernel statements for
  the attacker package: Theorem A (no-carry form, digit-wise), Theorem B.2
  (r_3(3^m) ≥ 2^m via the translated family), the padded digit-family
  predicate, the prime-strip law and Theorem D statements — written against
  Arsenal names, NO `sorry` in the statements, proofs marked as the next
  kernel wave's work where not spelled out. NOT pushed (commander pushes).

---

## §10. CONTEXT — named classical results (NOT used in any proof)

For honesty of placement only. **The Behrend lower bound itself is no longer
mere context: §3B of this file proves r_3(N) ≥ N·e^{−6√(ln N)} (N ≥ 16)
self-contained — the 1946 theorem is now a theorem of the campaign, with
its own machine battery (§6.8); the classical citation F. A. Behrend, Proc.
Natl. Acad. Sci. U.S.A. 32 (1946) 331–332 records the historical priority.**
Salem–Spencer-type constructions are the ancestors; Kelley–Meka (k = 3),
Green–Tao (k = 4), Leng–Sah–Sawhney (k ≥ 5) are the current upper-bound
frontier (corpus page) and REMAIN context — none is a step in any proof
above; the campaign law (repo math only) is respected. Rankin-type digit
constructions are the classical ancestors of Theorems C/D.

---

*W1-A1 — the engine never stops; it never lies.*
*W71-142K — the sphere lands; the fortress wall is now flanked from below at
N·e^{−6√(ln N)}. The engine never stops; it never lies.*
