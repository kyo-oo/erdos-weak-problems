# GST arbitrarily high-codimension non-tautological exceptional births from K3 diagonals

- **Date:** 2026-10-20
- **Program:** actual original-X rational Hodge-to-Chow source construction or a genuine Hodge counterexample.
- **Route:** proof-side explicit non-Picard perfect-complex/Chow geometric birth on a rational ambient blowup.
- **Code:** GSTK3PrimitiveGram.lean, construction commit \`3cf0d179c17e1feeb5b3135ab487e67e6a0b520a\`.
- **CI:** Mathbox K3 focused run #39413121271 triggered at the above SHA (revision-matched result pending at drafting).
- **Review:** exact intersection derivation and self-audit; all-r external-product geometry is a standard Künneth/Chow argument, not a fully instantiated scheme-level Lean theorem.

## 1. Genuine geometric original varieties at unbounded dimensions and codimensions

Choose a projective complex K3 surface S with a very ample divisor h and d=∫_S h²>0. For every integer r≥0, form the genuine connected smooth projective variety

$$
X_r=(S\times S)\times \mathbb P^r,\qquad
\dim X_r=4+r.
$$

On S×S write A=[pt]×S, B=S×[pt], U=h×h and Δ the diagonal. Define the **actual rational algebraic primitive diagonal cycle**

$$
D=\Delta-A-B-U/d\in CH^2(S\times S)_{\mathbb Q}.
$$

The K3 Betti intersection arithmetic is

$$
\langle D,D\rangle=21,\quad
\langle D,A\rangle=\langle D,B\rangle
=\langle D,U\rangle=0.
$$

Those are uniform identities for all d≠0, not rank hypotheses. The new Lean lemma \`primitive_diagonal_annihilates_all_three_decomposable_sources\` proves this exact rational Gram in the repository's native K3 coordinate model.

Let \(\tau=c_1(O_{\mathbb P^r}(1))\), and let \([\mathrm{pt}]=\tau^r\). Define the actual algebraic class

$$
Z_r=D\boxtimes[\mathrm{pt}]\in CH^{2+r}(X_r)_{\mathbb Q}
$$

with canonical Betti class \(\alpha_r=cl_{X_r}(Z_r)\), and the complementary **actual algebraic detector** \(\delta_r=cl_{X_r}(D\boxtimes 1)\in H^4(X_r,\mathbb Q)\). The Künneth intersection identity gives for **every r≥0**:

$$
\boxed{
\int_{X_r}\alpha_r\smile \delta_r
=\left(\int_{S\times S}D^2\right)
 \left(\int_{\mathbb P^r}\tau^r\right)
=21\ne0.
}
$$

This is a genuinely new unbounded-codimension geometric family of explicit algebraic classes, not an invented Hodge class or a proposed counterexample to Hodge. The transverse degree is correct: \(2+r+2=4+r=\dim X_r\).

## 2. Rational ambient blowups and explicit successful non-Picard return

Embed \(X_r\) via a chosen very ample product polarization with restricted hyperplane \(H_X=h_1+h_2+\tau\), then, if required, enlarge the projective embedding to ensure normal codimension c=N−(4+r)≥2. Form the **smooth rational** ambient blowup \(Y_r=Bl_{X_r}(\mathbb P^N)\), exceptional \(j:E\hookrightarrow Y_r\), projective normal bundle \(q:E\to X_r\), relative hyperplane \(\xi\).

The already-established actual GST exceptional native Chow birth is

$$
W_r=j_*(q^*Z_r)\in CH^{3+r}(Y_r)_{\mathbb Q}.
$$

It is honestly algebraic: the K3 diagonal, point factors, projective-bundle flat pullback and proper pushforward are algebraic. Since Y_r is smooth, rational K₀ / perfect-complex representatives exist for such Chow classes (with degree-by-degree Chern character and correct GRR normalization); this is not a specified single sheaf class without its Chern corrections.

The original-X return is

$$
R(W)=-q_*\bigl(\xi^{c-2}j^!W\bigr).
$$

The exceptional self-intersection and projective bundle laws give

$$
j^!j_*q^*Z_r=-\xi q^*Z_r,\qquad
q_*(\xi^{c-1}q^*Z_r)=Z_r.
$$

Therefore

$$
\boxed{R(W_r)=Z_r\in CH^{2+r}(X_r)_{\mathbb Q},\qquad
\langle\delta_r,cl_{X_r}(R(W_r))\rangle=21.}
$$

This is an explicit successful **non-Picard exceptional birth and return in EVERY codimension 2+r**, originating from independently constructed diagonal geometry, using no assumed preimage of an unknown Hodge target.

## 3. A stronger universal test of the attempted counterexample method

Use the ambient product embedding with \(H_X=h_1+h_2+\tau\). In rational Betti cohomology

$$
c(T_{S\times S})=(1+24A)(1+24B),\qquad
c(T_{\mathbb P^r})=(1+\tau)^{r+1}.
$$

Thus
\(c(T_{X_r})=(1+24A)(1+24B)(1+\tau)^{r+1}\).
The normal bundle satisfies

$$
c(N_{X_r/\mathbb P^N})= (1+H_X)^{N+1}/c(T_{X_r}).
$$

All returned ambient Picard-line-bundle Chern classes are therefore polynomials in \(h_1,h_2,\tau,A,B\); after multiplication by the detector D×1 and extraction of top degree, only the degree-two component on S×S matters, and it belongs to the span of A,B,U. The above Gram orthogonality proves:

$$
\boxed{
\int_{X_r}\delta_r\smile
cl\bigl(R(\mathrm{ch}_{r+3}(\mathcal O_{Y_r}(uH+vE)))\bigr)=0
}
$$

for **every r≥0**, all integer u,v, and all valid ambient embeddings with the chosen polarization. Finite rational virtual sums and nonsplit complexes filtered by these Picard line bundles remain invisible by Chern-character additivity. The statement concerns pure graded Chern character; a general Todd/GRR replacement requires checking the corresponding additional characteristic factors, which still lie in the tautological characteristic subring in this product test.

Thus a rational ambient blowup can successfully carry and return a non-tautological source in unbounded dimensions, but the complete Picard-generated K₀ sector fails to detect it.

## 4. Exact independent Wolfram regression

Using the actual K3 rational Gram and symbolic nonzero d, Wolfram returned

\`\`\`text
{<D,A>, <D,B>, <D,U>, <D,D>} = {0,0,0,21}.
\`\`\`

It also returned 21 for \(\langle D\times\tau^r,D\times1\rangle\) in each of r=0,…,8. The uniform proof is multiplicativity of intersection and \(\int_{\mathbb P^r}\tau^r=1\), **not** a finite computation extrapolation.

## 5. Decision

This completes one requested geometric construction **on a genuine unbounded family of original varieties, with arbitrarily high codimension and a nonzero native detector**, and simultaneously rules out all ambient Picard-only birth attempts for its distinguished class.

It does not construct sources for *every* rational Hodge class on every arbitrary original X, nor does it create a counterexample to the rational Hodge conjecture. The exact universal extension requires an independent non-tautological sheaf/perfect complex on each prescribed original X or rational ambient blowup whose returned canonical class detects its specified full-algebraic-span residual; simply increasing blowup arity cannot supply that input.

**Classification:** proved geometrically for the named product tower (standard projective bundle/Chow/Künneth identities), Lean verified only for its exact K3 base Gram once the focused CI succeeds; arbitrary-X global Hodge theorem remains a distinct obligation.
