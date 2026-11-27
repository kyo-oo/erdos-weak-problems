# GST primitive-cycle construction from projective products in ALL codimensions

**Status, 2026-10-15:** A mathematical construction of a nonzero genuine algebraic primitive cycle of codimension p on **X×P^p for every smooth projective complex X of dimension d and each 1<=p<=d**. There is no bound on d. This is a special product family *based on arbitrary X*, not a construction of every primitive class on X. Contributor identity intentionally withheld.

**Original target unchanged:** Every primitive rational Hodge class on every smooth projective complex X is algebraic. **NOT PROVED.** Passing a Lean check of rational coordinates is not proof that the original target holds.

## Step 1. Actual geometric objects and ring

Take a smooth projective complex d-fold X, an ample divisor H on X, and the hyperplane divisor T on P^p. Let
\[
Y=X\times\mathbb P^p,\qquad D=\dim Y=d+p,
\quad u=\pi_X^*c_1(H),\quad t=\pi_P^*c_1(T),
\quad L=u+t.
\]
The divisor L is ample, and u and t are classes of **actual algebraic divisors**, not formal Hodge-eigenvectors or hypothetical correspondence lifts.

Cup products satisfy \(u^{d+1}=0\), \(t^{p+1}=0\). The classes \(\{u^{p-j}t^j\}_{j=0}^p\) are independent in rational Betti cohomology, because each lies in a distinct Künneth bidegree and \(u^{p-j}\neq0\) for \(0\le p-j\le d\), by positive top hyperplane degree.

## Step 2. Exact closed algebraic primitive cycle, arbitrary p

Set \(k=D-2p+1=d-p+1\ge1\). Define the **actual rational algebraic codimension-p cycle**
\[
\boxed{
Z_{d,p}=\sum_{j=0}^{p}(-1)^j
\binom{d-p+j}{j}\,
\bigl(\pi_X^*H\bigr)^{p-j}
\cdot\bigl(\pi_P^*T\bigr)^j
}.
\]
Intersection of actual Cartier divisors gives every summand as an actual algebraic cycle. Coefficients are integers, so no arbitrary complex scalar or unproved rational descent appears.

Write \(P_{d,p}(u,t)\) for its rational cohomology class. We prove it is primitive in *the genuine Hard Lefschetz sense*, namely \(L^{D-2p+1}P_{d,p}=0\).

The generalized binomial theorem gives the rational formal-series identity
\[
(1+s)^{-k}=\sum_{j=0}^{\infty}(-1)^j
\binom{k+j-1}{j}s^j.
\]
Multiplying by \((1+s)^k\), the coefficients through degree p vanish except the constant term. Hence, modulo \(t^{p+1}\),
\[
(u+t)^kP_{d,p}(u,t)
\equiv u^{p+k}=u^{d+1}=0.
\]
This is an *exact universal symbolic proof*, not numerical extrapolation. It only uses \(u^{d+1}=t^{p+1}=0\), not the Hodge conjecture or a generic primitive-representative assumption.

Moreover the j=0 Künneth component of \(P_{d,p}\) is \(u^p\otimes1\ne0\). Thus \(Z_{d,p}\) yields a **nonzero algebraic primitive rational Hodge class**, for every d>=p>=1 and every smooth projective X of dimension d.

## Step 3. Codimension two as explicit rational coefficients

For \(p=2\), \(d\ge2\), the formula becomes
\[
Z_{d,2}=u^2-(d-1)ut+\tfrac{d(d-1)}2t^2.
\]
Multiplication by \(L^{d-1}\) in the cohomology of \(X\times\mathbb P^2\) has two potentially nonzero output coordinates:
\[
(d-1)c_0+c_1,\qquad
\binom{d-1}{2}c_0+(d-1)c_1+c_2.
\]
For the constructed coefficient triple \((1,-(d-1),d(d-1)/2)\), both are exactly zero. The first coefficient is 1, so the class is nonzero. If a class in the three-dimensional hyperplane subalgebra is primitive, both equations force its coefficients to be a rational multiple of this triple.

**Source:** \`GSTUniversalProjectiveProductPrimitive.lean\`.
**Lean gate:** \`gst-universal-product-primitive.yml\`; GitHub Actions run 38707838056 completed SUCCESSFULLY, following repair of the rational coordinate definitional reduction. Earlier runs 38706747849 and 38707188272 failed Lean elaboration (not a mathematical counterexample). The file proves the rational coefficient cancellation and the unique one-dimensional primitive kernel; it does **not** formalize the scheme-theoretic Künneth or cycle-class comparison.

At d=p=2 this is exactly the previously verified P²×P² primitive class \(u^2-ut+t^2\) in \`GSTMiddlePrimitiveProjectiveProduct.lean\` (CI 38692915421 success).

## Step 4. Independent exact algebra audit

Wolfram Language computed the binomial convolution
\[
\sum_{j=0}^{\ell}(-1)^j\binom{k+j-1}{j}\binom{k}{\ell-j}=0,
\quad\ell\ge1,\ k\ge1
\]
symbolically as zero. All pairs \(2\le d\le9\), \(1\le p\le d\) and \(1\le\ell\le p\) were additionally tested with exact integer arithmetic (no numerical tolerance). At d=6,p=3 the coefficients are \(1,-4,10,-20\).

The independent analytic reason is the negative-binomial power-series identity, valid as a formal series for integer k>0. The finite checks are supplemental and are not the universal proof.

## Step 5. Why this does NOT resolve the original Hodge conjecture

These classes are primitive on **Y=X×P^p**, not a construction of a representative for an *arbitrary primitive class α on X*. In fact all our classes are built from known algebraic hyperplane divisors. If α is an unknown primitive rational Hodge class on X, this construction provides no algebraic cycle on X representing α and no correspondence whose pushforward is α.

One could simply insert α as a coefficient of an arbitrary hypothetical cycle and push forward, but that would assume Hodge algebraicity—the prohibited circular move.

Further honest routes need a comparison mechanism between a non-CM primitive Hodge structure on arbitrary X and genuinely constructed projective/CM incidence cycles. Neither formal power-series manipulation nor a determinant computed in a special product establishes that map is surjective.

**Strongest surviving finding:** genuine algebraic primitive classes can be constructed for all p and unbounded dimensions in the special stabilized family \(X\times\mathbb P^p\), by one explicit polynomial cycle, with NO assumed primitive-cycle preimages. **Universal target: still open.**
