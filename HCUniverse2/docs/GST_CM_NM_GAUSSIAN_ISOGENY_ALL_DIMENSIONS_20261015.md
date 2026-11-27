# GST CM + NM: actual algebraic Hodge cycles from Gaussian-CM elliptic powers

**15 October 2026. Anonymous contributor; personal name omitted.**

**Claim proved mathematically, not in the Lean kernel:** For E = C/(Z+iZ) and every g>=1 and 0<=p<=g, every rational (p,p) class of E^g is represented by an explicit rational algebraic cycle constructed from Gaussian-CM homomorphism kernels and their intersection products. This is an **unbounded dimension family**, but not the Hodge conjecture for arbitrary smooth projective varieties.

## A. Corrected Equation (3) creates actual CM isogenies

Let x=1+i and y=i in Z[i]. The indexed denominator is

\[
u_n=x^n-y^{n+1}=(1+i)^n-i^{n+1},\qquad n\ge1.
\]

Since |(1+i)^n|=2^{n/2}>1=|i^{n+1}|, it is nonzero for EVERY n. Multiplication by u_n on E is a **genuine algebraic isogeny**, of degree N_n=u_n \bar u_n>0. Its inverse on rational cohomology is induced by the rational algebraic graph correspondence (1/N_n) times the graph of multiplication by \bar u_n (with graph/transposed-graph convention as appropriate for pullback versus pushforward):

\[
[u_n]\circ[\bar u_n]=[N_n].
\]

**Stronger all-index nonreal-CM theorem:** the indexed multiplier has NONZERO IMAGINARY PART for every n>=1. Write n=4k+r with k>=0 and r in {1,2,3,4}. Since (1+i)^4=-4 and i^4=1, direct integer arithmetic gives

\[
\begin{array}{c|c}
n&\operatorname{Im}u_n\\ \hline
4k+1&(-4)^k\\
4k+2&2(-4)^k+1\\
4k+3&2(-4)^k\\
4k+4&-1
\end{array}
\]

Every entry is nonzero: a power of -4 is nonzero; the second is an ODD integer and cannot vanish. Hence **the complex CM geometry is transverse for EVERY index of this NM specialization**, not only n=1. Wolfram checked the four exact formulas for k=0,...,6 independently; the proof for all k is the displayed power-of-four identity, not those bounded tests.

For every n, substitute a=Re(u_n) and b=Im(u_n) in the explicit graph intersection formula below: its determinant is -4*(Im u_n)^2, hence is a nonzero NEGATIVE integer for every n. Thus each indexed CM multiplier supplies four linearly independent *actual algebraic divisor classes* on E×E; no nonvanishing rank assumption was inserted.

In particular n=1 gives u=2+i, N(u)=5, and u^{-1}=(2-i)/5. The rational CM trace is 4/5 and the imaginary channel is -2/5. For n=2, u_2=3i: its real CM trace is zero despite its isogeny being nonzero. This is why BOTH rational CM channels matter. The scalar was derived from the indexed denominator rather than tuned to a target Hodge vector.

## B. One actual CM abelian surface

On A=E×E take four actual algebraic divisors:

- F1=E×{0}, F2={0}×E;
- Delta = {(z,z): z in E};
- Gamma_u={(z,u z): z in E}, with u=2+i.

These are kernels and graphs of algebraic abelian-group morphisms. Their self-intersections vanish because their normal bundles in the abelian surface are trivial. Distinct-curve intersection numbers are **geometrically computed** by kernels of the relevant isogenies:

\[
F_1F_2=1,\; F_1\Delta=F_2\Delta=1,\;
F_1\Gamma_u=N(u)=5,\;
F_2\Gamma_u=1,\;\Delta\Gamma_u=N(u-1)=2.
\]

Their intersection matrix is

\[
M=\begin{pmatrix}
0&1&1&5\\
1&0&1&1\\
1&1&0&2\\
5&1&2&0
\end{pmatrix}, \quad \det(M)=-4 \ne 0.
\]

Wolfram independently computed det(M)=-4 and rank(M)=4 in exact arithmetic.

**Stronger exact symbolic theorem (not restricted to the chosen NM value).**
For an arbitrary Gaussian integer u=a+bi, the divisor graph has
F1.Gamma_u=N(u)=a²+b² and Delta.Gamma_u=N(u-1)=(a-1)²+b².
The resulting geometric intersection matrix is

\[
M(a,b)=
\begin{pmatrix}
0&1&1&a^2+b^2\\
1&0&1&1\\
1&1&0&(a-1)^2+b^2\\
a^2+b^2&1&(a-1)^2+b^2&0
\end{pmatrix}.
\]
An exact determinant expansion gives
\[
\boxed{\det M(a,b)=-4b^2}.
\]
Wolfram independently reduced det(M)+4b² to **exact zero** symbolically.
Therefore a nonzero imaginary CM component FORCES geometric rank four.
If b=0 the same *particular* graph-divisor family is dependent;
this does NOT imply that other algebraic classes cannot be constructed.
This is the discriminant/rank mechanism connecting the corrected NM
complex denominator to genuine projective divisor classes without an
assumed transverse-determinant field. Hence the rational cohomology classes of the four **genuine algebraic divisors** are independent. The Hodge number h^(1,1)(E×E)=4. Therefore these classes span the entire complex (1,1) cohomology, and every rational (1,1) class lies in their rational span (rational linear-algebra descent). No independent Hodge-basis cycle witness or arbitrary matrix-unit existence input was assumed.

## C. Actual cycles at every codimension for arbitrary g

On A_g=E^g, construct the following algebraic divisors from coordinate-wise CM morphisms, for all 1<=j<k<=g:

\[
D_j=\{z_j=0\},\quad
D^{(1)}_{jk}=\{z_k-z_j=0\},\quad
D^{(u)}_{jk}=\{z_k-u z_j=0\},\quad u=2+i.
\]

There are g+2*binomial(g,2)=g² such divisors, **independent of a target Hodge class**.

By the standard Chern-form formula for a CM torus, the pullback of the degree-one divisor on E along a Gaussian-linear form f(z)=sum(v_j z_j) has Hermitian coefficient matrix H_v=(v_j \bar v_k), up to one fixed nonzero normalization. The Q-vector space of Hermitian g×g matrices over Q(i) has dimension g², with standard generators

\[
E_{jj},\quad E_{jk}+E_{kj},\quad i(E_{jk}-E_{kj})\quad (j<k).
\]

The D_j supply E_jj. After subtracting the diagonal entries, D^(1)_jk supplies -(E_jk+E_kj). The D^(u)_jk supplies a real off-diagonal component PLUS an imaginary off-diagonal component, because Im(u)=1. Subtracting the appropriate diagonal and twice the real off-diagonal expression isolates a nonzero multiple of i(E_jk-E_kj). Thus the classes of these g² **actual divisors** span all (1,1) directions over C and form a Q-basis of the rational divisor-class space. This is an explicit triangular elimination, not an assumed determinant.

For any 0<=p<=g, Hodge decomposition on E^g yields

\[
H^{p,p}(E^g) =
\bigwedge^p H^{1,0}(E^g)\otimes
\bigwedge^p H^{0,1}(E^g),\quad
h^{p,p}=\binom gp^2.
\]

Every basic wedge monomial with p holomorphic and p antiholomorphic one-forms is, up to a sign, a product of p elementary (1,1) classes. These elementary classes lie in the complex span of the constructed divisor classes. Therefore all H^(p,p) classes lie in the complex span of p-fold products of their **actual algebraic cycles**. Denote the rational span of these intersection products in H^(2p)(E^g,Q) by U_p. Then U_p⊗C=H^(p,p). For any rational Hodge class alpha, alpha⊗1 lies in U_p⊗C; choosing a Q-vector-space complement proves alpha∈U_p. Thus an explicit finite rational combination of intersections of the constructed divisors is a rational algebraic cycle representing alpha.

At p=0 use the fundamental class; for p>g cohomology degree 2p vanishes. Hence the rational Hodge conjecture holds **mathematically for this concrete E^g family at every g and p**.

This derivation uses classical theorems of elliptic geometry (algebraicity of CM endomorphisms, Chern forms of divisor pullbacks, exterior-algebra Hodge decomposition, and multiplicativity of cycle class). Those analytic/algebraic-geometric inputs are NOT yet proved in the repository's Lean formalization.

## D. Independent Wolfram checks

- On the actual E² graph cycles: exact intersection determinant -4 and rank 4.
- Gaussian norm N(2+i)=5 and N((2+i)-1)=2.
- For g=1,2,3,4, exact Hermitian-matrix divisor families have sizes 1,4,9,16, respectively, with full ranks and determinants 1,-1,-1,1 in fixed rational real/imaginary coordinates.
- The proof for arbitrary g is the triangular basis elimination above, not an extrapolation from the four computations.

## E. Exact missing implication for original Hodge conjecture

The construction is now **genuine geometry** in a class of abelian varieties, not an abstract CM matrix. However, an arbitrary smooth projective variety X is NOT thereby identified with E^g, nor equipped with a surjective algebraic correspondence from such a product. The statement that CM algebraic cycles and their transfers span all rational (p,p) classes of arbitrary X remains UNPROVED. Asserting that statement as a new GST law would be circular.

An especially dangerous shortcut is **diagonal** multiplication by i on E^g: on H^(p,p) it acts by i^p(-i)^p=1, so it never satisfies the global imaginary-quadratic polynomial J²=-I on those classes. Factor-selective CM morphisms and graph divisors are essential. This invalidates applying the earlier abstract CM transversality result to the diagonal CM action.

This route produced an unconditional actual-geometric CM family argument and pinpointed the arbitrary-variety transfer gap. It does **not** complete the original universal Hodge conjecture. No Lean kernel verification of the geometric family argument is claimed.