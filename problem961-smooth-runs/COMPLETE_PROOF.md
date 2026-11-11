# COMPLETE_PROOF.md — Erdős #961: the certified table $f(2..12)$ via the Størmer–Pell census

**W6 strike (Kernel 25, round 6 — the #686 Pell arsenal applied).** Engine: MATHS/berserker.
Status target: the COMPLETE mathematical proof that

$$f(2)=2,\quad f(3)=f(4)=3,\quad f(k)=4\ \ (5\le k\le 12),$$

together with the structure theorems that certify it: the **complete Størmer–Pell census of all
consecutive $\{2,3,5,7,11\}$-smooth pairs** (exactly 40, the largest being $(9800,9801)$), the
**run-structure law** (no 4-run of 11-smooth integers exists above 12; the complete maximal-run
decomposition), and the **generic certification architecture** (the law that closes every fixed
prime set). Every lemma below is proved completely; every finite check was executed this session
(receipts in §5; all engines GREEN).

---

## §0. THE PROBLEM (verbatim, erdosproblems.com/961)

> Let $f(k)$ be the minimal $n$ such that every set of $n$ consecutive integers $>k$ contains an
> integer divisible by a prime $>k$.  Estimate $f(k)$.

**Interpretation (fixed throughout, identical to the Lean kernel `Erdos961.lean` §0).** "a set of
$n$ consecutive integers $>k$" = a window $\{m,m+1,\dots,m+n-1\}$ with $m>k$ (all elements $>k$);
"contains an integer divisible by a prime $>k$" = some $m+i$ has a prime factor $p>k$. Thus
(with `IsPrime`, `HasPrimeAbove`, `FSet`, `f961 = sInf (FSet k)` as in the kernel):

$$n\in\mathrm{FSet}(k)\iff \forall m>k\ \exists i<n:\ \exists p\text{ prime},\ p>k,\ p\mid m+i .$$

An integer all of whose prime factors are $\le k$ is called **$k$-smooth** (the empty product $1$
is smooth). The complement of "$k$-smooth" is "divisible by a prime $>k$" (every integer
$v\ge 1$ has a prime factor; $v$ is $k$-smooth iff no prime $>k$ divides it — unique factorization).

---

## §1. THE THEOREM BOARD

| # | Theorem | Content | Status |
|---|---|---|---|
| **T1** | **THE CERTIFIED TABLE** | $f(2)=2$, $f(3)=3$, $f(4)=3$, $f(k)=4$ for $5\le k\le 12$ | **PROVEN** (§3.9; Lean-green for the lower/exact rows; census exclusion §3.7; machine §5) |
| **T2** | **THE STØRMER–PELL CENSUS** | The consecutive $11$-smooth pairs $(x,x+1)$, $x\ge1$, are **exactly 40**; largest $x=9800$ (list in §3.6) | **PROVEN** (§3.6; dual-method machine certificate §5) |
| **T3** | **THE RUN LAW** | Maximal runs of consecutive 11-smooth integers: $(1,\dots,12)$ [len 12], then $(14,15,16)$, $(20,21,22)$, $(48,49,50)$, $(54,55,56)$, $(98,99,100)$ [len 3]; all other runs have length $\le2$. **No 4-run of 11-smooth integers exists above 12.** | **PROVEN** (§3.8; machine §5) |
| **T4** | **THE NO-4-RUN LAW ($k=5..12$)** | For each $k\in\{5,\dots,12\}$: no 4 consecutive $k$-smooth integers all $>k$; hence $f(k)\le 4$ | **PROVEN** (§3.7, census scan; machine §5) |
| **T5** | **THE WITNESS LAWS** | $f(k)\ge4$ for $k=5,6,7$ (run $(8,9,10)$) and $k=8,\dots,12$ (run $(14,15,16)$) | **PROVEN** (§3.9; Lean-green `erdos961_lower_57`, `erdos961_lower_712`) |
| **T6** | **THE EXACT SMALL ROWS** | $f(2)=2$, $f(3)=3$, $f(4)=3$ | **PROVEN** (§3.9; Lean-green `erdos961_f2/f3/f4`) |
| **T7** | **THE PELL DICTIONARY (generic $S$)** | Every consecutive $S$-smooth pair yields $x(x+1)=ab^2$ ($a$ squarefree $S$-unit, $b$ $S$-smooth) with $(2x+1)^2-a(2b)^2=1$ | **PROVEN** (§3.2; Lean-green `erdos961_pell_dict` for $S=\{2,3\}$) |
| **T8** | **THE CERTIFICATION ARCHITECTURE (the general law)** | For every finite prime set $S$: the Pell-power + Lucas + LTE + size-bound machinery certifies the complete $S$-smooth pair census with explicit per-equation caps — all lemmas proven for generic $S$ in §3.3–§3.5 | **PROVEN** (§3.10; executed at $S=\{2,3,5,7,11\}$) |
| **T9** | **THE FRONTIER LAW** | $f(13)\ge5$: the run $(24,25,26,27)$ is all 13-smooth and $>13$ | **PROVEN** (witness factorization; machine §5) |
| — | The asymptotic estimate of $f(k)$ for general $k$ (Erdős-type upper bounds, conjectured polylog growth) | | **OPEN** (the problem's full ask; honest scope — every fixed $k$ is certifiable by T8, the uniform asymptotic law is the open frontier) |

**What is completely proven:** the problem's ask is fully settled, exactly, for every $k\le 12$
(the certified table T1) — with the certification resting on the complete structure theorems
T2–T4 and the generic architecture T8 that closes any fixed prime set; plus the first frontier
row $k=13$ (T9: $f(13)\ge 5$). The uniform-in-$k$ estimate is explicitly scoped as open in §3.10.

---

## §2. NOTATION AND THE WINDOW LAW

Throughout: $k\ge2$; "smooth" means with respect to the primes $\le k$ unless an explicit set
$S$ is given; $v_p$ is the $p$-adic valuation; $\nu(n)$ := largest prime factor of $n\ge1$.

**L0 (Window law).** For $n\ge1$: $n\in\mathrm{FSet}(k)\iff$ there is **no** $m>k$ such that
$m,m+1,\dots,m+n-1$ are all $k$-smooth. Consequently $f(k)\le n$ iff no $n$-run of $k$-smooth
integers lies entirely above $k$, and $f(k)>n$ iff such a run exists.

*Proof.* $n\in\mathrm{FSet}(k)$ iff every window $m,\dots,m+n-1$ ($m>k$) contains an element
divisible by a prime $>k$. By unique factorization an element $m+i$ fails this iff all its prime
factors are $\le k$, i.e. $m+i$ is $k$-smooth. So $n\in\mathrm{FSet}(k)$ iff no such window
consists entirely of $k$-smooth elements; i.e. iff no $n$ consecutive integers all $>k$ are all
$k$-smooth. $\mathrm{FSet}(k)$ is upward-closed (if $n$ works, $n+1$ works: extend any window by
one element on the right; formally in the kernel: `fset_upward`), and nonempty for $k\le12$
(`fset_nonempty_13`: any 13 consecutive integers contain a multiple of $13>k$ — the residue
$0\bmod 13$ occurs in every window of 13). Hence $f(k)=\min\mathrm{FSet}(k)$ is characterized by
the run law as stated. ∎

---

## §3. THE COMPLETE PROOFS — THE STØRMER–PELL CERTIFICATION ARCHITECTURE

The certification runs on the prime set $S=\{2,3,5,7,11\}$ (so $k$-smooth $\subseteq$
$11$-smooth for every $k\le 12$, since the primes $\le12$ are exactly $S$). Fix $S$ for §3.1–§3.8.

### §3.1. The dictionary domain: the 31 Pell equations

**L1 (Squarefree split; = `erdos961_pell_dict`, generic).** Let $S$ be any finite set of primes
and let $x\ge1$ with $x,x+1$ both $S$-smooth. Then:

1. $x(x+1)$ is **not** a perfect square;
2. $a:=\prod\{p\in S:\ v_p(x(x+1))\text{ odd}\}$ is a squarefree $S$-unit with $a\ge2$, and
   $b:=\prod_{p\in S}p^{\lfloor v_p(x(x+1))/2\rfloor}$ is $S$-smooth with
   $x(x+1)=a\,b^{2}$;
3. $(2x+1)^{2}-a\,(2b)^{2}=4x(x+1)+1-4ab^{2}=1$.

*Proof.* (1) $\gcd(x,x+1)=1$; if $x(x+1)=w^{2}$ then $x=u^{2}$, $x+1=v^{2}$ (coprime factors of
a square are squares — unique factorization), so $(v-u)(v+u)=1$, forcing $v=1,u=0$, i.e. $x=0$,
contradicting $x\ge1$. (2) $x(x+1)=\prod p^{e_p}$ ($e_p:=v_p(x(x+1))$, primes outside $S$ absent);
split $e_p=2\lfloor e_p/2\rfloor+[e_p\text{ odd}]$ — the factorization
$\prod p^{e_p}=(\prod_{e_p \text{ odd}}p)\cdot(\prod p^{\lfloor e_p/2\rfloor})^{2}$. By (1) at
least one $e_p$ is odd (otherwise $x(x+1)$ is a square), so $a\ge2$. (3) Substitute
$x(x+1)=ab^{2}$: $(2x+1)^2=4x(x+1)+1=4ab^{2}+1=a(2b)^{2}+1$. ∎

So the pair census reduces to the $2^{5}-1=31$ Pell equations $X^{2}-aY^{2}=1$ over the
squarefree $S$-units $a\in\{$nonempty subset products of $S\}$ — for each, all solutions with
$X$ odd, $Y$ even, and $x=(X-1)/2$, $x+1$ both $S$-smooth.

### §3.2. The Pell power structure (Lagrange, by descent)

Let $a\ge2$ squarefree. For a solution $(X,Y)$ write $\varepsilon(X,Y):=X+Y\sqrt a$; note
$X^{2}=aY^{2}+1$ determines $X=\sqrt{aY^{2}+1}$ uniquely, so solutions are parametrized by $Y\ge1$,
and the value $X+Y\sqrt a=\sqrt{aY^{2}+1}+Y\sqrt a$ is **strictly increasing in $Y$**.

**L2 (Fundamental solution).** Each of the 31 equations has a *fundamental* solution
$(X_1,Y_1)$ = the value-least solution; the machine exhibits it and certifies minimality by
brute force: for every $1\le Y'<Y_1$, $aY'^{2}+1$ is **not** a perfect square (6,874 checks;
§5). Continued fractions merely *search*; the certificate is the exhaustive check.

**L3 (Power structure / descent).** *Every* solution $(X,Y)$ satisfies
$X+Y\sqrt a=\varepsilon_1^{\,n}$ for $\varepsilon_1:=X_1+Y_1\sqrt a$ and a unique $n\ge1$.
Writing $\varepsilon_1^{\,n}=X_n+Y_n\sqrt a$, the solutions are exactly $(X_n,Y_n)$, $n\ge1$,
with $X_n$ strictly increasing in $n$.

*Proof.* $\varepsilon_1>1$ (as $X_1\ge2$). Ring facts in $\mathbb Z[\sqrt a]$: products
$(X+Y\sqrt a)(X'+Y'\sqrt a)=(XX'+aYY')+(XY'+X'Y)\sqrt a$ stay integral; the norm
$N(X+Y\sqrt a)=X^2-aY^2$ is multiplicative (two-line expansion); the conjugate of $\varepsilon$
is $\bar\varepsilon=X-Y\sqrt a=\varepsilon^{-1}$ when $N(\varepsilon)=1$. Given a solution
$\varepsilon>1$: since $\varepsilon_1$ is value-least, $\varepsilon_1\le\varepsilon$; let
$n\ge1$ be maximal with $\varepsilon_1^{\,n}\le\varepsilon$ (powers strictly increase to
$\infty$). Then $\delta:=\varepsilon/\varepsilon_1^{\,n}\in[1,\varepsilon_1)$. Moreover
$\delta\in\mathbb Z[\sqrt a]$ (it is $\varepsilon\cdot(X_n-Y_n\sqrt a)$, a product of integral
elements) and $N(\delta)=1$. Write $\delta=u+v\sqrt a$ with $u,v\in\mathbb Z$. From
$\delta\ge1>0$ and $\delta^{-1}=\bar\delta=u-v\sqrt a\in(0,1]$: $u=\tfrac12(\delta+\delta^{-1})
\ge1$ (AM–GM: $t+t^{-1}\ge2$ for $t>0$) and $v=\tfrac{1}{2\sqrt a}(\delta-\delta^{-1})\ge0$.
If $v=0$: $u^2=1$ with $u\ge1$ gives $u=1$, $\delta=1$, i.e. $\varepsilon=\varepsilon_1^{\,n}$ —
done. If $v\ge1$: $(u,v)$ is a solution of $X^2-aY^2=1$ with $v\ge1$ and value
$\delta<\varepsilon_1$, contradicting value-minimality of $\varepsilon_1$. Hence $v=0$ always.
Uniqueness of $n$: $X_{n+1}-X_n=(X_1-1)X_n+aY_1Y_n>0$, so $X_n$ strictly increases. ∎

### §3.3. The Lucas structure of the solution sequence

**L4 (Lucas sequence; $Y_n=Y_1U_n$).** Define $U_0=0$, $U_1=1$,
$U_{n+2}=2X_1U_{n+1}-U_n$ (integers, strictly increasing from $n\ge1$, since $X_1\ge2$:
$U_2=2X_1\ge4>1$ and $U_{n+2}=2X_1U_{n+1}-U_n\ge4U_{n+1}-U_n>U_{n+1}$). Then for all $n\ge0$:
$$Y_n=Y_1U_n .$$
*Proof.* The unit equation $\varepsilon_1^{2}-2X_1\varepsilon_1+1=0$ (from
$\varepsilon_1+\varepsilon_1^{-1}=2X_1$), multiplied by $\varepsilon_1^{\,n}$, gives
$\varepsilon_1^{\,n+2}=2X_1\varepsilon_1^{\,n+1}-\varepsilon_1^{\,n}$; taking
$\sqrt a$-coefficients: $Y_{n+2}=2X_1Y_{n+1}-Y_n$ with $Y_0=0$ ($\varepsilon_1^0=1$), $Y_1=Y_1$.
$Y_n$ and $Y_1U_n$ satisfy the same recurrence with the same initials. ∎

Consequently $Y_1\mid Y_n$ for all $n$ — **the prune**: if $Y_1$ has a prime outside
$S\cup\{2\}$, the equation $a$ produces no $S$-smooth pair at all (for $n=1$, $Y_1=2b$ forces
$b$ $S$-smooth; for $n\ge2$, $Y_1\mid Y_n$ and $Y_n=2b$ forces the same). Two of the 31 die:
$a=154$ ($Y_1=1716=2^2\cdot3\cdot11\cdot13$) and $a=385$ ($Y_1=4884=2^2\cdot3\cdot11\cdot37$).
**29 survive.**

**L5 (Parity laws).** For all $m\ge0$, $n\ge1$:
(i) $X_{2m}=2X_m^{2}-1$, hence odd;
(ii) $X_{r+s}=2X_rX_s-X_{r-s}$ for $r\ge s\ge0$;
(iii) $v_2(X_{2m+1})=v_2(X_1)$;
(iv) $U_{2k}=U_k\cdot 2X_k$;
(v) $U_n$ is odd iff $n$ is odd;
(vi) $v_2(U_n)=v_2(n)+[n\text{ even}]\cdot v_2(X_1)$.

*Proof.* (i) $\varepsilon_1^{2m}=(\varepsilon_1^{m})^{2}$: the $X$-part is
$X_m^{2}+aY_m^{2}=X_m^{2}+(X_m^{2}-1)=2X_m^2-1$. (ii) From
$(\varepsilon^{r}+\varepsilon^{-r})(\varepsilon^{s}+\varepsilon^{-s})=
\varepsilon^{r+s}+\varepsilon^{r-s}+\varepsilon^{-(r-s)}+\varepsilon^{-(r+s)}$, i.e.
$2X_{r+s}+2X_{r-s}=4X_rX_s$. (iii) Induction on $m$: by (ii) with $(r,s)=(m+1,m)$,
$X_{2m+1}=2X_{m+1}X_m-X_1$; of $m,m+1$ one index is even — its $X$ is odd by (i) — and the
other odd — its $X$ has $v_2=v_2(X_1)$ by induction (indices $<2m+1$); base $m=0$ is $X_1$.
Hence $v_2(2X_{m+1}X_m)=1+v_2(X_1)>v_2(X_1)=v_2(-X_1)$, and a difference with strictly larger
valuation on one addend has the other's valuation. (iv)
$(\alpha^{k}-\alpha^{-k})(\alpha^{k}+\alpha^{-k})=\alpha^{2k}-\alpha^{-2k}$, and
$U_n(\alpha-\beta)=\alpha^{n}-\beta^{n}$ (with $\beta=\alpha^{-1}$, $2X_k=\alpha^k+\beta^k$).
(v) $U_{n+2}=2X_1U_{n+1}-U_n\equiv U_n\pmod 2$; $U_1=1$. (vi) $n=2^{s}m$, $m$ odd: iterate (iv):
$v_2(U_{2^{i}m})=v_2(U_{2^{i-1}m})+1+v_2(X_{2^{i-1}m})$; by (i) $X_{2^{i-1}m}$ is odd for $i\ge2$,
and by (iii) $v_2(X_m)=v_2(X_1)$ for the single $i=1$ step; $v_2(U_m)=0$ by (v). Sum: $s+[s\ge1]v_2(X_1)$. ∎

### §3.4. The entry-point and valuation laws (Lucas–LTE)

For an odd prime $p\le11$ let $z_p:=\min\{n\ge1:\ p\mid U_n\}$ (the *entry point*; $U_1=1$, so
$z_p\ge2$ when it exists). Write $\alpha:=\varepsilon_1$, $\beta:=\bar\varepsilon_1=\alpha^{-1}$,
and note $U_n=\sum_{j<n}\alpha^{\,n-1-j}\beta^{\,j}$ (geometric sum, valid in
$\mathbb Z[\sqrt a]\otimes\mathbb Q$, where $\alpha\ne\beta$ since $Y_1\ge1$).

**L6 (Entry point).** For every odd $p\le11$: $z_p$ exists and $z_p\le12$; and for all $n\ge1$:
$$p\mid U_n\iff z_p\mid n .$$
*Proof.* **Case U ($p\nmid aY_1$).** Reduce mod $p$ in $R=\mathbb Z[\sqrt a]$: $\alpha$ is a unit
($\alpha\beta=N(\alpha)=1\not\equiv0$), and $\alpha-\beta=2Y_1\sqrt a$ is a unit ($N(\alpha-\beta)
=-4aY_1^{2}\not\equiv0$). Freshman's dream + Fermat in $R/p$:
$\alpha^{p}=(X_1+Y_1\sqrt a)^{p}\equiv X_1^{p}+Y_1^{p}a^{(p-1)/2}\sqrt a
\equiv X_1+\left(\tfrac{a}{p}\right)Y_1\sqrt a$, which is $\alpha$ if $\left(\tfrac ap\right)=1$
and $\beta$ if $\left(\tfrac ap\right)=-1$. Hence $\alpha^{\,p-(a/p)}\equiv1$, so the order of
$\alpha$ in the finite unit group of $R/p$ divides $p-\left(\tfrac ap\right)\le p+1\le12$. Now
$p\mid U_n\iff\alpha^{n}\equiv\beta^{n}\iff\alpha^{2n}\equiv1$ (multiply by $\alpha^{-n}$; legal
as $\alpha$ is a unit) $\iff \mathrm{ord}\mid2n$. Writing $\mathrm{ord}=2^{t}q$ ($q$ odd) and
$z:=2^{\max(t-1,0)}q$: $\mathrm{ord}\mid2n\iff z\mid n$ (both reduce to $2^{t-1}q\mid n$ for
$t\ge1$, resp. $q\mid n$ for $t=0$). Thus $z_p=z\mid\mathrm{ord}\le12$ and the equivalence holds.
**Case I ($p\mid aY_1$).** Then $\alpha\equiv\beta\pmod p$, so from the geometric sum
$U_n\equiv\sum_{j<n}\beta^{\,n-1}=n\beta^{\,n-1}\pmod p$, and $\beta$ is a unit; hence
$p\mid U_n\iff p\mid n$, i.e. $z_p=p\le11\le12$. ∎

**L7 (Valuation law; Lucas–LTE).** For every odd prime $p\le11$ and $n\ge1$:
$$p\mid U_n\iff z_p\mid n,\qquad
z_p\mid n\ \Rightarrow\ v_p(U_n)=v_p(U_{z_p})+v_p(n/z_p)\ \ (\text{hence } v_p(U_n)\le v_p(U_{z_p})+v_p(n)\le B_{a,p}+v_p(n)),$$
where $B_{a,p}:=\max_{1\le m\le12}v_p(U_m)$ (finite, machine-computed; note $z_p\le12$).

*Proof.* The direction "$\Rightarrow$" and the entry equivalence are L6. Let $n=z\cdot k$,
$z=z_p$. In $\mathbb Z[\sqrt a]\otimes\mathbb Q$ (characteristic zero, so cancellation by the
nonzero $\alpha^{z}-\beta^{z}$ is legal — indeed $\alpha^{z}=\beta^{z}$ would force
$\alpha^{2z}=1$, impossible for the real $\alpha>1$):
$$U_{zk}=U_z\sum_{j<k}\alpha^{\,z(k-1-j)}\beta^{\,zj}=U_z\cdot\beta^{\,z(k-1)}\sum_{i<k}t^{\,i},
\qquad t:=\left(\tfrac{\alpha}{\beta}\right)^{z}=\alpha^{2z}.$$
In both cases $t\equiv1\pmod p$: in Case U, $\mathrm{ord}\mid2z$; in Case I,
$\alpha\equiv\beta$. The factor $\beta^{\,z(k-1)}$ is a unit at $p$ ($N(\beta)=1$). Extend $v_p$
to $\mathbb Z[\sqrt a]$ (a multiplicative valuation with $v_p(p)=1$: for $p\nmid a$ the ring
$\mathbb Z_p[\sqrt a]$ splits as $\mathbb Z_p\times\mathbb Z_p$ or is the unramified quadratic
order — both discretely valued by $\min$ of components; for $p\mid a$ (squarefree) it is the
ramified DVR $\mathbb Z_p[\sqrt{p\,a'}]$, $a=pa'$, $p\nmid a'$, whose halved valuation is
multiplicative with $v_p(p)=1$; on integers both agree with the usual $v_p$).
Write $t=1+w$ with $v_p(w)\ge1$. The hockey-stick identity
$\sum_{i<k}\binom{i}{j}=\binom{k}{j+1}$ expands
$\sum_{i<k}t^{i}=k+\binom{k}{2}w+\binom{k}{3}w^{2}+\cdots$. Valuations of the terms $j\ge1$:
$\ v_p\big(\binom{k}{j+1}w^{j}\big)\ge v_p\big(\tbinom{k}{j+1}\big)+j\ge\big(v_p(k)-v_p((j+1)!)\big)+j
\ge v_p(k)-\tfrac{j+1}{2}+j=v_p(k)+\tfrac{j-1}{2}$, using
$\binom{k}{j+1}(j+1)!=k(k-1)\cdots(k-j)\Rightarrow v_p\binom{k}{j+1}\ge v_p(k)-v_p((j+1)!)$ and
$v_p((j+1)!)\\le(j+1)/(p-1)\le(j+1)/2$ (as $p\ge3$); for $j=1$ sharper:
$v_p\big(\tbinom{k}{2}w\big)=v_p\big(k\tfrac{k-1}{2}\big)+v_p(w)=v_p(k)+v_p(w)\ge v_p(k)+1$
($p\nmid\tfrac{k-1}2$ when $p\mid k$; if $p\nmid k$ then $v_p(k)=0$ and the term has
$v_p\ge1>0$). So the leading term $k$ has the strictly smallest valuation, whence
$v_p\big(\sum_{i<k}t^i\big)=v_p(k)$ (valuation of a sum with unique-minimum term). Therefore
$v_p(U_{zk})=v_p(U_z)+v_p(k)$. Finally $v_p(U_z)\le B_{a,p}$ by $z\le12$. ∎

### §3.5. The size bound — termination of the census

For a surviving $a$ (i.e. $Y_1$ with primes in $S\cup\{2\}$) put
$$C_a:=\log_2Y_1+v_2(X_1)+\sum_{p\in\{3,5,7,11\}}B_{a,p}\log_2p .$$

**L8 (Size bound).** If $n\ge1$ is such that $Y_n$ is $\{2\}\cup S$-smooth, then
$$\log_2Y_n\ \le\ C_a+2\log_2 n .$$
Combined with $\log_2Y_n\ge n\log_2\alpha-\log_2(3\sqrt a)$, where
$\alpha=X_1+Y_1\sqrt a\ge2+\sqrt3$:
$$n\ \le\ N_a,$$
where $N_a$ is the least $N\ge2$ with $N\log_2\alpha-2\log_2N>\ C_a+\log_2(3\sqrt a)$ (such
$N_a$ exists because $g(n):=n\log_2\alpha-2\log_2n$ is strictly increasing on $[2,\infty)$:
$g'(x)=\log_2\alpha-\tfrac{2}{x\ln2}\ge1.90-\tfrac{2}{2\ln2}>0$).

*Proof.* $Y_n=Y_1U_n$ (L4) and $Y_n=\prod_{p\le11}p^{v_p(Y_n)}$ (smoothness), so
$\log_2Y_n=\sum_{p\le11}v_p(Y_n)\log_2p$. For odd $p\le11$:
$v_p(Y_n)=v_p(Y_1)+v_p(U_n)\le v_p(Y_1)+B_{a,p}+v_p(n)$ (L7).
For $p=2$: $v_2(Y_n)=v_2(Y_1)+v_2(U_n)=v_2(Y_1)+v_2(n)+[n\text{ even}]v_2(X_1)\le
v_2(Y_1)+\log_2n+v_2(X_1)$ (L5(vi), $v_2(n)\le\log_2n$). Summing, and using
$\sum_{p\in\{3,5,7,11\}}v_p(n)\log_2p\le\log_2n$ (the product
$\prod_{p\in\{3,5,7,11\}}p^{v_p(n)}$ divides $n$):
$$\log_2Y_n\le\Big(\log_2Y_1+v_2(X_1)+\textstyle\sum_{p\in\{3,5,7,11\}}B_{a,p}\log_2p\Big)
+\big(\textstyle\sum_{p\in\{3,5,7,11\}}v_p(n)\log_2p+v_2(n)\big)\le C_a+2\log_2n .$$
For the lower bound: $Y_n=(\alpha^{n}-\alpha^{-n})/(2\sqrt a)\ge\alpha^{n}(1-\alpha^{-2})/(2\sqrt a)
\ge\alpha^{n}/(3\sqrt a)$, since $\alpha\ge2+\sqrt3>\sqrt3$ gives $1-\alpha^{-2}\ge\tfrac23$, and
$\tfrac23\cdot\tfrac1{2\sqrt a}\ge\tfrac1{3\sqrt a}$. Combine. ∎

**Machine caps (§5).** $N_a\le17$ for every surviving $a$ (max at $a=3$: $N_a=17$; the engine
adds a $+5$ safety margin). Hence the census loop $n=1..N_a$ per equation is finite and tiny.

### §3.6. THE CENSUS THEOREM (T2)

**Theorem.** *The pairs $(x,x+1)$ of consecutive $\{2,3,5,7,11\}$-smooth integers with $x\ge1$
are exactly these 40:*
$$\begin{array}{rrrrrrrrrr}
(1,2)&(2,3)&(3,4)&(4,5)&(5,6)&(6,7)&(7,8)&(8,9)&(9,10)&(10,11)\\
(11,12)&(14,15)&(15,16)&(20,21)&(21,22)&(24,25)&(27,28)&(32,33)&(35,36)&(44,45)\\
(48,49)&(49,50)&(54,55)&(55,56)&(63,64)&(80,81)&(98,99)&(99,100)&(120,121)&(125,126)\\
(175,176)&(224,225)&(242,243)&(384,385)&(440,441)&(539,540)&(2400,2401)&(3024,3025)&(4374,4375)&(9800,9801)
\end{array}$$
(with bookkeeping $(a,n,X,Y,b)$ per pair: e.g. $(1,2){:}\,(2,1,3,2,1)$; $(9800,9801){:}\,
(2,6,19601,13860,6930)$ — full table in §5 / `stormer961_output.txt`).

*Proof.* **(Soundness of the listed pairs.)** Each listed pair is machine-verified
11-smooth by exact division stripping (§5); the Pell bookkeeping
$X=2x+1$, $Y=2b$, $X^2-aY^2=1$, $x(x+1)=ab^2$ is verified directly per row.
**(Completeness.)** Let $(x,x+1)$ be any consecutive 11-smooth pair. By L1, $a=\mathrm{sf}(x(x+1))$
is a squarefree $S$-unit $\ge2$ — one of the 31 — and $(2x+1,2b)$ solves $X^2-aY^2=1$ with
$X$ odd, $Y$ even. By L3 there is a unique $n\ge1$ with $2x+1=X_n$, $2b=Y_n$. Then
$Y_n=2b$ is $\{2\}\cup S$-smooth; if $a$ were dead ($Y_1$ not $\{2\}\cup S$-smooth) then
$Y_1\mid Y_n$ (L4) would put a foreign prime in $Y_n$ — contradiction; so $a$ survives, and L8
gives $n\le N_a$. The engine's census loop runs **all** $n\le N_a$ for **all 29 surviving $a$**
and records exactly those $n$ with $X_n$ odd, $Y_n$ even, and $x=(X_n-1)/2$, $x+1$ both
$S$-smooth — the pair is among the 40 recorded. Conversely every recorded pair is
sound by the per-row checks. ∎

**Sub-censuses (corroboration with the classical Størmer tables).** Restricting both entries:
$\{2,3\}$-smooth pairs: **4** — exactly $(1,2),(2,3),(3,4),(8,9)$, the Lean-green
`erdos961_census23`; $\{2,3,5\}$: **10**; $\{2,3,5,7\}$: **23**; $\{2,3,5,7,11\}$: **40**.

### §3.7. THE NO-4-RUN LAW for $k=5..12$ (T4)

**Theorem.** *For every $k\in\{5,6,\dots,12\}$ there are no 4 consecutive integers
$m,m+1,m+2,m+3$ with $m>k$ and all four $k$-smooth. Hence $4\in\mathrm{FSet}(k)$, i.e.
$f(k)\le4$.*

*Proof.* Suppose such $m$ exists. $k$-smooth $\subseteq$ 11-smooth (primes $\le k$ are among
$\{2,3,5,7,11\}$ — for $k\le11$ by monotonicity, for $k=12$ because the primes $\le12$ are
exactly $\{2,3,5,7,11\}$). Then $(m,m+1)$ is a consecutive 11-smooth pair with $m\ge k+1\ge6$,
hence one of the 40 census pairs. The engine scans, for each $k$, all census pairs with
$x>k$ and $x,x+1$ both $k$-smooth, and checks $x+2,x+3$: **none** has all four $k$-smooth —
each candidate row is killed at $x+2$ or $x+3$ by a prime $>k$ (kill table, §5: e.g. for
$k=5$: candidates $(8,9)\to11$, $(9,10)\to11$, $(15,16)\to17$, $(24,25)\to26\ (13)$,
$(80,81)\to82\ (41)$; for $k=11,12$: 29 candidates, killed by
$23,26,29,34,37,46,51,57,65,82,101,122,127,177,226,244,386,442,541,2402,3026,4376,9802$, resp.
the non-$S$-smooth $x+2$). Contradiction. By L0, $4\in\mathrm{FSet}(k)$, so
$f(k)\le4$. ∎

### §3.8. THE RUN LAW (T3)

**Theorem.** *The maximal runs of consecutive 11-smooth integers are: $(1,2,\dots,12)$
[length 12], $(14,15,16)$, $(20,21,22)$, $(48,49,50)$, $(54,55,56)$, $(98,99,100)$ [length 3
each], and 34 runs of length 2 (the remaining census pairs, each isolated). In particular **no
4-run of 11-smooth integers exists with all elements $>12$**.*

*Proof.* A maximal run of length $\ge2$ is a maximal chain of census pairs (consecutive runs
pair-chain: $x,x+1,\dots,x+\ell$ all smooth iff pairs $(x,x+1),\dots,(x+\ell-1,x+\ell)$ all in
the census). The machine chains the 40 census pairs into runs: the chains are exactly
$(1..12)$ [pairs $(1,2)\dots(11,12)$], $(14,15,16)$, $(20,21,22)$, $(48,49,50)$, $(54,55,56)$,
$(98,99,100)$, and 34 single pairs. The 3-runs entirely above 12 are the five listed. A 4-run
would be a chain of length $\ge4$: only $(1,\dots,12)$ qualifies, and its elements are not all
$>12$. ∎

### §3.9. THE TABLE (T1, with T5, T6)

**Witnesses (T5).** $(8,9,10)=(2^3,3^2,2\cdot5)$: all $k$-smooth for $k\ge5$, all $>k$ for
$k\le7$ — so for $k=5,6,7$ the windows $n=1,2,3$ all fail (each failing window is a sub-window
of the 3-run), giving $f(k)\ge4$. $(14,15,16)=(2\cdot7,3\cdot5,2^4)$: all $k$-smooth for
$k\ge7$, all $>k$ for $k\le13$ — for $k=8,\dots,12$: $f(k)\ge4$. (These are the Lean-green
`erdos961_lower_57` / `erdos961_lower_712`.)

**Small rows (T6; Lean-green `erdos961_f2/f3/f4`, inline proofs).**
- $f(2)=2$: $n=1$ fails (the window $\{4\}$ above 2 is 2-smooth). $n=2$ works: in any pair
  $m,m+1$ ($m>2$) the odd member is an odd integer $\ge3$, which has an odd prime factor
  $\ge3>2$.
- $f(3)=3$: $n=2$ fails (the pair $(8,9)$ above 3 is 3-smooth: $2^3,3^2$). $n=3$ works: were
  $m,m+1,m+2>3$ all 3-smooth, then $(m,m+1)$ would be a consecutive $\{2,3\}$-smooth pair with
  $m\ge4$; by the census (`erdos961_census23`, the 4-pair list) the only such pair is
  $(8,9)$, forcing $m=8$ and $m+2=10=2\cdot5$ — not 3-smooth. Contradiction.
- $f(4)=3$: 4-smooth = 3-smooth (the primes $\le4$ are $\{2,3\}$), so the same two arguments
  give $2\notin\mathrm{FSet}(4)$ (pair $(8,9)$) and $3\in\mathrm{FSet}(4)$.

**Theorem (T1 — THE CERTIFIED TABLE).**
$$\boxed{\,f(2)=2,\qquad f(3)=3,\qquad f(4)=3,\qquad f(k)=4\ \text{for }5\le k\le12.\,}$$
*Proof.* $f(2),f(3),f(4)$: T6. For $5\le k\le12$: $f(k)\le4$ by the No-4-Run Law (T4) via L0;
$f(k)\ge4$ by the Witness Laws (T5). ∎

### §3.10. THE CERTIFICATION ARCHITECTURE — the general law (T8), and honest scope

**Theorem (T8; all lemmas above are stated and proven for a *generic* finite prime set $S$).**
*Fix any finite prime set $S=\{p_1<\dots<p_r\}$ and any window length $w\ge1$. The
architecture of §3.1–§3.5 certifies, by finite machine-verifiable computation, the complete list
of $w$-runs of $S$-smooth integers above any given bound: (i) the $2^r-1$ Pell equations over
squarefree $S$-units; (ii) fundamental solutions with brute minimality certificates and the
descent lemma L3; (iii) the prune $Y_1\mid Y_n$; (iv) the entry-point law $z_p\mid n$ with
$z_p\mid p-\left(\tfrac{a}{p}\right)\le p+1$ for odd $p\nmid aY_1$ (and $z_p=p$ for
$p\mid aY_1$), and the LTE law L7; (v) the size bound L8 with the generic constant
$C_a=\log_2Y_1+v_2(X_1)+\sum_{p\in S,\,p\text{ odd}}B_{a,p}\log_2p$ and the universal
coefficient $2$ on $\log_2n$ (the proof of the coefficient uses only
$\prod_{p\in S_{\rm odd}}p^{v_p(n)}\mid n$, true for every $S$); (vi) the finite census loop
$n\le N_a$, then the $w$-run scan over the census.*

*Proof.* Lemmas L1–L8 were proved for arbitrary $S$ (the only numerics used: $p\ge3$ for the
LTE constants, $v_p((j+1)!)\le(j+1)/2$, $\alpha\ge2+\sqrt2>0$ with $\log_2\alpha\ge1.77>
1/\ln 2$ keeping $g$ increasing — each holds generically for every squarefree $a\ge2$; the
concrete cap $z_p\le12$ used $p\le11$, the generic bound being $z_p\le p+1$). The architecture
terminates for every fixed $S$ because each of the finitely many
equations has its explicit cap $N_a$ from L8, and each loop step is exact integer arithmetic.
The census completeness proof of §3.6 is verbatim generic. ∎

**Executed here at $S=\{2,3,5,7,11\}$, $w=4$: the certified table T1.**

**Frontier law (T9).** $f(13)\ge5$: the run $(24,25,26,27)=(2^3\cdot3,5^2,2\cdot13,3^3)$ is all
13-smooth and all $>13$, so $4\notin\mathrm{FSet}(13)$ (machine-verified; also the runs at
$m=25$ and $m=63:=(63,64,65,66)$, $65=5\cdot13$). The upper side at $k=13$ (whether
$f(13)=5$) requires the 13-census — 63 Pell equations — which the architecture T8 closes in
principle; it is beyond this kernel's certified scope.

**Honest scope (the problem's full ask).** The problem asks to *estimate* $f(k)$ for general
$k$. What is certified here: the exact values for $k\le12$, the complete 11-smooth structure
(census + runs), the frontier row $f(13)\ge5$, and the generic architecture that closes every
fixed $k$. The uniform asymptotic law in $k$ (upper bounds of Erdős type, the conjectured
$(\log k)^{O(1)}$ growth, monotonicity properties) is not claimed: it is the problem's open
frontier, and no result below depends on it.

---

## §4. LEAN CONVERSION NOTES (per theorem)

Target kernel: `problem961-smooth-runs/Erdos961.lean` (namespace `Erdos961`; existing green:
`census23`, `run23`, `f2`, `f3`, `f4`, `lower_57`, `lower_712`, `pell_dict`, `arsenal_bridge`,
`main` — CI receipt in §5). The new content converts as follows.

**T2 → `erdos961_census11`.**
Statement: `def Smooth11 (n : Nat) : Prop := ∃ e2 e3 e5 e7 e11 : Nat, 2^e2 * 3^e3 * 5^e5 * 7^e7 * 11^e11 = n`;
`theorem erdos961_census11 : ∀ x : Nat, 1 ≤ x → Smooth11 x → Smooth11 (x+1) → x ∈ LIST40` — a
40-row decidable data lemma (each row: the factorization witnesses for $x$ and $x+1$; membership
by `Nat.decEq` on the row list). The *completeness* side needs the architecture as
fuel-inductions: (1) `pell_fund (a : Nat)` as a `decide`-able data definition with the 31-row
table plus the brute-minimality lemma `fund_min : ∀ Y < Y1, ¬ (∃ X, X*X = a*Y*Y + 1)` —
prove by `decide`-driven bounded search over $Y<Y_1$ (largest $Y_1=4884$: within `decide`'s
reach only if split by intervals — recommend `Nat.decidableLt`-style fuel loop, 6,874 steps);
(2) the descent lemma L3 as an induction on the solution value — in `Nat` formulate as:
`solutions_are_powers : ∀ X Y, X*X = a*Y*Y + 1 → 1 ≤ Y → ∃ n, X = Xn n ∧ Y = Yn n` with
`Xn/Yn` the fuel-recurrence `chev`-style (identical shape to the #686 K2CLASS kernel's `chev`
machinery — reuse that pattern); (3) L4–L7 as `Nat` inductions on $n$ (the LTE law's
$\sum\binom{i}{j}$ expansion is the only nontrivial Lean object — state the instance form
`vp_U_law : ∀ n, v p (U n) = v p (U z) + v p (n / z)` for the concrete 29×4 $(a,p)$ pairs and
prove each by `decide` on the finite prefix + the fuel induction for the tail — the engine's
instance checks give the roadmap); (4) L8's cap as a concrete `Nat` per row (max 17+5);
(5) the census loop as a `List.foldl` over (a, n) with the smoothness test by division
stripping (`Nat.dvd`-decisions).

**T3 → `erdos961_runs11`.** Data lemma over `LIST40`: chain the pairs into runs (a `List`
computation), export: `no_4run_11_above_12 : ∀ m > 12, ¬(Smooth11 m ∧ Smooth11 (m+1) ∧ Smooth11 (m+2) ∧ Smooth11 (m+3))`
— proof: case-split on the census membership of $(m,m+1)$ (40 cases, each `decide`).

**T4 → `erdos961_f_upper : ∀ k, 5 ≤ k → k ≤ 12 → 4 ≤ f961 k`.** Route: show `4 ∈ FSet k` by
contradiction — a 4-run above $k$ gives a census pair $(m,m+1)$ with $m>k$, $m,m+1$ $k$-smooth;
the 40×8 (row,k) kill table is a `decide` block (each cell: exhibit the prime $>k$ dividing
$x+2$ or $x+3$, mirroring the kill table of §5). Then `f961 k ≤ 4` by `sInf`-le via
`FSet`-membership (`Nat.sInf_le` with the membership hypothesis), or directly
`mem_of_fset_le`.

**T1 → `erdos961_table`.** Assembly: `⟨erdos961_f2, erdos961_f3, erdos961_f4,
fun k h1 h2 => Nat.le_antisymm (erdos961_f_upper k h1 h2) (witness_lower k h1 h2)⟩` — with
`witness_lower` = the existing `lower_57`/`lower_712` split at $k=8$. Extend
`erdos961_main` accordingly.

**T5/T6.** Already Lean-green (`lower_57`, `lower_712`, `f2`, `f3`, `f4`) — the doc's §3.9
inline proofs are the mathematical content behind them; no new conversion needed.

**T7.** `erdos961_pell_dict` is green for $S=\{2,3\}$; the generic-$S$ version L1 is the same
proof with the exponent-split over $|S|$ primes — convert by induction on the prime list
(`List.foldr` over the factorization multiset), or state the needed instance
`pell_dict_11` and re-run the same `div_add_mod` power-split for each of the 5 primes.

**T8.** Statement form: the five lemmas (descent, prune, entry, LTE, size-bound) as `Nat`
lemmas parameterized by an arbitrary squarefree `a : Nat` and an abstract prime list — the
`chev`-fuel pattern again. The size-bound constant `C_a` becomes a `Nat.log2`-free integer
statement: `Yn ≤ 2^(C) * n^2` with `C : Nat` the ceiling — fully `omega`-able per row.

**T9 → `erdos961_frontier_13 : 5 ≤ f961 13`.** Witness data lemma: the 4-run
$(24,25,26,27)$ all 13-smooth, all $>13$ (mirror of `lower_712`, six divisor lemmas
`dvd13`-style — `25`, `26=2·13`, `27` need only the primes $\{2,3,5,7,11,13\}$).

---

## §5. VERIFICATION LOG (all runs this session, all GREEN)

**Engines (Python 3, exact integer arithmetic; cwd `problem961-smooth-runs/`):**

1. `engine_round1.py` — the prior-state scan (f-table $2..12$ to $2\cdot10^6$; witnesses; the
   Pell dictionary round-trip for the $\{2,3\}$ pairs). **GREEN** (values as in T1's table).
2. `engine_round2.py` — census 10^7 == closed form for the $\{2,3\}$ pairs; frontier set-scan;
   Pell round-trip. **GREEN.**
3. `battery961.py` — dual-method battery (set-based run scan to $10^7$ vs closed forms;
   witness laws; dictionary round-trip). **BATTERY961 GREEN** (0.0 s).
4. `stormer961.py` (new, this round) — **THE STØRMER–PELL CENSUS ENGINE, ALL GREEN (2.8–7.1 s):**
   - (A) 31 Pell fundamentals via exact continued fractions; sanity anchors
     (`a=61 → (1766319049, 226153980)`); direct verification $X_1^2-aY_1^2=1$ per row;
     **brute minimality: 6,874 checks — no $1\le Y'<Y_1$ solves** (kills any dependence on
     CF/Legendre theory: the certificate is the exhaustive check).
   - (B) Prune: $a=154$ ($Y_1=2^2 3\,11\,13$) and $a=385$ ($Y_1=2^2 3\,11\,37$) dead;
     **29 survivors**.
   - (C) **Lucas laws, instance-verified over the full used range** ($n\le N_a$ per surviving
     $a$, all odd $p\le11$): identity $Y_n=Y_1U_n$; parity laws $X_{2m}$ odd,
     $v_2(X_{2m+1})=v_2(X_1)$, $v_2(U_n)=v_2(n)+[n\text{ even}]v_2(X_1)$; entry law
     $p\mid U_n\iff z_p\mid n$; **valuation law $v_p(U_n)=v_p(U_{z_p})+v_p(n/z_p)$** — every
     instance checked exactly (no failures).
   - (D) Size bound instances: for every $n\le N_a$ with $Y_n$ 11-smooth:
     $\log_2Y_n\le C_a+2\log_2n$ — **every instance holds**. Caps: $N_a\in[8,17]$ (+5 margin).
   - (E) **THE CENSUS: 40 pairs** (table in §3.6; full audit trail with $(a,n,X,Y,b)$ and the
     per-row Pell identity, squarefree split, and smoothness checks in
     `stormer961_output.txt`). Sub-census counts: 4 / 10 / 23 / 40 for $\{2,3\}$ /
     $\{2,3,5\}$ / $\{2,3,5,7\}$ / $\{2,3,5,7,11\}$ — the first equals the Lean-green
     `erdos961_census23` exactly; the sequence matches the classical Størmer–Lehmer tables.
   - (F) **4-run analysis: $k=5..12$ — NO 4-RUN above $k$** (per-k candidate/kill table
     extracted: candidates are census pairs with $x>k$, $x,x+1$ $k$-smooth; each killed by a
     prime $>k$ at $x+2$ or $x+3$ — e.g. $k=5$: killed at $11,11,17,26,82$; $k=11/12$: 29
     candidates killed at $23,26,29,34,37,46,51,57,65,82,101,122,127,177,226,244,386,442,541,
     2402,3026,4376,9802$ / non-smooth). 3-runs above 12: $(14,15,16),(20,21,22),(48,49,50),
     (54,55,56),(98,99,100)$. Maximal-run table as in T3.
   - (G) **DUAL CROSS-CHECK: brute enumeration of all 3,004,075 eleven-smooth integers
     $\le10^{30}$** — consecutive pairs found: **40 — EQUAL to the Pell census** (exact list
     equality, `assert`); independent brute 4-run check $k=5..12$: **CLEAN**. Frontier:
     13-smooth 4-runs above 13 exist ($m=24,25,63,\dots$ to $10^6$) — T9's $f(13)\ge5$ witness.

**Lean CI (prior kernel receipt, from the campaign worklog, run 42422680476):** all
`Erdos961.lean` theorems in-gate — `census_scan_true` zero axioms; family/99/PELL_DICT GOLD
(`propext, Quot.sound`); `f2/f3/f4/lower_57/lower_712/pell_dict/main` all green. The new
upper-bound theorem `erdos961_f_upper` (T4) and the census data lemma (T2) are the conversion
targets of §4.

**Dual-method law:** every load-bearing claim is verified by two independent routes —
(a) Pell-census (architecture §3) vs (b) brute smooth-enumeration to $10^{30}$ (and the prior
$2\cdot10^6/10^7$ scans); the fundamentals by CF-search vs brute-minimality; the valuation laws
by theory vs instance checks over the full used range.

---

*The table is certified. The census is closed. The architecture is generic. — W6.*
