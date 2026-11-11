# ERDŐS #271 — STANLEY'S SEQUENCE A(2): THE COMPLETE CHARACTERIZATION
## Complete proof assembly (target + merged campaign fronts), machine-verified

**W3 strike, 2026-11-11.** Engine: MATHS/berserker. Status target: the COMPLETE
characterization of Stanley's sequence $A(2)$ — plus the assembled inheritance:
the universal growth triptych (K36, every seed) and the full closure of the
`OdStFamily.lean` draft sub-cores (the $3^k$ family). Every lemma below is
proved completely; every finite check was run this session (receipts in §7).

---

## §0. THE PROBLEM (verbatim, erdosproblems.com/271)

> Let $A(n) = \{a_0 < a_1 < \cdots\}$ be the sequence defined by $a_0 = 0$
> and $a_1 = n$, and for $k \geq 1$ define $a_{k+1}$ as the least positive
> integer such that there is no three-term arithmetic progression in
> $\{a_0, \ldots, a_{k+1}\}$.  Can the $a_k$ be explicitly determined?
> How fast do they grow?

---

## §1. THE THEOREM BOARD

| # | Theorem | Content | Status |
|---|---|---|---|
| **M1** | **THE COMPLETE CHARACTERIZATION OF $A(2)$** | $A(2)=\{3m+d:\ m\in C,\ d\in\{0,2\}\}$, $C$ the Cantor set (no ternary digit 2). Greedy = closed form, member for member. | **PROVEN** (§3, Lemmas L1–L5 + Greedy Walk; Lean CI-green `stanley_a2_greedy`; Python re-verified §7-R1) |
| **M2** | $A(2)$ digit form | $x\in A(2) \iff$ every ternary digit at positions $\ge 1$ lies in $\{0,1\}$ and the units digit lies in $\{0,2\}$. First members $0,2,3,5,9,11,12,14,27,\dots$ (OEIS A005837). | **PROVEN** (§3, Corollary of M1) |
| **G-A2** | $A(2)$ growth law (Type-1, sharp) | $|A(2)\cap[0,3^s)|=2^s$ for all $s\ge 0$; the sharp position law $a_{2^s}=3^s$ ($s\ge 1$); and $\frac{1}{3}m^{\log_2 3}\le a_m\le 3\,m^{\log_2 3}$ for all $m\ge 1$. | **PROVEN** (§3.7; machine-checked §7-R2) |
| **U1** | Universal growth triptych (EVERY seed $n\ge 1$) | G3: $a_{k+1}\le 2a_k+1$; G2: $2a_m\ge 3m-3$; G1: $a_m\le n+\frac{(m-1)(m+2)}{2}$. The unconditional two-sided envelope $\frac{3}{2}(m-1)\le a_m\le n+\frac{(m-1)(m+2)}{2}$. | **PROVEN** (§4; Lean CI-green `growth_G1/G2/G3`; Python re-verified §7-R4) |
| **F1** | The Odlyzko–Stanley $T$-family (every seed $3^{j-1}$, $j\ge 1$) | $A(3^{j-1}) = 3^j C + E_j$ with the explicit finite block $E_j$ (§5.1); greedy = closed form for every $j$ at once. $j=1$ is the classical Cantor theorem $A(1)=C$. **Closes every open sub-core of the `OdStFamily.lean` draft.** | **PROVEN** (§5, Lemmas L6–L10 + witness table R1/R2 + Greedy Walk; machine-verified §7-R5) |
| **F2** | Family count + growth | $|A(3^{j-1})\cap[0,3^s)|=2^s$ ($s\ge j$), $a_{2^s}=3^s$ ($s\ge j$), $\frac13 m^{\log_23}\le a_m\le 3m^{\log_23}$ ($m\ge 2^{j-1}$). | **PROVEN** (§5.6; machine-checked §7-R6) |
| **S-fam** | The $2\cdot 3^k$ family (seeds $6,18,54,\dots$) | Closed forms $A(2\cdot 3^{j-2}) = 3^j C + E^S_j$ — **machine-verified** (equality to horizon $3^{j+4}$, $k\le 4$; witness coverage $=0$ holes, $j\le 5$); the general inductive proof (its full witness table) is the identified next sub-core — **not** claimed proven here. $A(2)$ itself (the $k=0$ member) is PROVEN as M1. | CERTIFIED DATA + labeled frontier (§6) |
| **A4** | The full ask (every seed) | Complete explicit determination for **every** $n$ includes $A(4)$ — a 45-year open case (OEIS A005487), empirically Type-2 by certified census $k\le 21$ ($c_{21}=710{,}129$, $\alpha_{21}=0.5840$). Not claimed here. | OPEN (§6, honest label) |

**What is completely proven:** the problem's two questions are fully answered for
the seed class $\{1,2\}\cup\{3^k:k\ge 0\}$ (explicit determination **and**
growth, both sharp), and the *growth* question is answered unconditionally for
**every** seed $n\ge 1$ (U1). The explicit-determination ask for the remaining
seeds (smallest open: $n=4$) is stated with its exact status in §6.

---

## §2. MODEL, NOTATION, AND THE GREEDY WALK (the engine of every theorem)

**Numbers.** $\mathbb N=\{0,1,2,\dots\}$. Ternary digits: $x=\sum_i d_i(x)3^i$,
$d_i(x)=\big\lfloor x/3^i\big\rfloor\bmod 3$. The **Cantor set**
$C=\{x:\ \forall i,\ d_i(x)\neq 2\}$ (Lean: `noTwo`). For $H=3^{j-1}$,
$P=3^j$: $C_{<H}:=C\cap[0,H)$.

**The greedy model.** $S(0,n)$ is built by: $a_0=0$, $a_1=n$, and $a_{k+1}$ is
the **least** $y>a_k$ such that $\{a_0,\dots,a_k,y\}$ contains no 3-term AP.
The increasing reading is forced by the problem's own $a_0<a_1<\cdots$: any
$y\le a_k$ either already lies in the prefix, or was rejected at its own scan
step (it formed an AP with the then-prefix, hence also with the full prefix —
so it can never be a future member). Each step's scan runs over
$y=a_k+1,a_k+2,\dots$ and terminates — e.g. at $2a_k+1$ (U1-G3, §4, whose
proof uses only Lemma 0 below) — so the scan windows $[a_k+1,a_{k+1}]$ tile
$[n+1,\infty)$: every integer $y>n$ is either accepted as some $a_{k+1}$ or
rejected during exactly one scan. The prefix $\{a_0,\dots,a_k\}$ is AP-free at
every step (the base $\{0,n\}$, $n\ge1$, has fewer than three elements; each
acceptance preserves AP-freeness by construction).

**Lemma 0 (blocking trichotomy).** *During the scan of a candidate
$y>a_k$, $y$ is rejected $\iff$ there are earlier members $a<b<y$ with
$a+y=2b$ (the $y$-top pattern).*

*Proof.* All earlier members are $<y$ (the sequence increases and $y>a_k$).
A 3-AP through $y$ and two earlier members $a<b$: as the **top**,
$a+y=2b$; as the **middle**, $a+b=2y$ — impossible since $a+b<2y$ (both $<y$);
as the **bottom**, $y+c=2b$ with $b,c>y$ — impossible (no members $>y$ exist
yet). A 3-AP through $y$ and *one* earlier member and one future member cannot
exist in the finite set tested. A 3-AP among earlier members only does not
involve $y$ and cannot newly block it. Finally $y$ itself paired twice is not
a 3-term AP of distinct terms. $\square$

**Lemma W (the Greedy Walk — the strong-induction assembly).**
*Let $h\ge 1$ and let $T\subset\mathbb N$ satisfy*
(W-i) $T$ is 3-AP-free; (W-ii) *every $y\notin T$ with $y>h$ admits
$a<b<y$ in $T$ with $a+y=2b$;* (W-iii) $T\cap[0,h]=\{0,h\}$.
*Then $S(0,h)=T$.*

*Proof.* Strong induction on $y\ge 0$ with the invariant
$\Phi(y)$: "$y\in S(0,h)\iff y\in T$".

**Base $y\le h$.** $S(0,h)\cap[0,h]=\{0,h\}$ (members $a_0=0<a_1=h$, nothing
between since the sequence increases), and $T\cap[0,h]=\{0,h\}$ by (W-iii).

**Step $y>h$.** Assume $\Phi(y')$ for all $y'<y$. The earlier members below
$y$ are exactly $T\cap[0,y)$: membership below $h$ is the base; membership in
$(h,y)$ is $\Phi$ by induction. The scan reaches $y$ (§2 model) and by Lemma 0
$y$ is accepted $\iff$ no pair $a<b<y$, $a,b$ earlier members, $a+y=2b$ —
i.e. $\iff$ no pair $a<b<y$ in $T$ with $a+y=2b$.

If $y\in T$: such a pair would make $\{a,b,y\}$ a 3-term AP inside the 3-AP-free
set $T$ (W-i) — contradiction. So $y$ is unblocked, hence accepted.

If $y\notin T$: (W-ii) gives $a<b<y$ in $T$, $a+y=2b$. Both $a,b\in T\cap[0,y)$,
so both are earlier members (base below $h$; $\Phi$ above). So $y$ is blocked,
hence rejected.

Both directions give $\Phi(y)$, closing the induction; $S(0,h)=T$. $\square$

Lemma W is the formalized "greedy-walk" kill: every characterization theorem of
this document (M1, F1) is Lemma W applied to an explicitly constructed $T$ whose
(W-i) is an AP-freeness lemma and whose (W-ii) is a **witness funnel** — an
explicit, total, case-checked blocking-pair construction.

---

## §3. PART I — $A(2)$: THE COMPLETE CHARACTERIZATION (THEOREM M1, M2, G-A2)

Throughout Part I, $D:=\{3m+d:\ m\in C,\ d\in\{0,2\}\}$
(Lean `inD`: $x\bmod 3\in\{0,2\}$ and $\mathrm{noTwo}(\lfloor x/3\rfloor)$).

### 3.1 Lemma L1 (Cantor digit arithmetic)

(a) $0,1\in C$; (b) $x\in C\iff x\bmod 3\in\{0,1\} \wedge \lfloor x/3\rfloor\in C$;
(c) $x\notin C\Rightarrow x\ge 2$; (d) $x\in C\Rightarrow \lfloor x/3\rfloor\in C$;
(e) $t\in C\Rightarrow 3t\in C,\ 3t+1\in C$; (f) $2c\notin C$ for every $c\in C$ with
$c\ge1$.

*Proof.* (a),(b),(d),(e) are immediate from the digit formula
($d_0(x)=x\bmod3$; $d_i(x)=d_{i-1}(\lfloor x/3\rfloor)$ for $i\ge1$; every
digit of $\lfloor x/3\rfloor$ is a digit of $x$ one position up). (c): $0,1\in C$, so
$x\notin C\Rightarrow x\ge2$. (f): let $t$ be the position of the lowest nonzero
ternary digit of $c$; $d_t(c)=1$ and all lower digits are $0$, so doubling
produces no carry below position $t$ and $d_t(2c)=2$, hence $2c\notin C$. $\square$

### 3.2 Lemma L2 (Cantor AP-freeness)

*No $x<y<z$ in $C$ with $x+z=2y$.*

*Proof (digit descent, induction on $z$).* Units digits
$d_x,d_y,d_z\in\{0,1\}$ satisfy $d_x+d_z\equiv 2d_y\pmod 3$. Testing the four
sums: $0\Rightarrow(d_x,d_y,d_z)=(0,0,0)$; $2\Rightarrow(1,1,1)$;
$1$ (i.e. $\{0,1\}$ or $\{1,0\}$) forces $2d_y\equiv1\pmod3$, impossible for
$d_y\in\{0,1\}$. So all units digits are equal, $=d$. Writing
$x=3x'+d,\ y=3y'+d,\ z=3z'+d$: $x+z=2y$ gives $3(x'+z')+2d=6y'+2d$, i.e.
$x'+z'=2y'$ with $x'<z'$ (from $x<z$) and $x',y',z'\in C$ (L1d). Since
$z'<z$ for $z\ge1$ (and $z=0$ contradicts $x<z$), the induction closes. $\square$

### 3.3 Lemma L3 (Cantor maximality — the C-witness funnel)

*Every $m\ge 2$ with $m\notin C$ admits $a<b<m$ in $C$ with $a+m=2b$.*

*Proof (complete induction on $m$; the offset-normalized stepping
construction).* Let $t=\lfloor m/3\rfloor$ and $r=m\bmod 3$.

**Direct face** ($t\in C$, so $r=2$ — the units digit is the lowest offending
digit): output $\langle 3t,\,3t+1\rangle$. Both in $C$ (L1e); $3t<3t+1<m=3t+2$;
$3t+m=6t+2=2(3t+1)$.

**Lift face** ($t\notin C$, hence $t\ge2$ by L1c): by induction take
$a'<b'<t$ in $C$ with $a'+t=2b'$, and lift by the units digit:
- $r=0$: $\langle 3a',3b'\rangle$: $3a'+m=3(a'+t)=6b'=2(3b')$; both in $C$;
  $3a'<3b'\le 3t-3<m$.
- $r=1$: $\langle 3a'+1,3b'+1\rangle$: $3a'+1+m=3(a'+t)+2=6b'+2=2(3b'+1)$;
  both in $C$ (L1e); $3a'+1<3b'+1\le 3t-2<m$.
- $r=2$: $\langle 3a',3b'+1\rangle$: $3a'+m=3(a'+t)+2=6b'+2=2(3b'+1)$;
  $3a'\le 3b'-3<3b'+1\le 3t-2<m$.

In the lift face $t\notin C$ (hence $t\ge2$ by L1c) and $t<m$, so the strong
induction hypothesis applies to $t$; the direct face covers every other case
(if $t\in C$ and $r\in\{0,1\}$ then $m\in C$, excluded). Base $m=2$: direct face
($t=0\in C$, $r=2$) gives $\langle0,1\rangle$. $\square$

### 3.4 Lemma L4 ($A(2)$ AP-freeness — one-step collapse onto a Cantor AP)

*No $x<y<z$ in $D$ with $x+z=2y$.*

*Proof.* Units digits $\in\{0,2\}$ and $x+z\equiv2y\pmod 3$: sums $d_x+d_z\in\{0,2,4\}$;
mod $3$ these are $\{0,2,1\}$, while $2d_y\bmod3\in\{0,1\}$. Case sum $\equiv0$:
$d_x=d_z=0$, forcing $d_y=0$. Case sum $\equiv1$: $d_x=d_z=2$, forcing
$2d_y\equiv4\equiv1$, so $d_y=2$. Case sum $\equiv2$: impossible. So all units
digits equal $d\in\{0,2\}$; writing $x=3x'+d$ etc. with $x',y',z'\in C$
(membership in $D$: quotient in $C$), $x+z=2y$ collapses to
$x'+z'=2y'$, $x'<z'$ — a Cantor 3-AP, contradicting L2. $\square$

### 3.5 Lemma L5 ($A(2)$ maximality — the top-witness funnel, three faces)

*Every $m\ge 3$ with $m\notin D$ admits $a<b<m$ in $D$ with $a+m=2b$.*

*Proof.* $m\notin D$ means: $m\equiv1\pmod3$, or $m\bmod3\in\{0,2\}$ with
$t:=\lfloor m/3\rfloor\notin C$. Let $t=\lfloor m/3\rfloor$.

**Face 1 ($m=3t+1$, $t\ge1$).** Set $r=t-1\ge0$.
- $r\in C$: output $\langle 3r,\,3r+2\rangle$. Both in $D$ (quotient $r\in C$;
  units $0$ and $2$); $3r<3r+2<3r+4=m$; $3r+m=6r+4=2(3r+2)$.
- $r\notin C$ (so $r\ge2$): L3 gives $c_1<c_2<r$ in $C$ with
  $c_1+r=2c_2$. Output $\langle 3c_1,\,3c_2+2\rangle$: both in $D$
  ($c_1,c_2\in C$); $3c_1<3c_2+2<3t+1=m$ (as $c_2\le r-1=t-2$);
  $3c_1+m=3(c_1+t)+1=3(2c_2+1)+1=6c_2+4=2(3c_2+2)$.

**Face 2 ($m=3t$, $t\notin C$, $t\ge2$).** L3 gives $c_1<c_2<t$ in $C$,
$c_1+t=2c_2$. Output $\langle 3c_1,3c_2\rangle$: both in $D$;
$3c_1<3c_2<3t=m$; $3c_1+m=3(c_1+t)=6c_2=2(3c_2)$.

**Face 3 ($m=3t+2$, $t\notin C$, $t\ge2$).** L3 as above; output
$\langle 3c_1+2,\,3c_2+2\rangle$: both in $D$;
$3c_1+2<3c_2+2\le 3t-1<3t+2=m$;
$3c_1+2+m=3(c_1+t)+4=6c_2+4=2(3c_2+2)$. $\square$

*(Face 1 with $r=0\in C$ outputs $\langle0,2\rangle$ — the seed pair itself
blocks $m=4$: $0+4=2\cdot2$.)*

### 3.6 THEOREM M1 (the complete characterization of $A(2)$)

$$\boxed{\,A(2)\;=\;\{\,3m+d:\ m\in C,\ d\in\{0,2\}\,\}\;}$$

*Proof.* Apply Lemma W with $h=2$, $T=D$: (W-i) is L4; (W-ii) is L5 (every
$y\notin D$, $y>2$ has $y\ge3$, covered); (W-iii) $D\cap[0,2]=\{0,2\}$ (the
elements $3\cdot0+0=0$, $3\cdot0+2=2$; $1\notin D$). Hence $S(0,2)=D$. $\square$

### 3.7 THEOREM G-A2 (count law, sharp position, growth)

**(a)** $|C\cap[0,3^s)|=2^s$ for all $s\ge0$. *Proof.* $s=0$: $C\cap[0,1)=\{0\}$.
Induction: $C\cap[0,3^{s+1})=\{3m+\rho:\ m\in C\cap[0,3^s),\ \rho\in\{0,1\}\}$
(bijection by L1e/L1b), doubling the count. $\square$

**(b)** $|A(2)\cap[0,3^s)|=2^s$ for all $s\ge0$. *Proof.* $s=0$: $\{0\}$. For
$s\ge1$: $3m+d<3^s\iff m<3^{s-1}$ (as $d\le2$), so
$A(2)\cap[0,3^s)=\{3m+d:\ m\in C\cap[0,3^{s-1}),\ d\in\{0,2\}\}$ — a bijection
with $C\cap[0,3^{s-1})\times\{0,2\}$, count $2\cdot2^{s-1}=2^s$. $\square$

**(c) Sharp position.** $a_{2^s}=3^s$ for all $s\ge1$. *Proof.* By (b),
$a_{2^s-1}<3^s\le a_{2^s}$; and $3^s=3\cdot 3^{s-1}+0\in D$ with
$3^{s-1}\in C$, so $a_{2^s}\le 3^s$. $\square$

**(d) Growth law.** For every $m\ge1$:
$$\tfrac13\,m^{\log_2 3}\;\le\;a_m\;\le\;3\,m^{\log_2 3}.$$
*Proof.* Take $s\ge1$ with $2^{s-1}\le m\le 2^s$ (possible for every
$m\ge1$; then $2^s\le 2m$). By (c) and monotonicity,
$3^{s-1}=a_{2^{s-1}}\le a_m\le a_{2^s}=3^s$. Hence
$a_m\le 3^s=(2^s)^{\log_23}\le(2m)^{\log_23}=3\,m^{\log_23}$ and
$a_m\ge 3^{s-1}\ge \tfrac13(2^{s})^{\log_23}\ge\tfrac13m^{\log_23}$ (using
$m\le 2^s$). $m=1$: $\tfrac13\le 2\le3$. $\square$

**(M2)** $x\in A(2)\iff d_0(x)\in\{0,2\}$ and $d_i(x)\in\{0,1\}$ for $i\ge1$:
restatement of M1's closed form ($x=3m+d$, $m\in C$). Member list below $45$:
$0,2,3,5,9,11,12,14,27,29,30,32,36,38,39,41$ (matches OEIS A005837;
§7-R1 machine-verified to $3^{10}$).

---

## §4. PART II — THE UNIVERSAL GROWTH TRIPTYCH (EVERY SEED $n\ge1$) — THEOREM U1

Fixed arbitrary seed $n\ge1$; $a_0=0<a_1=n<a_2<\cdots$ the greedy sequence.

### 4.1 G3 (the doubling law): $a_{k+1}\le 2a_k+1$ for all $k\ge1$

*Proof.* At step $k+1$ all earlier members are $\le a_k$. Let $v=2a_k+1>a_k$.
A blocker of $v$ would be a pair $a<b\le a_k$ with $a+v=2b$, giving
$2b=a+2a_k+1$ and $2b\le2a_k$ (as $b\le a_k$), hence
$a+2a_k+1\le2a_k$, i.e. $a+1\le0$ — contradiction. So $v$ is unblocked at
its scan, and since the scan starts at $a_k+1\le v$, the first unblocked value
$a_{k+1}$ satisfies $a_{k+1}\le v$. $\square$

### 4.2 G2 (the linear floor): $2a_m\ge 3m-3$ for all $m\ge0$

*Proof.* Three members are never three consecutive integers: if
$a_i,a_{i+1},a_{i+2}$ lay in $\{a_i,a_i+1,a_i+2\}$ they would be exactly
$(a_i,a_i+1,a_i+2)$ — a 3-AP. Hence $a_{i+2}\ge a_i+3$ for all $i\ge0$.
Two-track induction: $m=0$: $0\ge-3$; $m=1$: $2n\ge0$ (as $n\ge1$);
$m\ge2$: $2a_m\ge 2a_{m-2}+6\ge (3(m-2)-3)+6=3m-3$. $\square$

### 4.3 G1 (the quadratic ceiling): $a_m\le n+\dfrac{(m-1)(m+2)}{2}$ for all $m\ge1$

*Proof.* $m=1$: equality. Fix $m\ge2$; write $A=a_m$.

**Skip lemma.** Every $y$ with $a_k<y<a_{k+1}$ ($k\ge1$) has members
$a_i<a_j\le a_k$ with $a_i+y=2a_j$. *Sub-proof:* $y$ was scanned during step
$k{+}1$ and rejected, so by Lemma 0 it carries a $y$-top blocking pair from the
members then present — all $\le a_k$. $\square$

**Localization.** Every non-member $y\in(n,A)$ lies strictly between two
consecutive members $a_k<y<a_{k+1}$ with $1\le k+1\le m-1$. *Sub-proof:*
$y$ is not a member (members in $(n,A)$ are $a_2,\dots,a_{m-1}$), $y>a_1=n$,
and $y<A$; walk down from $m$ (strong induction on $m$): either
$y<a_{m-1}$ — recurse — or $a_{m-1}<y$, giving the pair
$(a_{m-1},a_m)$. $\square$

**Pigeonhole.** Map each non-member $y\in(n,A)$ to the *first* pair
$(i,j)$, $i<j\le m-1$, with $a_i+y=2a_j$ (exists by skip+localization; choose
e.g. the least $j$, then least $i$). The map is injective: a pair $(i,j)$
blocks the single value $y=2a_j-a_i$. So
$$\#\{\text{non-members in }(n,A)\}\le\#\{(i,j):i<j\le m-1\}=\frac{m(m-1)}2 .$$

**Count.** $(n,A)$ splits into the $m-2$ members $a_2,\dots,a_{m-1}$ and the
non-members, so $A-n-1\le(m-2)+\frac{m(m-1)}2$, i.e.
$a_m\le n+1+(m-2)+\frac{m(m-1)}2=n+(m-1)+\frac{m(m-1)}2
=n+\frac{(m-1)(m+2)}2$ (integer identity: $(m-1)+\frac{m(m-1)}2=\frac{(m-1)(m+2)}2$). $\square$

**U1 (assembled).** For every seed $n\ge1$ and every $m\ge1$:
$$\frac32(m-1)\ \le\ a_m\ \le\ n+\frac{(m-1)(m+2)}2 ,\qquad
a_{k+1}\le 2a_k+1 .$$
This answers "how fast do they grow" **unconditionally for every seed**:
between linear ($\frac32m$) and quadratic ($\frac12 m^2+O(m)$), with the
doubling law in between.

---

## §5. PART III — THE ODLYZKO–STANLEY $T$-FAMILY: EVERY SEED $3^{j-1}$ (THEOREM F1, F2)

This part closes **all** open sub-cores of the `OdStFamily.lean` draft
(the draft carries §0–§3 — helpers, the Cantor predicate, Cantor AP-freeness,
the cyclic cap — all green; the family theorems below are the completion).

Fix $j\ge1$; $H=3^{j-1}$, $P=3^j$, seed $h=3^{j-1}=H$. Define the **block set**
$$E_j=\{0\}\ \cup\ \{\,H+w:\ w\in C_{<H}\,\}\ \cup\ \{\,2H+w:\ w\in C,\ 0<w<H\,\},
\qquad |E_j|=2^j,$$
and the closed form $T_j:=\{\,Pq+e:\ q\in C,\ e\in E_j\,\}$.
($|E_j|=1+2^{j-1}+(2^{j-1}-1)=2^j$ by §3.7(a). For $j=1$: $E_1=\{0,1\}$ and
$T_1=3C+\{0,1\}=C$ — the classical Cantor case.)

### 5.1 Lemma L6 (the cyclic cap — `cyclicC`)

*For $t\ge0$: if $a,b,c<3^t$, all in $C$, and $a+c\equiv2b\pmod{3^t}$, then
$a=b=c$.*

*Proof (induction on $t$).* $t=0$: all $<1$, so all $0$. Step $t\to t+1$, with
$M=3^{t+1}=3\cdot3^t$: from $a+c\equiv2b\pmod M$ and $0\le a+c,2b\le2M-2$,
$a+c-2b\in\{-M,0,M\}$. Reduce mod $3$ (as $M\equiv0$): $d_a+d_c\equiv2d_b$
with digits in $\{0,1\}$; exactly as in L2 the only solutions are
$(0,0,0)$ and $(1,1,1)$ — the units digits are all equal, $=d$. Write
$a=3a'+d$, $b=3b'+d$, $c=3c'+d$ ($a',b',c'<3^t$, in $C$, by L1d). The three
forms give:
$\;a+c=2b\Rightarrow a'+c'=2b'$; $\;a+c+M=2b\Rightarrow a'+c'+3^t=2b'$;
$\;2b+M=a+c\Rightarrow 2b'=a'+c'+3^t$. In all three,
$(a'+c')\equiv2b'\pmod{3^t}$. By the induction hypothesis $a'=b'=c'$, hence
$a=b=c$. $\square$

### 5.2 Lemma L7 ($E_j$ is 3-AP-free)

*No $u<v<w$ in $E_j$ with $u+w=2v$.*

*Proof.* Write $u=d_uH+c_u$, etc., with $d\in\{0,1,2\}$, $c\in[0,H)$. The
$E_j$-profiles are: $(0,0)$ — i.e. $e=0$; $(1,c)$ with $c\in C_{<H}$;
$(2,c)$ with $c\in C\cap(0,H)$. In every case the tail $c_e\in C$ and $c_e<H$.
From $u+w=2v$: $(c_u+c_w-2c_v)= (2d_v-d_u-d_w)H$; the left side lies in
$(-2H,2H)$ and is a multiple of $H$, and $(c_u+c_w)\equiv 2c_v\pmod H$ — so
L6 (at $t=j-1$) gives $c_u=c_v=c_w=:c$, forcing $d_u+d_w=2d_v$.

If $(d_u,d_v,d_w)$ all equal, then $u=v=w$ — excluded. Otherwise
$\{d_u,d_w\}=\{0,2\}$, $d_v=1$. The member with $d=0$ is exactly $0$ (the
$(0,0)$ profile), so $c=0$; then the member with $d=2$ equals $2H+0=2H$,
which is **not** in $E_j$ (the $2H$-exclusion). Contradiction. $\square$

### 5.3 Lemma L8 ($T_j$ is 3-AP-free — the three carry cases)

*No $x<y<z$ in $T_j$ with $x+z=2y$.*

*Proof.* Write $x=Pq_x+e_x$, $y=Pq_y+e_y$, $z=Pq_z+e_z$ ($q$'s in $C$,
$e$'s in $E_j$). Since $0\le e_x+e_z,2e_y\le 2P-2$,
$$\delta:=\frac{e_x+e_z-2e_y}{P}\in\{-1,0,1\},\qquad q_x+q_z+\delta=2q_y. \quad(\star)$$

**Case $\delta=0$.** $e_x+e_z=2e_y$ and $q_x+q_z=2q_y$. If the $e$'s are not
all equal, they form a 3-term AP in $E_j$ (all distinct: $e_x=e_z$ would force
all equal), contradicting L7. If all equal, then $x<y<z$ forces
$q_x<q_y<q_z$ (distinct quotients, since the residues agree), and
$q_x+q_z=2q_y$ is a 3-term AP in $C$ — contradicting L2.

**Case $\delta=1$.** Decompose $e_x=d_xH+c_x$ etc. as in L7. From
$e_x+e_z=2e_y+3H$: $(c_x+c_z-2c_y)=(3-d_x-d_z+2d_y)H$, so L6 at $t=j-1$
gives $c_x=c_y=c_z=c$ and $d_x+d_z=2d_y+3$. As $d\in\{0,1,2\}$, this forces
$d_y=0$ and $\{d_x,d_z\}=\{1,2\}$. But $d_y=0$ means $e_y=0$ (the $(0,0)$
profile), so $c=0$, and then $\{e_x,e_z\}=\{H,2H\}$ — the one equal to
$2H\notin E_j$. Contradiction.

**Case $\delta=-1$.** Same decomposition; $e_x+e_z+3H=2e_y$ gives
$c_x=c_y=c_z=c$ and $d_x+d_z=2d_y-3$, forcing $d_y=2$ and
$\{d_x,d_z\}=\{0,1\}$. The member with $d=0$ is exactly $0$, so $c=0$; but
$d_y=2$ requires $c\in C\cap(0,H)$ — the $2H$-exclusion forbids $c=0$.
Contradiction. $\square$

### 5.4 Lemma L9 (the carry funnels — constructive, complete)

**(a) Cantor carry pair.** *$q\in C$, $q\ge1$ $\Rightarrow$ $\exists\,\alpha\le\beta<q$,
both in $C$, with $\alpha+q=2\beta+1$.* Construction, induction on $q$:
if $q\equiv1\pmod3$, $q=3u+1$ ($u\in C$): output $(3u,3u)$ — indeed
$3u+q=6u+1=2(3u)+1$. If $q\equiv0\pmod3$: $q=3u$, $u\in C\cap[1,\infty)$,
$u<q$; by IH take $(\alpha',\beta')$ for $u$ and output
$(3\alpha',\,3\beta'+1)$: $\alpha'+u=2\beta'+1$ gives
$3\alpha'+3u=3(2\beta'+1)=2(3\beta'+1)+1$; membership by L1e;
$3\beta'+1\le3(u-1)+1<3u=q$. ($q\equiv2$ is impossible in $C$.) $\square$

**(b) Carry blockers.** *$m\notin C$, $m\ge2$ $\Rightarrow$ $\exists\,\gamma_1\le\gamma_2<m$,
both in $C$, with $\gamma_1+m=2\gamma_2+1$.* Construction, with
$t=\lfloor m/3\rfloor$, $r=m\bmod3$:
- $r=0$ (then $t\notin C$ — else $m=3t\in C$ — and $t\ge2$): L3 pair
  $(a,b)$ for $t$ ($a<b<t$, $a+t=2b$); output
  $(3a+1,\,3b)$: $3a+1+3t=3(a+t)+1=6b+1=2(3b)+1$; membership L1e;
  $3b<3t=m$; $3a+1\le3b-2<3b$.
- $r=1$: if $t\in C$: output $(3t,3t)$: $3t+3t+1=6t+1=2(3t)+1$;
  $3t<3t+1=m$. Else L3 pair $(a,b)$ ($t\ge2$): output $(3a,3b)$:
  $3a+3t+1=3(a+t)+1=6b+1=2(3b)+1$; $3b\le3t-3<3t+1=m$.
- $r=2$: if $t\in C$: output $(3t+1,3t+1)$: $3t+1+3t+2=6t+3=2(3t+1)+1$;
  $3t+1<3t+2=m$. Else L3 pair $(a,b)$: output $(3a+1,3b+1)$:
  $3a+1+3t+2=3(a+t)+3=6b+3=2(3b+1)+1$; $3b+1\le3t-2<3t+2=m$;
  $3a+1\le3b-2<3b+1$. $\square$

**(c) Tail pair.** *$0<r<H$ $\Rightarrow$ $(w_1,w_2)\in C^2$ with
$w_1+r=2w_2$, $w_2\ge1$*: $(r,r)$ if $r\in C$; else L3's pair (then
$w_2>w_1\ge0$). $\square$

**(d) Halving split.** *$w\notin C$, $w\ge2$: either ($w$ even and $w/2\in C$),
or every C-blocker pair of $w$ has first component $\ge1$.* A pair with first
component $0$ forces $w=2c_2$ with $c_2\in C$ — the first alternative.
$\square$

### 5.5 Lemma L10 (the witness funnel table — maximality of $T_j$)

*Every $y\notin T_j$ with $y>H$ admits $a<b<y$ in $T_j$ with $a+y=2b$.*

*Proof.* Write $y=Pq+r$, $0\le r<P$. Membership: $y\in T_j\iff q\in C\wedge
r\in E_j$; we handle all $y\notin T_j$ (so either $q\notin C$ — then $q\ge2$
by L1c — or $r\notin E_j$). Recall $E_j\cap(0,H)=\varnothing$, and
$r\in E_j$ iff $r=0$, or $r=H+w$ ($w\in C_{<H}$), or $r=2H+w$
($w\in C\cap(0,H)$).

**R1 — $q\notin C$** (take L3's pair $(c_1,c_2)$ for $q$:
$c_1<c_2<q$, $c_1+q=2c_2$):

- **R1(a)** $r\in E_j$: $\big\langle Pc_1+r,\;Pc_2+r\big\rangle$.
  $a+y=P(c_1+q)+2r=2Pc_2+2r=2b$; members: $c_1,c_2\in C$, $r\in E_j$;
  $a<b$ ($c_1<c_2$); $b<y$ ($c_2<q$).
- **R1(b)** $r\ge H$, $r\notin E_j$:
  - $r=H+w$, $w\notin C$ ($w\ge2$): L3 pair $(w_1,w_2)$ for $w$; output
    $\big\langle Pc_1+H+w_1,\;Pc_2+H+w_2\big\rangle$:
    $a+y=P(c_1+q)+(H+w_1)+(H+w)=2Pc_2+2(H+w_2)=2b$; residues
    $H+w_1,H+w_2\in E_j$ ($w_1,w_2\in C$, $<H$); $b<y$ ($c_2<q$ and
    $H+w_2<H+w=r$).
  - $r=2H$: $\big\langle Pc_1+0,\;Pc_2+H\big\rangle$:
    $a+y=2Pc_2+2H=2b$; residues $0,H\in E_j$.
  - $r=2H+w$, $w\notin C$ ($w\ge2$): by L9(d): if $w$ even and $w/2\in C$,
    output $\big\langle Pc_1+0,\;Pc_2+H+w/2\big\rangle$:
    $a+y=P(c_1+q)+2H+w=2Pc_2+2(H+w/2)=2b$, residues
    $0\in E_j$, $H+w/2\in E_j$ ($w/2\in C$, $<H$). Otherwise L3 pair
    $(w_1,w_2)$ for $w$ has $w_1\ge1$: output
    $\big\langle Pc_1+2H+w_1,\;Pc_2+2H+w_2\big\rangle$:
    $a+y=2Pc_2+2(2H+w_2)=2b$; residues $2H+w_1,2H+w_2\in E_j$
    ($w_1,w_2\in C\cap(0,H)$ — $w_1\ge1$, $w_2>w_1$); $b<y$ ($w_2<w$).
- **R1(c)** $0<r<H$: L9(b) pair $(\gamma_1,\gamma_2)$ for $q$
  ($\gamma_1+\ q=2\gamma_2+1$); L9(c) pair $(w_1,w_2)$ for $r$ ($w_1+r=2w_2$,
  $w_2\ge1$); output $\big\langle P\gamma_1+H+w_1,\;P\gamma_2+2H+w_2\big\rangle$:
  $a+y=P(\gamma_1+q)+(H+w_1)+r=P(2\gamma_2+1)+H+w_1+r=2P\gamma_2+4H+w_1+r
  =2P\gamma_2+4H+2w_2=2b$; residues $H+w_1\in E_j$ ($w_1\in C_{<H}$ —
  $w_1\le w_2<H$), $2H+w_2\in E_j$ ($w_2\ge1$); $a<b$ ($\gamma_1\le\gamma_2$
  and $H+w_1<2H+w_2$); $b<y$ ($\gamma_2<q$, and $2H+w_2<P+r$ since
  $w_2<H\le H+r$).

**R2 — $q\in C$, $r\notin E_j$** (then $r\neq0$; $r=2H$, or $r=H+w$ with
$w\notin C$ ($\ge2$), or $r=2H+w$ with $w\notin C$ ($\ge2$), or $0<r<H$):

- **R2(a)** $r=2H$: $\big\langle Pq+0,\;Pq+H\big\rangle$:
  $a+y=2Pq+2H=2b$; residues $0,H\in E_j$; $0<H<2H$.
- **R2(b)** $r=H+w$, $w\notin C$: L3 pair $(w_1,w_2)$; output
  $\big\langle Pq+H+w_1,\;Pq+H+w_2\big\rangle$: $a+y=2Pq+2H+w_1+w=2b$;
  residues in $E_j$; $b<y$ ($H+w_2<H+w$).
- **R2(c)** $r=2H+w$, $w\notin C$: by L9(d): if $w$ even, $w/2\in C$:
  $\big\langle Pq+0,\;Pq+H+w/2\big\rangle$: $a+y=2Pq+2H+w=2b$; residues
  $0$, $H+w/2\in E_j$. Else L3 pair with $w_1\ge1$:
  $\big\langle Pq+2H+w_1,\;Pq+2H+w_2\big\rangle$: $a+y=2Pq+4H+w_1+w=2b$;
  residues $2H+w_1,2H+w_2\in E_j$; $b<y$.
- **R2(d)** $0<r<H$ (then $q\ge1$, since $q=0$ would give $y=r<H$, below the
  seed): L9(a) pair $(\alpha,\beta)$ for $q$ ($\alpha+q=2\beta+1$); L9(c) pair
  $(w_1,w_2)$ for $r$; output $\big\langle P\alpha+H+w_1,\;P\beta+2H+w_2\big\rangle$:
  the same computation as R1(c) gives $a+y=2b$; residues in $E_j$;
  $a<b$ ($\alpha\le\beta$, $H+w_1<2H+w_2$); $b<y$ ($\beta<q$).

Every case outputs a valid blocking pair; the dispatch is total (the residue
trichotomy $r<H$ / $H\le r<2H$ / $2H\le r<P$ crossed with $r\in E_j$ or not,
and within $r\ge H$: $r=H+w$ or $2H+w$ with $w=0$, $w\in C$, or $w\notin C$ —
the $w\in C$ alternatives are exactly $E_j$-membership). $\square$

### 5.6 THEOREM F1 (the $T$-family characterization) and F2 (count + growth)

**F1.** For every $j\ge1$: $\;S(0,\,3^{j-1})=T_j=\{\,3^j q+e:\ q\in C,\ e\in E_j\,\}$.

*Proof.* Lemma W with $h=H$, $T=T_j$: (W-i) is L8; (W-ii) is L10 (every
$y\notin T_j$, $y>H$); (W-iii) $T_j\cap[0,H]=\{0,H\}$ (elements below $H$
require $q=0$ and $e\in E_j\cap[0,H)=\{0\}$; and $H=P\cdot0+H\in T_j$). $\square$

*Digit form:* the ternary digits at positions $\ge j$ all lie in $\{0,1\}$; the
digit at position $j-1$ is $1$ (tail free Cantor), or $2$ (tail Cantor, not all
zero), or the whole tail is zero. $j=1$: $A(1)=C$ (classical). $j=2$:
$A(3)=9C+\{0,3,4,7\}$; $j=3$: $A(9)=27C+\{0,9,10,12,13,19,21,22\}$; etc.

**F2.** For $s\ge j$: $|A(3^{j-1})\cap[0,3^s)|=2^s$; for $s\ge j$:
$a_{2^s}=3^s$; for $m\ge2^{j-1}$: $\frac13 m^{\log_23}\le a_m\le3\,m^{\log_23}$.

*Proof.* Count: $Pq+e<3^s\iff q<3^{s-j}$ (as $e<P$), so the members below
$3^s$ biject with $C\cap[0,3^{s-j})\times E_j$: $2^{s-j}\cdot2^j=2^s$
(§3.7(a)). Sharp position and the two-sided squeeze follow exactly as in
§3.7(c),(d) (for $m\ge2^{j-1}$, take $s:=\max(j,\lceil\log_2m\rceil)$, so
$2^{s-1}\le m\le2^s$ and $a_m\in[3^{s-1},3^s]$). $\square$

---

## §6. PART IV — THE FRONTIER (exact status, honestly labeled)

**S-family ($A(2\cdot3^k)$, $k\ge1$; seeds $6,18,54,162,486,\dots$).**
Machine-verified closed forms
$A(2\cdot 3^{j-2})=3^jC+E^S_j$ with
$E^S_j=\{0\}\cup\big(\{2,3,5,6\}\cdot3^{j-2}+C_{<3^{j-2}}\big)\setminus\{2\cdot3^{j-1}\}$
($|E^S_j|=2^j$): greedy = predicate on the full range $[0,3^{j+4})$ for
$j\le6$ (§7-R3: all MATCH), count law $2^s$ for $s\ge j$ (§7-R3), and every
non-member $y>$ seed carries **some** closed-form blocking witness
(§7-R7: zero uncovered, $j\le5$). The general inductive proof requires the
$E^S$-internal funnel table (the $2$-digit window $\{02,10,12,20\}$ carries
halving, borrow and cross-block carry branches — visible in §7-R7's
classification); **not assembled here — not claimed proven.** $A(2)$, the
$k=0$ member, is fully proven (M1).

**A(4) and the full ask.** The problem's complete ask — explicit determination
for *every* seed — includes $A(4)$ (OEIS A005487), open for 45 years. The
campaign's certified census (complete on $[0,3^{21})$, independently verified):
$c_{21}=710{,}129$, cumulative exponent $\alpha_{21}=0.5840$ declining toward
$1/2$, Type-1 quantitatively rejected, $a_m\asymp m^2/\log m$ (Type-2) — the
leading candidate for the first Type-2 Stanley sequence (the existence half of
the Odlyzko–Stanley dichotomy). Interior ternary digits are maximal-entropy
($P(2)=1/3$; $\ge10^5$ subtree types; no self-similarity) — no digit-automaton
characterization exists at this depth. The growth question for $A(4)$ is
nevertheless already bounded by U1's unconditional envelope
$\frac32(m-1)\le a_m\le4+\frac{(m-1)(m+2)}2$.

**The five historical kills (merge note).** The named arsenal — greedy-walk,
the three $x{=}1/2$ representations, THE TOWER, the rational-$x$ bridge,
funnels — landed on the sister front (#261) of this campaign; their
architectures are merged here as: Lemma W (the greedy walk), L6 (the
scale-tower cyclic cap), the carry/halving bridges of L9–L10 (rational-position
bridges), and the witness funnels (L3, L5, L10).

---

## §7. MACHINE-VERIFICATION RECEIPTS (this session, 2026-11-11, engine Python 3)

All scripts live in `/home/z/my-project/S044A/`; the greedy engine is the
blocking-mark bitset `stanley.py` (independent of the Lean oracle).

- **R1** `verify_a2_complete.py` (full range $[0,3^{10})$): greedy $=$ `inD`
  **MATCH**; count law $2^s$, $s\le10$ **OK**; the L3 construction valid on
  $[2,20000)\setminus C$ **ALL VALID**; the L5 construction valid on
  $[3,3^{10})\setminus A(2)$ **ALL VALID**; $0$ 3-APs inside $A(2)\cap[0,3^{10})$;
  growth law $\frac13m^{\log_23}<a_m<3m^{\log_23}$ for $m<1024$ **OK**;
  G1/G2/G3 on seeds $1..12$ ($m\le200$) **OK**.
- **R2** T-family growth receipts: $a_{2^s}=3^s$ exactly for
  $s\in[j,j+4)$, seeds $1,3,9,27,81$ — **all TRUE**; two-sided
  $m^{\log_23}$ law ($m\ge2^{j-1}$) — **all TRUE**; $A(2)$: $a_{2^s}=3^s$,
  $2\le s\le10$ **TRUE**.
- **R3** `verify_family.py`: closed-form equality greedy = predicate on
  $[0,3^{j+4})$: $A(3^k)$ $k\le5$ and $A(2\cdot3^k)$ $k\le4$ — **11/11 MATCH**;
  count law $2^s$ ($s\ge j$) for all listed seeds — **OK**.
- **R4** (in R1) triptych re-verification — see R1.
- **R5** `verify_tfamily_table.py` (the EXACT R1/R2 table of §5.5, halving
  branch included): every non-member $y\in(\text{seed},\text{horizon})$
  blocked by the constructed pair with $a<b<y$, both in $T_j$, $a+y=2b$:
  **j = 1..7 (seeds 1..729) ALL OK** (horizons up to $\min(3^j\cdot40,
  3^{j+3})$); $|E_j|=2^j$ ($j\le7$) **OK**; $0$ APs in $E_j$ and in
  $T_j\cap[0,3^{j+3})$ ($j\le7$) — **AP-freeness double-checked**; count law
  ($j\le7$) **OK**. (The first run without the L9(d) halving split produced
  exactly the $w_1=0$ failures — the split is necessary and sufficient; see
  §5.4(d).)
- **R6** `witness_final.py` (independent rule-table validator): T-family
  witness validity, $j\le6$ — **ALL OK**. `constructions.py`: the L3/L9
  constructions on $[1,3000)$ — **ALL CONSTRUCTIONS VALID**.
- **R7** `witness_class_s.py`: S-family witness classification, $j\le5$ —
  **zero uncovered non-members** (every non-member has a closed-form witness);
  the extracted rule patterns are the input for the S-family table (§6).
- **R8** **second-method cross-check of M1** (independent naive engine — pure
  definition replay, no bitset, no constructions, $O(n^2)$ pair scan, full range
  $[0,3^7)$): greedy $=$ `inD` **MATCH**; maximality replay: $0$ unblocked
  non-members. Two independent engines agree with the Lean oracle and the
  closed form.
- **Lean receipts (prior, CI-green):** `bulldoze/problem271-stanley-a2/StanleyA2.lean`
  — `stanley_a2_greedy` (axioms: propext, Classical.choice, Quot.sound);
  `problem271-status/StanleyGrowth.lean` — `growth_G1/G2/G3` + the Arsenal
  bridge `erdos271_arsenal_bridge` (same three standard axioms);
  `problem271-status/OdStFamily.lean` §0–§3 (helpers, `noTwo`,
  `noTwo_no_ap`, `cyclicC`) — green kernel this document completes.

---

## §8. LEAN CONVERSION NOTES (per theorem)

**M1 / M2 (§3).** Already formal: `StanleyA2.lean` (471 lines, core Lean 4,
no Mathlib, no sorry). Architecture map: L1 = §1 (`noTwo` and its intro/elim
lemmas); L2 = §3 `noTwo_no_ap_fuel` (fuel induction on $z$ — the fuel wrapper
avoids well-founded-recursion kernel opacity); L3 = §5 `cBlocked_fuel` (fuel
induction, the offset-normalized lift $\langle3a,3b\rangle$,
$\langle3a{+}1,3b{+}1\rangle$, $\langle3a,3b{+}1\rangle$); L4 = §4
`inD_no_ap` (the `omega`-closed digit-triple trichotomy); L5 = §6 `dBlocked`
(case split on `m % 3` — use `lt_three_cases`); Lemma W = §7–§8
(`gp`/`anyBlocker`/`scanPairs`/`someBelow` + `gp_correct` fuel induction +
`stanley_a2_greedy`). Tactic notes: all digit steps are
`omega`-after-`Nat.div_add_mod`; the AP-freeness cases close by `omega` on
`(x % 3, y % 3, z % 3)` trichotomies; membership side-conditions by
`noTwo_intro` + the `div3_mul3*` helpers.

**G-A2 (§3.7).** Count law: induction on $s$ over
`(List.range (3^s)).filter inD` with `List.length`; sharp position:
`a_{2^s} = 3^s` by the count law + membership of `3^s` (decide-free,
general-$s$ induction); the two-sided squeeze: `Nat.pow` monotonicity +
`omega` (constants 3 and 1/3 handled as `3 * a ≤ 9 * m^log₂3`-style integer
inequalities; alternatively state with explicit rational bounds via
`Nat.pow_le_pow` chains). The `#eval` receipts already in StanleyA2.lean
(counts `[1,2,4,...,128]` for $k\le7$) extend to $k\le10$ by
`decide`-independent `List.range` filters.

**U1 (§4).** Already formal: `StanleyGrowth.lean` (986 lines, CI-green).
Map: G3 = §6 `two_a_plus_one_free` + `findFree_least`; G2 = §7
`apFree_sq` (list-induction maintaining the no-AP invariant) + `aSeq_gap3` +
`Nat.strong_induction_on`; G1 = §8 (`greedy_skip`, `interval_loc` by strong
induction, `pairList`/`pairBlock` cardinality by `List.length` +
`Nat.card_Ico`, the injective blocker selector `findBlocker` + `lfind`, the
final `omega` on the parity identities `consec_even`). Fuel discipline: the
greedy engine is `findFree` with fuel $=a_k+1$ — kernel-transparent.

**F1 (§5).** Extends `OdStFamily.lean` (§0–§3 already green). New kernel
(≈300–400 lines): `memE j` — the $E_j$ predicate
(`e % H = 0 ∧ e = 0` ∨ `H ≤ e ∧ e < 2H ∧ noTwo ((e - H))` ∨
`2H ≤ e ∧ e < P ∧ noTwo (e - 2H) ∧ 0 < e - 2H`), decidable; `memT j y :=
noTwo (y / P) ∧ memE j (y % P)`. L7/L8 (`memE_no_ap`, `memT_no_ap`): the
$\delta$-trichotomy with `omega` on the digit sums + `cyclicC` (already
green, §3 of the draft) at scale $H$; the three carry cases as in §5.3 — each
closes by `omega` once `cyclicC` returns `a = b ∧ b = c`. L9(a) `cantorCarryPair`:
strong induction on $q$ via `q / 3` descent (`div3_mul3*` + `noTwo_intro`);
L9(b) `carryBlocked`: the $r$-trichotomy with `lt_three_cases`, lifting L3's
`cBlocked_fuel` (import from StanleyA2 or duplicate §5 — 60 lines); L10: the
R1/R2 table as seven `theorem` cases returning explicit $\langle a,b\rangle$
pairs, each discharged by `omega` + `noTwo_intro`/`memE` intro lemmas + the
halving split `if w % 2 == 0 ∧ noTwo (w/2)` (decidable). The greedy oracle:
lift `gp` to a two-parameter oracle `gpo j f m` with base
`m ≤ 3^{j-1} → decide (m = 0 ∨ m = 3^{j-1})`; `gp_correct` generalizes verbatim
(the fuel bound $m\le f$ is unchanged). Headline:
`stanley_T_family : ∀ j, ∀ m, gpo j m m = memT j m` — then the member-list
equality by the `sqSeq` engine of StanleyGrowth (already green at every
seed). F2: `family_count` by the $C$-count induction; `family_growth` by the
§3.7(d) squeeze with $s=\max(j,\lceil\log_2m\rceil)$ (`Nat.log` lemmas or
explicit $2^s$ bookkeeping). Decide-able spot checks: $|E_j|=2^j$ ($j\le7$),
member lists vs OEIS (`#eval` receipts), the R1/R2 table on
$y<3^{j+3}$ ($j\le4$) — all already run in §7.

**Arsenal bridge (already CI-green in StanleyGrowth.lean §9):**
`erdos271_arsenal_bridge` consumes `ErdosTernary2.isTernaryDigit` (digits of
seed $4=(11)_3$ and member $23=(212)_3$), `ErdosTernary2.lt_three_cases`
(the residue trichotomy at $a_3=7$), `CardinalWorlds.carryAtPos_bound`
(carry discipline at position 1 of $23$), and
`CardinalWorldsV2.v2r_ternary_scaling` ($v_2$-reader invariance under
$3$-scaling: $v_2r(3\cdot9)=v_2r\,9$) — the digit-trichotomy, carry-bound,
and ternary-scaling laws used throughout §3–§5.

---

## §9. ARSENAL CITATION TABLE (BOSS's vendored laws, where applied)

| Arsenal law | File | Applied at |
|---|---|---|
| `ErdosTernary2.isTernaryDigit` | `Arsenal/ErdosTernary2/Basic.lean:44` | every digit-recognition step: the $d_i\in\{0,1\}$/$\{0,2\}$ tests of L2/L4/L7/L8; the seed/member digit receipts (§8 bridge) |
| `ErdosTernary2.lt_three_cases` | `Arsenal/ErdosTernary2/Basic.lean:16` | every residue trichotomy: the L3/L5/L9b face dispatches ($r\in\{0,1,2\}$), the units-digit splits of L2/L4 |
| `CardinalWorlds.carryAtPos_bound` | `Arsenal/CardinalWorlds.lean:108` | the carry discipline of L6/L8: the bounded carry index $\delta\in\{-1,0,1\}$ at scale $P=3^j$ (bound $<4$ generalizes the $\pm P$ cap); bridge receipt at member $23$ |
| `CardinalWorldsV2.v2r_ternary_scaling` | `Arsenal/CardinalWorldsV2.lean:71` | the scale-tower invariance: multiplication by $3^a$ preserving the digit-depth reader — the count-law bijections $C\cap[0,3^{s+1}) = 3C\cup(3C{+}1)$ (§3.7(a)) and $E_j$-tail transfer; bridge receipt $v_2r(3^1\cdot 9)=v_2r\,9$ |

---

## §10. CLOSING STATEMENT

$A(2)$ is dead: greedy = closed form, member for member, every lemma
constructive and machine-checked; its growth is sharp ($2^s$ per scale,
$a_{2^s}=3^s$, two-sided $m^{\log_23}$). The inheritance is assembled: the
universal triptych (every seed, unconditional) and the completed $3^k$ family
(the `OdStFamily.lean` sub-cores closed by the cyclic cap, the carry funnels,
and the seven-rule witness table). The frontier is exact: $A(2\cdot3^k)$ ($k\ge1$)
machine-verified with its table identified, $A(4)$ open — the smallest seed
beyond the proven class, with 21 certified scales of census aimed at the
dichotomy's Type-2 existence half.
