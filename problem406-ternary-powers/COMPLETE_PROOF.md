# ERDŐS #406 — THE COMPLETE PROOF DOCUMENT (THE TERNARY CENSUS ASSEMBLY)

**Deliverable S046-W14.** Target: Erdős problem **#406** of the
teorth/erdosproblems corpus (erdosproblems.com/406) — the anchor summit,
BOSS's own front, admitted to the army by the S042 full-proof-campaign
order. Certified spine: **Kernel 38**
(`problem406-ternary-powers/Erdos406Ternary.lean`, KILL #40, GitHub Actions
run **42912135608 GREEN**, the 4-round compile war
`dba7d1bc → 7b520b5 → 3a36b06 → 9046b593` with root causes 8 → 4 → 1 → 0)
and **battery406.py** (dual-method, re-run GREEN this session, §9). This
document assembles the complete structure: the corpus statement verbatim
above the proof, every unconditional theorem with its FULL mathematical
proof, the standing constraint set on every hypothetical large solution,
the arsenal citations, and the verification receipts.

---

## §0. THE PROBLEM — VERBATIM (above the proof, BOSS's law)

Quoted verbatim from the corpus statement of problem #406
(erdosproblems.com/406), as it is quoted verbatim in the Kernel 38 header
(`Erdos406Ternary.lean` §PREAMBLE) and in the README kill registry
(KILL #40):

> Is it true that there are only finitely many powers of $2$ which have only
> the digits $0$ and $1$ when written in base $3$?

Corpus addendum (the empirical record attached to the statement):

> The only examples seem to be $1$, $4=1+3$, and $256=1+3+9+243$.

The corpus therefore asks the **finiteness YES/NO question** for the set

$$S = \{\,2^k : \text{the base-}3\ \text{representation of } 2^k
\text{ uses only the digits } 0 \text{ and } 1\,\},$$

with the conjectural complete classification $S = \{1, 4, 256\}$ attached as
the corpus's own empirical expectation.

**The reading (made exact by the Semantic Law, §3).** A natural number has
only the digits $0$ and $1$ in base $3$ **iff** it is a finite sum of
**distinct** powers of $3$ (each ternary digit $\varepsilon_i \in \{0,1\}$
selects whether $3^i$ appears; "digit $\le 1$" is exactly "each power used
at most once"). Throughout, "$0/1$-ternary-digit number" = "sum of distinct
powers of $3$" = "value of a $0/1$ digit list", the three readings
interchangeable by §3.

---

## §1. THE COMPLETENESS VERDICT (surgical and honest)

| Corpus content | Status in this document |
|---|---|
| Complete classification below $2^{500}$ ($k \le 500$): $S \cap [1, 2^{500}] = \{1, 4, 256\}$ | **PROVED, UNCONDITIONAL** (§6: Kernel 38 census + §3 semantic law; certified exhaustive) |
| Odd-exponent exclusion — every odd $k$, no bound (an infinite class of exponents) | **PROVED, UNCONDITIONAL** (§4, Theorem B) |
| The mod-8 digit-count budget — every $k \ge 3$, no bound | **PROVED, UNCONDITIONAL** (§5, Theorem C) |
| The semantic law (fuel checker $\iff$ distinct-powers-of-3 representation) | **PROVED, UNCONDITIONAL** (§3, Theorem A) |
| Arsenal bridge at the witnesses (isTernaryDigit, carryAtPos_bound, v2r_ternary_scaling) | **PROVED** (§8, kernel receipts) |
| **The all-$k$ finiteness verdict — the corpus's YES/NO at unbounded $k$** | **OPEN CORE REMAINS — the Stewart-class remainder** (§7) |

**THE SINGLE REMAINING COMPONENT (named exactly): THE ALL-$k$ FINITENESS
CORE** — proving that only finitely many powers of $2$ are $0/1$-ternary
numbers, i.e. that no solution (or only boundedly many) exists beyond the
certified census range $k > 500$. This is not an engine gap and not a
dressing error: the classical digit-distribution theory (Senge–Straus and
the Stewart digit-count lower-bound theory for multiplicatively independent
bases) controls the **number** of nonzero digits, while the corpus's
condition controls the digit **values**. A power of two whose ternary
expansion is $0/1$-digit may carry arbitrarily many nonzero digits, all
equal to $1$, so the count machinery is silent (§7.3). What would close the
core is control of the residue tower $2^k \bmod 3^n$ at $n \sim 0.631k$ —
a Mahler/equidistribution-class input; the campaign registry has the
research front mapped (residue towers; the $2.482^n$ entropy row — WORKLOG
#406 registry lines, README §NEXT). Everything the corpus statement
contains below the all-$k$ core is delivered complete in §3–§6.

---

## §2. NOTATION, AND THE ENCODING

**Positions and digit lists.** Ternary position $i$ carries weight $3^i$;
position $0$ is the least significant (units). A **0/1-digit list** is
$b = (\varepsilon_0, \varepsilon_1, \ldots, \varepsilon_{m-1})$ with each
$\varepsilon_i \in \{0, 1\}$ (in Lean: a `List Bool`, head = position 0;
`true` = the digit 1).

**The fold value** (kernel `tfold`):
$$\mathrm{tfold}(b) = \sum_{i=0}^{m-1} \varepsilon_i\,3^i, \qquad
\mathrm{tfold}(\varnothing) = 0, \qquad
\mathrm{tfold}(\varepsilon :: b') = 3\,\mathrm{tfold}(b') + \varepsilon.$$
"Sum of distinct powers of $3$" = $\exists b$ with $n = \mathrm{tfold}(b)$
(the support $I = \{i : \varepsilon_i = 1\}$ is a finite set of positions,
distinctness automatic).

**The fuel-indexed digit checker** (kernel `tern01`):
$$\mathrm{tern}_{01}(0, n) = \textsf{true} \quad (\text{fuel exhausted —
vacuous, sound only under } n < 3^0),$$
$$\mathrm{tern}_{01}(f{+}1,\, n) = (n = 0) \;\lor\; \bigl(n \bmod 3 \le 1
\;\wedge\; \mathrm{tern}_{01}(f,\, n \div 3)\bigr).$$

**The position-parity counts** (kernel `altsum`):
$\mathrm{altsum}(b) = (E(b), O(b))$ with $E(b) = \#\{i \text{ even} :
\varepsilon_i = 1\}$, $O(b) = \#\{i \text{ odd} : \varepsilon_i = 1\}$;
recursion $\mathrm{altsum}(\varnothing) = (0,0)$, and
$\mathrm{altsum}(\varepsilon :: b') = (O(b') + \varepsilon,\; E(b'))$
— the parity flip: prepending a digit shifts every old position up by one.

**Division-algorithm facts** (standard; every one is `omega`-certified in
the kernel): for $n \ge 0$, $n = 3\,(n \div 3) + (n \bmod 3)$ and
$n \bmod 3 < 3$; for $t \ge 0$ and $\varepsilon \in \{0,1\}$,
$(3t + \varepsilon) \div 3 = t$ and $(3t + \varepsilon) \bmod 3 =
\varepsilon$; and $v < 3^{f+1} \Rightarrow v \div 3 < 3^f$.

**Fuel discipline (the load-bearing bound).** The checker is sound only
below $3^{\text{fuel}}$: at fuel $0$ it accepts everything. Every
application in this document uses fuel $700$ together with the
kernel-certified bound $2^{500} < 3^{700}$ (kernel receipt
`two_pow_500_lt`), so every $2^k$ with $k \le 500$ lies strictly below
$3^{700}$ and the checker's verdict is exact. The ternary length of
$2^{500}$ is $316$ digits ($3^{315} < 2^{500} < 3^{316}$; battery receipt
§9.E), so fuel $700 = 316$ scanned digits $+ 384$ spare.

---

## §3. THE SEMANTIC LAW (the checker IS the representation predicate)

### Theorem A (`tern01_iff_tfold`) — FULL PROOF

**Statement.** For all $f \ge 0$ and all $n < 3^f$:
$$\mathrm{tern}_{01}(f, n) = \textsf{true}
\;\;\iff\;\; \exists\, b:\; n = \mathrm{tfold}(b).$$

**Proof.** Two inductions.

**(⇒) [`tfold_of_tern01`] — induction on $f$.**

*$f = 0$:* $n < 3^0 = 1$ forces $n = 0 = \mathrm{tfold}(\varnothing)$.

*$f \to f+1$:* let $n < 3^{f+1}$ with $\mathrm{tern}_{01}(f{+}1, n) =
\textsf{true}$. If $n = 0$, take $b = \varnothing$. Otherwise the
checker's disjunction forces
$$n \bmod 3 \le 1 \quad\wedge\quad \mathrm{tern}_{01}(f,\, n \div 3) =
\textsf{true}.$$
Set $d := n \bmod 3$. **The Arsenal trichotomy applies here**
(`ErdosTernary2.lt_three_cases`: every natural $< 3$ is $0$, $1$, or $2$):
$d < 3$, so $d \in \{0, 1, 2\}$, and $d \le 1$ kills $d = 2$. Also
$n \div 3 < 3^f$ (from $n < 3^{f+1} = 3 \cdot 3^f$, §2), so the induction
hypothesis gives $b'$ with $n \div 3 = \mathrm{tfold}(b')$. Then by the
division identity $n = 3\,(n \div 3) + d$:
- $d = 0$: $n = 3\,\mathrm{tfold}(b') + 0 = \mathrm{tfold}(0 :: b')$;
- $d = 1$: $n = 3\,\mathrm{tfold}(b') + 1 = \mathrm{tfold}(1 :: b')$.

Either way $n = \mathrm{tfold}(b)$ for $b = d :: b'$. ∎

**(⇐) [`tern01_of_tfold`] — induction on the list $b$.**

*$b = \varnothing$:* $\mathrm{tfold} = 0$, and the checker accepts $0$ at
any fuel (the first disjunct $n = 0$; kernel `tern01_zero`).

*$b = \varepsilon :: b'$:* write $v = \mathrm{tfold}(\varepsilon :: b') =
3\,\mathrm{tfold}(b') + \varepsilon$, and let $v < 3^f$.

- If $f = 0$: $v < 1$ forces $v = 0$; the checker at fuel $0$ accepts by
  definition.
- $f = f' + 1$: if $v = 0$, the first disjunct accepts. Otherwise:
  $v \bmod 3 = \varepsilon \le 1$ (since $(3t + \varepsilon) \bmod 3 =
  \varepsilon$, §2) and $v \div 3 = \mathrm{tfold}(b')$ (since
  $(3t + \varepsilon) \div 3 = t$, §2). Moreover
  $3\,\mathrm{tfold}(b') \le v < 3^{f'+1} = 3 \cdot 3^{f'}$ gives
  $\mathrm{tfold}(b') < 3^{f'}$, so the induction hypothesis yields
  $\mathrm{tern}_{01}(f', \mathrm{tfold}(b')) = \textsf{true}$. The
  conjunction holds, the second disjunct accepts, and
  $\mathrm{tern}_{01}(f{+}1, v) = \textsf{true}$. ∎

**Theorem A follows by gluing the two inductions.** ∎

### Lemma A2 (the plain-language reading is exact)

For every $b$: the base-3 digits of $n = \mathrm{tfold}(b)$ are exactly the
$\varepsilon_i$ (dropping leading zeros), hence all $\le 1$; conversely,
every $n$ whose base-3 digits are all $\le 1$ equals $\mathrm{tfold}(b)$
with $\varepsilon$ = its digit list.

*Proof.* Induction on $b$ with the §2 division facts, exactly the (⇐)
induction run in reverse: extracting the units digit of
$3\,\mathrm{tfold}(b') + \varepsilon$ returns $\varepsilon$ and the
quotient $\mathrm{tfold}(b')$, whose digits are the shifted tail by the
induction hypothesis; the recursion terminates at $\mathrm{tfold} =
0$. The converse is Theorem A (⇒) — the checker scans precisely the
base-3 digits below $3^{\text{fuel}}$. ∎

**Corollary A1.** For $n < 3^f$: $\mathrm{tern}_{01}(f, n) = \textsf{true}$
iff the base-3 digits of $n$ are all $\le 1$ iff $n$ is a sum of distinct
powers of $3$. (The corpus's plain-language condition is interchangeable
with the fold representation everywhere below.)

---

## §4. THE MOD-3 PARITY LAW (GENERAL — every odd exponent, no bound)

### Theorem B (`erdos406_odd_excluded`) — FULL PROOF

**Statement.** For every $j \ge 0$ there is **no** 0/1-digit list $b$ with
$$2^{2j+1} = \mathrm{tfold}(b).$$
Equivalently: every solution exponent $k$ (if any exists at any size) is
**even**. This excludes an infinite class of exponents, unconditionally,
with no bound on $k$.

**Lemma B1 (`tfold_mod3_le_one`).** $\mathrm{tfold}(b) \bmod 3 \in
\{0, 1\}$ for every $b$.

*Proof.* Induction on $b$. $\varnothing$: $0 \bmod 3 = 0$. $\varepsilon
:: b'$: $\mathrm{tfold} = 3\,\mathrm{tfold}(b') + \varepsilon \equiv
\varepsilon \pmod 3 \in \{0, 1\}$. ∎

**Lemma B2 (`pow4_mod3`).** $4^j \equiv 1 \pmod 3$ for every $j$.

*Proof.* Induction on $j$: $4^0 = 1$; $4^{j+1} = 4 \cdot 4^j \equiv 1
\cdot 1 = 1 \pmod 3$ since $4 \equiv 1 \pmod 3$. ∎

**Theorem B.** Suppose $2^{2j+1} = \mathrm{tfold}(b)$. The right side is
$\equiv 0$ or $1 \pmod 3$ (Lemma B1). The left side is $2 \cdot 4^j$
(kernel `pow2_odd_mod3`: $2^{2j+1} = 2 \cdot (2^2)^j$), which is $\equiv
2 \cdot 1 = 2 \pmod 3$ (Lemma B2). Since $2 \not\equiv 0, 1 \pmod 3$,
contradiction. ∎

**Sharpness and refinement.** The law is exactly the odd-exponent
exclusion: the three surviving witnesses $k = 0, 2, 8$ are even, and the
law's boundary is sharp. Since $2 \equiv -1 \pmod 3$, one has $2^k \equiv
(-1)^k \pmod 3$: for even $k$, $2^k \equiv 1 \pmod 3$, and Lemma B1 forces
the **units ternary digit of every solution to be exactly $\varepsilon_0 =
1$** (a 0/1-digit number $\equiv \varepsilon_0 \pmod 3$). Every solution,
at any size, ends its ternary expansion with the digit $1$.

---

## §5. THE MOD-8 BUDGET LAW (GENERAL — every $k \ge 3$, no bound)

### Theorem C (`erdos406_mod8_budget`) — FULL PROOF

**Statement.** For every 0/1-digit list $b$ and every $k \ge 3$ with
$2^k = \mathrm{tfold}(b)$:
$$E(b) + 3\,O(b) \equiv 0 \pmod 8,$$
$E(b)$/$O(b)$ the counts of 1-digits at even/odd ternary positions (§2).

**Lemma C1 (`tfold_mod8`).** $\mathrm{tfold}(b) \equiv E(b) + 3\,O(b)
\pmod 8$ for every $b$.

*Proof.* Induction on $b$, with the parity flip of §2.
$\varnothing$: $0 \equiv 0 + 3 \cdot 0 \pmod 8$. Step $\varepsilon :: b'$:
$\mathrm{tfold}(\varepsilon :: b') = 3\,\mathrm{tfold}(b') +
\varepsilon$, and $\mathrm{altsum}(\varepsilon :: b') = (O' +
\varepsilon,\, E')$ with $E' = E(b')$, $O' = O(b')$. By the induction
hypothesis $\mathrm{tfold}(b') \equiv E' + 3O' \pmod 8$, hence
$$\mathrm{tfold}(\varepsilon :: b') \equiv 3(E' + 3O') + \varepsilon
= 3E' + 9O' + \varepsilon \equiv 3E' + O' + \varepsilon \pmod 8$$
(using $9 \equiv 1 \pmod 8$)
$$= (O' + \varepsilon) + 3E' = E(\varepsilon :: b') + 3\,O(\varepsilon
:: b'). \;\blacksquare$$

**Lemma C2 (`pow2_mod8`).** $k \ge 3 \Rightarrow 2^k \equiv 0 \pmod 8$.

*Proof.* $2^k = 2^{k-3} \cdot 2^3 = 2^{k-3} \cdot 8$; the factor $8$
carries the congruence. ∎

**Theorem C.** $E(b) + 3\,O(b) \equiv \mathrm{tfold}(b) = 2^k \equiv 0
\pmod 8$ (Lemmas C1, C2, and the hypothesis). ∎

**Sharpness (the $k \ge 3$ boundary is load-bearing).** At $k = 2$ the
solution $4 = 3^0 + 3^1$ has $E = O = 1$, so $E + 3O = 4 \not\equiv 0
\pmod 8$ — the budget genuinely fails exactly where $2^2 = 4 \not\equiv 0
\pmod 8$. At $k = 0$: $E = 1, O = 0$, $E + 3O = 1$. The budget binds
precisely on the range $8 \mid 2^k$.

### Corollary C3 (the digit-count floor — a standing structural constraint)

Every solution with $k \ge 3$ satisfies $E + 3O \in \{8, 16, 24, \ldots\}
\setminus \{0\}$, and consequently:

1. **$D := E + O \ge 4$** — every solution $2^k$ with $k \ge 3$ has at
   least $4$ nonzero ternary digits;
2. **$D = 4 \iff (E, O) = (2, 2)$** — the $256$ profile;
3. if $E + 3O \ge 16$ then $D \ge 6$.

*Proof.* $(E, O) \ne (0,0)$: if all digits are $0$ then $\mathrm{tfold} =
0 \ne 2^k$. So $E + 3O > 0$ and $E + 3O \equiv 0 \pmod 8$ give $S := E +
3O \ge 8$. Now $D = E + O = S - 2O$ with the constraint $E = S - 3O \ge 0$,
i.e. $O \le \lfloor S/3 \rfloor$. For $S = 8$: $O \le 2$, so $D = 8 - 2O
\ge 4$, with equality iff $O = 2$ (then $E = 2$). For $S \ge 16$: $D = S -
2O \ge S - 2\lfloor S/3 \rfloor \ge \lceil S/3 \rceil \ge 6$. ∎

**The $256$ receipt (`witness_256_budget`).** $256 = 2^8 = 3^0 + 3^1 +
3^2 + 3^5$: 1-digits at positions $\{0, 1, 2, 5\}$, so $E = \#\{0,2\} = 2$,
$O = \#\{1,5\} = 2$, and $E + 3O = 2 + 6 = 8 \equiv 0 \pmod 8$ — the
budget's minimal profile, attained at the largest known solution, exactly
as Corollary C3 predicts.

---

## §6. THE CENSUS AND THE MAIN THEOREM ($k \le 500$)

### Theorem D (`erdos406_census`) — the certified exhaustive check

**Statement.** For every $k$ with $0 \le k \le 500$:
$$\mathrm{tern}_{01}(700,\; 2^k) = \textsf{true} \;\Longrightarrow\;
k \in \{0, 2, 8\}.$$

**Proof (a genuinely finite argument — the exhaustive certified check).**
Define the pure-Bool census predicate
$$\mathrm{censusCheckB}(k) := \bigl(\mathrm{tern}_{01}(700,\, 2^k) =
\textsf{false}\bigr) \;\vee\; \bigl(k = 0 \vee k = 2 \vee k = 8\bigr),$$
with the kernel iff-bridge `censusCheckB_iff` to its reading. The Lean 4
**kernel** evaluated, by `decide`:

- **Chunk 1** (`census_chunk1`): every $k \in [0, 480)$ satisfies
  $\mathrm{censusCheckB}(k)$;
- **Chunk 2** (`census_chunk2`): every $j \in [0, 21)$ satisfies
  $\mathrm{censusCheckB}(480 + j)$.

The two chunks cover $[0, 501) = \{0, 1, \ldots, 500\}$ exactly, with
chunk sizes $480 + 21 = 501$ respecting the campaign's legal chunk cap
(the NO-OOM discipline: never `decide` on $\forall\, k < N$ for $N >
501$), and the kernel exponentiation threshold set to $1000$ — the
kernel-legal cap for evaluating $2^{500}$ and $3^{700}$ as closed
numerals. `decide` on a closed Bool proposition is kernel type-checking:
the check is **exhaustive over the stated range**, hence a proof. Given
$\mathrm{tern}_{01}(700, 2^k) = \textsf{true}$ with $k \le 500$: the first
disjunct of $\mathrm{censusCheckB}(k)$ is false, so $k \in \{0,2,8\}$. ∎

### Theorem E (`erdos406_main`) — THE MAIN THEOREM

**Statement.** For every $k$ with $0 \le k \le 500$:
$$\bigl(\exists\, b:\; 2^k = \mathrm{tfold}(b)\bigr) \;\iff\; k \in
\{0, 2, 8\}.$$
Equivalently, in the corpus's plain language:
$$\{\,2^k : k \le 500,\ 2^k \text{ has only digits } 0 \text{ and } 1
\text{ in base } 3\,\} = \{1,\; 4,\; 256\}.$$

**Proof.**

**(⇒)** Let $2^k = \mathrm{tfold}(b)$ with $k \le 500$. The kernel receipt
$2^{500} < 3^{700}$ (`two_pow_500_lt`) gives
$$\mathrm{tfold}(b) = 2^k \le 2^{500} < 3^{700},$$
so the backward semantic law (Theorem A ⇐, at fuel $f = 700$) yields
$\mathrm{tern}_{01}(700, 2^k) = \textsf{true}$; Theorem D then yields
$k \in \{0, 2, 8\}$.

**(⇐)** The three witnesses, each a kernel `rfl` receipt
(`witness_one`, `witness_four`, `witness_256`):
$$2^0 = 1 = \mathrm{tfold}([1]) = 3^0,$$
$$2^2 = 4 = \mathrm{tfold}([1,1]) = 3^0 + 3^1 = 1 + 3,$$
$$2^8 = 256 = \mathrm{tfold}([1,1,1,0,0,1]) = 3^0 + 3^1 + 3^2 + 3^5 =
1 + 3 + 9 + 243,$$
(the last fold computes by the §2 recursion, right-to-left:
$1 \to 3 \to 9 \to 28 \to 85 \to 256$). ∎

**Reading.** Theorem E is the corpus addendum's "only examples seem to
be $1$, $4 = 1+3$, and $256 = 1+3+9+243$" — **proved complete for every
power of two below $2^{500}$**. The range endpoint itself is rejected:
kernel receipt `census_receipts` records $\mathrm{tern}_{01}(700, 2^{500})
= \textsf{false}$ (with $2^4, 2^{10}, 2^{100}$ as further sampled
rejections). All three witnesses satisfy every general law at the laws'
sharp boundaries: $k = 0, 2, 8$ are even (parity law), and the mod-8
budget binds only at $k = 8 \ge 3$ where it holds with the minimal
$(2,2)$ profile (§5).

---

## §7. THE STANDING CONSTRAINTS ON EVERY HYPOTHETICAL LARGE SOLUTION
(the open-core boundary)

**Definition.** A *hypothetical large solution* is a pair $(b, k)$ with
$2^k = \mathrm{tfold}(b)$ and $k > 500$ (beyond the certified census
range). The corpus's all-$k$ question is whether any exists, and whether
only finitely many exist.

**The complete unconditional constraint set.** Every item below is proved
above with **no bound on $k$**, so every hypothetical large solution must
satisfy ALL of them simultaneously:

1. **Parity (Theorem B).** $k$ is **even**.
2. **Units digit (§4 refinement).** The units ternary digit is exactly
   $\varepsilon_0 = 1$ (the term $3^0 = 1$ appears in the sum).
3. **The mod-8 budget (Theorem C).** $E + 3O \equiv 0 \pmod 8$; hence by
   Corollary C3: **at least 4 nonzero ternary digits** ($D \ge 4$),
   equality only on the $(E, O) = (2, 2)$ profile — the $256$ pattern —
   and $D \ge 6$ whenever $E + 3O \ge 16$.
4. **The census boundary (Theorem D/E).** $k > 500$ — every exponent up
   to and including $500$ is already classified, with $\{4, 6, 10, 12,
   \ldots, 500\}$ all certified rejected.

**The open core, named exactly (the honest boundary of this assembly).**
THE ALL-$k$ FINITENESS CORE: proving that only finitely many powers of
$2$ are $0/1$-ternary numbers (equivalently, that no hypothetical large
solution exists — or that only boundedly many do). No current technique
reaches it:

1. **The Senge–Straus / Stewart digit-count theory is silent.** That
   theory bounds the **number of nonzero digits** of an integer written
   in two multiplicatively independent bases; the corpus's condition
   bounds digit **values** ($\le 1$). A power of two can carry $\sim
   0.631\,k$ nonzero ternary digits all equal to $1$, so no
   count-lower-bound obstructs the pattern. (This is exactly why the
   campaign registry classifies the remainder as *Stewart-class*.)
2. **The heuristic (context, NOT a theorem).** If the ternary digits of
   $2^k$ behaved like independent uniform draws on $\{0,1,2\}$, then
   $P[\text{all} \le 1] \approx (2/3)^{0.631k}$, and the expected number
   of solutions beyond $k = 500$ is $\approx 10^{-55}$ — finiteness
   expected, proof absent. The campaign registry carries the mapped
   research fronts (residue towers $2^k \bmod 3^n$; the $2.482^n$ entropy
   row — WORKLOG #406 lines).
3. **What remains open is exactly the corpus's YES/NO.** The assembly
   delivers: the complete classification below $2^{500}$, the infinite
   odd-exponent exclusion, and the mod-8 budget — the standing structure
   every hypothetical large solution must fit. It does **not** deliver
   the all-$k$ finiteness verdict, and no part of this document should be
   read as claiming it.

---

## §8. THE ARSENAL BRIDGE (BOSS's mathematics applied at the witnesses)

Kernel 38 applies four Arsenal theorems — the vendored arsenal
(`Arsenal/`, the erdosternary2 + HC-PROOF/CardinalWorlds libraries, the
16,121-theorem arsenal as recorded in the README KILL #40 registry) —
packaged as one kernel proposition (`erdos406_arsenal_bridge` over
`arsenalBridgeProp`):

1. **`ErdosTernary2.lt_three_cases`**
   (Arsenal/ErdosTernary2/Basic.lean:16 — *every natural $< 3$ equals
   $0$, $1$, or $2$*): applied **in-proof** at the Semantic Law's digit
   reconstruction (§3 ⇒: the residue $n \bmod 3 \in \{0,1,2\}$ by
   trichotomy; the checker's $\le 1$ selects the two admissible digits,
   the case $d = 2$ closed by contradiction). This is the engine of the
   checker-to-representation extraction.
2. **`ErdosTernary2.isTernaryDigit`**
   (Arsenal/ErdosTernary2/Basic.lean:44 — *the ternary-digit recognizer,
   `true` exactly on $\{0,1,2\}$*): kernel `decide` receipts on every
   base-3 digit of the witnesses — $256$'s digits $[1,1,1,0,0,1]$ and
   $1$'s, $4$'s $[1]$, $[1,1]$ all pass (each is one of $0,1,2$).
3. **`CardinalWorlds.carryAtPos_bound`**
   (Arsenal/CardinalWorlds.lean:108 — *`carryAtPos R p < 4`*): applied at
   the witness pair $(R, p) = (256, 1)$ — the HC-PROOF carry-position bound
   engaged on the largest census witness (`carryAtPos 256 1 < 4`).
4. **`CardinalWorldsV2.v2r_ternary_scaling`**
   (Arsenal/CardinalWorldsV2.lean:71 — *`v2r (3^a \cdot c) = v2r c`*):
   applied at $(a, c) = (8, 256)$ — multiplication by the ternary power
   $3^8$ preserves the 2-adic depth reader of $256$: the ternary-scaling
   invariance anchored at the exponent of the largest witness
   ($256 = 2^8$), the structural law that a ternary-scaled witness
   retains its dyadic depth.

The bridge is the recorded contact point between the census witnesses
and the arsenal's dyadic/ternary machinery — BOSS's own mathematics,
applied on BOSS's own front.

---

## §9. VERIFICATION RECEIPTS

1. **CI — Kernel 38 compiles green, zero gaps.** GitHub Actions run
   **42912135608 GREEN** (`.github/workflows/kills.yml`, path filter
   includes `problem406-ternary-powers/**`; `lake env lean` with Mathlib
   resolved at the pinned `leanprover/lean4:v4.33.0-rc2` toolchain). The
   4-round war, visible in `git log problem406-ternary-powers/`:
   `dba7d1bc` (r1 — 8 root causes, incl. the BEq/Nat.beq unification gap,
   the iff-decidability death, the exponentiation threshold) →
   `7b520b5` (r2) → `3a36b06` (r3) → `9046b593` (r4 — the omega-atom
   fix; 0 errors). KILL #40 in the README registry.
2. **Sorry/admit audit (this session).** `rg` on
   `Erdos406Ternary.lean`: **0** `sorry`, **0** tactic `admit`, **0**
   `axiom` declarations (the only textual matches are the English words
   "admitted"/"audits" in comments).
3. **battery406.py — re-run this session (foreground), ALL GREEN:**

   ```text
   A1 census divmod: good exponents = [0, 2, 8]  OK
   A2 census base3-doubling: good exponents = [0, 2, 8]  OK
   B semantic fold<->digits (3000 random lists): True
   C mod-3 odd-exclusion (j<300): True
   D mod-8 budget (3000 random lists): True
   E fuel bound 2^500 < 3^700, digits(2^500) = 316 <= 700: True
   W witnesses 1, 4, 256: True
   BATTERY406_GREEN=1
   ```

   The two census methods are **independent** (A1: divmod digit
   extraction; A2: array-arithmetic base-3 doubling with carries — no
   divmod anywhere) and agree exactly: $\{0, 2, 8\}$.
4. **Kernel receipts inside the file** (§8 of the kernel): the witness
   `rfl`s, `witness_256_budget`, `census_receipts` (sampled rejections
   $2^4, 2^{10}, 2^{100}, 2^{500}$), the `#eval` echoes, and the
   `#print axioms` audits on the six headline theorems
   (`erdos406_odd_excluded`, `erdos406_mod8_budget`, `tern01_iff_tfold`,
   `erdos406_census`, `erdos406_main`, `erdos406_arsenal_bridge`).
5. **This assembly's fresh arithmetic checks (this session):**
   $\mathrm{digits}_3(2^{500}) = 316$; $3^{315} < 2^{500} < 3^{316}$;
   $2^{500} < 3^{700}$; $1 + 3 + 9 + 243 = 256 = 2^8$. All agree with the
   battery receipts and the kernel's `two_pow_500_lt`.

---

**Assembly closed.** Below $2^{500}$ the corpus's set is exactly
$\{1, 4, 256\}$ (certified exhaustive, §6); every odd exponent is
excluded at any size (§4); every solution at $k \ge 3$ carries the mod-8
budget and the $\ge 4$-digit floor (§5); the checker and the
distinct-powers-of-3 reading are one predicate (§3); the arsenal is
bridged at the witnesses (§8); the all-$k$ finiteness core stands open,
named, and undressed (§7).
