# K2CLASS_COMPLETE_PROOF.md — Erdős #686, the k=2 square classification: COMPLETE PROOFS (W1)

Target kernel: `problem686-pell-ratio/Erdos686K2Class.lean`. Every proof below is complete,
machine-verified on instances (§K), and Lean-conversion-ready. Notation: for fixed $y\ge 2$
write $a_n:=\mathrm{chev}\,y\,n$; all arithmetic is in $\mathbb{N}$ with truncated subtraction —
**every subtraction used below is exhibited as exact**. $u\mid v$ is $\mathbb{N}$ divisibility.

## VERDICT TABLE

| # | Theorem | Status | Kill method |
|---|---|---|---|
| T1 | `cassini` | **PROVEN** | induction on $n$: multiply the additive law by $a_{n+1}$ and by $a_{n+2}$, subtract |
| T2 | `gap_hop` | **REFUTATED AS WRITTEN; PROVEN after one-token repair** | file RHS equals $y\cdot a_j$ (not $(y{-}1)a_j$); counterexample $y{=}10,j{=}1$: $90\neq100$ |
| T3 | `pair_diff_mod4` | **PROVEN** | constant-gap law $g_{i+1}=g_i+(y-2)a_{i+1}$, $y\equiv2\ (4)$ ⟹ $g_i\equiv1\ (4)$ |
| T4 | `erdos686k2_witness_of_chain` | **PROVEN** | $X=E/2$, $Y=y/2$; master Pell identity $X^2+t^2=t^2Y^2+1$ from Cassini + additive law |
| T5 | `mutual_step` | **PROVEN** | $W:=u_0u_2=u_1^2-1$: $u_1\mid (W-1)(W+1)=W^2-1=(u_0^2-1)u_2^2+(u_2^2-1)$ |
| T6 | `chain_of_mutual` | **PROVEN** | fuel induction on $u_0$; Cassini cancellation climb |
| T7 | `erdos686k2class` | **PROVEN** | ⟸ T4; ⟹ divisor pair $(d_1,d_2)$ of $t^2-1$ → `Mutual t d₁` → T6 → Y-law $y=4n+6$ |
| T8 | `erdos686k2_nogo` | **PROVEN** | modular: $y\in\{10,14\}$; $j=1$ gives $t\in\{10,14\}$ (excluded), $j\ge2$ gives $t\ge99>16$ |

Kernel repairs flagged (all verified in §K): **(R1)** `gap_hop` RHS typo; **(R2)** `gap_ge` /
`pair_diff_mod4` Lean proofs route through the false `gap_hop` — repaired skeletons below;
**(R3)** arsenal-bridge conjunct `v2r (2^2 * 2401) = v2r 2401` is **false** ($v_2(4\cdot2401)=2\ne0$);
use `v2r (3^2 * 2401) = v2r 2401` (exactly `CardinalWorldsV2.v2r_ternary_scaling 2 2401`).

---

## §A SUPPORT LEMMAS (used by the targets; each complete)

**Definitions (verbatim, kernel §0).**
```lean
def Rep2 (N m n : Nat) : Prop :=
  (m + 1) * (m + 2) = N * (n + 1) * (n + 2) ∧ 1 ≤ n ∧ n + 2 ≤ m
def chev (y : Nat) : Nat → Nat
  | 0 => 1 | 1 => y | (n + 2) => y * chev y (n + 1) - chev y n
def Mutual (u₀ u₁ : Nat) : Prop := (u₀ ∣ u₁ * u₁ - 1) ∧ (u₁ ∣ u₀ * u₀ - 1)
```

**L1 (`chev_mono`, `chev_mono'`, `chev_pos`; file lines 57–109, sound as written).**
$y\ge2\Rightarrow a_n\le a_{n+1}$ for all $n$.
*Proof.* Induction on $n$. $n=0$: $a_0=1\le y=a_1$. Step: $a_{n+2}=y\,a_{n+1}-a_n$ (definition) and
$y\,a_{n+1}\ge 2a_{n+1}=a_{n+1}+a_{n+1}\ge a_{n+1}+a_n$ (IH), so the subtraction is exact and
$a_{n+2}=y\,a_{n+1}-a_n\ge a_{n+1}$. ∎ Then `chev_mono'` ($i\le j\Rightarrow a_i\le a_j$, induction on $j$)
and `chev_pos` ($1\le a_n$ since $a_0=1\le a_n$). In Lean these three are already green — keep.

**L2 (`chev_add`; file lines 112–122, sound as written).** $y\ge2\Rightarrow a_n+a_{n+2}=y\cdot a_{n+1}$.
*Proof.* $a_{n+2}=y\,a_{n+1}-a_n$ by definition; $a_n\le a_{n+1}\le y\,a_{n+1}$ (L1 and $1\le y$), so the
truncated subtraction is exact and $a_n+a_{n+2}=a_n+(y\,a_{n+1}-a_n)=y\,a_{n+1}$ (`Nat.add_sub_cancel'`). ∎

**L4 (gap sequence).** Define $g_i:=a_{i+1}-a_i$ for $i\ge0$ (exact by L1).
**(i)** $g_0=y-1$. **(ii)** $g_{i+1}=(y-2)\,a_{i+1}+g_i$. **(iii)** $g_i\ge y-1$ (`gap_ge`). **(iv)** if
$y\equiv2\pmod4$ then $g_i\equiv1\pmod4$ — all for every $i\ge0$.
*Proof of (ii).* L2 at $i$: $a_i+a_{i+2}=y\,a_{i+1}$, so $a_{i+2}=y\,a_{i+1}-a_i$ exactly and
$g_{i+1}=a_{i+2}-a_{i+1}=y\,a_{i+1}-a_i-a_{i+1}=(y-1)a_{i+1}-a_i$ [exact: $a_i\le a_{i+1}\le(y-1)a_{i+1}$
since $a_i+a_{i+1}\le a_i+a_{i+2}=y\,a_{i+1}$]. Then $(y-1)a_{i+1}-a_i=(y-2)a_{i+1}+(a_{i+1}-a_i)
=(y-2)a_{i+1}+g_i$ [exact: $(y-2)a_{i+1}+g_i+a_i=(y-2)a_{i+1}+a_{i+1}=(y-1)a_{i+1}\ge a_i$]. ∎
*Proof of (iii).* Induction on $i$: $g_0=y-1$; $g_{i+1}=g_i+(y-2)a_{i+1}\ge g_i\ge y-1$ since
$(y-2)a_{i+1}\ge0$. ∎ *(This is the repaired `gap_ge`: statement true, proof rerouted off `gap_hop`.)*
*Proof of (iv).* Induction on $i$: $g_0=y-1\equiv1\pmod4$ ($y\equiv2$); $g_{i+1}=g_i+(y-2)a_{i+1}\equiv g_i$
($y-2\equiv0\pmod4$). ∎

---

## T1. `cassini` — PROVEN

**Lean statement (verbatim).**
```lean
theorem cassini (y : Nat) (hy : 2 ≤ y) (n : Nat) :
    chev y n * chev y (n + 2) + 1 = chev y (n + 1) * chev y (n + 1) := by
```

**Proof.** Induction on $n$ (hypotheses $y\ge2$ throughout).
*Base $n=0$:* $a_0a_2+1=1\cdot(y^2-1)+1=y^2=a_1^2$; the subtraction $y\cdot y-1$ is exact because
$y\ge2\Rightarrow y^2\ge4\ge1$.
*Step $n\to n+1$:* IH: $a_na_{n+2}+1=a_{n+1}^2$. Take the additive law L2 at $n$ and $n+1$:
$$A_1:\ a_n+a_{n+2}=y\,a_{n+1},\qquad A_2:\ a_{n+1}+a_{n+3}=y\,a_{n+2}.$$
Multiply $A_2$ by $a_{n+1}$ and $A_1$ by $a_{n+2}$ (ring, valid in $\mathbb N$):
$$a_{n+1}^2+a_{n+1}a_{n+3}=y\,a_{n+1}a_{n+2},\qquad a_na_{n+2}+a_{n+2}^2=y\,a_{n+1}a_{n+2}.$$
Equal right-hand sides give $a_{n+1}a_{n+3}+a_{n+1}^2=a_na_{n+2}+a_{n+2}^2$. By IH,
$a_na_{n+2}=a_{n+1}^2-1$ (exact: $a_{n+1}^2=a_na_{n+2}+1\ge1$), hence
$$a_{n+1}a_{n+3}+a_{n+1}^2=(a_{n+1}^2-1)+a_{n+2}^2\ \Longrightarrow\ a_{n+1}a_{n+3}+1=a_{n+2}^2.\qquad\blacksquare$$

**LEAN CONVERSION NOTES.** The in-file skeleton (lines 126–157) is *already this proof* and is sound:
keep it. Base: `rw [chev_zero, chev_two, chev_one]`, extract `P := y*y` (`obtain ⟨P, hP⟩ : ∃ P, y*y = P`),
`Nat.mul_pos` for `1 ≤ P`, `omega`. Step: `have A1 := chev_add y hy n; have A2 := chev_add y hy (n+1)`,
the two multiplied identities `c1`, `c2` via `rw [← A2]; ring` / `rw [← A1]; ring`, `c3` by `ring`,
then the atom-extraction block (`m1,m2,m4,m5,M,M'`) and final `omega`. No changes needed.

---

## T2. `gap_hop` — REFUTATED AS WRITTEN; PROVEN after one-token repair

**Lean statement (verbatim, file lines 162–163).**
```lean
theorem gap_hop (y : Nat) (hy : 2 ≤ y) (j : Nat) (hj : 1 ≤ j) :
    (y - 1) * chev y j = chev y (j + 1) - chev y (j - 1) + 2 * chev y (j - 1) := by
```

**Refutation.** The RHS is $(a_{j+1}-a_{j-1})+2a_{j-1}=a_{j+1}+a_{j-1}=y\cdot a_j$ by the additive law L2
at $j-1$. The statement therefore asserts $(y-1)a_j=y\,a_j$, i.e. $a_j=0$ — false for every $y\ge2$
($a_j\ge1$). Concrete counterexample: $y=10$, $j=1$: LHS $=9\cdot10=90$, RHS $=99-1+2\cdot1=100$.
Verified numerically (§K.2). **The CI failure of the whole §2/§3 cascade starts here.**

**Repaired statement (one token: RHS middle term `chev y (j - 1)` → `chev y j`, drop `2 *`).**
```lean
theorem gap_hop (y : Nat) (hy : 2 ≤ y) (j : Nat) (hj : 1 ≤ j) :
    (y - 1) * chev y j = chev y (j + 1) - chev y j + chev y (j - 1) := by
```

**Proof.** Additive law L2 at $j-1$ (valid index since $j\ge1$): $a_{j-1}+a_{j+1}=y\,a_j$. Then
$$(y-1)a_j=y\,a_j-a_j=(a_{j-1}+a_{j+1})-a_j=(a_{j+1}-a_j)+a_{j-1},$$
where $y\,a_j-a_j$ is exact ($1\le y$), $(a_{j-1}+a_{j+1})-a_j$ and the regrouping are exact because
$a_j\le a_{j+1}$ (L1). ∎ *(Equivalent form used downstream: $g_j=(y-1)a_j-a_{j-1}$, i.e. L4(ii) at $j-1$:
$g_j=g_{j-1}+(y-2)a_j$; both are the file's intended `hga2` identity.)*

**LEAN CONVERSION NOTES.** Fix the statement as above; the in-file proof body then closes:
`have A1 := chev_add y hy (j - 1)` gives `chev y (j-1) + chev y (j-1+2) = y * chev y j` — first
`norm_num`/`omega`-rewrite `j - 1 + 2 = j + 1` (`Nat.add_assoc` handles: `(j-1)+2 = (j+1)` by `omega`
on the index — do `have hidx : j - 1 + 2 = j + 1 := by omega` and `rw [hidx] at A1`), extract
`P := y * chev y j`, `rw [...] at *`, close with `omega` (needs mono facts `chev y (j-1) ≤ chev y j ≤
chev y (j+1)` from `chev_mono'` in context for sub-exactness). Verified identity $y\le40$, $j\le8$ (§K.2b).

---

## T3. `pair_diff_mod4` — PROVEN

**Lean statement (verbatim).**
```lean
theorem pair_diff_mod4 (y : Nat) (hy4 : y % 4 = 2) (hy : 2 ≤ y) (j : Nat) (hj : 1 ≤ j) :
    (chev y (j + 1) - chev y (j - 1)) % 4 = 2 := by
```

**Proof.** Write $E:=a_{j+1}-a_{j-1}$ (exact: $a_{j-1}\le a_j\le a_{j+1}$ by L1). Split:
$$E=(a_{j+1}-a_j)+(a_j-a_{j-1})=g_j+g_{j-1}$$
(exact, same order facts). By L4(iv) — which needs exactly the hypothesis $y\equiv2\pmod4$ —
$g_j\equiv1\pmod4$ and $g_{j-1}\equiv1\pmod4$ (indices $j\ge1\ge0$ and $j-1\ge0$). Hence
$E\equiv1+1\equiv2\pmod4$. ∎

*Note (why the file's `key` must carry `hy4`).* The stronger-looking claim
$(a_k-a_{k-1})\bmod4=(y-1)\bmod4$ for **all** $y\ge2$ is false: $y=3$, $k=2$ gives
$(8-3)\bmod4=1\ne2$. Inside the theorem `hy4` is in context, so the in-file `key` is only ever
used under $y\equiv2\pmod4$ — the *statement* of the repaired key should record this (or route
through L4(iv), which does).

**LEAN CONVERSION NOTES — two routes, both verified.**
*Route B (recommended, cleanest):* prove one lemma
```lean
theorem gap_mod4 (y : Nat) (hy4 : y % 4 = 2) (hy : 2 ≤ y) (i : Nat) :
    (chev y (i + 1) - chev y i) % 4 = 1 := by
  induction i with
  | zero => rw [chev_one, chev_zero]; omega
  | succ i ih =>
    have A := chev_add y hy i          -- a_i + a_{i+2} = y·a_{i+1}
    have hm1 := chev_mono y hy i       -- a_i ≤ a_{i+1}
    have hm2 := chev_mono y hy (i + 1) -- a_{i+1} ≤ a_{i+2}
    obtain ⟨Q, hQ⟩ : ∃ Q, (y - 2) * chev y (i + 1) = Q := ⟨_, rfl⟩
    have hstep : chev y (i + 2) - chev y (i + 1) = Q + (chev y (i + 1) - chev y i) := by
      rw [hQ]; omega                    -- from A + hm1 + hm2 (all subs exact)
    have hQ0 : Q % 4 = 0 := by rw [hQ, Nat.mul_mod]; omega   -- (y-2) ≡ 0 (mod 4)
    rw [hstep, hQ0]; omega
```
then `pair_diff_mod4`:
```lean
have hm1 := chev_mono' y hy (j - 1) j (by omega)
have hm2 := chev_mono' y hy j (j + 1) (by omega)
have g1 := gap_mod4 y hy4 hy (j - 1)   -- (a_j - a_{j-1}) % 4 = 1
have g2 := gap_mod4 y hy4 hy j          -- (a_{j+1} - a_j) % 4 = 1
have hE : chev y (j + 1) - chev y (j - 1)
    = (chev y (j + 1) - chev y j) + (chev y j - chev y (j - 1)) := by omega
rw [hE, g2, g1]; omega
```
*Route A (minimal diff to the file):* keep the file's `key` induction but add `hy4` to the `key`
statement and use the **repaired** `gap_hop` (T2) — the corrected hop *is* the file's `hga2`
(`a_{k+1} - a_k + a_{k-1} = (y-1)·a_k`), after which the file's existing `hmodP`/`ih`/`omega` step
closes provided the order facts `chev y (k-1) ≤ chev y k ≤ chev y (k+1)` and
`chev y (k-1) ≤ (y-1) * chev y k` are in context (`chev_mono'` + `Nat.mul_le_mul_left`).
Verified $y\in\{6,10,\dots,54\}$, $j\le8$; negative control confirms `hy4` is necessary (§K.3).

---

## T4. `erdos686k2_witness_of_chain` — PROVEN

**Lean statement (verbatim).**
```lean
theorem erdos686k2_witness_of_chain (y j : Nat) (hy4 : y % 4 = 2) (hy10 : 10 ≤ y)
    (hj : 1 ≤ j) :
    Rep2 (chev y j * chev y j) ((chev y (j + 1) - chev y (j - 1)) / 2 - 3) / 2
      (y / 2 - 3) / 2 := by
```

**Proof.** Set
$$t:=a_j,\quad d_1:=a_{j-1},\quad d_2:=a_{j+1},\quad E:=d_2-d_1,\quad X:=E/2,\quad Y:=y/2,\quad
m:=(X-3)/2,\quad n:=(Y-3)/2.$$

**(1) Parity and exactness.** $y\equiv2\pmod4$ and $y\ge10$ give $y=2Y$ with $Y$ odd, $Y\ge5$.
`pair_diff_mod4` gives $E\equiv2\pmod4$; hence $E=2X$ exactly and $X$ is odd.

**(2) The divisor pair.** Additive law L2 at $j-1$: $d_1+d_2=y\,t=2Yt$; and $d_2-d_1=2X$ by (1).
Solving: $d_1=Yt-X$, $d_2=Yt+X$; in particular $X\le Yt-1$ since $d_1\ge1$ (`chev_pos`).

**(3) MASTER identity $X^2+t^2=t^2Y^2+1$.** Cassini (T1) at $j-1$ (index shift $(j-1)+2=j+1$):
$d_1d_2+1=t^2$. Substitute (2):
$$(Yt-X)(Yt+X)+1=t^2\ \Longrightarrow\ (Yt)^2-X^2+1=t^2\ \Longrightarrow\ X^2+t^2=t^2Y^2+1$$
(the expansion $(Yt-X)(Yt+X)=(Yt)^2-X^2$ is exact since $X\le Yt$; `sub_add_mul`). Equivalently
$$X^2-1=t^2\,(Y^2-1).\tag{$\star$}$$

**(4) The Rep2 product.** $X$ odd and $X\ge9$ (see (5)) give $X=2m+3$, $m+1=\frac{X-1}2$,
$m+2=\frac{X+1}2$; likewise $Y=2n+3$ odd, $n+1=\frac{Y-1}2$, $n+2=\frac{Y+1}2$. So
$(m+1)(m+2)=\frac{X^2-1}4$ and $(n+1)(n+2)=\frac{Y^2-1}4$ (exact: $X\pm1$, $Y\pm1$ even; $X,Y$ odd
$\Rightarrow X^2-1,Y^2-1\equiv0\bmod8$). Dividing $(\star)$ by $4$:
$$4(m+1)(m+2)=t^2\cdot4(n+1)(n+2)\ \Longrightarrow\ (m+1)(m+2)=t^2(n+1)(n+2)$$
(cancel the factor 4). This is `Rep2`'s first conjunct with $N=t^2$.

**(5) Size conditions.** $n\ge1$: $Y\ge5\Rightarrow Y-3\ge2\Rightarrow n\ge1$.
$m\ge n+2$: since $2m+3=X$, $2n+3=Y$ (both odd), $m\ge n+2\iff X\ge Y+4$. Now
$E=g_j+g_{j-1}\ge2(y-1)$ by L4(iii) (indices $j,j-1\ge0$), so
$$X=\tfrac E2\ \ge\ y-1\ =\ 2Y-1\ \ge\ Y+4\quad(\iff Y\ge5).\qquad\blacksquare$$

The conclusion literally instantiates $m=\bigl((a_{j+1}-a_{j-1})/2-3\bigr)/2$ (i.e. $(X-3)/2$ with
$X=E/2$) and $n=(y/2-3)/2$: exactly the statement's witnesses.

**LEAN CONVERSION NOTES.** The in-file skeleton (lines 233–306) is *this proof* and is sound once the
upstream T2/T3/`gap_ge` repairs land (it consumes `pair_diff_mod4` and `gap_ge` as black boxes, both
true). Keep: `hEmod/hXodd/hEge/hYodd`, `hsum` (`chev_add`), `hcass` (index-shifted `cassini`),
atom extraction (`t, Yk, X, m, n`), `hmaster` via `sub_add_mul T X hXle` + `omega`, `h4m/h4n` by
`ring`, final `omega` after extracting `A,B,C,P,Q,R`. `hEge` needs `gap_ge y hy j hj` and
`gap_ge y hy (j+1) (by omega)` — with the repaired `gap_ge` (§A L4(iii)); note `E = g_j + g_{j-1}`
holds for $j=1$ too ($g_0=y-1$), so `omega` closes `hEge` from the two `gap_ge` instances plus the
`hE` splitting identity (context facts `chev y (j-1) ≤ chev y j ≤ chev y (j+1)`).

---

## T5. `mutual_step` — PROVEN

**Lean statement (verbatim).**
```lean
theorem mutual_step (u₀ u₁ : Nat) (hu1 : 2 ≤ u₁) (hslt : u₁ < u₀)
    (hmut : Mutual u₀ u₁) :
    ∃ u₂ : Nat, u₀ * u₂ = u₁ * u₁ - 1 ∧ Mutual u₁ u₂ ∧ u₂ < u₁ := by
```

**Proof.** Hypotheses: $u_0\mid u_1^2-1$, $u_1\mid u_0^2-1$, $2\le u_1<u_0$. Put
$u_2:=(u_1^2-1)/u_0$ (well-defined: $u_0\mid u_1^2-1$) and $W:=u_0u_2$.

**(a)** $W=u_1^2-1$: write $u_0c=u_1^2-1$ (divisor witness); then $u_2=(u_1^2-1)/u_0=c$
(`Nat.mul_div_cancel_left`, $u_0>0$), so $u_0u_2=u_1^2-1$.

**(b)** $u_2\ge1$: $u_1\ge2\Rightarrow u_1^2-1\ge3>0$; $u_0\mid u_1^2-1$, $u_0>0\Rightarrow u_0\le u_1^2-1$
(positive divisor), so $u_2=(u_1^2-1)/u_0\ge1$ (`Nat.div_pos`).

**(c)** $u_2<u_1$: $u_1<u_0$ and $u_1\ge1$ give $u_1^2<u_1u_0$ (`Nat.mul_lt_mul_left`), hence
$u_1^2-1\le u_1u_0-2<u_1u_0$, so $u_2=(u_1^2-1)/u_0<u_1$ (`Nat.div_lt_of_lt_mul`).

**(d)** `Mutual u₁ u₂`, i.e. $u_1\mid u_2^2-1$ and $u_2\mid u_1^2-1$.
*Second:* $u_1^2-1=W=u_0u_2=u_2u_0$ — witness $u_0$.
*First:* $W+1=u_1^2$, so $u_1\mid W+1$; hence $u_1\mid(W-1)(W+1)=W^2-1$ (difference of squares,
valid since $W\ge1$; `sub_add_mul W 1 hW1`). Also $u_1\mid(u_0^2-1)\cdot u_2^2$ (hypothesis, times
$u_2^2$). The identity (pure ring, $\mathbb N$):
$$W^2-1=(u_0^2-1)u_2^2+(u_2^2-1)\qquad(\text{since }W=u_0u_2)$$
gives, by subtraction of divisibilities (`Nat.dvd_sub'`): $u_1\mid u_2^2-1$. ∎

**LEAN CONVERSION NOTES.** The in-file proof (lines 312–373) is *this proof*, complete and sound:
`hMpos/huo/hle/hu2pos/hexact` = (a),(b); `hu2lt` = (c) via `Nat.mul_lt_mul_left` +
`Nat.div_lt_of_lt_mul`; the final block = (d) with `hdW : u₁ ∣ W+1`, `hA := hdW.mul_left (W-1)`,
`hC` from the divisor witness of `hd2`, `hsa := sub_add_mul W 1 hW1`, `hW2 : W*W = u₀*u₀*(E*E)`
(`ring`), `hFC := Nat.sub_one_mul`, `hAB := Nat.dvd_sub' hA hC`, `hdiff` by `omega`, closing
`rw [← hdiff]; exact hAB`. No changes needed.

---

## T6. `chain_of_mutual` — PROVEN (the descent)

**Lean statement (verbatim).**
```lean
theorem chain_of_mutual : ∀ (k u₀ u₁ : Nat), u₁ < u₀ → u₀ ≤ k → 1 ≤ u₁ → Mutual u₀ u₁ →
    ∃ y j : Nat, 2 ≤ y ∧ 1 ≤ j ∧ u₀ = chev y j ∧ u₁ = chev y (j - 1) := by
```

**Proof.** Induction on the fuel $k$ (strong induction on $u_0$ in disguise).
*$k=0$:* $1\le u_1<u_0\le0$ is contradictory — vacuous.
*$k+1$:* given $u_1<u_0\le k+1$, $1\le u_1$, `Mutual u₀ u₁`. Two cases:
* **Base case $u_1=1$.** Return $(y,j):=(u_0,1)$: $2\le y$ (since $u_0>u_1=1$), $1\le j$,
  $\mathrm{chev}\,u_0\,1=u_0$, $\mathrm{chev}\,u_0\,0=1=u_1$.
* **Descent case $u_1\ge2$.** `mutual_step` (T5) yields $u_2$ with $u_0u_2=u_1^2-1$,
  `Mutual u₁ u₂`, $u_2<u_1$; also $u_2\ge1$ by T5(b). Apply the induction hypothesis with fuel $k$
  to the pair $(u_1,u_2)$ — legal since $u_2<u_1\le k$ (from $u_1<u_0\le k+1$) — obtaining
  $y\ge2$, $j\ge1$ with
  $$u_1=\mathrm{chev}\,y\,j,\qquad u_2=\mathrm{chev}\,y\,(j-1).$$
  **Cassini climb.** Cassini (T1) at $j-1$ (index shift $(j-1)+2=j+1$):
  $$\mathrm{chev}\,y\,(j-1)\cdot\mathrm{chev}\,y\,(j+1)+1=(\mathrm{chev}\,y\,j)^2,$$
  i.e. $u_2\cdot\mathrm{chev}\,y\,(j+1)=u_1^2-1=u_0u_2$. Cancel $u_2\ge1$
  (`Nat.mul_right_cancel`): $u_0=\mathrm{chev}\,y\,(j+1)$. Return $(y,j+1)$: $2\le y$ ✓,
  $1\le j+1$ ✓, $u_0=\mathrm{chev}\,y\,(j+1)$ ✓, $u_1=\mathrm{chev}\,y\,((j+1)-1)=\mathrm{chev}\,y\,j$ ✓. ∎

**LEAN CONVERSION NOTES.** The in-file proof (lines 380–428) is *this proof*, complete and sound:
`by_cases hu1 : u₁ = 1` → base constructor `⟨u₀, 1, by omega, by omega, chev_one u₀, by rw [hu1, chev_zero]⟩`;
descent branch: `mutual_step`, `hu2pos` inline (`Nat.div_pos (Nat.le_of_dvd hMpos hmut.1)`),
`ih u₁ u₂ (by omega) (by omega) hu2pos hmut2`, `hcass2` = the index-shifted Cassini, atom extraction
(`cA,P,Q`), `hu0eq` via `Nat.mul_right_cancel` on `u₀ * chev y (j-1) = cA * chev y (j-1)`
(the `hLeft/hRight/omega` block), final constructor with `show j + 1 - 1 = j from rfl`. No changes.

---

## T7. `erdos686k2class` — PROVEN (the main iff)

**Lean statement (verbatim).**
```lean
theorem erdos686k2class (t : Nat) (h2 : 2 ≤ t) :
    ((∃ m n : Nat, Rep2 (t * t) m n) ↔
      ∃ y j : Nat, y % 4 = 2 ∧ 10 ≤ y ∧ 1 ≤ j ∧ t = chev y j) := by
```

**Proof.**

**(⟸) chain → Rep2.** Given $y\equiv2\pmod4$, $y\ge10$, $j\ge1$, $t=\mathrm{chev}\,y\,j$:
T4 (`erdos686k2_witness_of_chain`) directly furnishes $m,n$ with `Rep2 (chev y j · chev y j) m n`,
which is `Rep2 (t·t) m n`. ∎

**(⟹) Rep2 → chain.** Given `Rep2 (t²) m n`: $(m+1)(m+2)=t^2(n+1)(n+2)$, $1\le n$, $n+2\le m$.
Put $X:=2m+3$, $Y:=2n+3$ (both odd), $T:=tY$.

**(1) MASTER′.** $(2m+3)^2=4(m+1)(m+2)+1$ and $(2n+3)^2=4(n+1)(n+2)+1$ (ring). Substituting the
Rep2 equation: $X^2-1=t^2(Y^2-1)$, i.e.
$$X^2+t^2=t^2Y^2+1.\tag{$\star'$}$$

**(2) $X<T$, so $d_1:=T-X\ge1$.** If $T\le X$ then $T^2\le X^2$ (`Nat.mul_le_mul`), and $(\star')$
($X^2+t^2=T^2+1$) gives $T^2+t^2\le X^2+t^2=T^2+1$, whence $t^2\le1$, i.e. $t\le1$ —
contradicting $t\ge2$. So $X<T$; set $d_1:=T-X\ (\ge1)$ and $d_2:=X+T$. Then
$d_2-d_1=2X\ge18>0$ (as $X=2m+3$, $m\ge n+2\ge3$), so $d_1<d_2$, and (`sub_add_mul`, commuted)
$$d_1d_2=(T-X)(X+T)=T^2-X^2=t^2-1\qquad(\text{from }(\star')),$$
where both subtractions are exact ($X\le T$; $t\ge2$).

**(3) $d_1<t$.** If $t\le d_1$ then $t^2\le d_1^2\le d_1d_2=t^2-1<t^2$ (`Nat.mul_le_mul`, $1\le d_1\le d_2$) —
contradiction.

**(4) `Mutual t d₁`.**
*$t\mid d_1^2-1$:* $d_1+d_2=2T=2tY$, so $t\mid d_1+d_2$; hence $t\mid d_1(d_1+d_2)=d_1^2+d_1d_2
=d_1^2+(t^2-1)$; since $t\mid t^2$, subtraction (`Nat.dvd_sub'`) gives $t\mid d_1^2-1$.
*$d_1\mid t^2-1$:* $d_1d_2=t^2-1$ — witness $d_2$.

**(5) Descent.** `chain_of_mutual` (T6) with fuel $t$ on $(t,d_1)$ ($1\le d_1<t$, `Mutual`) yields
$y\ge2$, $j\ge1$ with $t=\mathrm{chev}\,y\,j$ and $d_1=\mathrm{chev}\,y\,(j-1)$.

**(6) $d_2=\mathrm{chev}\,y\,(j+1)$.** Cassini at $j-1$:
$\mathrm{chev}\,y\,(j-1)\cdot\mathrm{chev}\,y\,(j+1)=t^2-1=d_1d_2$; cancel $d_1\ge1$ (`chev_pos`,
`Nat.mul_right_cancel`).

**(7) Y-LAW: $y=4n+6$.** $d_1+d_2=2tY$ (step 2) and $d_1+d_2=\mathrm{chev}\,y\,(j-1)+
\mathrm{chev}\,y\,(j+1)=y\cdot\mathrm{chev}\,y\,j=y\,t$ (additive law L2 at $j-1$). So
$y\,t=2tY=t\,(2Y)$; cancel $t\ge1$ (`Nat.mul_right_cancel`): $y=2Y=2(2n+3)=4n+6$.
Hence $y\equiv2\pmod4$ and $y\ge10\iff n\ge1$ ✓ (hypothesis). Together with $j\ge1$,
$t=\mathrm{chev}\,y\,j$: the right-hand side. ∎

**LEAN CONVERSION NOTES.** The in-file proof (lines 435–553) is *this proof*, sound once upstream
repairs land: `hmaster` (= $(\star')$, `ring` after `hX2/hY2`), `hXY` by `by_contra` +
`Nat.mul_le_mul` + extraction + `omega` (= step 2 first half), `hd1/hd2/hprod` via
`sub_add_mul T X` + extraction + `omega` (step 2), `hd1t` `by_contra` (step 3), `hFirst/hSecond`
(step 4: `Nat.dvd_mul_of_dvd_left hdvdt`, `Nat.dvd_sub'`), `chain_of_mutual t d1 …` (step 5),
`hchevadd/hcassj` with index-shift `rw`, `hd2eq` via `Nat.mul_right_cancel` (step 6),
`hyY` via extraction + `Nat.mul_comm` + `Nat.mul_right_cancel` (step 7), final
`⟨y, j, by omega, by omega, hj1, hteq⟩` — the two `omega`s consume `hyY : y = 2*(2*n+3)`.
No changes needed beyond upstream T2/T3/gap_ge.

---

## T8. `erdos686k2_nogo` — PROVEN (scan-free, modular)

**Lean statement (verbatim).**
```lean
theorem erdos686k2_nogo (t : Nat) (h2 : 2 ≤ t) (h16 : t ≤ 16)
    (hnot : t ≠ 10 ∧ t ≠ 14) : ¬ ∃ m n : Nat, Rep2 (t * t) m n := by
```

**Proof.** Suppose `Rep2 (t²) m n`. By T7 (⟹) there are $y,j$ with $y\equiv2\pmod4$, $y\ge10$,
$j\ge1$, $t=\mathrm{chev}\,y\,j$.
* $y\le t$: $\mathrm{chev}\,y\,j\ge\mathrm{chev}\,y\,1=y$ (`chev_mono'`, $1\le j$), so
  $y\le t\le16$.
* Residue split (exhaustive): $10\le y\le16$, $y\equiv2\pmod4$ ⟹ $y\in\{10,14\}$.
* **Case $y=10$.** If $j=1$: $t=\mathrm{chev}\,10\,1=10$ — contradicts $t\ne10$.
  If $j\ge2$: $t=\mathrm{chev}\,10\,j\ge\mathrm{chev}\,10\,2=10^2-1=99>16$ (`chev_mono'`) —
  contradicts $t\le16$.
* **Case $y=14$.** If $j=1$: $t=14$ — contradicts $t\ne14$. If $j\ge2$:
  $t\ge\mathrm{chev}\,14\,2=14^2-1=195>16$ — contradiction.

All four subcases contradict; no `Rep2` exists for $t$. ∎
*(Modular throughout: the residue class $y\equiv2\pmod4$ and monotonicity only; no scan of $(m,n)$.)*

**LEAN CONVERSION NOTES.** The in-file proof (lines 557–589) is *this proof* and is sound once T7 is
green: `by_cases hy10v : y = 10` × `by_cases hj1v : j = 1`; the $j\ge2$ arms use
`chev_mono' y hy 2 j (by omega)`, `rw [chev_two]`, `Nat.mul_le_mul` for $10\cdot10\le y\cdot y$
(resp. $14\cdot14$), extraction + `omega`. Keep. Note $10^2-1=99>16$ and $14^2-1=195>16$ close by
`omega` after the `P := y*y` extraction (the in-file pattern).

---

## §J ARSENAL BRIDGE (receipts — BOSS's laws, where they apply)

The witness numbers of the $t=980$ edge ($m=2399$, $n=1$): $X=4801$, $m+2=2401$,
$(m+1)(m+2)=2400\cdot2401=5762400$.

* `ErdosTernary2.isTernaryDigit` (Basic.lean:44) + **`lt_three_cases`** (Basic.lean:16,
  $n<3\Rightarrow n=0\vee n=1\vee n=2$): the residues $[4801\bmod3,(4801/3)\bmod3,(4801/9)\bmod3]
  =[1,1,2]$ and $[2401\bmod3,\dots]=[1,2,2]$ are all ternary digits — `by decide` (each `x % 3 < 3`,
  case-split via `lt_three_cases`).
* **`carryAtPos_bound`** (CardinalWorlds.lean:108, `carryAtPos R p < 4`): applied at
  $(R,p)=(5762400,1)$ — the carry bound on the witness product. `carryAtPos_bound 5762400 1`.
* **`v2r_ternary_scaling`** (CardinalWorldsV2.lean:71, `v2r (3^a·c) = v2r c`): **REPAIR R3** — the
  file's fourth conjunct `v2r (2^2 * 2401) = v2r 2401` is **false**: $v_2(4\cdot2401)=2\ne0=v_2(2401)$.
  Replace it with `v2r (3^2 * 2401) = v2r 2401`, which *is* `CardinalWorldsV2.v2r_ternary_scaling 2 2401`
  verbatim (this is the CI's "v2r bridge type mismatch": the lemma is about ternary powers $3^a$,
  the goal was written with the dyadic $2^2$). The "3 unknown identifiers" in the CI intel are the
  bridge's arsenal names — they resolve once the Arsenal files compile; the false conjunct is the
  remaining real error.

---

## §K NUMERICAL VERIFICATION LOG (independent battery `/tmp/w1_verify2.py`, W1_VERIFY_GREEN)

1. **cassini**: 11 values of $y$ ($2..102$), $n\le8$ — all identities hold.
2. **gap_hop**: file version REFUTED at $(y,j)=(10,1)$: $90\ne100$. Corrected identity
   $(y-1)a_j=a_{j+1}-a_j+a_{j-1}$: holds for all $2\le y\le40$, $1\le j\le8$.
3. **pair_diff_mod4**: $y\in\{6,10,\dots,54\}$, $j\le8$ — $(a_{j+1}-a_{j-1})\bmod4=2$ always;
   negative control: without $y\equiv2\ (4)$ the gap law fails ($y=3$, $k=2$) — hypothesis necessary.
4. **gap_ge** ($y\le40$, $k\le8$) and **gap mod-4 law** ($g_i\equiv1\bmod4$): hold.
5. **witness construction**: 649 chain values ($y\in\{10,14,\dots,1006\}$, $j\le7$, $t\le10^8$):
   $E\equiv2\ (4)$, $X,Y$ odd, $E=2X$, $y=2Y$, $E\ge2(y-1)$, $X\ge Y+4$, $n\ge1$, $m\ge n+2$,
   master $X^2+t^2=t^2Y^2+1$, and $(m+1)(m+2)=t^2(n+1)(n+2)$ — all hold; plus the kernel's 8 edge
   receipts (980/2716/9701/323/10604/17524/99/195).
6. **mutual_step**: exhaustively, all 1246 mutual pairs $2\le u_1<u_0\le1200$: $u_2$ integral,
   `Mutual u₁ u₂`, $1\le u_2<u_1$.
7. **chain_of_mutual**: all 6073 mutual pairs $u_0\le3000$ lie on a Chebyshev chain; the descent
   (every `mutual_step` + Cassini climb) simulated on 3145 pairs, 0 failures.
8. **classification seal (airtight, exhaustive)**: for every $2\le t\le1000$, ALL `Rep2(t²)`
   solutions were enumerated via the divisor pairs of $t^2-1$ (bijective with solutions, no search
   bound): the representable set is *exactly* the chain set $\{\mathrm{chev}\,y\,j: y\equiv2\ (4),
   y\ge10, j\ge1\}$ — 255 values, 255 solutions (one each; the k=2 square witness is unique), and
   the Y-law $t=\mathrm{chev}\,(4n+6)\,j$ holds on **every** solution.
9. **nogo**: $t\in\{2,\dots,16\}\setminus\{10,14\}$: zero solutions (exhaustive divisor scan).
10. **bridge receipts**: ternary digits all $<3$; $5762400=2400\cdot2401$; $v_2(4\cdot2401)=2\ne0$
    (conjunct false as written), $v_2(9\cdot2401)=0=v_2(2401)$ (repair confirmed).

*End-to-end conclusion: the classification `Rep2(t²) ⟺ Chebyshev chain (y ≡ 2 mod 4, y ≥ 10,
j ≥ 1)` is a theorem; the kernel's mathematics is complete once repairs R1–R3 land. All 8 targets
PROVEN, zero gaps.*
