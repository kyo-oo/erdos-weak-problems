# GST Worldtrace: 140,804 normalized exponent cores, every scale

**Date:** 2026-10-29 (IST). **Scope:** An infinite family theorem about the original ternary-digit-two property; it does **not** settle all exponents. **Research branch:** \`gpt6/erdos-worldtrace-block-lift-20261029\`.

## Exact all-scale statement

For every \(u,s\in\mathbb N\) with \(1\le u\le140804\) and \(K=u3^s\notin\{1,4\}\),
there is a positive ternary position \(p\le s+42\) with
\[
 (4^{u3^s}/3^p)\bmod3=2.
\]
For \(s\ge29\), the sharper \(p\le s+30\) holds. This statement is obtained by combining established GST identities with **exact finite computations**; the 140,804-wide finite certificate has not yet been kernel-formalized.

## Algebraic infinite-scale reduction

The GST tower coefficient \(c_s=(4^{3^s}-1)/3^{s+1}\) is defined using the exact relation \(4^{3^s}=1+3^{s+1}c_s\). Its cubic recursion is
\[
c_{s+1}=c_s+3^{s+1}c_s^2+3^{2s+1}c_s^3.
\]
For \(s\ge29\), the corrections vanish modulo \(Q=3^{30}=205891132094649\); hence \(c_s\equiv c_{29}\pmod Q\). An exact 29-step modular recurrence beginning with \(c_0=1\) yields
\[
c_{29}\bmod Q=28881270545965.
\]
The existing GST tower-digit read theorem (also independently derived from the new whole-block lift on branch \`gpt6/erdos-tower-window-20261029\`) is
\[
 d_3(4^{u3^s},s+1+k)=d_3(uc_s,k),\quad0\le k\le s.
\]
Thus a digit 2 in the lowest 30 trits of \(u c_{29}\) supplies a digit 2 in \(4^{u3^s}\) for every \(s\ge29\), with \(p\le s+30\).

## Complete finite certificates

1. **Thirty-trit fixed coefficient:** Enumerate *every* multiplier \(u=1,\ldots,140805\). At stages \(k=0,\ldots,29\), remove each \(u\) having \(((u c_{29})//3^k)\bmod3=2\). Exactly one survivor remains: **140805**. At levels 28, 29, 30 the survivor counts are respectively **3, 2, 1**. This proves all smaller multipliers have a digit 2 in the 30-trit window. Wolfram Language independently reproduced \(Q\), \(c_{29}\) and the least survivor.

2. **Small scales \(s=0,\ldots,28\):** Enumerate all \(u=1,\ldots,140804\), excluding only \(u3^s=1,4\): exactly \(29(140804)-2=\mathbf{4,083,314}\) cases. For each scale, generate \(x_u=4^{u3^s}\bmod3^{s+60}\) via \(x_{u+1}=x_u (4^{3^s}\bmod3^{s+60})\bmod3^{s+60}\), using exact integer modular exponentiation (never constructing the huge full power). Every case contains digit 2. The largest first-hit relative offset \(p-s-1\) is **41**, at \(s=19,u=102967,p=61\). Consequently \(p\le s+42\).

**Executable certificate:** \`scripts/gpt6_fixed_core_140804_certificate.py\`. Its dedicated workflow is \`.github/workflows/gpt6_fixed_core_140804_certificate.yml\`. The smaller 566-multiplier finite case is additionally kernel-checked by Lean in \`GSTFixedCoreCertificate.lean\` on its own branch (run #40778225004). The unconditional whole-block transport and tower-digit projection passed isolated Lean kernel checks (runs #40776559885 and #40777507076).

## Precise non-claims

- The 140805 coefficient-window survivor is **not** asserted to be a digit-two-free power. It only survives **30 specified coefficient trits**.
- The theorem covers unbounded \(s\) but bounded multiplier \(u\). The full Erdős theorem requires every nonexceptional exponent, including unrestricted \(u\).
- A successful V5 comparator that only builds and scans for \`sorry\` is not an unconditional kernel theorem; no such full result is claimed here.
- The residual-Ω termination and natural-path rigidity implications remain the specific final mathematical obligations.
