# WORKLOG_W77_142K — Wave 77, Lane 142K (commander-absorbed; the LOGDECAY round)

Branch: w77-142k. English only. The dispatch channel was down at wave
release (all six Task launches returned "context deadline exceeded" — the
S076/S058 failure mode); per the S058/S076 precedent the commander
absorbed the lane directly. Every event:

## Events

1. **Brief + bank read.** W77_BRIEFS/142K.md (own authorship, vaulted at
   campaign 06fe8b8); the bank: SUBLINEAR_PROOF_V2.md (the explicit
   tower N ≥ 480·(1024/eps)^(⌈13300/eps²⌉+2), eps ∈ (0,1/8]), the L-EP /
   L-NW / L-BP / UNION-FIRING / L-TERM stack, receipts 264/264.

2. **The inversion derived by hand before any code.** The exact identity
   13300/eps² = L/(2ℓ) at eps = √(26600·ℓ/L) (since 13300·2 = 26600);
   the exponent bound ⌈x⌉ ≤ x+1; the log bound ln(1024/eps) ≤ A + ℓ/2;
   the sandwich: coefficient 3/4 − A/(2ℓ) ≥ 0.55, ℓ ≤ L/1000, giving
   (∗) with margin 2.194·10⁷ at L₂ = 4·10⁷. Both monotonicity arguments
   carry explicit derivative signs (h′(L) > 0 for L > 1,702,400;
   (ln L)/L decreasing for L > e).

3. **engine142logdecay.py written and run.** 60-digit precision (mpmath
   via sympy); Method A (exact chain) + Method B (direct tower with the
   exponent as an exact integer, precision-guarded at 10⁻⁴⁰); 200-point
   geometric grid + extremes to 10¹²⁰; negative controls at L = 10⁶
   (eps = 0.606 > 1/8 — banked theorem inapplicable, chain correctly
   fails) and L = 2.9·10⁷ (below the eps-boundary L* ≈ 2.9268·10⁷).
   BUG (minor, caught in-round): mpf does not accept :.0f formatting —
   receipt line fixed; the mathematics was unaffected.

4. **RESULT: 19/19 GREEN. THEOREM LOGDECAY certified.**
   r_3(N) ≤ √26600·N·√(ln ln N/ln N) for every N ≥ ⌈exp(4·10⁷)⌉.
   The first polylog-saving law in-package.

5. **LOGDECAY.md written** (the complete proof: Steps 1–4, the sandwich,
   the engine certificate, the arsenal combination — 6 new citations on
   top of the input law's 39).

6. **NEW_CLAIMS.md appended** (C142-LOGDECAY in the comparator schema).

7. **Lane sealed:** commit + push w77-142k.

## The mathematics that closed the lane (summary)

The banked SUBLINEAR tower already CONTAINED the polylog shape —
extracting it required: the exact rational identity 13300/eps² = L/(2ℓ)
(making the exponent explicit), the ceil discipline, two monotone
sandwiches with derivative-signed proofs, and a dual-method 60-digit
engine. Pure combination, as ordered: banked law + exact arithmetic =
new law. Next lanes on this front: the increment-shape push (LOGPOWER —
the L-EP re-analysis for the (log N)^{-c} shape) and the k=4 foundation
(R4-VARN).

The engine never stops; it never lies. In English, always.

## W77-142K KILL 3 (R4-VARN) — LANDED
- engine142r4.py written + run all parts GREEN (receipts142r4varn.txt).
- r_4(M) certified M=1..16 exhaustive (first k=4 stone).
- R4-VARN proven with explicit constants: delta >= 0.85 at N=1000,
  c_4(1.00) >= 1.108e-3, plug-back 40/40 both codes.
- Divisor law: analytic M0(M0-1) < M0^2; empirical worst 7 (N=200, sampled).
- Model-step data banked for the amplification front.
- KILL 2 (LOGPOWER) documented as the named front (LOGDECAY banked at 2c00992).
