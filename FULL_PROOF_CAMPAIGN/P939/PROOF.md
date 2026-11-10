# P939 — Erdős #939, r-powerful sums, r = 4 — FULL PROOF CAMPAIGN

## §0. TARGET
Erdős–Moll–Walsh r-powerful question, r=4: do there exist pairwise-coprime
4-powerful a, b, c with a + b = c? (n is r-powerful iff p | n ⟹ p^r | n.)

## §1. SUCCESS CONTRACT (BINDING)
COMPLETE = one of:
- **YES**: explicit a, b, c (fully factored, machine-certified: pairwise gcd's
  = 1, every prime exponent ≥ 4, a + b = c) — the construction/verdict.
- **NO**: an impossibility theorem covering ALL triples, proved with elementary
  toolkit (CRT/Pell/valuation/descent), no external machinery.
Weaker substitutes that do NOT count: restricted families (e.g. all-4th-powers
= FLT n=4), numerics-as-proof, "expected finitely many" heuristics.
If neither pole is reachable, deliver maximal rigorous advance + the exact
named wall (specific statement + why every available engine fails).

## §2. STATE ON ENTRY (from brief) — AND A CRITICAL CORRECTION FOUND (T+5min)
- Brief: "zero solutions ≤ 10^15 (5,622 4-powerfuls, 8.9M coprime pairs); r=3
  done externally (Nitaj/Cohn)."
- **AUDIT OF THE PRIOR HUNT (problem939-rpowerful/hunt939b.py)**: the
  generator `gen()` multiplies only by `q = p**4` repeatedly ⇒ it enumerates
  ONLY exponents e_p ≡ 0 (mod 4), i.e. PERFECT FOURTH POWERS {m^4 ≤ 10^15},
  m = 2..5623 = exactly 5,622 numbers. The pair test then checks sums against
  this same set ⇒ the "census" only verified Fermat's n=4 theorem
  (x^4 + y^4 = z^4 has no coprime solutions). **IT NEVER TOUCHED THE ACTUAL
  r=4 SEARCH SPACE** (4-powerful numbers with an exponent in {5,6,7} mod 4,
  e.g. 2^5 = 32, 2^5·3^4 = 2592, ...).
- True census size (to be computed): #4-powerful ≤ X = C4·X^{1/4}(1+o(1)),
  C4 = ∏_p (1 + p^{-5/4} + p^{-3/2} + p^{-7/4}) ≈ 12 ⇒ ≈ 68,000 ≤ 10^15,
  NOT 5,622. Expected #coprime-pair solutions ≤ 10^15 ≈ O(1) (to be
  computed exactly from the census) ⇒ the corrected brute force is a LIVE
  kill-shot, not a lottery.

## §3. STRUCTURE THEORY (engine for both poles)
- **Kernel decomposition (Lemma K)**: n is 4-powerful ⟺ n = s·m^4 with s
  4th-power-free and rad(s) | m. (v_p(n) = v_p(s) + 4v_p(m) ≥ 4.)
- **2-adic trichotomy (Lemma T)**: in any solution, either 16 | a and b, c
  odd, or 16 | c and a, b odd (v2(a+b) = 1 if a≡b odd·squares — squares mod
  16 are 0,1,4,9; odd+odd ≡ 2 or 10 mod 16). Both live.
- **Quality bound (Lemma Q)**: a+b=c pairwise-coprime 4-powerful ⟹
  rad(abc) ≤ (abc)^{1/4} ≤ c^{3/4} ⟹ abc-quality q ≥ 4/3 (known abc-hit
  territory, record q ≈ 1.63 — quality alone is NOT an obstruction).
- **Fermat wall (Lemma F)**: all three perfect 4th powers ⟹ FLT n=4 kills.
  Any witness needs ≥ 1 side with an exponent ≡ 5,6,7 (mod 4) prime.
- **Template A (square hypotenuse)**: if c = z^2 (all c-exponents even) then
  z is powerful and d1·x^4 + d2·y^4 = z^2 (kernels d_i, rad(d_i)|base) —
  genus-1 quartic ⇔ j=1728 twist E: V^2 = U^3 − 4aU (2-covering maps
  U = 2(v+u^2), V = 2uU verified on 1+8=9 ↔ (8,16) on V^2=U^3−32U).
- **r=3 mechanism (reconstructed)**: x^3+y^3 = (x+y)·N(x+yω); x+yω =
  (a+bω)^3 forces N = W^3 (Eisenstein cube), leaving x+y = F(a,b) =
  a^3+3a^2b−6ab^2+b^3 = NORM in the cyclic cubic field Q(ζ9)^+ (disc 729);
  second-layer norm-cube ⟹ j=0 twist rank. r=4 analogue: Q(√2) quartic norm
  layer × ζ5 cyclic-quartic norm layer ⇒ again elliptic (j=1728) — the
  algebraic lane is EC point search over kernel twists + powerful-z filter.

## §4. ATTACK REGISTRY (live)
1. Corrected brute force ≤ 10^15 (numpy int64, coprime-bitmask + membership)
   — RUNNING.
2. r=3 in-house hunt (witnesses + kernel statistics to steer r=4).
3. Deep kernel scan (big-int 4-powerful oracle via p^4-stripping + 4th-root
   residual test) to ~10^18–10^20.
4. Template A: kernel pairs (d1,d2), Pell orbits of d1X^2+d2Y^2=z^2 with
   X,Y square + z powerful; EC integer points on V^2 = U^3 ± 4d1d2U.
5. NO-lane: 2-adic/modular obstruction hunt (Lemma T analysis), descent
   attempts on structured sub-families.

## §5. LOG
- T+0: brief read, folders created, prior hunt audited ⇒ VACUOUS CENSUS
  discovered (major campaign correction). Corrected engine being built.
