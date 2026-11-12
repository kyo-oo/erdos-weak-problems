#306 STATUS — round-1 kernel (W56-2), branch campaign.

- LANDED: problem306-semiprime-egyptian/Erdos306.lean — 747 lines, namespace
  E306, header per spec (Arsenal 3-import, maxRecDepth 65536, maxHeartbeats
  4M), zero unproved obligations, receipt `E306_SEMIPRIME_GREEN` + 56
  `#print axioms` lines.
- DEFINITIONS: isPrimeSmall (trial division), isSemiprime (p ≤ q general),
  isSemiprimeD (p < q campaign class) + imp; 9 prime certs (2..23) via
  isPrimeSmall.of_bound (house omega/Nat.mul_le_mul pattern); 66 semiprime
  certificates (33 denominators × both forms) + e306_semiprime_law.
- REPRESENTATIONS LANDED (19 decide-certified identities, python-verified
  via Fraction arithmetic in hunt_w56*.py): 1/2 (9 terms, D=2730), 2/3 (21,
  D=9699690), 3/5 (13, D=510510), 4/5 (23, D=223092870), 5/6 (28, D=223092870),
  3/10 (8, D=30030), 2/5 (8, D=2730), 3/7 (7), 4/7 (10), 1/3, 1/5, 1/7, 2/7
  (3 each), 3/13, 3/11, 8/21, 3/14, 2/21 (2), 1/6 (1) + 18 distinctness laws
  (strict chains) + e306_rep_board / e306_distinct_board / e306_witness_board.
- STRUCTURE: semiprime_even (4 ≤ n), semiprimeD_six (6 ≤ n), split_lemma +
  4 amicable-triple decide certs (2,3,5 / 2,5,7 / 3,5,7 / 2,3,7), Arsenal
  bridge (isTernaryDigit_* + v2r_mul_three at anchor 21 = 3·7).
- OBSTRUCTION: no_rep_quarter_two — 1/4 has NO two-term distinct-semiprime
  representation (1/4 and 3/4 are structurally impossible under the campaign
  squarefree-b law, not engine misses).
- NOT LANDED this round: the UNIT 1 = Σ 1/n_i (DFS exhausted over windows
  ≤ 53; pair-reciprocal totals only ~0.90L up to ≤ 23, exact complement
  subset-sums hard) — round-2 path: MITM/LP or staged disjoint windows.
- Semiprime_density_floor SKIPPED per mission (needs Bertrand, round 2).
