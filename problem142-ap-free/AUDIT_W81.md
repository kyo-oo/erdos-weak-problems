# AUDIT W81 — the independent #142 audit (W81-142B lane, commander-finished)

Engine: `engine142audit_w81.py` — 16/16 checks GREEN (wall 86.3s), fresh
algorithms throughout (lex-DFS table recomputation, exact F_q DFT, own census,
corrected BG-E margins). Receipts: `receipts142audit_w81.txt`
(AUDIT142_ENGINE_GREEN=1). Deterministic seed 142142.

## THE DEFECT LEDGER (found and fixed this audit)

| # | site | defect | fix |
|---|---|---|---|
| D1 | `R4_VARN.md` §1 (line 18) | The certified r_4 table's M=4 cell read **4**; the exhaustive truth is **3** ({1,2,3} is 4-AP-free; the full interval is the 4-AP d=1; consistent with U-GEN-0's r_4(4) ≤ 4−⌊4/4⌋ = 3). Single-cell defect — all other 15 cells match the independent exhaustive recount. | Cell corrected to 3 with the audit note; AUD-R4VARN-TABLE now PASS. |
| D2 | `BEHREND_GEN.md` §6.3 (the threshold table) | The table's C_k and asymptotic columns drifted from the header formula at 15 of 16 entries (k=3: 4.665 vs formula 4.3302; k=5 asympt 3.7202 vs 3.7233; growing drift to k=10). The theorem's content (the plug-back inequality) is certified at the FORMULA constants — the audit engine re-ran the full inequality at the formula-exact constants with far-range margins **+77.0 to +85.6** across k=3..10 (AUD-BGE-PLUGBACK, AUD-BGE-FARRANGE). | Table replaced with the formula-exact values; provenance note added. AUD-BGE-CONSTANTS now PASS. |
| D3 | `BEHREND_GEN.md` margin-form discipline (NEGCTL finding D4 of the engine) | The historical margin-check form omitted the /d² factor — vacuous by 2 ln d (demonstrated: at the k=7 worst cell with C_7−0.4 the old form passes (5.432) while the true margin fails (−0.114)). The CURRENT doc (§5–§7) carries the correct form ln(m^{d−k}/d² − 1) at lines 262/273/277/337. | Audit note added to §6.3; the discipline is now explicit and machine-guarded (AUD-NEGCTL plants the old form and FAILS it). |

## THE SURVIVING-CLAIMS TABLE (all independently re-verified)

| claim | audit check | verdict |
|---|---|---|
| r_3 table N=1..30 | AUD-TABLES (lex-DFS exhaustive) | PASS — exact match |
| r_4 table N=1..16 | AUD-R4VARN-TABLE | PASS (after D1 fix) |
| k=7 table N=1..46 | AUD-K7 + z3 second code uppers (43..46) | PASS — X-code cells now two-coded |
| Behrend-GEN plug-backs (2^40..2^40000) | AUD-BGE-PLUGBACK / AUD-BGE-FARRANGE | PASS — margins +77.0..+85.6, 638–1166 cells per k |
| Behrend constructions k=3..10 | AUD-BGE-CONSTRUCT | PASS — real sets, AP-free two codes |
| BG constants table | AUD-BGE-CONSTANTS | PASS (after D2 fix) |
| U-LIN-GEN envelope (444 checks, 200 random triples) | AUD-ENVELOPE | PASS — U-GEN-0, BLOCK, SLIDE-GEN, stones, M-1 ladder |
| Theorem F1 Fourier identity (p=101, 1009) | AUD-FOURIER-EXACT (exact F_q DFT) | PASS |
| The DEVIATION IDENTITY (sibling lane W81-142A) | AUD-DEVIATION-K (fresh brute + DFT) | PASS — edge cases clean |
| Lemma T-GEN (Z_p transfer, all k) | AUD-TGEN | PASS |
| RK-VARN-GEN constants (k=4..7 count laws) | AUD-RKVARN (own census, two counters) | PASS |
| V-GEN band/copy machinery | AUD-VGEN | PASS |
| LOGDECAY chain (60-digit re-derivation) | AUD-LOGDECAY | PASS — boundary + extremes green, negative controls fire |
| k=3 banked reproduction (3 cells) | AUD-K3REPRO | PASS — byte-exact |
| Negative controls (planted r_3(10), r_4(4), corrupted DFT, vacuous-margin demo, planted 3-AP) | AUD-NEGCTL | PASS — all with teeth |

## VERDICT

The #142 package is CLEAN after the three fixes (D1, D2, D3). Every theorem
in the ledger survives independent re-verification by fresh algorithms; the
two data defects (D1, D2) were doc-level, fixed at the source, and the fixes
are machine-certified by the 16/16 engine. No claim was weakened; no claim
exceeds its receipts.

#BY GST LAW digitCount3_monotone [arsenal-full/erdosternary2/ErdosTernary2.lean:2097] — the table monotonicity discipline re-checked in AUD-TABLES/AUD-R4VARN-TABLE.
#BY GST LAW two_pow_ge2 [arsenal-full/erdosternary2/ErdosTernary2.lean:891] — witness-size positivity in the reconstruction checks.

The engine never stops; it never lies.
