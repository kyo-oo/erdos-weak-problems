# WORKLOG — W76-142K (the correction wave, Erdos #142 sublinear close)

## Events

- E00: brief read; the W75 bank read (SUBLINEAR_PROOF.md sections 1-5 closed, section 6 open); the commander's NEW_LAWS_142.md v2-corrected architecture received (the dilution kill: ONE fixed ambient group, localized windows, relative densities).
- E01: the V2 engine battery run: EP-CK/POP-CK/ITER-CK-2/V-CK-2 — two bugs found+fixed (c0sym scale: C is the F-correlation, C_0 = p*M(p-M); the p>1009 T2 scan summed only differences in B). 196/196 GREEN.
- E02: SUBLINEAR_PROOF_V2.md written (v2: the interval pair-bound termination) — REFUTED MY OWN L-PB-INT in writing (r_3(26)=9: 6*C(9,2)=216 > AP(26)=156 — the incidence direction was backwards). v3 (table-termination) — the window is not forced down; the small-L ratios (up to 1.0 at L=2) break the firing lemma below 38. v4: L-TERM discovered (the demand-vs-possible inconsistency at delta_c = 0.6096) — the windowed application meets the transfer dilution; THE UNION FIRING LAW settles it: delta* = 0.81, table fires L in [3,48] (max ratio 0.8), mesh fires L >= 49 (cap 0.659).
- E03: THE W75 LEMMA I CONSTANT CHAIN FOUND BROKEN (2*pi/M >= 0.196*delta vs the claimed delta^2/16 = 0.0625*delta; sum|f| = 2*delta*(1-delta)*p not delta*p — the error exceeds the main term at every delta). REPAIRED: M = ceil(128/delta), Re >= kappa*p/2, error <= (pi/32)*delta^2*p < delta^2*p/8 — and the repaired chain has NO delta <= 1/2 ceiling. Probe I-CK-HI certified delta in [0.52, 0.70] at p in {1009, 2003}: 14/14 green.
- E04: engine142v2_extra.py written (firing/bp/pb/mesh/ickhi/df/law lanes; bugs fixed: int64 overflow in np.dot(C,C) -> Python-int squares; Fraction float overflow -> log10(int); the exhaustive small-p enumeration -> max-size DFS; the arc probe's density construction fixed to symmetric arcs). FINAL: 264/264 PASS, 0 FAIL.
- E05: LAW-SPEC 23/23: every arsenal law read at its file:line with the statement quoted (the combination table is real).
- E06: THEOREM SUBLINEAR closed: N0(eps) = 480*(1024/eps)^(ceil(13300/eps^2)+2), the union firing law, DF-CK 4/4. SUBLINEAR_ENGINE_V2_GREEN=1 + EXTRA_LANES_GREEN=1.
- Sandbox note: the mid-round sandbox wipe killed the first worktrees; everything re-derived from the pushed bank (81537c4) — the progress-pack law saved the lane.

The engine never stops; it never lies. In English, always.
