# WORKLOG — W77-142E (ENGINE lane, Erdős #142, wave W77)

Lane: 142E (the ENGINE extensions). Brief: W77_BRIEFS/142E.md (binding).
Worktree: /home/z/waves/w77-142e @ 06fe8b8 → w77-142e branch.
Discipline: ENGINE_CHARTER (two-method law, UNSAT twice, timeouts never UNSAT,
negative controls, receipts for everything, push at every milestone).

---

## SESSION 1 (resume of the interrupted first strike)

**State found on entry** (untracked `experiments_v3/` from the first strike of this
wave, reaped mid-run by the sandbox — the checkpoint law saved it):

- `engine142table_v3.py`, `bnb142v3.c` (+ built binary), `checker142libv3.py`,
  `laws142lib.py` — the W77 v3 engine stack, complete and self-tested.
- `ckpt_table_v3.json`: **k=3 cells N=49..57 all CERTIFIED-BOTH** (Z3 bisection
  SAT@v + UNSAT@v+1 ×2 seeds; C BnB forced-0 + no-force agree; third checker on
  both witnesses; OEIS A003002 match). Values:
  49→16, 50→16, 51→17, 52→17, 53→17, 54→18, 55→18, 56→18, 57→18.
  Anchor N=48 (banked, value 16) re-validated. The push was cut at N=57 by the
  sandbox reap (no stop_reason, `done: false`) — NOT a budget stop.
- BnB batch artifacts: `bnbv3_k3_1_48.jsonl` (banked column reproduced 1..48),
  `bnbv3_k4_1_28.jsonl` + `bnbv3_k5_1_28.jsonl` (forced-0), and the no-force
  cross-runs for 21..28 — all values match OEIS A003003/A003004 21..28.

**Environment audit**: z3 5.4.1 ✓, gcc 14.2.0 ✓, gmpy2 2.3.2 ✓, sympy 1.14.0 ✓,
numpy 2.1.3 ✓, 2 cores ✓. pysat was NOT installed (contrary to the environment
note) — installed this session: `python-sat 1.9.dev24` (Minisat22, Glucose3,
Cadical153 verified on a planted-UNSAT smoke case). pysat becomes the bonus
THIRD solver layer on top of the binding brief discipline (Z3 + C BnB + checker
+ OEIS).

**Plan for this session** (per the brief, in order):
1. Commit the first-strike artifacts (protect cells 49..57). [DONE — see commits]
2. COMPONENT 1: resume the k=3 push to N=64 (or the furthest certified frontier
   within the 20-min cell budget).
3. COMPONENT 2: k=4 and k=5 pushes N=21..28 (first full two-method certs there).
4. COMPONENT 3: model-step escalation — k=3 no-wrap at p ∈ {10007, 65537};
   the k=4 model-step law (internal 4-APs of P(a,d,L) == integer 4-APs of
   [0,L-1] for L ≤ ⌊√p⌋, threshold (p+3)/2, both wrap directions), dual-method.
5. COMPONENT 4: the k=4 second moment — 18 cells (δ ∈ {0.3,0.5,0.7} ×
   N ∈ {10³,10⁴} × {interval, random, Beatty}), quartic identity SM-1',
   CS bound SM-2', spectral SM-3', popular SM-4', Stanley 4-AP-free controls,
   dual-counted.
6. NEW_CLAIMS.md additions; receipts142e_w77.txt; push at every milestone.

**Event log (append-only):**

- [S1.0] Entry audit: checkpoint k3 49..57 CERTIFIED-BOTH intact; environment
  verified; pysat installed as bonus third solver.
