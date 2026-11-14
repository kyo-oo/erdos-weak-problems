# W64-B ROUND STATUS — Erdős #708 (Task W64-B, worktree w63-d1-p708)

## THE ROUND TARGET
Kernel62 (#708) CI-green on my branch: the g(4) box master
(`erdos708_g4_master`: construction + exclusion + exact row on the
1365 x 40 census box) surviving the CI, plus the kernel61 guard sync.

## RUN 43589088597 POST-MORTEM (the diagnosis)
- kernel-a, kernel-b: SUCCESS. kernel-c: FAILURE — the ONLY annotation:
  "The hosted runner lost communication with the server" — the RUNNER ITSELF
  died (OOM/starvation mode), NOT a Lean error, NOT a step exit-code.
- Job ran 11:54:11Z -> 13:04:12Z (70 min) vs the healthy kernel-c baseline
  13.6 min (run 43598294749, branch w63-a1-p411, old Erdos708.lean).
- Root cause: `e708_g4_box_exact`'s 54600-instance AGGREGATE decide at the
  32M-heartbeat override (commit ae020570) — the elaborator ground ~60 min
  on the elaborator-whnf of the giant `List.all` chain over
  `coverExact` DFS calls and the runner died. The heartbeat raise REMOVED
  the deterministic-timeout guard-rail (4M default, run 43585957179) and
  converted a clean failure into a runner death.
- Cross-evidence: r9 log (kernel-c-r9-full.log, run 43595452811,
  branch w63-a1-p411 b937f69a): kernel62 PASSED on the OLD pre-volley
  Erdos708.lean (47 s lean run, no box decide) — kernel62 CAN pass; the
  aggregate decide was the sole new load.

## THE REPAIR (this round, the NO-OOM restructure)
Replaced the aggregate decide with THE WITNESS-TABLE structure:
- `w708OK4` (+`w708OK4_spec`): the exactly-4 row checker (length = 4,
  ascent, window residency, divisibility) — the corpus's |B| = g(4) cell.
- `nthD708`: the bounded nth (default [] — misalignment FAILS loudly).
- `rowOK708`: p = (A, [B_1..B_40]) — the 40 covers of A at t = 1..40.
- THE DATA: 114 chunks (`wchunk708_0..113`, 12 A-rows = 480 instances
  per chunk, the <= 501 NO-OOM law), in EXACT box708 order; the full
  table `wrows708` = the append chain.
- THE CERTS: 114 chunk theorems (`e708_g4_chunk_k := by decide`, each a
  bounded elaborator decide at the 4M default), assembled by
  `e708_all_append` (self-proven core-only) into `e708_g4_rows_exact`.
- THE ALIGNMENT CERT: `e708_wrows_dom : wrows708.map Prod.fst = box708`
  (kernel-decided — the data cannot drift from the computed box).
- THE BRIDGE: `e708_g4_box_exact` — THE ORIGINAL AGGREGATE STATEMENT,
  VERBATIM — now proven from the table via `List.all_eq_true.mpr` +
  `List.mem_map` + `w708OK4_spec` + `e708_exact_enum_complete`.
  §14-§17 (corpus, exact-2_3_4_5, the MASTER, box_max, receipts)
  UNCHANGED — the whole dependency tree below box_exact is untouched.
- The 32M-heartbeat override is GONE; file-wide 4M default governs all.

## DUAL-METHOD VERIFICATION (local, Python)
- gen708_witab.py: the coverExact DFS mirror (Lean def transcribed
  literally, take-first) hunted all 54600 witnesses: 0 failures;
  each emitted row independently rechecked (subset-of-window + length +
  ascent + gmpy2 divisibility): 54600/54600 GREEN (g4_witgen_out.txt).
- Parse-back self-check: the FILE's own emitted data re-parsed and the
  rowOK708 semantics re-simulated: 54600 instances, 0 failures; the
  A-column equals box708's exact order.
- Witness-element checksum (determinism): 5500392.

## THE GUARD SYNC (kernel61's masked CI-guard defect)
- kernel61's names-grep greps 'E411.' but the namespace is 'Erdos411'
  (never exposed before because compile errors always failed the step
  first; fixed on w63-a1-p411 eadcfb4e + banked green at 1aab7fe,
  run 43598294749).
- COMMANDER-AUTHORIZED SYNC executed:
  `git checkout w63-a1-p411 -- .github/workflows/kills.yml
   problem411-iterated-totient/Erdos411.lean` (the full green state).
- kernel62's own guard EXTENDED with the g4-master receipts:
  `grep -F "E708_G4_MASTER_GREEN"` + the five-name
  `E708.(e708_g4_box_exact|e708_g4_box_corpus|e708_exact_2_3_4_5|
   erdos708_g4_master|erdos708_g4_box_max)` axiom-print grep — the
  dual-direction master structure is now CI-grepped directly.

## CI VERDICT
**GREEN — run 43602748433** (kernel-c SUCCESS 14:22:20Z, kernel62 GREEN with the
five-name master axiom-prints + E708_G4_MASTER_GREEN receipt; see STATUS_W64.md,
the round report of record). One intermediate failure first: 43600972276 died on
a single stacked-doc-comment parse error (1595:69), fixed by 064806a.
