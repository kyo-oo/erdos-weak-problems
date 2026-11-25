# WORKLOG S089o–S089p — THE LIVE-STREAM INSTRUMENT, THE THRASH DIAGNOSIS, THE RATCHET LAW

**Session context:** continuation after context reset; battlefield state recovered
from the git witness (S089n head 2b0763a, profiler probe deployed, verdict pending).

## S089o — THE INSTRUMENT CALIBRATION (local, zero CI cost)

The S089n profiler probe was calibrated post-mortem with a local elan install
(lean4 v4.33.0-rc2, core-only, mathlib-free) and found **DEAD ON ARRIVAL**:

1. **LEAN 4.33 BATCH MODE IS FULLY BUFFERED.** A 300k-declaration file killed
   mid-run through a pipe yields ZERO output — not the elaborated defs, not
   interleaved `#check` markers, nothing. `set_option profiler true` emits NO
   per-declaration `took` lines AT ALL — only a cumulative end-of-process
   summary ("cumulative profiling times: elaboration Xms, parsing Yms, ...")
   that dies with the process. SIGTERM and SIGINT flush nothing.
   **Corollary (campaign law): every historical "silent burn" log —
   S089k's 998s GhostHalf, S089m's 674s/688s word burns, S089n's 9m10s —
   carried ZERO information. The silence was the buffering, not the module.**
2. **THE WEAPON THAT WORKS: `stdbuf -oL -eL`.** LD_PRELOAD line-buffering
   propagates through lake to the lean grandchildren. Calibration: a killed
   lean streamed 4 marker lines with stdbuf vs 0 without. All 20 build
   commands in pins406.yml wrapped — reaper exit-143 kills can no longer
   destroy evidence.
3. **THE /PROC WATCHDOG:** 15s-tick `pgrep`-locked telemetry (read_bytes,
   VmRSS) of the live lean process, echoed by bash (streams regardless of
   lean's buffering). Deployed on both word jobs.

## S089o — THE CHAIN-CACHE REPAIR

All 10 jobs saved under ONE key (`pins406-OS-<sha>`); actions/cache is
**first-save-wins**, so only the spine's oleans ever propagated — every
downstream job would have silently rebuilt its predecessors (latent bug,
never surfaced because no run ever passed the word modules). Keys are now
per-job (`pins406-OS-<JOB>-<sha>`) with three-tier restore: exact job →
chain prefix (`pins-`/`ghost-` via `startsWith`) → global.

## S089o — THE FIRST INSTRUMENTED VERDICT (run 45716163527, head 5f43285)

Cold pool (zero concurrent runs — the S089m pool-saturation theory tested
and DEAD). Both word jobs killed at 11.8/13.9 min by runner shutdown —
but the instruments finally spoke:

- **Imports load FAST:** RSS 7.9→13.8GB in ~2 min, plateau by minute 3.
  The "5-7 min import load" belief was wrong.
- **The elaboration was ALIVE:** a 316MB read burst at lean-minute ~4
  and a 1GB burst at minute ~7 with RSS churn 9.9→14.8GB. Defs produce
  no messages — the silence was WORK, not death. The module was ~90%
  elaborated at kill time.
- **THE THRASH DIAGNOSIS:** RSS ~15GB on 16GB runners with the 10GB swap
  shield = swap-in storms (the read bursts) = elaboration at ~10% speed.
  The module is not slow; it is drowning.
- **native_decide is INNOCENT:** local microbenchmark — 20 receipt-scale
  sites (3^61-modular arithmetic on 29-digit constants) elaborate in
  0.33s total.
- **The reaper is the hosted platform stopping the runner service** of
  memory-heavy (~15GB RSS) jobs at ~9-11 min of lean life, stochastically
  (same-runner-label 46-50-min monolith builds survived 3/3 in the S089h
  era; GhostHalf went green once in S089k).

## S089p — THE RATCHET LAW

Per-job cache keys make every green module **permanent** (its olean banks
under its own key; same-sha reruns replay it). `rerun-failed-jobs` therefore
**ratchets**: green modules never re-elaborate, the frontier module re-rolls
its survival dice each attempt. The autonomous ratchet loop
(`/home/z/ratchet.py`, log `/home/z/ratchet.log`) polls the run, classifies
failures (reaper kills retried; REAL failures — compile errors, now visible
via stdbuf — stop the loop for repair), and fires rerun-failed-jobs until
green. Repo is PUBLIC: standard runners are free; retries cost only time.

**The scoreboard this round:** no new kills claimed; the CI-carrier war for
the chamber's first full green advanced from "blind" to "instrumented,
diagnosed, and convergent."
