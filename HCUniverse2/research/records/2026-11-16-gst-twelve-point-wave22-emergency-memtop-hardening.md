# 2026-11-16 — THE TWELVE-POINT WAVE 22: THE EMERGENCY MEM_TOP PAIR + THE TOOLCHAIN HARDENING

## Target

Two items, one push:

1. **The emergency repair (W22-D's audit find):** the wave-21 commit db8feaed
   claimed the two HodgeData `mem_top` arity fixes but never landed them —
   the W21-A/W21-C ownership gap.  `rationalHodgeSubspace_of_top`'s two
   closers (`exact Submodule.mem_top m` / `exact Submodule.mem_top _`, at
   :301/:304 in the wave-21 file) are the verbatim run-20 killers: at the pin
   `Submodule.mem_top` takes its element IMPLICIT
   (Mathlib/Algebra/Module/Submodule/Lattice.lean:143, `@[simp] lemma
   mem_top {x : M} : x \u2208 (\u22a4 : Submodule R M)`) — the applications are
   arity-wrong, a deterministic CI failure.  **The fix:** the bare form
   `exact Submodule.mem_top` (the element unifies from the goal at default
   transparency — the same bare form W21-C shipped at Landing:145/:300 and
   FoldWord:806).
2. **The toolchain hardening (W22-A):** run 43915904584 attempt 1 died at the
   elan-install step — the elan-init.sh script's internal
   `releases/latest/download` tarball fetch 403'd on BOTH script mirrors
   (they are byte-identical scripts with the same hardcoded URL — the
   "fallback" was fake redundancy).  The hardened step pins elan v4.2.4,
   downloads the tarball directly (bypassing the script's flaky download
   line), retries 3x per mirror across 2 genuinely distinct mirrors, and
   fails loud.  Fault-injection tested in-sandbox (happy path / mirror-1-dead
   failover / total failure).

## The wave-21 correction

The wave-21 record claimed 8-of-8; the truth is 6-of-8 (the record now
carries the correction section).  The audit wave (W22-D) caught the gap
BEFORE the attempt-2 verdict wasted a full adjudication cycle on a known
failure — the structural gate gains a claim-vs-diff clause from this wave on.

## Agent accounting (the W7 wave)

- **W22-A** — the toolchain hardening (delivered; the mirror table verified
  from this sandbox; the diff rides this push).
- **W22-B** — the CI watch (died at the context deadline; the commander
  took the watch).
- **W22-C** — the FoldWord geometry recon (died at the context deadline;
  the mission stays queued for the next wave).
- **W22-D** — the wave-21 adversarial audit (delivered: items 1-4 PASS with
  pinned evidence; item 5 the BLOCKER find — the unshipped mem_top pair;
  the ownership-gap root cause and the claim-vs-diff gate lesson).

## Disclosure

No kernel verdict for wave 22 at this record's write time.  The wave-22 push
(mem_top pair + yml hardening + the record correction) fires the lane; the
attempt-2 run on db8feaed (if it completed before this push) adjudicated the
six shipped wave-21 kills only.  Tiers 5-6 (FoldWord, Landing) remain
never-elaborated, one green step away.
