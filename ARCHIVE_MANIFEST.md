# ERDOS CAMPAIGN — FULL ZIP BAG (S059)

Sealed: 2025-11-13 · Git HEAD: `fa4a160` · Branch: `campaign` · Remote: https://github.com/kyo-oo/erdos-weak-problems.git
Remote == Local verified at seal time (zero-loss confirmed).

---

## 1. WHAT IS IN THIS BAG

```
erdos-campaign-zipbag.zip
├── MANIFEST.md                 ← this file (inventory + restore guide)
├── erdos-weak-problems/        ← THE FULL CAMPAIGN REPO (incl. .git — complete 217-commit history)
│   ├── Arsenal/                    BOSS's own mathematics (ErdosTernary2/Basic.lean, CardinalWorlds.lean, CardinalWorldsV2.lean)
│   ├── problem*/                   47 problem folders — every engine, battery, census, witness, Lean kernel, CI error log
│   ├── bulldoze/                   the bulldoze wave (261 towers, 271 Stanley A2, 404 padic kernel)
│   ├── .github/workflows/kills.yml the GitHub CI verification pipeline
│   ├── WORKLOG.md                  3,474-line full campaign war diary
│   ├── THE_CORE.md / THE_LIST.md   campaign laws + the 39-problem target list
│   └── README.md / CAMPAIGN_ROUND3.md / S032_NEW_VOLLEY_ROUND1.md / EVIDENCE_306.txt
├── skills/
│   ├── MATHS_SKILL.md          ← SKILL #1: the MATHS Berserker protocol (persona engine)
│   └── PROVE_THAT_SHIT_SKILL.md ← SKILL #2: the prove-that-shit workflow engine (selection gate → research loop → adversarial audit)
├── secrets/
│   └── ghtoken.txt             ← BOSS's GitHub token (CI push access — PRIVATE, do not leak)
└── dashboard/
    └── page.tsx                ← Command Center dashboard source (GREEN_KERNELS / IN_FLIGHT / LAWS board)
```

## 2. CAMPAIGN SCOREBOARD AT SEAL TIME

| Metric | Count |
|---|---|
| Problem directories | 47 |
| Lean files | 149 |
| Lines of Lean | 54,820 |
| COMPLETE_PROOF.md writeups | 14 |
| DERIVATION documents (.md/.tex) | 19 |
| Python engines/batteries/censuses | 169 |
| Git commits (full history in .git) | 217 |
| Green kernels (K46 Pell/Størmer base, K47 #961 census, K53 #677, K54 #348, K55 #274, K58 #961x2, K59 #273, K60 #939, K62 #708, K63 #317, K64 #289, + CI-green assembly line) | 18+ kernels green on GitHub Actions |
| CI verification | GitHub Actions only (kills.yml), run 43289917121 = SUCCESS, all later verdicts logged in WORKLOG.md |

Key math achievements sealed inside:
- **#961 Pell/Størmer machine**: K46 `pell_compose` Brahmagupta identity + descent engine (axiom-clean: `[propext, Quot.sound]`), K47 census board (40 smooth-11 witness pairs, frontier chain 5_97), exclusion layers.
- **#317 signed harmonic**: full n!-cross-multiplied machinery, minimal-value classification n=5/6/7 (decide sweeps 243/729/2187 codes), Theorem-A mod-5 mechanism.
- **#261 funnels/Stanley**: C-engine certificates (29MB run261 corpus), funnel structure laws.
- **#203 Sierpiński-23**: L=27720 family exhausted (41 members, budget 1.0563), 55440 engine (52 members, budget 1.1628), v5 anneal checkpoints.
- **#1056 factorial intervals, #686 Pell ratio, #1063 binomial frontier, #404 q3-chain, #1212, #711, #282, #289, #389, #394, #451, #461, #1072, #1073, #1074, #1108** — engines, batteries, witnesses, Lean kernels, all inside.

## 3. THE TWO SKILLS (BOSS's order: "2 skill list")

1. **MATHS** (`skills/MATHS_SKILL.md`) — the Berserker persona: one-round law, meta-thinking protocol (Third Eye + War Council), verification law, delivery gate.
2. **prove-that-shit** (`skills/PROVE_THAT_SHIT_SKILL.md`) — the workflow engine: tractability selection, problem-specific proof prompts, attempt→audit→repair loops, durable artifacts.

Activation chain (LAW): MATHS first (persona), then prove-that-shit (engine), then finish in the same round.

## 4. THE TOKEN

`secrets/ghtoken.txt` — the GitHub access token used for all campaign pushes.
Usage: `git push https://x-access-token:$(cat ghtoken.txt)@github.com/kyo-oo/erdos-weak-problems.git campaign`

## 5. RESTORE / RESUME GUIDE

1. Unzip anywhere: `unzip erdos-campaign-zipbag.zip`
2. Resume the repo with full history:
   ```
   cd erdos-weak-problems
   git status                      # clean at fa4a160
   git remote -v                   # origin → github.com/kyo-oo/erdos-weak-problems.git
   git log --oneline | head        # 217 commits intact
   ```
3. CI: push any commit to `campaign` branch → `.github/workflows/kills.yml` runs Lean verification on GitHub Actions. **NEVER compile locally.**
4. Skills: copy `skills/*.md` into any agent's skills folder (structure: `<skills-dir>/MATHS/SKILL.md`, `<skills-dir>/prove-that-shit/SKILL.md`).
5. Dashboard: drop `dashboard/page.tsx` into a Next.js App Router project as `src/app/page.tsx`.
6. Read `erdos-weak-problems/WORKLOG.md` tail for the exact battle state (S058 W58-E repairs + S059 seal).

## 6. INTEGRITY

- Zip verified with `unzip -t` (all entries OK).
- SHA256 of the zip recorded in the delivery report.
- Git: remote HEAD `fa4a1606da4d7c4f8e4840bed00936c974137c70` == local HEAD == the repo inside this bag.

The engine never stops; it never lies.
