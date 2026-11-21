# SANDBOX PROTECTION SYSTEM — MASTER RESTORE RUNBOOK (S077)

**The law: NO PROGRESS IS EVER LOST.** Even on a COMPLETE sandbox reset, everything
survives in two external vaults:

1. **PROGRESS VAULT = GitHub** — `kyo-oo/erdos-weak-problems`, branch `campaign`.
   Every seal, every kernel, every worklog, every CI verdict. The full history.
2. **TOKEN VAULT = the Drive bag** —
   `https://drive.google.com/file/d/1ZCY5hbZyId7AWeBD-o0yOiRFlxGmKnW-/view?usp=sharing`
   (the 27.5 MB zip: skills + token + repo snapshot at seal time `fa4a160`).

---

## A. FULL RESTORE PROCEDURE (fresh machine, from zero)

```bash
# 1. Get the token (from the Drive bag; confirm-token form may be required):
#    Drive id: 1ZCY5hbZyId7AWeBD-o0yOiRFlxGmKnW-
curl -sL "https://drive.usercontent.google.com/download?id=1ZCY5hbZyId7AWeBD-o0yOiRFlxGmKnW-&export=download&confirm=t" -o bag.zip
unzip -o bag.zip -d /tmp/bag
mkdir -p /home/z/my-project/.secrets
cp /tmp/bag/erdos-zipbag/secrets/ghtoken.txt /home/z/my-project/.secrets/ghtoken.txt
chmod 600 /home/z/my-project/.secrets/ghtoken.txt

# 2. Clone the LATEST campaign branch (the progress vault — ALWAYS fresher than the bag):
cd /home/z/my-project
git clone https://github.com/kyo-oo/erdos-weak-problems.git erdos-weak-problems
cd erdos-weak-problems && git checkout campaign

# 3. Re-arm the push channel (token NEVER printed, NEVER committed — repo is PUBLIC):
TOKEN=$(cat /home/z/my-project/.secrets/ghtoken.txt | tr -d '[:space:]')
git remote set-url origin "https://x-access-token:${TOKEN}@github.com/kyo-oo/erdos-weak-problems.git"

# 4. Read the war memory: WORKLOG_S076.md (latest), THE_LIST.md, THE_CORE.md, this runbook.
# 5. Re-arm the protection engine: /home/z/my-project/backup/backup.sh + cron guardian.
```

## B. THE PROTECTION ENGINE

- `/home/z/my-project/backup/backup.sh` — seals ALL uncommitted work, pushes campaign,
  refreshes the `sandbox-vault` branch. Run after every deliverable and before any
  long compute. `ghtoken.txt` chmod 600, NEVER in git.
- **Cron guardian**: automated backup turns (fixed_rate, 8h) — the engine fires even
  if the session forgets.
- **Anchors**: this runbook lives at `/home/z/my-project/BACKUP.md` AND is committed to
  the `sandbox-vault` branch on GitHub AND referenced in every WORKLOG header.

## C. THE CURRENT MISSION (S077)

TARGET: Erdos #406 ONLY — crack the `hTailF` hypothesis completely (BOSS order,
standing). The hypothesis = `the_act` = CAP(185)-class = the even-exponent half.
State after S077 (the war-council round): LX (the S076-named popcount-cap
conjecture) is REFUTED (1603072 = 3^0+3^7+3^8+3^13 = 2^9*3131, popcount 4,
v2 = 9 > 8); Kernel 70 TwoAdic406.lean banks THE 2-ADIC BUDGET TOWER + THE
RIDER TOWER + the pairing laws + the refutation receipts; DustLaw406 healed
(dust_edge banked — the census-composition lane armed); the official
comparator gate 21/21 PASS ("YOUR SOLUTION IS OKAY"). The named next lanes:
(1) the census bridge (noTernaryTwo form of the Kernel-38 census -> composes
with dust_edge into the first infinite-family anti-clustering law); (2) THE
ENTROPY LAW v2(n) <~ k*log2(eM/k) + O(1) (the LX successor — rider-killing
if proven); (3) Frame W (the 3-adic logarithm tower decomposition).
Reading: COMPLETE_PROOF.md sections 0-11, WORKLOG_S074-S077, CapLaw406.lean
(Kernel 68), DustLaw406.lean, TwoAdic406.lean (Kernel 70), ExtraLaws406.lean
(Kernel 69), Erdos406Ternary.lean (Kernel 38 census).
Constraints: BOSS's theorems ONLY (Arsenal + repo kernels), GitHub CI for Lean
(NEVER local Lean install), DeepMind comparator (challenge + solution) directly,
English only. NEVER forget: run backup.sh before ending any session.

The engine never stops; it never lies. In English, always.
