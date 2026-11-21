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

## C. THE CURRENT MISSION (S078)

TARGET: Erdos #406 ONLY — crack the `hTailF` hypothesis completely (BOSS order,
standing). The hypothesis = `the_act` = the even-exponent half = CAP(185)-class.
State after S078 (the assault round): the S077-named lane #1 CLOSED (Kernel 71
AntiCluster406.lean: the census bridge + THE FIRST INFINITE-FAMILY
ANTI-CLUSTERING LAW — dust j's edge window = {0,1,4} at EVERY level; the deep
level-uniform form j >= 315); Kernel 72 DustFamily406.lean (THE FIVE EXACT
FAMILY LAWS: fam7 = 0, fam1 = 2^(j-2), fam4 = 2^(j-2), tower = 2^(j-1),
mod3two = 0, every level forever); the assault engines (assault406.py +
assault406b.py: W's trits, THE THREE MIDDLE-THIRD PI-POINTS 2*W*pi = -7/-1/+5
in Z_3 — all three NON-NATURAL 3-adics; the shadow dust = 2 classes per family
with the pi-point always present; the window increment law); battery406d.py
6/6 GREEN; the official comparator 25/25 PASS ("YOUR SOLUTION IS OKAY",
ledger 18 claims). The kill chain remains CAP(185) alone. The named next
lanes: (1) THE PI-POINT LANE (prove no natural core carries the full shadow
package — kills the tower family's package carriers; the three fixed points
are non-natural 3-adics), (2) the entropy law v2(n) <~ k*log2(eM/k) + O(1),
(3) Frame W (the 3-adic logarithm tower decomposition).
Reading: COMPLETE_PROOF.md sections 0-12, WORKLOG_S074-S078, CapLaw406.lean
(Kernel 68), DustLaw406.lean, TwoAdic406.lean (Kernel 70), ExtraLaws406.lean
(Kernel 69), AntiCluster406.lean (Kernel 71), DustFamily406.lean (Kernel 72),
Erdos406Ternary.lean (Kernel 38 census).
Constraints: BOSS's theorems ONLY (Arsenal + repo kernels), GitHub CI for Lean
(NEVER local Lean install), DeepMind comparator (challenge + solution) directly,
English only. NEVER forget: run backup.sh before ending any session.

The engine never stops; it never lies. In English, always.
