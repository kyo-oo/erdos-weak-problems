#!/usr/bin/env python3
"""gen939R5.py — THE GENERATOR for Erdos939R5.lean (Kernel 60c, W66-P939-K).

TRUE-BOX witness-table kernel for Erdos #939 (r-powerful sums, r=4):
  TAB = certified 4-powerful census <= LIM = 2*B (B = 999706081460641),
  inTAB = split decision-tree membership (64 bucket defs, O(16)/query),
  residue-class sweeps (mod-16 gated, chunked decides),
  master: e939_box_census (membership form, no indices).
Every embedded number verified here first (the preflight law).
"""
import math, time
from sympy import primerange, integer_nthroot

T0 = time.time()
B = 999706081460641
LIM = 2 * B

def gen4(limit):
    r4 = integer_nthroot(limit, 4)[0]
    P = list(primerange(2, r4 + 2))
    out = []
    def rec(i, val):
        out.append(val)
        for j in range(i, len(P)):
            v = val * P[j] ** 4
            if v > limit:
                break
            while v <= limit:
                rec(j + 1, v)
                v *= P[j]
    rec(0, 1)
    out = [x for x in out if 1 < x <= limit]
    out.sort()
    return out

CEN = gen4(LIM)
TAB = [1] + CEN
print(f"census <= LIM: |TAB| = {len(TAB)} (excl 1: {len(CEN)})", flush=True)
assert TAB[0] == 1 and TAB == sorted(TAB) and len(set(TAB)) == len(TAB)
assert 6686 ** 4 <= LIM < 6687 ** 4

TABSET = set(TAB)
TABODD = [x for x in TAB if x % 2 == 1]
TABODDB = [x for x in TABODD if x <= B]
print(f"|TABODD| = {len(TABODD)}  |TABODDB| = {len(TABODDB)}", flush=True)

TABODD_r = {r: [x for x in TABODD if x % 16 == r] for r in range(16)}
TABODDB_r = {r: [x for x in TABODDB if x % 16 == r] for r in range(16)}
assert all(x % 16 == 0 for x in TAB if x % 2 == 0)
assert all(x == 1 or x >= 16 for x in TAB)

# ---- tree (python mirror) ----------------------------------------------------
def py_eval_tree(arr, n):
    if not arr:
        return False
    if len(arr) == 1:
        return n == arr[0]
    mid = (len(arr) + 1) // 2
    left, right = arr[:mid], arr[mid:]
    if n < right[0]:
        return py_eval_tree(left, n)
    return py_eval_tree(right, n)

assert all(py_eval_tree(TAB, x) for x in TAB)
for x in [0, 2, 3, 15, 17, LIM // 2, LIM, LIM + 1, 10 ** 15, 82, 4097]:
    if x not in TABSET:
        assert not py_eval_tree(TAB, x), x
print("tree exactness (positive + sample) OK", flush=True)

# ---- sweep mirror (preflight law) --------------------------------------------
def checkEO(o, c):
    if c <= o:
        return True
    if o + B < c:
        return True
    if (c - o) not in TABSET:
        return True
    return 1 < math.gcd(c - o, o)

def checkOO(a, b):
    if b <= a:
        return True
    if (a + b) not in TABSET:
        return True
    return 1 < math.gcd(a, b)

CHUNK = 40
chunks_r = {r: [TABODDB_r[r][i:i + CHUNK] for i in range(0, len(TABODDB_r[r]), CHUNK)]
            for r in range(16)}

hits = 0
coprime = 0
viol = 0
for r in range(16):
    for ch in chunks_r[r]:
        for o in ch:
            for c in TABODD_r[r]:
                if not checkEO(o, c):
                    viol += 1
                if c > o and o + B >= c and (c - o) in TABSET:
                    hits += 1
                    if math.gcd(c - o, o) == 1:
                        coprime += 1
for r in range(16):
    comp = (16 - r) % 16
    for ch in chunks_r[r]:
        for a in ch:
            for b in TABODDB_r[comp]:
                if not checkOO(a, b):
                    viol += 1
                if b > a and (a + b) in TABSET:
                    hits += 1
                    if math.gcd(a, b) == 1:
                        coprime += 1
print(f"sum-hits (residue-mirrored): {hits}, coprime: {coprime}, violations: {viol}", flush=True)
assert coprime == 0 and viol == 0
print(f"ALL PREFLIGHT CHECKS PASSED ({time.time()-T0:.1f}s)", flush=True)

# ---- Lean emission ------------------------------------------------------------
def packed(vals, per_line=8, ind=4):
    lines = []
    for i in range(0, len(vals), per_line):
        lines.append(", ".join(str(v) for v in vals[i:i + per_line]))
    return ("\n" + " " * ind).join(lines)

def emit_subtree(arr):
    """balanced BST membership string over arr (split every level)."""
    if not arr:
        return "false"
    if len(arr) == 1:
        return f"decide (n = {arr[0]})"
    mid = (len(arr) + 1) // 2
    left, right = arr[:mid], arr[mid:]
    return f"(if n < {right[0]} then {emit_subtree(left)} else {emit_subtree(right)})"

# 64 buckets
NBUCK = 64
buckets = []
per = (len(TAB) + NBUCK - 1) // NBUCK
for i in range(0, len(TAB), per):
    buckets.append(TAB[i:i + per])
bounds = [bk[0] for bk in buckets[1:]]  # 63 boundaries

def emit_root(idxs, indent):
    """balanced dispatch tree over bucket indices."""
    if len(idxs) == 1:
        return f"inTABb_{idxs[0]} n"
    mid = (len(idxs) + 1) // 2
    left, right = idxs[:mid], idxs[mid:]
    pivot = bounds[idxs[mid] - 1] if idxs[mid] - 1 < len(bounds) else bounds[-1]
    pad = " " * indent
    return (f"if n < {pivot} then\n{pad}  {emit_root(left, indent + 2)}\n{pad}else\n{pad}  {emit_root(right, indent + 2)}")

ROOT_STR = emit_root(list(range(len(buckets))), 2)

out = []
w = out.append

w("""import Arsenal.ErdosTernary2.Basic
import Arsenal.CardinalWorlds
import Arsenal.CardinalWorldsV2

/-! # Erdos939R5 — THE TRUE-BOX WITNESS-TABLE KERNEL (Kernel 60c, W66)
Erdős #939 (r-powerful sums), the r=4 box theorem, table form.

`TAB` is the certified census of 4-powerful numbers `n <= LIM = 2*B`
with `B = 999706081460641` (the Kernel 60b bracket bound), including 1,
sorted, dual-method verified (preflight939R5.py + engine939_w66.py; the
1e19 extension: 449,087 values, 246,243 sum-hits, zero coprime witnesses;
the r=3 positive control validates the scanner).

THE THEOREM (`e939_box_census`): any two census members `a, b <= B` whose
sum `a + b` is again a census member satisfy `1 < Nat.gcd a b` — there is
NO pairwise-coprime 4-powerful triple `a + b = c` with `a, b <= B` inside
the certified census. Proof: parity split; the structural gates (every
even census member is `≡ 0 mod 16`; the even/odd sum lands in the odd
residue class of the odd member; the odd/odd sum landing in the census is
`≡ 0 mod 16`) route every candidate pair into the mod-16 residue-class
sweeps, which are decided chunk by chunk.

Honest scope: complete and unconditional over the certified census table.
The structural bridge `rpow 4 n = true → n ≤ LIM → n ∈ TAB` (the genVals
recursion completeness) is the next-round lane; the table completeness
itself is certified by the two independent python engines whose receipts
ship beside this kernel (preflight939R5_output.txt, table939_w66/). -/

set_option maxRecDepth 262144
set_option maxHeartbeats 4000000

namespace E939R5

/-! ## Constants -/

/-- The box bound (the Kernel 60b bracket witness: 999706081460641 < 10^15). -/
def B : Nat := 999706081460641

/-- The census ceiling: `a + b <= 2*B` for `a, b <= B`. -/
def LIM : Nat := 1999412162921282

/-! ## Structural machinery (verbatim Kernel 60) -/

def noDivFrom : Nat → Nat → Bool
  | 0, _ => true
  | d+1, n => decide ((d + 1 ≤ 1 ∨ n % (d + 1) ≠ 0) ∧ noDivFrom d n = true)

def prime (n : Nat) : Bool := Nat.ble 2 n && noDivFrom (n - 1) n

def divAll (r n : Nat) : Nat → Bool
  | 0 => true
  | d+1 => decide (divAll r n d = true ∧
      (n % (d+1) ≠ 0 ∨ prime (d+1) ≠ true ∨ n % (d+1) ^ r = 0))

def rpow (r n : Nat) : Bool := decide (1 ≤ n ∧ divAll r n n = true)

theorem prime_ge_two (e : Nat) (h : prime e = true) : 2 ≤ e := by
  cases e with
  | zero =>
    have h0 : prime 0 = false := rfl
    rw [h0] at h
    exact Bool.noConfusion h
  | succ k =>
    cases k with
    | zero =>
      have h1 : prime 1 = false := rfl
      rw [h1] at h
      exact Bool.noConfusion h
    | succ j => omega

theorem divAll_row (r n e : Nat) (hp : prime e = true) (hne : n % e = 0) :
    ∀ d : Nat, e ≤ d → divAll r n d = true → n % e ^ r = 0 := by
  intro d
  induction d with
  | zero =>
    intro hle hd
    have h2 := prime_ge_two e hp
    exact absurd hle (by omega)
  | succ k ih =>
    intro hle hd
    have hprop := of_decide_eq_true hd
    cases hprop with
    | intro hk hrow =>
      cases hle with
      | refl =>
        cases hrow with
        | inl h1 => exact absurd hne h1
        | inr h2 =>
          cases h2 with
          | inl h3 => exact absurd hp h3
          | inr h4 => exact h4
      | step hst => exact ih hst hk

theorem rpow_prime_div (r n e : Nat) (h : rpow r n = true) (hp : prime e = true)
    (hd : n % e = 0) : n % e ^ r = 0 := by
  by_cases hle : e ≤ n
  · have hprop := of_decide_eq_true h
    cases hprop with
    | intro _ hd2 => exact divAll_row r n e hp hd n hle hd2
  · have hlt : n < e := by omega
    rw [Nat.mod_eq_of_lt hlt] at hd
    subst hd
    exact Nat.zero_mod _

theorem mod16_obstruction (a b : Nat) (ha : rpow 4 a = true) (hb : rpow 4 b = true)
    (h1 : a % 2 = 1) (h2 : b % 2 = 1) (hsum : rpow 4 (a + b) = true) :
    (a + b) % 16 = 0 := by
  have heven : (a + b) % 2 = 0 := by omega
  have hp2 : prime 2 = true := rfl
  have hd16 : (a + b) % 2 ^ 4 = 0 := rpow_prime_div 4 (a + b) 2 hsum hp2 heven
  exact hd16
""")

w(f"/-! ## The certified census table ({len(TAB)} members) -/")
w("")
w("/-- The 4-powerful census `≤ LIM`, sorted, including 1. -/")
w("def TAB : List Nat := [")
w(packed(TAB))
w("]")
w("")

w(f"/-! ## The odd residue classes ({len(TABODD)} odd members) -/")
w("")
for r in range(16):
    w(f"/-- Odd census members `≡ {r} (mod 16)` ({len(TABODD_r[r])} members). -/")
    w(f"def TABODD_{r} : List Nat := [")
    w(packed(TABODD_r[r]))
    w("]")
    w("")

w(f"/-! ## The `≤ B` odd chunks ({len(TABODDB)} members, decide-sized) -/")
w("")
nchunks_total = 0
for r in range(16):
    for i, ch in enumerate(chunks_r[r]):
        w(f"/-- Chunk {i} of the odd `≤ B` members `≡ {r} (mod 16)`. -/")
        w(f"def CHUNKB_{r}_{i} : List Nat := [")
        w(packed(ch))
        w("]")
        w("")
        nchunks_total += 1

for r in range(16):
    n = len(chunks_r[r])
    if n == 0:
        w(f"/-- Odd `≤ B` census members `≡ {r} (mod 16)` (empty class). -/")
        w(f"def TABODDB_{r} : List Nat := []")
    else:
        chain = " ++ ".join(f"CHUNKB_{r}_{i}" for i in range(n))
        w(f"/-- Odd `≤ B` census members `≡ {r} (mod 16)` (chunk concat). -/")
        w(f"def TABODDB_{r} : List Nat := {chain}")
    w("")

w("/-- All odd census members `≤ B`. -/")
w("def TABODDB : List Nat := TAB.filter (fun n => decide (n % 2 = 1) && decide (n ≤ B))")
w("")

w(f"/-! ## The membership tree ({len(buckets)} bucket defs) -/")
w("")
for i, bk in enumerate(buckets):
    w(f"/-- Bucket {i} of the `inTAB` decision tree ({len(bk)} members). -/")
    w(f"def inTABb_{i} : Nat → Bool :=")
    w(f"  fun n => {emit_subtree(bk)}")
    w("")
w("/-- Balanced decision-tree membership in `TAB` (O(log |TAB|) per query). -/")
w("def inTAB : Nat → Bool :=")
w(f"  fun n => {ROOT_STR}")
w("")

w("""/-! ## Generic helpers -/

theorem all_nil {α : Type} (p : α → Bool) : ([] : List α).all p = true := rfl

theorem allMem {α : Type} (p : α → Bool) : ∀ (l : List α), l.all p = true →
    ∀ x : α, x ∈ l → p x = true := by
  intro l
  induction l with
  | nil => intro _ x hx; cases hx
  | cons hd tl ih =>
    intro h x hx
    have hstep : (p hd && tl.all p) = true := h
    cases hx with
    | head => simp
    | tail _ hmem =>
      have hpb : p hd = true ∨ p hd = false := by cases h : p hd <;> simp [h]
      rcases hpb with hpb | hpb
      · rw [hpb] at hstep; simp at hstep; exact ih hstep x hmem
      · rw [hpb] at hstep; simp at hstep

theorem all_append {α : Type} (p : α → Bool) : ∀ l₁ l₂ : List α,
    (l₁ ++ l₂).all p = (l₁.all p && l₂.all p) := by
  intro l₁
  induction l₁ with
  | nil => intro l₂; rfl
  | cons hd tl ih =>
    intro l₂
    simp only [List.all_cons, ih]
    cases p hd <;> simp
""")

w("/-! ## The table certs (decide-verified) -/")
w("")
w("theorem tab_pos : TAB.all (fun n => decide (1 ≤ n)) = true := by decide")
w("")
w("theorem tab_min16 : TAB.all (fun n => decide (n = 1) || decide (16 ≤ n)) = true := by decide")
w("")
w("/-- Every even census member is `≡ 0 (mod 16)` (the `2^4` gate). -/")
w("theorem tab_even16 : TAB.all (fun n => decide (n % 2 = 1) || decide (n % 16 = 0)) = true := by decide")
w("")
w("theorem tab_all_inTAB : TAB.all (fun n => inTAB n) = true := by decide")
w("")
for r in range(16):
    w(f"theorem tabodd_{r}_filter : TABODD_{r} = TAB.filter (fun n => decide (n % 2 = 1) && decide (n % 16 = {r})) := by decide")
    w(f"theorem tabodb_{r}_filter : TABODDB_{r} = TABODDB.filter (fun n => decide (n % 16 = {r})) := by decide")
    w("")

w("/-! ## The class routing lemmas -/")
w("")
for r in range(16):
    w(f"theorem mem_tabodb_cls_{r} : ∀ x : Nat, x ∈ TABODDB → (x ∈ TABODDB_{r} ↔ x % 16 = {r}) := by")
    w("  intro x hx")
    w(f"  rw [tabodb_{r}_filter]")
    w("  constructor")
    w("  · intro h")
    w("    have h2 := (List.mem_filter.mp h).2")
    w(f"    have h3 : x % 16 = {r} := of_decide_eq_true h2")
    w("    omega")
    w("  · intro h")
    w("    exact (List.mem_filter.mpr ⟨hx, by simp only [decide_eq_true]; omega⟩)")
    w("")
for r in range(16):
    w(f"theorem mem_tabodd_cls_{r} : ∀ x : Nat, x ∈ TAB → (x ∈ TABODD_{r} ↔ x % 2 = 1 ∧ x % 16 = {r}) := by")
    w("  intro x hx")
    w(f"  rw [tabodd_{r}_filter]")
    w("  constructor")
    w("  · intro h")
    w("    have h2 := (List.mem_filter.mp h).2")
    w("    simp only [Bool.and_eq_true, decide_eq_true] at h2")
    w("    exact h2")
    w("  · intro h")
    w("    exact (List.mem_filter.mpr ⟨hx, by simp only [Bool.and_eq_true, decide_eq_true];")
    w("      exact h⟩)")
    w("")

w("/-! ## The EO sweep (even + odd): for `o` odd `≤ B` in class `r` and `c` odd")
w("    in class `r` with `o < c ≤ o + B`, if `c - o` is a census member then")
w("    `1 < gcd (c - o) o`. -/")
w("")
for r in range(16):
    for i in range(len(chunks_r[r])):
        w(f"theorem sweepEO_{r}_{i} : (CHUNKB_{r}_{i}).all (fun o => (TABODD_{r}).all (fun c =>")
        w("    decide (c ≤ o) || decide (o + B < c) || (!inTAB (c - o)) ||")
        w("    decide (1 < Nat.gcd (c - o) o))) = true := by decide")
        w("")
    n = len(chunks_r[r])
    if n == 0:
        w(f"theorem sweepEO_{r} : (TABODDB_{r}).all (fun o => (TABODD_{r}).all (fun c =>")
        w("    decide (c ≤ o) || decide (o + B < c) || (!inTAB (c - o)) ||")
        w("    decide (1 < Nat.gcd (c - o) o))) = true := by")
        w("  rfl")
    else:
        proof = ", ".join(f"sweepEO_{r}_{i}" for i in range(n))
        w(f"theorem sweepEO_{r} : (TABODDB_{r}).all (fun o => (TABODD_{r}).all (fun c =>")
        w("    decide (c ≤ o) || decide (o + B < c) || (!inTAB (c - o)) ||")
        w("    decide (1 < Nat.gcd (c - o) o))) = true := by")
        w(f"  simp only [TABODDB_{r}, all_append, all_nil, Bool.and_eq_true]")
        w(f"  exact ⟨{proof}⟩")
    w("")

w("/-! ## The OO sweep (odd + odd): for `a < b` odd `≤ B` with")
w("    `(a + b) ≡ 0 (mod 16)` and `a + b` a census member, `1 < gcd a b`. -/")
w("")
for r in range(16):
    comp = (16 - r) % 16
    for i in range(len(chunks_r[r])):
        w(f"theorem sweepOO_{r}_{i} : (CHUNKB_{r}_{i}).all (fun a => (TABODDB_{comp}).all (fun b =>")
        w("    decide (b ≤ a) || (!inTAB (a + b)) ||")
        w("    decide (1 < Nat.gcd a b))) = true := by decide")
        w("")
    n = len(chunks_r[r])
    if n == 0:
        w(f"theorem sweepOO_{r} : (TABODDB_{r}).all (fun a => (TABODDB_{comp}).all (fun b =>")
        w("    decide (b ≤ a) || (!inTAB (a + b)) ||")
        w("    decide (1 < Nat.gcd a b))) = true := by")
        w("  rfl")
    else:
        proof = ", ".join(f"sweepOO_{r}_{i}" for i in range(n))
        w(f"theorem sweepOO_{r} : (TABODDB_{r}).all (fun a => (TABODDB_{comp}).all (fun b =>")
        w("    decide (b ≤ a) || (!inTAB (a + b)) ||")
        w("    decide (1 < Nat.gcd a b))) = true := by")
        w(f"  simp only [TABODDB_{r}, all_append, all_nil, Bool.and_eq_true]")
        w(f"  exact ⟨{proof}⟩")
    w("")

# ---- the kill lemmas (residue dispatch) ----
w("/-! ## The residue-dispatch kill lemmas -/")
w("")
w("/-- The EO kill: `e` even census member (`16 ∣ e`, `16 ≤ e ≤ B`), `o` odd")
w("    census member `≤ B`, `c = e + o` odd census member with `c ≡ o (mod 16)`:")
w("    `1 < gcd e o` via the residue sweep of `o`'s class. -/")
w("theorem eo_kill (e o c : Nat) (hc : c = e + o) (hcmem : c ∈ TAB) (hco : c % 2 = 1)")
w("    (hcr : c % 16 = o % 16) (homem : o ∈ TABODDB) (hinTABe : inTAB e = true)")
w("    (hinTABc : inTAB c = true) (hage : 16 ≤ e) (hale : e ≤ B) : 1 < Nat.gcd e o := by")
w("  match hres : o % 16 with")
for r in range(16):
    w(f"  | {r} =>")
    w(f"    have hbcl : o ∈ TABODDB_{r} := (mem_tabodb_cls_{r} o homem).mpr (by omega)")
    w(f"    have hcmemr : c ∈ TABODD_{r} := (mem_tabodd_cls_{r} c hcmem).mpr ⟨hco, by omega⟩")
    w(f"    have hsw := allMem (fun x => (TABODD_{r}).all (fun y =>")
    w("        decide (y ≤ x) || decide (x + B < y) || (!inTAB (y - x)) ||")
    w(f"        decide (1 < Nat.gcd (y - x) x))) TABODDB_{r} sweepEO_{r} o hbcl")
    w("    have hbool := allMem (fun y =>")
    w("        decide (y ≤ o) || decide (o + B < y) || (!inTAB (y - o)) ||")
    w(f"        decide (1 < Nat.gcd (y - o) o)) TABODD_{r} hsw c hcmemr")
    w("    simp only [Bool.or_eq_true] at hbool")
    w("    rcases hbool with h | h")
    w("    · have := of_decide_eq_true h; omega")
    w("    rcases h with h | h")
    w("    · have := of_decide_eq_true h; omega")
    w("    rcases h with h | h")
    w("    · rw [show c - o = e by omega] at h")
    w("      cases hh : inTAB e with")
    w("      | false => rw [hh] at hinTABe; exact absurd hinTABe (by decide)")
    w("      | true => rw [hh] at h; simp at h")
    w("    · rw [show c - o = e by omega] at h")
    w("      exact of_decide_eq_true h")
w("  | (k + 16) => exact absurd (Nat.mod_lt o 16) (by omega)")
w("")

w("/-- The OO kill: `a < b` odd census members `≤ B`, `c = a + b` a census")
w("    member with `c ≡ 0 (mod 16)`: `1 < gcd a b` via the complement sweep. -/")
w("theorem oo_kill (a b c : Nat) (hc : c = a + b) (hcmem : c ∈ TAB) (hc16 : c % 16 = 0)")
w("    (halt : a < b) (hamem : a ∈ TABODDB) (hbmem : b ∈ TABODDB)")
w("    (hinTABc : inTAB c = true) : 1 < Nat.gcd a b := by")
w("  match hres : a % 16 with")
for r in range(16):
    comp = (16 - r) % 16
    w(f"  | {r} =>")
    w(f"    have hacl : a ∈ TABODDB_{r} := (mem_tabodb_cls_{r} a hamem).mpr (by omega)")
    w(f"    have hbres : b % 16 = {comp} := by omega")
    w(f"    have hbcl : b ∈ TABODDB_{comp} := (mem_tabodb_cls_{comp} b hbmem).mpr hbres")
    w(f"    have hsw := allMem (fun x => (TABODDB_{comp}).all (fun y =>")
    w("        decide (y ≤ x) || (!inTAB (x + y)) || decide (1 < Nat.gcd x y)))")
    w(f"        TABODDB_{r} sweepOO_{r} a hacl")
    w("    have hbool := allMem (fun y =>")
    w("        decide (y ≤ a) || (!inTAB (a + y)) || decide (1 < Nat.gcd a y))")
    w(f"        TABODDB_{comp} hsw b hbcl")
    w("    simp only [Bool.or_eq_true] at hbool")
    w("    rcases hbool with h | h")
    w("    · have := of_decide_eq_true h; omega")
    w("    rcases h with h | h")
    w("    · rw [show a + b = c by omega] at h")
    w("      cases hh : inTAB c with")
    w("      | false => rw [hh] at hinTABc; exact absurd hinTABc (by decide)")
    w("      | true => rw [hh] at h; simp at h")
    w("    · exact of_decide_eq_true h")
w("  | (k + 16) => exact absurd (Nat.mod_lt a 16) (by omega)")
w("")

# ---- the master theorem ----
w("/-! ## The master theorem -/")
w("")
w("/-- THE BOX THEOREM (table form): any two census members `a, b ≤ B` whose")
w("    sum is again a census member satisfy `1 < gcd a b` — no pairwise-coprime")
w("    4-powerful triple `a + b = c` with `a, b ≤ B` exists in the census. -/")
w("theorem e939_box_census : ∀ a b : Nat, a ∈ TAB → b ∈ TAB → a ≤ B → b ≤ B →")
w("    (a + b) ∈ TAB → 1 < Nat.gcd a b := by")
w("  intro a b hma hmb hlea hleb hsum")
w("  have hinTABa : inTAB a = true := allMem inTAB TAB tab_all_inTAB a hma")
w("  have hinTABb : inTAB b = true := allMem inTAB TAB tab_all_inTAB b hmb")
w("  have hinTABs : inTAB (a + b) = true := allMem inTAB TAB tab_all_inTAB (a + b) hsum")
w("  have hamem : a ∈ TABODDB := (List.mem_filter.mpr ⟨hma, by")
w("    simp only [Bool.and_eq_true, decide_eq_true]; omega⟩)")
w("  have hbmem : b ∈ TABODDB := (List.mem_filter.mpr ⟨hmb, by")
w("    simp only [Bool.and_eq_true, decide_eq_true]; omega⟩)")
w("  have hcertA : a % 2 = 1 ∨ a % 16 = 0 := by")
w("    have h := allMem (fun n => decide (n % 2 = 1) || decide (n % 16 = 0)) TAB tab_even16 a hma")
w("    simp only [Bool.or_eq_true, decide_eq_true] at h")
w("    exact h")
w("  have hcertB : b % 2 = 1 ∨ b % 16 = 0 := by")
w("    have h := allMem (fun n => decide (n % 2 = 1) || decide (n % 16 = 0)) TAB tab_even16 b hmb")
w("    simp only [Bool.or_eq_true, decide_eq_true] at h")
w("    exact h")
w("  have hcertS : (a + b) % 2 = 1 ∨ (a + b) % 16 = 0 := by")
w("    have h := allMem (fun n => decide (n % 2 = 1) || decide (n % 16 = 0)) TAB tab_even16")
w("      (a + b) hsum")
w("    simp only [Bool.or_eq_true, decide_eq_true] at h")
w("    exact h")
w("  have hamin : a = 1 ∨ 16 ≤ a := by")
w("    have h := allMem (fun n => decide (n = 1) || decide (16 ≤ n)) TAB tab_min16 a hma")
w("    simp only [Bool.or_eq_true, decide_eq_true] at h")
w("    exact h")
w("  have hbmin : b = 1 ∨ 16 ≤ b := by")
w("    have h := allMem (fun n => decide (n = 1) || decide (16 ≤ n)) TAB tab_min16 b hmb")
w("    simp only [Bool.or_eq_true, decide_eq_true] at h")
w("    exact h")
w("  have ha2 : a % 2 = 0 ∨ a % 2 = 1 := by omega")
w("  have hb2 : b % 2 = 0 ∨ b % 2 = 1 := by omega")
w("  rcases ha2 with hae | hao")
w("  rcases hb2 with hbe | hbo")
w("  · -- EE : both even, 2 divides the gcd")
w("    have hdva : 2 ∣ a := Nat.dvd_of_mod_eq_zero (by omega)")
w("    have hdvb : 2 ∣ b := Nat.dvd_of_mod_eq_zero (by omega)")
w("    have hgd : 2 ∣ Nat.gcd a b := Nat.dvd_gcd hdva hdvb")
w("    have hpos : 0 < Nat.gcd a b := Nat.gcd_pos_of_pos_left _ (by omega)")
w("    omega")
w("  · -- EO : a even, b odd")
w("    have h16a : a % 16 = 0 := by")
w("      rcases hcertA with h | h")
w("      · omega")
w("      · exact h")
w("    have hage : 16 ≤ a := by")
w("      rcases hamin with h | h")
w("      · omega")
w("      · exact h")
w("    have hco : (a + b) % 2 = 1 := by omega")
w("    have hcr : (a + b) % 16 = b % 16 := by omega")
w("    exact eo_kill a b (a + b) rfl hsum hco hcr hbmem hinTABa hinTABs hage hlea")
w("  · -- OE : a odd, b even (symmetric)")
w("    have h16b : b % 16 = 0 := by")
w("      rcases hcertB with h | h")
w("      · omega")
w("      · exact h")
w("    have hbge : 16 ≤ b := by")
w("      rcases hbmin with h | h")
w("      · omega")
w("      · exact h")
w("    have hco : (b + a) % 2 = 1 := by omega")
w("    have hcr : (b + a) % 16 = a % 16 := by omega")
w("    have hsum' : (b + a) ∈ TAB := by rw [Nat.add_comm]; exact hsum")
w("    have h := eo_kill b a (b + a) rfl hsum' hco hcr hamem hinTABb hinTABs hbge hleb")
w("    rw [Nat.gcd_comm] at h")
w("    exact h")
w("  · -- OO : both odd")
w("    have h16s : (a + b) % 16 = 0 := by")
w("      rcases hcertS with h | h")
w("      · omega")
w("      · exact h")
w("    rcases Nat.lt_trichotomy a b with hlt | heq | hgt")
w("    · exact oo_kill a b (a + b) rfl hsum h16s hlt hamem hbmem hinTABs")
w("    · -- a = b : the gcd is a itself, and a ≠ 1")
w("      have hne : a ≠ 1 := by")
w("        intro h1")
w("        have h2 : 1 + 1 ∈ TAB := by rw [show 1 + 1 = a + b by omega]; exact hsum")
w("        have h3 := allMem (fun n => decide (n = 1) || decide (16 ≤ n)) TAB tab_min16")
w("          (1 + 1) h2")
w("        simp only [Bool.or_eq_true, decide_eq_true] at h3")
w("        rcases h3 with h4 | h4")
w("        · omega")
w("        · omega")
w("      have hge : 16 ≤ a := by")
w("        rcases hamin with h | h")
w("        · exact absurd h hne")
w("        · exact h")
w("      rw [heq, Nat.gcd_self]")
w("      omega")
w("    · have hsum' : (b + a) ∈ TAB := by rw [Nat.add_comm]; exact hsum")
w("      have h16s' : (b + a) % 16 = 0 := by rw [Nat.add_comm]; exact h16s")
w("      have h := oo_kill b a (b + a) rfl hsum' h16s' hgt hbmem hamem hinTABs")
w("      rw [Nat.gcd_comm] at h")
w("      exact h")
w("")

# ---- board + receipts ----
w("/-! ## The board -/")
w("")
w("/-- The W66 board: the structural mod-16 obstruction (rpow form) + the box")
w("    theorem (table form) + the Nitaj r=3 witnesses + the bracket. -/")
w("theorem board939R5 :")
w("    (∀ a b : Nat, rpow 4 a = true → rpow 4 b = true → a % 2 = 1 → b % 2 = 1 →")
w("        rpow 4 (a + b) = true → (a + b) % 16 = 0)")
w("    ∧ (∀ a b : Nat, a ∈ TAB → b ∈ TAB → a ≤ B → b ≤ B → (a + b) ∈ TAB →")
w("        1 < Nat.gcd a b)")
w("    ∧ 19902511 + 756249048 = 776151559")
w("    ∧ 1392672604221 + 2126285555779 = 3518958160000")
w("    ∧ 999706081460641 < 1000000000000000")
w("    ∧ 1000000000000000 < 1000417426149376 :=")
w("  ⟨mod16_obstruction, e939_box_census, by decide, by decide, by decide, by decide⟩")
w("")
w("end E939R5")
w("")
w("/-! ## Receipts -/")
w("")
w("#print axioms E939R5.tab_all_inTAB")
w("#print axioms E939R5.sweepEO_0")
w("#print axioms E939R5.sweepOO_0")
w("#print axioms E939R5.eo_kill")
w("#print axioms E939R5.oo_kill")
w("#print axioms E939R5.e939_box_census")
w("#print axioms E939R5.board939R5")
w("#eval \"E939R5_BOX_GREEN\"")
w("")

src = "\n".join(out) + "\n"
with open("Erdos939R5.lean", "w") as f:
    f.write(src)
print(f"WROTE Erdos939R5.lean: {src.count(chr(10))} lines, {len(src)} bytes", flush=True)
print(f"chunks: {nchunks_total} total; classes TABODDB_r sizes: "
      f"{[len(TABODDB_r[r]) for r in range(16)]}", flush=True)
print(f"GEN939R5_ALL_OK ({time.time()-T0:.1f}s)", flush=True)
