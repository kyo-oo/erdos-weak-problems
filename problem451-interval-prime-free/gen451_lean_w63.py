#!/usr/bin/env python3
"""GEN 451 LEAN W63 — generate the Lean-side extension rows k = 21..28 for
Erdos451_Data.lean (witness residues w_k, window enumerations win_k, coverage
chunks c_k_j <= 500 elements, NO-OOM discipline) and Erdos451.lean (the eight
final theorems erdos451_k21..k28 + the extension complete board
erdos451_complete_ext), from the triple-route certified values.

PRE-FLIGHT LAW: every generated `= true := by decide` proposition is
MIRRORED in Python (exact Bool semantics of Nat.ble/Nat.mod/List ops) and
asserted True BEFORE emission — no unverified line ever reaches the files.
"""
import sys

# ---------------- the certified frontier (battery451_ext_w63.py, GREEN) ----
W62 = {21: 805, 22: 2691, 23: 1884, 24: 2664}
W63 = {25: 7653, 26: 7654, 27: 36887, 28: 36888}
ROWS = {**W62, **W63}
CHUNK = 500


def primes_in(lo, hi):
    return [p for p in range(lo + 1, hi)
            if p >= 2 and all(p % d for d in range(2, int(p**0.5) + 1))]


def isP(q):  # exact mirror of Erdos451_Data.isP (trial division, Bool)
    if not (2 <= q):
        return False
    return all(q % (d + 2) != 0 for d in range(q - 2))


# -------- re-derive the values by the modular sieve (independent re-check) -
for k, v in sorted(ROWS.items()):
    ps = primes_in(k, 2 * k)
    n = 2 * k + 1
    while not all(not (1 <= n % p <= k) for p in ps):
        n += 1
    assert n == v, f"modular re-derivation mismatch k={k}: {n} != {v}"

PS = {k: primes_in(k, 2 * k) for k in sorted(ROWS)}


def lst(ps):
    return "[" + ", ".join(str(p) for p in ps) + "]"


# ---------------- generate the Data §4 block ------------------------------
data_lines = []
nchunks = {}


def emit_w(k, n, ps):
    for p in ps:
        assert not (1 <= n % p <= k), f"w_{k} mirror FALSE at p={p}"
    data_lines.append(
        f"theorem w_{k} : ({lst(ps)}.all (fun p => !(Nat.ble 1 ({n} % p) "
        f"&& Nat.ble ({n} % p) {k}))) = true := by decide")


def emit_win(k, ps):
    for q in range(2 * k):  # mirror of List.range (2k) .all
        cond = not (k < q and isP(q)) or (q in ps)
        assert cond, f"win_{k} mirror FALSE at q={q}"
    data_lines.append(
        f"theorem win_{k} : ((List.range {2 * k}).all (fun q => "
        f"!(decide ({k} < q) && isP q) || decide (q ∈ {lst(ps)}))) = true := by decide")


def chunks_for(k, n):
    """contiguous coverage chunks (base, cnt) tiling [2k+1, n-1]"""
    base = 2 * k + 1
    total = n - 2 * k - 1
    cs = []
    b, left = base, total
    while left > 0:
        c = min(CHUNK, left)
        cs.append((b, c))
        b += c
        left -= c
    return cs


def emit_c(k, n, ps):
    cs = chunks_for(k, n)
    for j, (b, c) in enumerate(cs, 1):
        # mirror: List.range c .all (off => ps.any (p => 1 <= (b+off)%p <= k))
        for off in range(c):
            m = b + off
            assert any(1 <= m % p <= k for p in ps), \
                f"c_{k}_{j} mirror FALSE at m={m}"
        data_lines.append(
            f"theorem c_{k}_{j} : ((List.range {c}).all (fun off => {lst(ps)}.any "
            f"(fun p => Nat.ble 1 (({b} + off) % p) && "
            f"Nat.ble (({b} + off) % p) {k}))) = true := by decide")
    return len(cs)


for k in sorted(ROWS):
    emit_w(k, ROWS[k], PS[k])
    emit_win(k, PS[k])
    nchunks[k] = emit_c(k, ROWS[k], PS[k])

# ---------------- generate the kernel §7b block ---------------------------
kern_lines = []


def hpr_block(k, ps):
    out = [
        f"  have hpr : ∀ q ∈ {lst(ps)}, q.Prime ∧ {k} < q ∧ q < 2 * {k} := by",
        "    intro q hq",
        "    simp only [List.mem_cons, List.mem_nil_iff] at hq",
        "    rcases hq with " + " | ".join(["rfl"] * len(ps)) + " | hfalse"]
    for _ in ps:
        out.append("    · exact ⟨by norm_num, by norm_num, by norm_num⟩")
    out.append("    · exact hfalse.elim")
    return out


def cov_tree(k, ps, cs, i0, i1, depth):
    """balanced binary rcases tree over chunk indices [i0, i1) — every node
    a pure trichotomy (omega), every leaf a cov_decode on one chunk."""
    ind = "    " + "  " * depth
    if i1 - i0 == 1:
        b, c = cs[i0]
        return [ind + f"exact cov_decode {k} {b} {c} {lst(ps)} "
                f"Erdos451Data.c_{k}_{i0 + 1} m (by omega) (by omega)"]
    mid = (i0 + i1) // 2
    bmid = cs[mid][0]
    out = [ind + f"rcases (by omega : m < {bmid} ∨ {bmid} ≤ m) "
           f"with h{depth} | h{depth}"]
    for branch in (cov_tree(k, ps, cs, i0, mid, depth + 1),
                   cov_tree(k, ps, cs, mid, i1, depth + 1)):
        for j, ln in enumerate(branch):
            out.append(ind + "· " + ln.lstrip() if j == 0 else ln)
    return out


def emit_kernel_row(k):
    ps, n = PS[k], ROWS[k]
    cs = chunks_for(k, n)
    lines = [
        f"theorem erdos451_k{k} : 2 * {k} < {n} ∧",
        f"    (∀ q, q.Prime → {k} < q → q < 2 * {k} → ¬ q ∣ prodK {n} {k}) ∧",
        f"    (∀ m, 2 * {k} < m → m < {n} → ∃ q, q.Prime ∧ {k} < q ∧ "
        f"q < 2 * {k} ∧ q ∣ prodK m {k}) := by"]
    lines += hpr_block(k, ps)
    lines += [
        f"  have hwin : ∀ q, q.Prime → {k} < q → q < 2 * {k} → q ∈ {lst(ps)} :=",
        f"    win_decode {k} {lst(ps)} Erdos451Data.win_{k}",
        f"  have hw : ∀ q ∈ {lst(ps)}, ¬ (1 ≤ {n} % q ∧ {n} % q ≤ {k}) :=",
        f"    wit_decode {k} {n} {lst(ps)} Erdos451Data.w_{k}",
        f"  have hcov : ∀ m, 2 * {k} < m → m < {n} → "
        f"∃ q ∈ {lst(ps)}, 1 ≤ m % q ∧ m % q ≤ {k} := by",
        "    intro m hm1 hm2"]
    lines += cov_tree(k, ps, cs, 0, len(cs), 0)
    lines.append(
        f"  exact final_helper {k} {n} {lst(ps)} hpr hwin "
        f"(by norm_num) (by norm_num) hw hcov")
    return lines


for k in sorted(ROWS):
    kern_lines += emit_kernel_row(k)
    kern_lines.append("")

# ---------------- generate the kernel §11 board block ----------------------
board_lines = [
    "theorem erdos451_complete_ext :",
    "    (∀ q : Nat, q.Prime → isP q = true) ∧",
    "    (∀ p : Nat, p.Prime → ∀ k n, p ∣ prodK n k → ∃ j, 1 ≤ j ∧ j ≤ k ∧ p ∣ (n - j)) ∧",
    "    (∀ j n k : Nat, 1 ≤ j → j ≤ k → ∀ p, p ∣ (n - j) → p ∣ prodK n k) ∧",
    "    (∀ p k n : Nat, p.Prime → k < p → k ≤ n → (p ∣ prodK n k ↔ 1 ≤ n % p ∧ n % p ≤ k)) ∧"]
for k in sorted(ROWS):
    n = ROWS[k]
    board_lines += [
        f"    (2 * {k} < {n} ∧",
        f"      (∀ q, q.Prime → {k} < q → q < 2 * {k} → ¬ q ∣ prodK {n} {k}) ∧",
        f"      (∀ m, 2 * {k} < m → m < {n} → ∃ q, q.Prime ∧ {k} < q ∧ "
        f"q < 2 * {k} ∧ q ∣ prodK m {k})) ∧"]
board_lines += [
    "    arsenalBridgeProp :=",
    "  ⟨fun q hq => isP_of_prime q hq,",
    "   fun p hp k n hdvd => prime_dvd_prodK p hp k n hdvd,",
    "   fun j n k hj1 hjk p hpdiv => dvd_prodK_factor j n k hj1 hjk p hpdiv,",
    "   fun p k n hp hk hkn => erdos451_crit p k n hp hk hkn,"]
for k in sorted(ROWS):
    board_lines.append(f"   erdos451_k{k},")
board_lines += [
    "   erdos451_arsenal_bridge_full⟩",
    "",
    '#eval "ERDOS451_FRONTIER_EXT_GREEN"']
for k in sorted(ROWS):
    board_lines.append(f"#print axioms erdos451_k{k}")
board_lines.append("#print axioms erdos451_complete_ext")

# ---------------- assemble the insertion texts -----------------------------
tot_c = sum(nchunks.values())
DATA_DOC = f"""/-! ## §4 THE W63 EXTENSION ROWS (k = 21..28; S063 W62 certified the
values n_21..n_24 in Python, W63 volley task W63-C3 lands the Lean rows
k = 21..28): the 8 witness residues + the 8 window enumerations + the
{tot_c} completeness chunks (all ≤ {CHUNK}-element, NO-OOM discipline),
generated AND mirror-verified by gen451_lean_w63.py from the triple-route
battery battery451_ext_w63.py (ALL GREEN):
n_21 = 805, n_22 = 2691, n_23 = 1884, n_24 = 2664 (W62),
n_25 = 7653, n_26 = 7654, n_27 = 36887, n_28 = 36888 (W63). -/
"""
data_block = DATA_DOC + "\n".join(data_lines) + "\n\n"

KERN_DOC = """/-! ## §7b THE EIGHT EXTENSION THEOREMS (k = 21..28, W62 + W63 volleys;
original product formulation, unconditional: witness ∧ leastness). The
certified frontier of this kernel is now k = 2..28: n_21 = 805,
n_22 = 2691, n_23 = 1884, n_24 = 2664, n_25 = 7653, n_26 = 7654,
n_27 = 36887, n_28 = 36888. Same §6 assembly machinery, same §5 decode
toolkit, same dual-method machine certificate (battery451_ext_w63.py,
triple-route GREEN). -/

"""
kern_block = KERN_DOC + "\n".join(kern_lines) + "\n"

BOARD_DOC = """/-! ## §11 THE W63 EXTENSION COMPLETE BOARD (the one-statement assembly
of the W62+W63 extension volley, in the §10 `erdos451_complete` pattern: the
four general laws + the eight rows k = 21..28 stated EXACTLY as §7b states
them + the arsenal bridge §9 — together with §10 this boards the certified
frontier k = 2..28 unconditionally. Honest scope unchanged: the general
asymptotics of n_k remain open and are NOT claimed.) -/
"""
board_block = BOARD_DOC + "\n".join(board_lines) + "\n"

# ---------------- insert into the files ------------------------------------
DATA_PATH = "/home/z/waves/w63-c3-p451/problem451-interval-prime-free/Erdos451_Data.lean"
KERN_PATH = "/home/z/waves/w63-c3-p451/problem451-interval-prime-free/Erdos451.lean"

with open(DATA_PATH, "r", encoding="utf-8") as f:
    dtxt = f.read()
marker = '#eval "ERDOS451_DATA_GREEN"'
assert dtxt.count(marker) == 1
assert "w_25" not in dtxt  # not yet inserted
dtxt = dtxt.replace(marker, data_block + marker)
with open(DATA_PATH, "w", encoding="utf-8") as f:
    f.write(dtxt)

with open(KERN_PATH, "r", encoding="utf-8") as f:
    ktxt = f.read()
marker2 = "/-! ## §8 THE ARSENAL BRIDGE"
assert ktxt.count(marker2) == 1
ktxt = ktxt.replace(marker2, kern_block + "\n" + marker2)
marker3 = "end Erdos451"
assert ktxt.count(marker3) == 1
ktxt = ktxt.replace(marker3, board_block + "\n" + marker3)
with open(KERN_PATH, "w", encoding="utf-8") as f:
    f.write(ktxt)

print(f"GEN451 W63 OK — Data: {len(data_lines)} theorems "
      f"(8 w + 8 win + {tot_c} c-chunks); kernel: 8 rows + board "
      f"({len(kern_lines) + len(board_lines)} lines)")
print("chunk counts per k:", nchunks)
