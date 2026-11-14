#!/usr/bin/env python3
"""#708 W63-D1/W64-B THE NO-OOM WITNESS-TABLE RESTRUCTURE (the runner-death repair).

Run 43589088597 post-mortem: kernel-c's kernel62 step at the 32M-heartbeat
54600-instance aggregate decide ground ~60 min and the HOSTED RUNNER DIED
(lost communication = OOM/starvation). The repair: replace the aggregate
decide with an explicit WITNESS TABLE (one 4-cell cover per (A, t) of the
box [2,16] x t=1..40, in EXACT box708 order), chunk-decided at the
480-instance discipline (12 A-rows per chunk, 114 chunks).

This generator:
  1. enumerates box708 in the exact Lean cmap708/winUp order (mirror);
  2. hunts one exactly-4 witness per (A, t) with the coverExact DFS mirror
     (the Lean def transcribed literally, take-first = the Lean || order);
  3. DUAL-METHOD verifies every emitted witness independently (explicit
     subset-of-window + length + ascent + gmpy2 divisibility);
  4. emits the new §13 Lean block + splices it into Erdos708.lean
     (replacing the old §13: the 32M-heartbeat aggregate decide).

Output receipt: g4_witgen_out.txt.
"""
import sys, time

OUT = "/home/z/waves/w63-d1-p708/problem708-product-divisibility"
LEAN = OUT + "/Erdos708.lean"
sys.path.insert(0, OUT)
import gmpy2

T_MAX = 40
ROWS_PER_CHUNK = 12          # 12 A-rows x 40 t = 480 instances per chunk <= 501


def prod(l):
    r = 1
    for x in l:
        r *= x
    return r


def winUp(s, k):
    return list(range(s, s + k))


def cmap(l, f):
    out = []
    for x in l:
        out += f(x)
    return out


# ---------------- the Lean box708, transcribed exactly ----------------
def box708():
    return cmap(winUp(2, 15), lambda a:
                cmap(winUp(a + 1, 16 - a), lambda b:
                     cmap(winUp(b + 1, 16 - b), lambda c:
                          [[a, b, c, d] for d in winUp(c + 1, 16 - c)])))


# ---------------- the Lean coverExact, transcribed exactly (witness-tracking) ----------------
def coverExact_wit(P, l, k, acc):
    """Returns a list (the cell-selection, in l's order) or None.
    Mirrors: [] 0 acc -> dvB; [] k+1 -> false; _::l 0 -> skip; x::l k+1 -> take || skip."""
    if not l:
        if k == 0:
            return [] if acc % P == 0 else None   # dvB P acc (empty selection)
        return None
    if k == 0:
        return coverExact_wit(P, l[1:], 0, acc)  # skip (budget exhausted)
    x, rest = l[0], l[1:]
    take = coverExact_wit(P, rest, k - 1, acc * x)  # take first (Lean || order)
    if take is not None:
        return [x] + take
    return coverExact_wit(P, rest, k, acc)         # skip


def verify_row(A, t, B):
    """DUAL-METHOD row check on the emitted witness (independent of the DFS)."""
    M = max(A)
    P = gmpy2.mpz(prod(A))
    if len(B) != 4:
        return False
    if list(B) != sorted(B) or len(set(B)) != 4:
        return False
    for b in B:
        if not (t < b <= t + M):
            return False
    x = gmpy2.mpz(1)
    for b in B:
        x *= b
    return x % P == 0


def main():
    t0 = time.time()
    box = box708()
    assert len(box) == 1365, len(box)
    # the table: per A (in box order), the 40 witnesses B_{t=1..40}
    fails = 0
    total = 0
    tab = []           # tab[i] = (A, [B_1, ..., B_40])
    wit_sum = 0        # checksum: sum of all witness elements (determinism receipt)
    for A in box:
        M = max(A)
        P = prod(A)
        row = []
        for t in range(1, T_MAX + 1):
            win = list(range(t + 1, t + M + 1))
            B = coverExact_wit(P, win, 4, 1)
            total += 1
            if B is None or not verify_row(A, t, B):
                fails += 1
                print("FAIL", A, t, B)
                row.append(None)
                continue
            row.append(B)
            wit_sum += sum(B)
        tab.append((A, row))
    print(f"instances: {total}, failures: {fails}, wit_sum: {wit_sum} "
          f"({time.time()-t0:.1f}s)")
    assert fails == 0, fails
    assert total == 54600

    # ---------------- emit the Lean §13 block ----------------
    L = []
    ap = L.append
    ap("/-! ## §13 THE g(4) BOX WITNESS-TABLE DECIDES (the W64-B NO-OOM")
    ap("restructure). -/")
    ap("")
    ap("/-- THE RUNNER-DEATH POST-MORTEM AND THE REPAIR: the r10 aggregate")
    ap("decide (one `decide` over all 1365 x 40 = 54600 coverExact instances)")
    ap("deterministically timed out at the 4M default (run 43585957179);")
    ap("raised to 32M heartbeats it ground ~60 minutes and the hosted runner")
    ap("DIED (run 43589088597 — `lost communication`, the OOM/starvation")
    ap("mode). THE NO-OOM RESTRUCTURE: the box construction is now certified")
    ap("by an EXPLICIT witness table — for every four-element demand set A of")
    ap("the census box and every window start t = 1..40, a covering")
    ap("cell-selection of size EXACTLY 4, as data, in exact box708 order —")
    ap("chunk-decided at the 480-instance discipline (12 A-rows x 40 t per")
    ap("chunk, 114 chunks, every chunk its own bounded `decide`), assembled")
    ap("by an append lemma, and bridged back to THE ORIGINAL AGGREGATE")
    ap("STATEMENT (`e708_g4_box_exact`, verbatim) via `e708_exact_enum_complete`.")
    ap("The Python mirror hunted every witness with the coverExact DFS (the")
    ap("Lean def transcribed literally) and dual-method verified each emitted")
    ap("row (subset-of-window + length + ascent + gmpy2 divisibility) —")
    ap("54600/54600 rows GREEN, g4_witgen_out.txt. Zero sorry. Zero admit. -/")
    ap("")
    ap("/-- THE EXACTLY-4 ROW CHECKER: the corpus's |B| = g(n) cell as a Bool —")
    ap("length EXACTLY 4, strict ascent, window residency, divisibility cover. -/")
    ap("def w708OK4 (A : List Nat) (t : Nat) (B : List Nat) : Bool :=")
    ap("  (decide (B.length = 4)) && (ascB B) &&")
    ap("    (B.all (fun b => (decide (t < b)) && (decide (b ≤ t + maxA A)))) &&")
    ap("    (decide (prod708 B % prod708 A = 0))")
    ap("")
    ap("/-- THE ROW-CHECKER SPEC: a true row certifies the exact-4 cover in")
    ap("the corpus's own terms. -/")
    ap("theorem w708OK4_spec (A : List Nat) (t : Nat) (B : List Nat)")
    ap("    (h : w708OK4 A t B = true) :")
    ap("    B.length = 4 ∧ sub708 B (win708 t (maxA A)) ∧ prod708 A ∣ prod708 B := by")
    ap("  simp only [w708OK4, Bool.and_eq_true] at h")
    ap("  obtain ⟨⟨⟨h4, hasc⟩, hall⟩, hcov⟩ := h")
    ap("  have hmem : ∀ b, b ∈ B → t < b ∧ b ≤ t + maxA A := by")
    ap("    intro b hb")
    ap("    have hrow := (List.all_eq_true.mp hall) b hb")
    ap("    simp only [Bool.and_eq_true] at hrow")
    ap("    exact ⟨of_decide_eq_true hrow.1, of_decide_eq_true hrow.2⟩")
    ap("  exact ⟨of_decide_eq_true h4, e708_asc_bridge t (maxA A) B hasc hmem,")
    ap("    Nat.dvd_of_mod_eq_zero (of_decide_eq_true hcov)⟩")
    ap("")
    ap("/-- The bounded nth (default [] — a misaligned lookup can never pass")
    ap("the row checker: the empty product 1 is never divisible by")
    ap("prod(A) >= 24, so alignment failures FAIL loudly, never silently). -/")
    ap("def nthD708 : List (List Nat) → Nat → List Nat")
    ap("  | [], _ => []")
    ap("  | B :: _, 0 => B")
    ap("  | _ :: W, n + 1 => nthD708 W n")
    ap("")
    ap("/-- THE TABLE ROW: p = (A, [B_1, ..., B_40]) — the 40 exactly-4")
    ap("covers of A at t = 1..40, in order. -/")
    ap("def rowOK708 (p : List Nat × List (List Nat)) : Bool :=")
    ap("  (List.range 40).all (fun r => w708OK4 p.1 (r + 1) (nthD708 p.2 r))")
    ap("")
    ap("/-- THE APPEND LEMMA (core-only, self-proven): chunk concatenation")
    ap("assembles the row table. -/")
    ap("theorem e708_all_append (f : List Nat × List (List Nat) → Bool)")
    ap("    (l₁ l₂ : List (List Nat × List (List Nat)))")
    ap("    (h₁ : l₁.all f = true) (h₂ : l₂.all f = true) :")
    ap("    (l₁ ++ l₂).all f = true := by")
    ap("  apply List.all_eq_true.mpr")
    ap("  intro x hx")
    ap("  rcases List.mem_append.mp hx with hx | hx")
    ap("  · exact (List.all_eq_true.mp h₁) x hx")
    ap("  · exact (List.all_eq_true.mp h₂) x hx")
    ap("")
    nchunks = (len(tab) + ROWS_PER_CHUNK - 1) // ROWS_PER_CHUNK
    ap(f"/-! ### The {nchunks} witness chunks (the 480-instance NO-OOM discipline). -/")
    ap("")
    # ---- chunk defs ----
    for k in range(nchunks):
        rows = tab[k * ROWS_PER_CHUNK:(k + 1) * ROWS_PER_CHUNK]
        ap(f"def wchunk708_{k} : List (List Nat × List (List Nat)) :=")
        ap("  [")
        for i, (A, wrow) in enumerate(rows):
            A_s = "[" + ", ".join(str(x) for x in A) + "]"
            ap(f"    ({A_s}, [")
            for j, B in enumerate(wrow):
                B_s = "[" + ", ".join(str(x) for x in B) + "]"
                ap(f"      {B_s}" + ("," if j < len(wrow) - 1 else ""))
            ap("    ])" + ("," if i < len(rows) - 1 else ""))
        ap("  ]")
        ap("")
    # ---- the full table = the append chain ----
    names = [f"wchunk708_{k}" for k in range(nchunks)]
    ap("/-- THE FULL WITNESS TABLE (the box's 1365 A-rows in exact box708")
    ap("order, each with its 40 covers): the append chain of the chunks. -/")
    ap("def wrows708 : List (List Nat × List (List Nat)) :=")
    chain = ""
    for i, nm in enumerate(names):
        chain += nm + (" ++ " if i < len(names) - 1 else "")
        if (i + 1) % 8 == 0 and i < len(names) - 1:
            ap("  " + chain)
            chain = ""
    if chain:
        ap("  " + chain)
    ap("")
    # ---- chunk cert theorems ----
    for k in range(nchunks):
        ap(f"theorem e708_g4_chunk_{k} : (wchunk708_{k}).all rowOK708 = true := by")
        ap("  decide")
    ap("")
    # ---- the assembly ----
    ap("/-- THE TABLE ASSEMBLY: every row of the full table is certified")
    ap(f"(the {nchunks} chunk decides composed by the append lemma). -/")
    ap("theorem e708_g4_rows_exact : wrows708.all rowOK708 = true := by")
    # build bottom-up
    ap(f"  have s{nchunks-1} : (wchunk708_{nchunks-1}).all rowOK708 = true := e708_g4_chunk_{nchunks-1}")
    for k in range(nchunks - 2, -1, -1):
        # RIGHT-ASSOC rest term: w_{k+1} ++ (w_{k+2} ++ (... ++ w_last))
        # (must match the previous have's LHS syntactically — Lean's ++ is right-assoc)
        inner = names[nchunks - 1]
        for m in range(nchunks - 2, k, -1):
            inner = f"({names[m]} ++ {inner})"
        tgt = f"(wchunk708_{k} ++ {inner}).all rowOK708 = true"
        ap(f"  have s{k} : {tgt} :=")
        ap(f"    e708_all_append rowOK708 wchunk708_{k} ({inner}) e708_g4_chunk_{k} s{k+1}")
    ap("  exact s0")
    ap("")
    # ---- the domain cert ----
    ap("/-- THE ALIGNMENT CERTIFICATE: the table's demand-set column IS")
    ap("box708 (kernel-decided list equality — the data cannot drift from")
    ap("the computed box). -/")
    ap("theorem e708_wrows_dom : (wrows708.map Prod.fst) = box708 := by")
    ap("  decide")
    ap("")
    # ---- the aggregate, original statement ----
    ap("/-- THE BOX CONSTRUCTION DECIDE (THE ORIGINAL AGGREGATE STATEMENT,")
    ap("verbatim — now proven from the certified witness table): for every")
    ap("four-element demand set A of the census box and every window start")
    ap("t = 1..40 (r = t - 1), the exact-budget enumerator finds an")
    ap("exactly-4 cover: 1365 x 40 = 54600 instances, table-certified.")
    ap("The Python mirror ran the identical DFS over the same box with")
    ap("0 failures — g4_verify_out.txt (B) + g4_witgen_out.txt. -/")
    ap("theorem e708_g4_box_exact : (box708).all (fun A =>")
    ap("    (List.range 40).all (fun r =>")
    ap("      coverExact (prod708 A) (win708 (r + 1) (maxA A)) 4 1)) = true := by")
    ap("  apply List.all_eq_true.mpr")
    ap("  intro A hA")
    ap("  rw [← e708_wrows_dom] at hA")
    ap("  obtain ⟨p, hp, hAp⟩ := List.mem_map.mp hA")
    ap("  subst hAp")
    ap("  have hrow := (List.all_eq_true.mp e708_g4_rows_exact) p hp")
    ap("  have hrow' : ((List.range 40).all (fun r =>")
    ap("      w708OK4 p.1 (r + 1) (nthD708 p.2 r))) = true := hrow")
    ap("  apply List.all_eq_true.mpr")
    ap("  intro r hr")
    ap("  have hw := (List.all_eq_true.mp hrow') r hr")
    ap("  obtain ⟨h4, hsub, hdvd⟩ := w708OK4_spec p.1 (r + 1) (nthD708 p.2 r) hw")
    ap("  exact e708_exact_enum_complete (prod708 p.1) (win708 (r + 1) (maxA p.1))")
    ap("    4 1 (nthD708 p.2 r) hsub h4 (by rw [Nat.one_mul]; exact hdvd)")
    block = "\n".join(L) + "\n"

    # ---------------- splice into Erdos708.lean ----------------
    src = open(LEAN).read().split("\n")
    # locate the old §13: from the header line to the end of the old box_exact theorem
    i13 = None
    for i, ln in enumerate(src):
        if ln.startswith("/-! ## §13 THE BOX CONSTRUCTION DECIDE"):
            i13 = i
            break
    assert i13 is not None, "§13 header not found"
    # end: the line '  decide' that terminates the old box_exact theorem
    iend = None
    for i in range(i13, len(src)):
        if src[i] == "  decide" and "e708_g4_box_exact" in "\n".join(src[i-6:i+1]):
            iend = i
            break
    assert iend is not None, "old box_exact end not found"
    newsrc = src[:i13] + block.split("\n")[:-1] + src[iend + 1:]
    open(LEAN, "w").write("\n".join(newsrc))
    print(f"spliced: old §13 lines {i13}..{iend} ({iend-i13+1} lines) -> "
          f"{len(block.splitlines())} lines; file now {len(newsrc)} lines")

    # ---------------- receipt ----------------
    with open(OUT + "/g4_witgen_out.txt", "w") as f:
        f.write("=== #708 W64-B THE NO-OOM WITNESS-TABLE RESTRUCTURE ===\n")
        f.write(f"box708 rows: {len(tab)} (C(15,4) = 1365)\n")
        f.write(f"(A,t) instances: {total} (1365 x 40)\n")
        f.write(f"witness rows verified (dual: DFS-hunt + explicit recheck): "
                f"{total - fails}/{total}, failures: {fails}\n")
        f.write(f"chunks: {nchunks} x <= {ROWS_PER_CHUNK} A-rows "
                f"({ROWS_PER_CHUNK * 40} instances per chunk, <= 501 law)\n")
        f.write(f"witness-element checksum (determinism): {wit_sum}\n")
        f.write(f"generator: {time.time()-t0:.1f}s\n")
        f.write("VERDICT: GREEN — witness table complete, dual-method verified\n")
    print("receipt written")


if __name__ == "__main__":
    main()
