#!/usr/bin/env python3
"""
THE §7 FREEZE GENERATOR v2 — f(2,2) = 254 UNCONDITIONAL.
Kills `hob : obstructionCheck = true` of erdos404_f22_exact via the module ladder.

Module DAG:
  ExactF22 -> F22DataS (254 state-set literals)
           -> F22DataC (coin literals + recursive suffix defs)
           -> F22DataD1/2 (flatMap chunks + dedup accumulators + L defs)
           -> F22Chain (ddA + unfold lemmas)
  ExactF22 -> F22SweepA (coinFrom + spec + levels 0..126) -> F22SweepB (levels 127..252 + assembly + coinList_eq)
  F22SweepB -> F22Coins (insert + sort ladders -> table_eq)
  F22DataS/C/D + F22Chain -> F22FM0/1 (flatMap decides) , F22DD* (chunk decides + dd chains)
  F22Coins + FM* + DD* -> F22Asm0/1 (round + run theorems) -> F22All (all-chain + FINAL THEOREM)

Key corrections vs the wiped build (baked in):
  - The DP rounds use the SORTED coins fz_C_r (table order), NOT fz_UC_r.
  - The last dedup chunk gets NO fz_ddA application (the old regex-patch bug).
  - coinFrom_spec is FILTER-FREE (Base's classOf_bound_all absorbs the filter).
"""
import os, sys

WAR   = "/home/z/f22war"
REPO  = "/home/z/erdos-weak-problems"
CHAIN = os.path.join(REPO, "problem404-q3-chain")
CP    = 262
NROUND = 253
WORK_CAP = 60000

OPTIONS = """set_option exponentiation.threshold 1024
set_option maxHeartbeats 4000000
set_option maxRecDepth 262144"""

# ============================================================ dumps
def parse_dumps():
    raw = open(os.path.join(WAR, "dumps_raw.txt")).read()
    big = " ".join(raw.split())
    def chunk_from(pos, opener):
        i = big.index(opener, pos)
        depth = 0
        for j in range(i, len(big)):
            if big[j] == '[': depth += 1
            elif big[j] == ']':
                depth -= 1
                if depth == 0:
                    return eval(big[i:j+1]), j+1
        raise ValueError("unbalanced")
    coinList, p1 = chunk_from(0, "[(3,")
    table,    p2 = chunk_from(p1, "[(3,")
    allSets,  p3 = chunk_from(p2, "[[(0, 1)]")
    return coinList, table, allSets

# ============================================================ Python DP
def v2(n): return (n & -n).bit_length() - 1 if n else 0
def fact(n):
    r = 1
    for i in range(2, n+1): r *= i
    return r
def P_(i): return fact(i) // 2
def classOf(i): return v2(P_(i))
def coinUnit(i):
    c = classOf(i)
    return (P_(i) // (1 << c)) % (1 << (CP - c))
def insertCoin(c, ds):
    out, ins = [], False
    for d in ds:
        if not ins and (c[1] < d[1] or (c[1] == d[1] and c[0] < d[0])):
            out.append(c); ins = True
        out.append(d)
    if not ins: out.append(c)
    return out
def sortCoins(cs):
    r = []
    for c in reversed(cs): r = insertCoin(c, r)
    return r
def step1(V, t, u, o):
    prec = CP - V
    s = (u * (1 << (t - V)) + o) % (1 << prec)
    if s == 0: return (CP, 1)
    z = v2(s)
    return (V + z, s >> z)
def dedupAux(l, acc):
    for y in l:
        if y not in acc: acc = [y] + acc
    return acc
def stepCoin(c, S):
    V = c[1]
    live = [st for st in S if V <= st[0]]
    stepped = []
    for st in live: stepped.extend([st, step1(V, st[0], st[1], c[2])])
    return dedupAux(stepped, [])
def maxT(S): return max([t for t, _ in S], default=0)

def coin_lit(c): return f"({c[0]}, {c[1]}, {c[2]})"
def set_lit(S): return "[" + ", ".join(f"({p[0]}, {p[1]})" for p in S) + "]"

# ============================================================ main
def main():
    coinList, table, allSets = parse_dumps()
    assert len(coinList) == 253 and len(table) == 253 and len(allSets) == 254
    myCoinList = [(i, classOf(i), coinUnit(i)) for i in range(256) if i >= 3 and classOf(i) <= 246]
    assert [tuple(x) for x in myCoinList] == [tuple(x) for x in coinList], "coinList mismatch"
    assert [tuple(x) for x in sortCoins(myCoinList)] == [tuple(x) for x in table], "table mismatch"
    S = [(0, 1)]; mySets = [S]
    for c in table:
        S = stepCoin(tuple(c), S); mySets.append(S)
    for r in range(254):
        assert [tuple(x) for x in mySets[r]] == [tuple(x) for x in allSets[r]], f"set {r} mismatch"
    assert all(maxT(s) <= 253 for s in mySets)
    print("[PRE-VERIFY] DP: 254/254 sets exact, obstructionCheck = true")

    # sweep data
    F, V = 6, 1
    sweep = []
    for k in range(3, 256):
        cls = V - 1
        u = (F // 2 // (1 << cls)) % (1 << (CP - cls))
        kept = cls <= 246
        assert (not kept) or (k, cls, u) == tuple(coinList[k-3]), f"sweep coin {k} mismatch"
        sweep.append((k, F, V, kept))
        F = (k+1) * F; V = V + v2(k+1)
    assert all(s[3] for s in sweep), "expected all 253 levels kept"
    print("[PRE-VERIFY] sweep: 253/253 coins exact")

    # sort ladder verification
    TAIL = {NROUND: []}
    for r in range(NROUND-1, -1, -1):
        TAIL[r] = [tuple(table[r])] + TAIL[r+1]
    for r in range(NROUND):
        assert insertCoin(tuple(coinList[r]), TAIL[r+1]) == TAIL[r], f"insert {r} mismatch"
    print("[PRE-VERIFY] sort ladder: 253/253 inserts exact")

    # rounds data
    rounds = []
    for r in range(NROUND):
        c = tuple(table[r]); Sin = mySets[r]; Sout = mySets[r+1]
        assert stepCoin(c, Sin) == Sout, f"round {r} mismatch"
        Vc = c[1]
        live = [st for st in Sin if Vc <= st[0]]
        L = []
        for st in live: L.extend([st, step1(Vc, st[0], st[1], c[2])])
        chunks, accs = [], []
        i = 0; acc = []
        while i < len(L):
            j = i; work = 0; tacc = list(acc)
            while j < len(L):
                y = L[j]
                cost = (tacc.index(y) + 1) if y in tacc else len(tacc) + 1
                if work + cost > WORK_CAP and j > i: break
                work += cost
                if y not in tacc: tacc = [y] + tacc
                j += 1
            chunks.append(L[i:j]); accs.append(list(acc))
            acc = dedupAux(L[i:j], acc)
            i = j
        assert acc == Sout, f"round {r} chunked dedup mismatch"
        # verify each chunk theorem
        for ci, ch in enumerate(chunks):
            a = list(accs[ci]); out = dedupAux(ch, a)
            if ci + 1 < len(chunks): assert out == accs[ci+1]
            else: assert out == Sout
        rounds.append(dict(r=r, Sout=Sout, L=L, chunks=chunks, accs=accs))
    total_chunks = sum(len(rd["chunks"]) for rd in rounds)
    print(f"[PRE-VERIFY] rounds: {NROUND}/253 exact, chunks: {total_chunks}")

    def W(name, text):
        open(os.path.join(CHAIN, name), "w").write(text)
        print(f"[EMIT] {name}: {len(text)} bytes, {text.count(chr(10))} lines")

    # ---------------- F22DataS
    t = [f"import ExactF22", "", OPTIONS, "-- The DP trace: fz_S_r = the r-th state set (r = 0 is the initial set)."]
    for r in range(254):
        t.append(f"def fz_S_{r} : List (Nat × Nat) := {set_lit(mySets[r])}")
    W("F22DataS.lean", "\n".join(t) + "\n")

    # ---------------- F22DataC
    t = ["import ExactF22", "", OPTIONS,
         "-- Coin literals + recursive suffix defs.",
         "-- fz_UC_r: r-th coin in coinList order (i ascending); fz_UTAIL_r: unsorted suffix.",
         "-- fz_C_r: r-th coin in table (sorted) order; fz_TAIL_r: sorted suffix."]
    for r in range(NROUND):
        t.append(f"def fz_UC_{r} : Nat × Nat × Nat := {coin_lit(coinList[r])}")
    t.append(f"def fz_UTAIL_{NROUND} : List (Nat × Nat × Nat) := []")
    for r in range(NROUND-1, -1, -1):
        t.append(f"def fz_UTAIL_{r} : List (Nat × Nat × Nat) := fz_UC_{r} :: fz_UTAIL_{r+1}")
    for r in range(NROUND):
        t.append(f"def fz_C_{r} : Nat × Nat × Nat := {coin_lit(table[r])}")
    t.append(f"def fz_TAIL_{NROUND} : List (Nat × Nat × Nat) := []")
    for r in range(NROUND-1, -1, -1):
        t.append(f"def fz_TAIL_{r} : List (Nat × Nat × Nat) := fz_C_{r} :: fz_TAIL_{r+1}")
    W("F22DataC.lean", "\n".join(t) + "\n")

    # ---------------- F22DataD1/2
    for half, (lo, hi) in enumerate([(0, 127), (127, NROUND)]):
        t = ["import ExactF22", "", OPTIONS, "-- flatMap outputs (chunked) + dedup accumulators."]
        for rd in rounds[lo:hi]:
            r = rd["r"]; chs = rd["chunks"]
            for j, ch in enumerate(chs):
                t.append(f"def fz_CH_{r}_{j+1} : List (Nat × Nat) := {set_lit(ch)}")
            for j, ac in enumerate(rd["accs"]):
                t.append(f"def fz_A_{r}_{j+1} : List (Nat × Nat) := {set_lit(ac)}")
            if len(chs) == 1:
                t.append(f"def fz_L_{r} : List (Nat × Nat) := fz_CH_{r}_1")
            else:
                inner = f"fz_CH_{r}_{len(chs)}"
                for j in range(len(chs)-1, 0, -1):
                    inner = f"(fz_CH_{r}_{j} ++ {inner})"
                t.append(f"def fz_L_{r} : List (Nat × Nat) := {inner}")
        W(f"F22DataD{half+1}.lean", "\n".join(t) + "\n")

    # ---------------- F22Chain
    W("F22Chain.lean", f"""import ExactF22

{OPTIONS}

/-- dedupAux is chunk-associative. -/
theorem fz_dedupAux_cons (y : Nat × Nat) (ys : List (Nat × Nat)) (acc : List (Nat × Nat)) :
    dedupAux (y :: ys) acc = if memB y acc then dedupAux ys acc else dedupAux ys (y :: acc) := by
  simp only [dedupAux]

theorem fz_ddA : ∀ (l₁ l₂ : List (Nat × Nat)) (acc : List (Nat × Nat)),
    dedupAux (l₁ ++ l₂) acc = dedupAux l₂ (dedupAux l₁ acc) := by
  intro l₁
  induction l₁ with
  | nil => intro l₂ acc; rfl
  | cons y ys ih =>
      intro l₂ acc
      rw [List.cons_append, fz_dedupAux_cons, fz_dedupAux_cons]
      by_cases h : memB y acc = true
      · rw [if_pos h, if_pos h, ih]
      · rw [if_neg h, if_neg h, ih]

/-- stepCoin in the frozen form. -/
theorem fz_stepCoin_eq (c : Nat × Nat × Nat) (S : List (Nat × Nat)) :
    stepCoin c S = dedupAux ((S.filter (fun st => decide (c.2.1 ≤ st.1))).flatMap
      (fun st => [st, step1 c.2.1 st.1 st.2 c.2.2])) [] := by rfl

/-- dpRun in the frozen form. -/
theorem fz_dpRun_cons (c : Nat × Nat × Nat) (cs : List (Nat × Nat × Nat)) (S : List (Nat × Nat)) :
    dpRun (c :: cs) S = stepCoin c S :: dpRun cs (stepCoin c S) := by rfl
""")

    # ---------------- F22SweepA
    t = [f"""import ExactF22
import F22DataC

{OPTIONS}

/-- The sweep: builds the coin list from k upward, carrying (k, fact k, v2 (fact k)).
    Fuel-structural (first param counts down). -/
def coinFrom : Nat → Nat → Nat → Nat → List (Nat × Nat × Nat)
  | 0, _, _, _ => []
  | f + 1, k, F, V =>
      let cls := V - 1
      let u := (F / 2 / 2 ^ cls) % 2 ^ (CP - cls)
      if cls ≤ 246 then (k, cls, u) :: coinFrom f (k + 1) ((k + 1) * F) (V + v2 (k + 1))
      else coinFrom f (k + 1) ((k + 1) * F) (V + v2 (k + 1))

theorem coinFrom_ne (f k F V : Nat) :
    coinFrom (f + 1) k F V =
      (if V - 1 ≤ 246 then (k, V - 1, (F / 2 / 2 ^ (V - 1)) % 2 ^ (CP - (V - 1))) :: coinFrom f (k + 1) ((k + 1) * F) (V + v2 (k + 1))
      else coinFrom f (k + 1) ((k + 1) * F) (V + v2 (k + 1))) := by
  simp only [coinFrom]

/-- map congruence (core lacks List.map_congr). -/
theorem fz_map_congr {{α β : Type}} {{f g : α → β}} : ∀ (l : List α),
    (∀ x, x ∈ l → f x = g x) → l.map f = l.map g := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a as ih =>
      intro h
      rw [List.map_cons, List.map_cons, h a (List.Mem.head _),
          ih (fun x hx => h x (List.Mem.tail _ hx))]

/-- range' start-shift. -/
theorem fz_range'_map : ∀ (n s : Nat), List.range' (s + 1) n = (List.range' s n).map (fun x => x + 1) := by
  intro n
  induction n with
  | zero => intro s; rfl
  | succ n ih =>
      intro s
      rw [List.range'_succ, List.range'_succ, List.map_cons, ih (s + 1)]

/-- range front-peel (via the range' bridge). -/
theorem fz_range_front (n : Nat) : List.range (n + 1) = 0 :: (List.range n).map (fun x => x + 1) := by
  rw [List.range_eq_range', List.range_eq_range', List.range'_succ, fz_range'_map n 0]

/-- THE SPEC (filter-free: Base's classOf_bound_all absorbs the filter). -/
theorem coinFrom_spec : ∀ (N k F V : Nat), k + N = 256 → 3 ≤ k → F = fact k → V = v2 (fact k) →
    coinFrom N k F V = (List.range N).map (fun j => (j + k, classOf (j + k), coinUnit (j + k))) := by
  intro N
  induction N with
  | zero =>
      intro k F V hk _ _ _
      obtain rfl : k = 256 := by omega
      rfl
  | succ N ih =>
      intro k F V hk h3 hF hV
      have hk255 : k < 256 := by omega
      have hbound : classOf k ≤ 246 := by
        have hq := List.all_eq_true.mp classOf_bound_all k (List.mem_range.mpr hk255)
        rw [Bool.or_eq_true] at hq
        cases hq with
        | inl hlt3 => exact absurd (of_decide_eq_true hlt3) (by omega)
        | inr hb => exact of_decide_eq_true hb
      have hcls : V - 1 = classOf k := by
        have hc := v2_fact_classOf k (by omega)
        omega
      have hunit : F / 2 / 2 ^ classOf k % 2 ^ (CP - classOf k) = coinUnit k := by
        unfold coinUnit P
        rw [hF]
      have hF' : (k + 1) * F = fact (k + 1) := by rw [hF, ← fact_succ]
      have hV' : V + v2 (k + 1) = v2 (fact (k + 1)) := by
        have key := v2_mul ((k + 1) + F) (k + 1) F (by omega) (by omega) (by rw [hF]; exact fact_pos k)
        rw [hF, ← hV, ← fact_succ] at key
        omega
      have hkeep : V - 1 ≤ 246 := by rw [hcls]; exact hbound
      rw [coinFrom_ne N k F V, if_pos hkeep, hcls, hunit]
      rw [ih (k + 1) ((k + 1) * F) (V + v2 (k + 1)) (by omega) (by omega) hF' hV']
      rw [fz_range_front N, List.map_cons, List.map_map]
      congr 1
      · simp only [Nat.zero_add]
      · apply fz_map_congr
        intro x hx
        have hxe : x + 1 + k = x + (k + 1) := by omega
        simp only [Function.comp_apply]
        rw [hxe]
"""]
    for (k, F, V, kept) in sweep[:127]:
        r = k - 3
        F2, V2_ = (k+1) * F, V + v2(k+1)
        fuel, fuel2 = 253 - r, 252 - r
        if kept:
            t.append(f"theorem fz_cf_{r} : coinFrom {fuel} {k} {F} {V} = {coin_lit(coinList[r])} :: coinFrom {fuel2} {k+1} {F2} {V2_} := by rfl")
        else:
            t.append(f"theorem fz_cf_{r} : coinFrom {fuel} {k} {F} {V} = coinFrom {fuel2} {k+1} {F2} {V2_} := by rfl")
    W("F22SweepA.lean", "\n".join(t) + "\n")

    # ---------------- F22SweepB
    t = ["import F22SweepA", "", OPTIONS, "-- levels 127..252 + the suffix assembly + coinList_eq."]
    for (k, F, V, kept) in sweep[127:]:
        r = k - 3
        F2, V2_ = (k+1) * F, V + v2(k+1)
        fuel, fuel2 = 253 - r, 252 - r
        if kept:
            t.append(f"theorem fz_cf_{r} : coinFrom {fuel} {k} {F} {V} = {coin_lit(coinList[r])} :: coinFrom {fuel2} {k+1} {F2} {V2_} := by rfl")
        else:
            t.append(f"theorem fz_cf_{r} : coinFrom {fuel} {k} {F} {V} = coinFrom {fuel2} {k+1} {F2} {V2_} := by rfl")
    # the assembly (from the end); r indexes UTAIL (k = r + 3)
    t.append(f"theorem fz_sw_all_{NROUND-1} : coinFrom 1 255 {sweep[252][1]} {sweep[252][2]} = fz_UTAIL_{NROUND-1} := by rw [fz_cf_{NROUND-1}]; rfl")
    for r in range(NROUND-2, -1, -1):
        t.append(f"theorem fz_sw_all_{r} : coinFrom {253-r} {r+3} {sweep[r][1]} {sweep[r][2]} = fz_UTAIL_{r} := by rw [fz_cf_{r}, fz_sw_all_{r+1}]; rfl")
    # coinList_eq
    t.append(f"""
/-- The coinList filter is constantly-`3 ≤ i` (classOf_bound_all). -/
theorem fz_filter_pt (i : Nat) (hi : i < 256) :
    (decide (3 ≤ i) && decide (classOf i ≤ 246)) = decide (3 ≤ i) := by
  have hq := List.all_eq_true.mp classOf_bound_all i (List.mem_range.mpr hi)
  rw [Bool.or_eq_true] at hq
  cases hq with
  | inl hlt3 =>
      have hi3 : i < 3 := of_decide_eq_true hlt3
      have hn : ¬ (3 ≤ i) := by omega
      rw [decide_eq_false hn, Bool.false_and]
  | inr hb =>
      rw [decide_eq_true (of_decide_eq_true hb), Bool.and_true]

/-- range 256 filtered by 3 ≤ · = map (+3) (range 253). -/
theorem fz_filter_singleton_true (a : Nat) (h : decide (3 ≤ a) = true) :
    List.filter (fun i => decide (3 ≤ i)) [a] = [a] := by
  simp only [List.filter]
  rw [h]

theorem fz_range_filter_ge (N : Nat) :
    ((List.range (N + 3)).filter (fun i => decide (3 ≤ i))) = (List.range N).map (fun x => x + 3) := by
  induction N with
  | zero => rfl
  | succ N ih =>
      have hrw : N + 1 + 3 = N + 3 + 1 := by omega
      rw [hrw, List.range_succ, List.filter_append, ih, List.range_succ, List.map_append,
          List.map_cons, List.map_nil]
      rw [fz_filter_singleton_true (N + 3) (decide_eq_true (by omega))]

theorem coinList_eq : coinList = fz_UTAIL_0 := by
  unfold coinList
  rw [show (256 : Nat) = 253 + 3 from rfl,
      List.filter_congr (fun i hi => fz_filter_pt i (List.mem_range.mp hi)),
      fz_range_filter_ge 253, List.map_map]
  show List.map (fun x => (x + 3, classOf (x + 3), coinUnit (x + 3))) (List.range 253) = fz_UTAIL_0
  rw [← coinFrom_spec 253 3 6 1 (by omega) (by omega) (by rfl) (by decide)]
  exact fz_sw_all_0
""")
    W("F22SweepB.lean", "\n".join(t) + "\n")

    # ---------------- F22Coins
    t = ["import F22SweepB", "", OPTIONS, "-- the insert ladder + the sort ladder + table_eq."]
    for r in range(NROUND):
        t.append(f"theorem fz_is_{r} : insertCoin fz_UC_{r} fz_TAIL_{r+1} = fz_TAIL_{r} := by decide +kernel")
    t.append("""theorem fz_sortCoins_cons (c : Nat × Nat × Nat) (cs : List (Nat × Nat × Nat)) :
    sortCoins (c :: cs) = insertCoin c (sortCoins cs) := by rfl""")
    t.append(f"theorem fz_sc_{NROUND} : sortCoins fz_UTAIL_{NROUND} = fz_TAIL_{NROUND} := by rfl")
    for r in range(NROUND-1, -1, -1):
        t.append(f"""theorem fz_sc_{r} : sortCoins fz_UTAIL_{r} = fz_TAIL_{r} := by
  show sortCoins (fz_UC_{r} :: fz_UTAIL_{r+1}) = fz_TAIL_{r}
  rw [fz_sortCoins_cons, fz_sc_{r+1}]
  exact fz_is_{r}""")
    t.append("""
/-- THE SORTED TABLE, FROZEN: table = fz_TAIL_0. -/
theorem table_eq : table = fz_TAIL_0 := by
  rw [table, coinList_eq, fz_sc_0]
""")
    W("F22Coins.lean", "\n".join(t) + "\n")

    # ---------------- F22FM0/1
    for half, (lo, hi) in enumerate([(0, 127), (127, NROUND)]):
        t = [f"import ExactF22\nimport F22DataS\nimport F22DataC\nimport F22DataD{half+1}\n\n{OPTIONS}\n-- flatMap decides."]
        for rd in rounds[lo:hi]:
            r = rd["r"]
            t.append(f"""theorem fz_FM_{r} : (fz_S_{r}.filter (fun st => decide (fz_C_{r}.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_{r}.2.1 st.1 st.2 fz_C_{r}.2.2]) = fz_L_{r} := by decide +kernel""")
        W(f"F22FM{half}.lean", "\n".join(t) + "\n")

    # ---------------- F22DD* : THIN slicing (the residue law: ~25 single-chunk decides or 1 multi-chunk round per process)
    singles = [rd for rd in rounds if len(rd["chunks"]) == 1]
    multis  = [rd for rd in rounds if len(rd["chunks"]) > 1]
    SLICE = 25
    n_s_mod = (len(singles) + SLICE - 1) // SLICE
    for idx in range(n_s_mod):
        lo, hi = idx * SLICE, min((idx + 1) * SLICE, len(singles))
        t = [f"import ExactF22\nimport F22DataS\nimport F22DataC\nimport F22DataD1\nimport F22DataD2\n\n{OPTIONS}\n-- single-chunk dedup decides + chains (slice {idx})."]
        for rd in singles[lo:hi]:
            r = rd["r"]
            t.append(f"theorem fz_dcr_{r}_1 : dedupAux fz_CH_{r}_1 fz_A_{r}_1 = fz_S_{r+1} := by decide +kernel")
            t.append(f"theorem fz_dd_{r} : dedupAux fz_L_{r} [] = fz_S_{r+1} := fz_dcr_{r}_1")
        W(f"F22DD{idx}.lean", "\n".join(t) + "\n")
    mmods = []
    for idx, rd in enumerate(multis):
        r = rd["r"]; n = len(rd["chunks"])
        lines = [f"import ExactF22\nimport F22DataS\nimport F22DataC\nimport F22DataD1\nimport F22DataD2\nimport F22Chain\n\n{OPTIONS}\n-- multi-chunk round {r} ({n} chunks)."]
        for j in range(1, n + 1):
            tgt = f"fz_A_{r}_{j+1}" if j < n else f"fz_S_{r+1}"
            lines.append(f"theorem fz_dcr_{r}_{j} : dedupAux fz_CH_{r}_{j} fz_A_{r}_{j} = {tgt} := by decide +kernel")
        inner = f"fz_CH_{r}_{n}"
        for j in range(n - 1, 0, -1):
            inner = f"(fz_CH_{r}_{j} ++ {inner})"
        rws = []
        for j in range(1, n):
            rws.append("fz_ddA"); rws.append(f"fz_dcr_{r}_{j}")
        rws.append(f"fz_dcr_{r}_{n}")
        lines.append(f"""theorem fz_dd_{r} : dedupAux fz_L_{r} [] = fz_S_{r+1} := by
  show dedupAux {inner} fz_A_{r}_1 = fz_S_{r+1}
  rw [{", ".join(rws)}]""")
        W(f"F22DDm{idx}.lean", "\n".join(lines) + "\n")
        mmods.append(f"F22DDm{idx}")

    # ---------------- F22Asm0/1
    dd_imports = [f"F22DD{i}" for i in range(n_s_mod)] + mmods
    for half, (lo, hi) in enumerate([(0, 127), (127, NROUND)]):
        t = [f"""import F22Chain
import F22Coins
import F22DataS
import F22DataC
import F22FM{half}
""" + "\n".join(f"import {m}" for m in dd_imports) + f"""

{OPTIONS}
-- round + run theorems (pure rewrites)."""]
        for rd in rounds[lo:hi]:
            r = rd["r"]
            t.append(f"""theorem fz_round_{r} : stepCoin fz_C_{r} fz_S_{r} = fz_S_{r+1} := by
  rw [fz_stepCoin_eq, fz_FM_{r}]
  exact fz_dd_{r}""")
        for rd in rounds[lo:hi]:
            r = rd["r"]
            t.append(f"""theorem fz_run_{r} : dpRun fz_TAIL_{r} fz_S_{r} = fz_S_{r+1} :: dpRun fz_TAIL_{r+1} fz_S_{r+1} := by
  show dpRun (fz_C_{r} :: fz_TAIL_{r+1}) fz_S_{r} = fz_S_{r+1} :: dpRun fz_TAIL_{r+1} fz_S_{r+1}
  rw [fz_dpRun_cons, fz_round_{r}]""")
        W(f"F22Asm{half}.lean", "\n".join(t) + "\n")

    # ---------------- F22All slices + thin final (the monolithic 254-decl OOM cure)
    def fz_all_block(r):
        if r == NROUND:
            return ["/-- The all-chain: every set of the run satisfies the maxT bound. -/",
                    f"theorem fz_all_{NROUND} : List.all (dpRun fz_TAIL_{NROUND} fz_S_{NROUND}) (fun S => decide (maxT S \u2264 253)) = true := by rfl"]
        nxt = r + 1
        return [f"theorem fz_all_{r} : List.all (dpRun fz_TAIL_{r} fz_S_{r}) (fun S => decide (maxT S \u2264 253)) = true := by",
                "  rw [fz_run_%d, List.all_cons, Bool.and_eq_true]" % r,
                "  exact \u27e8by decide +kernel, fz_all_%d\u27e9" % nxt]
    KILL_FINAL = """
/-- **THE HYPOTHESIS KILL: obstructionCheck = true, UNCONDITIONALLY.** -/
theorem obstructionCheck_true : obstructionCheck = true := by
  unfold obstructionCheck allSets
  rw [table_eq, List.all_cons, Bool.and_eq_true]
  exact \u27e8by decide +kernel, fz_all_0\u27e9

/-- **f(2,2) = 254 \u2014 UNCONDITIONAL, ZERO HYPOTHESES.** -/
theorem erdos404_f22_final :
    v2 (2 + (witnessB.map fact).sum) = 254
    \u2227 \u2200 B : List Nat, NoDupL B \u2192 (\u2200 i \u2208 B, 3 \u2264 i) \u2192
      v2 (2 + (B.map fact).sum) \u2264 254 :=
  erdos404_f22_exact obstructionCheck_true

#print axioms obstructionCheck_true
#print axioms erdos404_f22_final
"""
    slices = [("F22AllA", "import F22Asm0\nimport F22Asm1", range(NROUND, 221, -1)),
              ("F22AllB", "import F22AllA", range(221, 189, -1)),
              ("F22AllC", "import F22AllB", range(189, 157, -1)),
              ("F22AllD", "import F22AllC", range(157, 125, -1)),
              ("F22AllE", "import F22AllD", range(125, 93, -1)),
              ("F22AllF", "import F22AllE", range(93, 61, -1)),
              ("F22AllG", "import F22AllF", range(61, 29, -1)),
              ("F22AllH", "import F22AllG", range(29, 0, -1))]
    for name, imp, rng in slices:
        body = []
        for r in rng:
            body.extend(fz_all_block(r)); body.append("")
        W(name + ".lean", imp + "\n\n" + OPTIONS + "\n\n" + "\n".join(body) + "\n")
    tail = []
    tail.extend(fz_all_block(0)); tail.append("")
    W("F22All.lean", "import F22AllH\n\n" + OPTIONS + "\n\n" + "\n".join(tail) + KILL_FINAL)

    print(f"\n[DONE] modules emitted to {CHAIN}")
    print("Total chunks:", total_chunks, "| multi-chunk rounds:", len(multis), "| DDm modules:", len(mmods))

if __name__ == "__main__":
    main()
