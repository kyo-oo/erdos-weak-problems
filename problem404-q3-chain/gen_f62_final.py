#!/usr/bin/env python3
"""
THE §7 FREEZE GENERATOR — f(6,2) = 133 UNCONDITIONAL (the (6,2) port).
Kills `hob : obstructionCheck = true` of erdos404_f62_exact via the module
ladder (the Kill-#14 architecture at half scale — L83/L84 doctrine).

Port constants (ExactF62): CP = 138, P i = fact i / 720, coins i ∈ [7,135]
(filter 7 ≤ i && classOf i ≤ 127 — all kept), NROUND = 129, initial set
[(0,1)], bound maxT ≤ 129, cls = V − 4 (v2 720 = 4), sweep k = 7..135,
F₀ = fact 7 = 5040, V₀ = 4.

Module DAG (F62 twins of the F22 ladder):
  ExactF62 -> F62DataS (130 state-set literals)
           -> F62DataC (coin literals + recursive suffix defs)
           -> F62DataD1/2 (flatMap chunks + dedup accumulators + L defs)
           -> F62Chain (ddA + unfold lemmas)
  ExactF62 -> F62SweepA (coinFrom + spec + levels 0..64) -> F62SweepB (levels 65..128 + assembly + coinList_eq)
  F62SweepB -> F62Coins (insert + sort ladders -> table_eq)
  F62DataS/C/D + F62Chain -> F62FM0/1 (flatMap decides), F62DD* (chunk decides + dd chains)
  F62Coins + FM* + DD* -> F62Asm0/1 (round + run theorems) -> F62All* (all-chain + FINAL THEOREM)
"""
import os

REPO  = "/home/z/my-project/erdos-weak-problems"
CHAIN = os.path.join(REPO, "problem404-q3-chain")
CP    = 138
NROUND = 129
BOUND  = 129     # maxT ≤ 129  (g(6,2) = 129, first unreachable 130)
K0     = 7       # first coin index
KN     = 136     # range 136  (coins 7..135)
F0     = 5040    # fact 7
V0     = 4       # v2 (fact 7)
VBAS   = 4       # v2 720
CLSCAP = 127     # classOf ≤ 127
WORK_CAP = 60000

OPTIONS = """set_option exponentiation.threshold 1024
set_option maxHeartbeats 4000000
set_option maxRecDepth 262144"""

# ============================================================ Python DP
def v2(n): return (n & -n).bit_length() - 1 if n else 0
def fact(n):
    r = 1
    for i in range(2, n+1): r *= i
    return r
def P_(i): return fact(i) // 720
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
    # --- the coin list (all 129 kept — classOf_bound_all)
    coinList = [(i, classOf(i), coinUnit(i)) for i in range(KN) if i >= K0 and classOf(i) <= CLSCAP]
    assert len(coinList) == NROUND, f"coinList size {len(coinList)} != {NROUND}"
    table = sortCoins(coinList)
    assert len(table) == NROUND
    S = [(0, 1)]; mySets = [S]
    for c in table:
        S = stepCoin(tuple(c), S); mySets.append(S)
    assert len(mySets) == NROUND + 1
    assert all(maxT(s) <= BOUND for s in mySets), "OBSTRUCTION FAILS"
    peak = max(len(s) for s in mySets)
    print(f"[PRE-VERIFY] DP: {NROUND+1}/{NROUND+1} sets exact, obstructionCheck = true, peak states {peak}")

    # --- sweep data (k = 7..135, F carries fact k, V carries v2 (fact k))
    F, V = F0, V0
    sweep = []
    for k in range(K0, KN):
        cls = V - VBAS
        u = (F // 720 // (1 << cls)) % (1 << (CP - cls))
        kept = cls <= CLSCAP
        assert (not kept) or (k, cls, u) == tuple(coinList[k - K0]), f"sweep coin {k} mismatch"
        sweep.append((k, F, V, kept))
        F = (k + 1) * F; V = V + v2(k + 1)
    assert all(s[3] for s in sweep), "expected all 129 levels kept"
    print("[PRE-VERIFY] sweep: 129/129 coins exact")

    # --- sort ladder verification
    TAIL = {NROUND: []}
    for r in range(NROUND-1, -1, -1):
        TAIL[r] = [tuple(table[r])] + TAIL[r+1]
    for r in range(NROUND):
        assert insertCoin(tuple(coinList[r]), TAIL[r+1]) == TAIL[r], f"insert {r} mismatch"
    print("[PRE-VERIFY] sort ladder: 129/129 inserts exact")

    # --- rounds data (chunked dedup)
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
        for ci, ch in enumerate(chunks):
            a = list(accs[ci]); out = dedupAux(ch, a)
            if ci + 1 < len(chunks): assert out == accs[ci+1]
            else: assert out == Sout
        rounds.append(dict(r=r, Sout=Sout, L=L, chunks=chunks, accs=accs))
    total_chunks = sum(len(rd["chunks"]) for rd in rounds)
    print(f"[PRE-VERIFY] rounds: {NROUND}/129 exact, chunks: {total_chunks}")

    def W(name, text):
        open(os.path.join(CHAIN, name), "w").write(text)
        print(f"[EMIT] {name}: {len(text)} bytes, {text.count(chr(10))} lines")

    # ---------------- F62DataS
    t = [f"import ExactF62", "", OPTIONS, "-- The DP trace: fz_S_r = the r-th state set (r = 0 is the initial set)."]
    for r in range(NROUND + 1):
        t.append(f"def fz_S_{r} : List (Nat × Nat) := {set_lit(mySets[r])}")
    W("F62DataS.lean", "\n".join(t) + "\n")

    # ---------------- F62DataC
    t = ["import ExactF62", "", OPTIONS,
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
    W("F62DataC.lean", "\n".join(t) + "\n")

    # ---------------- F62DataD1/2
    for half, (lo, hi) in enumerate([(0, 65), (65, NROUND)]):
        t = ["import ExactF62", "", OPTIONS, "-- flatMap outputs (chunked) + dedup accumulators."]
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
        W(f"F62DataD{half+1}.lean", "\n".join(t) + "\n")

    # ---------------- F62Chain
    W("F62Chain.lean", f"""import ExactF62

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

    # ---------------- F62SweepA
    t = [f"""import ExactF62
import F62DataC

{OPTIONS}

/-- The sweep: builds the coin list from k upward, carrying (k, fact k, v2 (fact k)).
    Fuel-structural (first param counts down). -/
def coinFrom : Nat → Nat → Nat → Nat → List (Nat × Nat × Nat)
  | 0, _, _, _ => []
  | f + 1, k, F, V =>
      let cls := V - {VBAS}
      let u := (F / 720 / 2 ^ cls) % 2 ^ (CP - cls)
      if cls ≤ {CLSCAP} then (k, cls, u) :: coinFrom f (k + 1) ((k + 1) * F) (V + v2 (k + 1))
      else coinFrom f (k + 1) ((k + 1) * F) (V + v2 (k + 1))

theorem coinFrom_ne (f k F V : Nat) :
    coinFrom (f + 1) k F V =
      (if V - {VBAS} ≤ {CLSCAP} then (k, V - {VBAS}, (F / 720 / 2 ^ (V - {VBAS})) % 2 ^ (CP - (V - {VBAS}))) :: coinFrom f (k + 1) ((k + 1) * F) (V + v2 (k + 1))
      else coinFrom f (k + 1) ((k + 1) * F) (V + v2 (k + 1))) := by
  simp only [coinFrom]

/-- map congruence (core lacks List.map_congr). -/
theorem fz_map_congr {{{{α β : Type}}}} {{{{f g : α → β}}}} : ∀ (l : List α),
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
theorem coinFrom_spec : ∀ (N k F V : Nat), k + N = {KN} → {K0} ≤ k → F = fact k → V = v2 (fact k) →
    coinFrom N k F V = (List.range N).map (fun j => (j + k, classOf (j + k), coinUnit (j + k))) := by
  intro N
  induction N with
  | zero =>
      intro k F V hk _ _ _
      obtain rfl : k = {KN} := by omega
      rfl
  | succ N ih =>
      intro k F V hk h7 hF hV
      have hk135 : k < {KN} := by omega
      have hbound : classOf k ≤ {CLSCAP} := by
        have hq := List.all_eq_true.mp classOf_bound_all k (List.mem_range.mpr hk135)
        rw [Bool.or_eq_true] at hq
        cases hq with
        | inl hlt7 => exact absurd (of_decide_eq_true hlt7) (by omega)
        | inr hb => exact of_decide_eq_true hb
      have hcls : V - {VBAS} = classOf k := by
        have hc := v2_fact_classOf k (by omega)
        omega
      have hunit : F / 720 / 2 ^ classOf k % 2 ^ (CP - classOf k) = coinUnit k := by
        unfold coinUnit P
        rw [hF]
      have hF' : (k + 1) * F = fact (k + 1) := by rw [hF, ← fact_succ]
      have hV' : V + v2 (k + 1) = v2 (fact (k + 1)) := by
        have key := v2_mul ((k + 1) + F) (k + 1) F (by omega) (by omega) (by rw [hF]; exact fact_pos k)
        rw [hF, ← hV, ← fact_succ] at key
        omega
      have hkeep : V - {VBAS} ≤ {CLSCAP} := by rw [hcls]; exact hbound
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
    for (k, F, V, kept) in sweep[:65]:
        r = k - K0
        F2, V2_ = (k+1) * F, V + v2(k+1)
        fuel, fuel2 = NROUND - r, NROUND - 1 - r
        if kept:
            t.append(f"theorem fz_cf_{r} : coinFrom {fuel} {k} {F} {V} = {coin_lit(coinList[r])} :: coinFrom {fuel2} {k+1} {F2} {V2_} := by rfl")
        else:
            t.append(f"theorem fz_cf_{r} : coinFrom {fuel} {k} {F} {V} = coinFrom {fuel2} {k+1} {F2} {V2_} := by rfl")
    W("F62SweepA.lean", "\n".join(t) + "\n")

    # ---------------- F62SweepB
    t = ["import F62SweepA", "", OPTIONS, f"-- levels 65..128 + the suffix assembly + coinList_eq."]
    for (k, F, V, kept) in sweep[65:]:
        r = k - K0
        F2, V2_ = (k+1) * F, V + v2(k+1)
        fuel, fuel2 = NROUND - r, NROUND - 1 - r
        if kept:
            t.append(f"theorem fz_cf_{r} : coinFrom {fuel} {k} {F} {V} = {coin_lit(coinList[r])} :: coinFrom {fuel2} {k+1} {F2} {V2_} := by rfl")
        else:
            t.append(f"theorem fz_cf_{r} : coinFrom {fuel} {k} {F} {V} = coinFrom {fuel2} {k+1} {F2} {V2_} := by rfl")
    # the assembly (from the end); r indexes UTAIL (k = r + 7)
    t.append(f"theorem fz_sw_all_{NROUND-1} : coinFrom 1 {KN-1} {sweep[NROUND-1][1]} {sweep[NROUND-1][2]} = fz_UTAIL_{NROUND-1} := by rw [fz_cf_{NROUND-1}]; rfl")
    for r in range(NROUND-2, -1, -1):
        t.append(f"theorem fz_sw_all_{r} : coinFrom {NROUND-r} {r+K0} {sweep[r][1]} {sweep[r][2]} = fz_UTAIL_{r} := by rw [fz_cf_{r}, fz_sw_all_{r+1}]; rfl")
    # coinList_eq
    t.append(f"""
/-- The coinList filter is constantly-`7 ≤ i` (classOf_bound_all). -/
theorem fz_filter_pt (i : Nat) (hi : i < {KN}) :
    (decide ({K0} ≤ i) && decide (classOf i ≤ {CLSCAP})) = decide ({K0} ≤ i) := by
  have hq := List.all_eq_true.mp classOf_bound_all i (List.mem_range.mpr hi)
  rw [Bool.or_eq_true] at hq
  cases hq with
  | inl hlt7 =>
      have hi7 : i < {K0} := of_decide_eq_true hlt7
      have hn : ¬ ({K0} ≤ i) := by omega
      rw [decide_eq_false hn, Bool.false_and]
  | inr hb =>
      rw [decide_eq_true (of_decide_eq_true hb), Bool.and_true]

/-- range 136 filtered by 7 ≤ · = map (+7) (range 129). -/
theorem fz_filter_singleton_true (a : Nat) (h : decide ({K0} ≤ a) = true) :
    List.filter (fun i => decide ({K0} ≤ i)) [a] = [a] := by
  simp only [List.filter]
  rw [h]

theorem fz_range_filter_ge (N : Nat) :
    ((List.range (N + {K0})).filter (fun i => decide ({K0} ≤ i))) = (List.range N).map (fun x => x + {K0}) := by
  induction N with
  | zero => rfl
  | succ N ih =>
      have hrw : N + 1 + {K0} = N + {K0} + 1 := by omega
      rw [hrw, List.range_succ, List.filter_append, ih, List.range_succ, List.map_append,
          List.map_cons, List.map_nil]
      rw [fz_filter_singleton_true (N + {K0}) (decide_eq_true (by omega))]

theorem coinList_eq : coinList = fz_UTAIL_0 := by
  unfold coinList
  rw [show ({KN} : Nat) = {NROUND} + {K0} from rfl,
      List.filter_congr (fun i hi => fz_filter_pt i (List.mem_range.mp hi)),
      fz_range_filter_ge {NROUND}, List.map_map]
  show List.map (fun x => (x + {K0}, classOf (x + {K0}), coinUnit (x + {K0}))) (List.range {NROUND}) = fz_UTAIL_0
  rw [← coinFrom_spec {NROUND} {K0} {F0} {V0} (by omega) (by omega) (by rfl) (by decide)]
  exact fz_sw_all_0
""")
    W("F62SweepB.lean", "\n".join(t) + "\n")

    # ---------------- F62Coins
    t = ["import F62SweepB", "", OPTIONS, "-- the insert ladder + the sort ladder + table_eq."]
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
    t.append(f"""
/-- THE SORTED TABLE, FROZEN: table = fz_TAIL_0. -/
theorem table_eq : table = fz_TAIL_0 := by
  rw [table, coinList_eq, fz_sc_0]
""")
    W("F62Coins.lean", "\n".join(t) + "\n")

    # ---------------- F62FM0/1
    for half, (lo, hi) in enumerate([(0, 65), (65, NROUND)]):
        t = [f"import ExactF62\nimport F62DataS\nimport F62DataC\nimport F62DataD{half+1}\n\n{OPTIONS}\n-- flatMap decides."]
        for rd in rounds[lo:hi]:
            r = rd["r"]
            t.append(f"""theorem fz_FM_{r} : (fz_S_{r}.filter (fun st => decide (fz_C_{r}.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_{r}.2.1 st.1 st.2 fz_C_{r}.2.2]) = fz_L_{r} := by decide +kernel""")
        W(f"F62FM{half}.lean", "\n".join(t) + "\n")

    # ---------------- F62DD* : thin slicing
    singles = [rd for rd in rounds if len(rd["chunks"]) == 1]
    multis  = [rd for rd in rounds if len(rd["chunks"]) > 1]
    SLICE = 25
    n_s_mod = (len(singles) + SLICE - 1) // SLICE
    for idx in range(n_s_mod):
        lo, hi = idx * SLICE, min((idx + 1) * SLICE, len(singles))
        t = [f"import ExactF62\nimport F62DataS\nimport F62DataC\nimport F62DataD1\nimport F62DataD2\n\n{OPTIONS}\n-- single-chunk dedup decides + chains (slice {idx})."]
        for rd in singles[lo:hi]:
            r = rd["r"]
            t.append(f"theorem fz_dcr_{r}_1 : dedupAux fz_CH_{r}_1 fz_A_{r}_1 = fz_S_{r+1} := by decide +kernel")
            t.append(f"theorem fz_dd_{r} : dedupAux fz_L_{r} [] = fz_S_{r+1} := fz_dcr_{r}_1")
        W(f"F62DD{idx}.lean", "\n".join(t) + "\n")
    mmods = []
    for idx, rd in enumerate(multis):
        r = rd["r"]; n = len(rd["chunks"])
        lines = [f"import ExactF62\nimport F62DataS\nimport F62DataC\nimport F62DataD1\nimport F62DataD2\nimport F62Chain\n\n{OPTIONS}\n-- multi-chunk round {r} ({n} chunks)."]
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
        W(f"F62DDm{idx}.lean", "\n".join(lines) + "\n")
        mmods.append(f"F62DDm{idx}")

    # ---------------- F62Asm0/1
    dd_imports = [f"F62DD{i}" for i in range(n_s_mod)] + mmods
    for half, (lo, hi) in enumerate([(0, 65), (65, NROUND)]):
        t = [f"""import F62Chain
import F62Coins
import F62DataS
import F62DataC
import F62FM{half}
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
        W(f"F62Asm{half}.lean", "\n".join(t) + "\n")

    # ---------------- F62All slices + thin final
    def fz_all_block(r):
        if r == NROUND:
            return ["/-- The all-chain: every set of the run satisfies the maxT bound. -/",
                    f"theorem fz_all_{NROUND} : List.all (dpRun fz_TAIL_{NROUND} fz_S_{NROUND}) (fun S => decide (maxT S ≤ {BOUND})) = true := by rfl"]
        nxt = r + 1
        return [f"theorem fz_all_{r} : List.all (dpRun fz_TAIL_{r} fz_S_{r}) (fun S => decide (maxT S ≤ {BOUND})) = true := by",
                "  rw [fz_run_%d, List.all_cons, Bool.and_eq_true]" % r,
                "  exact ⟨by decide +kernel, fz_all_%d⟩" % nxt]
    KILL_FINAL = f"""
/-- **THE HYPOTHESIS KILL: obstructionCheck = true, UNCONDITIONALLY.** -/
theorem obstructionCheck_true : obstructionCheck = true := by
  unfold obstructionCheck allSets
  rw [table_eq, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_0⟩

/-- **f(6,2) = 133 — UNCONDITIONAL, ZERO HYPOTHESES.** -/
theorem erdos404_f62_final :
    v2 (720 + (witnessB.map fact).sum) = 133
    ∧ ∀ B : List Nat, NoDupL B → (∀ i ∈ B, 7 ≤ i) →
      v2 (720 + (B.map fact).sum) ≤ 133 :=
  erdos404_f62_exact obstructionCheck_true

#print axioms obstructionCheck_true
#print axioms erdos404_f62_final
"""
    slices = [("F62AllA", "import F62Asm0\nimport F62Asm1", range(NROUND, 97, -1)),
              ("F62AllB", "import F62AllA", range(97, 65, -1)),
              ("F62AllC", "import F62AllB", range(65, 33, -1)),
              ("F62AllD", "import F62AllC", range(33, 0, -1))]
    for name, imp, rng in slices:
        body = []
        for r in rng:
            body.extend(fz_all_block(r)); body.append("")
        W(name + ".lean", imp + "\n\n" + OPTIONS + "\n\n" + "\n".join(body) + "\n")
    tail = []
    tail.extend(fz_all_block(0)); tail.append("")
    W("F62All.lean", "import F62AllD\n\n" + OPTIONS + "\n\n" + "\n".join(tail) + KILL_FINAL)

    print(f"\n[DONE] modules emitted to {CHAIN}")
    print("Total chunks:", total_chunks, "| multi-chunk rounds:", len(multis), "| DDm modules:", len(mmods))

if __name__ == "__main__":
    main()
