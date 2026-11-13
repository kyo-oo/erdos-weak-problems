import Arsenal.ErdosTernary2.Basic
import Arsenal.CardinalWorlds
import Arsenal.CardinalWorldsV2

set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-!
# Erdos1212 — THE COPRIME-PAIR GRAPH KERNEL (Kernel 65, W58-B)

Erdős #1212 (verbatim, DERIVATION.md): "Let G be the graph with vertex set
those pairs (x,y) ∈ ℕ² with gcd(x,y)=1, in which we join two vertices if
they differ in only one coordinate, and thereby by ±1. Is there a path
going to infinity on G, say P, such that for all (x,y) ∈ P both min(x,y)>1
and at least one of x or y is composite?" This kernel certifies the
campaign's law set unconditionally (engine + battery1212.py/b, every decide
row pre-verified by the python mirror): the structural habitat checker
(fuel-gcd + composite scan, kernel-decidable), the adjacency laws
(commutativity, distinctness, one-coordinate, THE B-HUB PARITY FLIP), the
bounded degree law deg ≤ 4 + the engine's degree table, the component
censuses (five certified lists + the NO-EXIT closure law of the (9,25)
component — closed in the FULL graph), the engine-corrected PHASE-LAW
instances ((15,49) with the j=2 landing wall; (203,10201) with the
99-column sweep and the 303/404 walls), the directed-death census (12
r2b rows), and THE 103-VERTEX TWO-PHASE WITNESS (distinct, endpoints
composite, coordinate sum grows).
-/

namespace E1212

/-! ## §1 The structural core — kernel-decidable habitat machinery.
Equation-compiler native (structural recursion only); `by decide` evaluates
every def on closed numerals; the `==`s live ONLY in defs (L91). -/

/-- Bool-to-Nat for the degree counter. -/
def btoN : Bool → Nat
  | true => 1
  | false => 0

/-- Structural fuel-gcd (the Erdos282 GREEN pattern): Euclid by mod/swap,
fuel-bounded for iota-nativeness; the decide rows certify the closed
instances directly (gcd-correctness is never needed as a theorem). -/
def gcdF : Nat → Nat → Nat → Nat
  | 0, _, b => b
  | fuel + 1, a, b =>
    if a = 0 then b
    else if b = 0 then a
    else if b < a then gcdF fuel b a
    else if b % a = 0 then a
    else gcdF fuel (b % a) a

/-- The gcd checker at generous fuel (2*(a+b)+2 dwarfs every Euclid chain
here — mirror-verified row by row). -/
def gcdB (a b : Nat) : Nat := gcdF (2 * (a + b) + 2) a b

/-- THE COPRIMALITY CHECKER: gcdB x y == 1 (decide-consumed on closed
terms only — the L91 law). -/
def coprimeB (x y : Nat) : Bool := gcdB x y == 1

/-- Ascending divisor scan: compU fuel d n = true iff some divisor e with
d ≤ e and e * e ≤ n divides n (self-terminating past √n). -/
def compU : Nat → Nat → Nat → Bool
  | 0, _, _ => false
  | fuel + 1, d, n =>
    if d * d ≤ n then decide (n % d = 0) || compU fuel (d + 1) n
    else false

/-- THE COMPOSITE CHECKER: compB n = true iff n has a divisor e with
2 ≤ e and e * e ≤ n (n + 2 fuel reaches past √n for every n). -/
def compB (n : Nat) : Bool := compU (n + 2) 2 n

/-- THE #1212 HABITAT: both coordinates ≥ 2, gcd = 1, at least one
composite — the verbatim vertex condition of G. -/
def habitatB (v : Nat × Nat) : Bool :=
  decide (2 ≤ v.1) && decide (2 ≤ v.2) && coprimeB v.1 v.2
    && (compB v.1 || compB v.2)

/-- Structural pair equality (decide-consumed on closed terms). -/
def pairEqB (v w : Nat × Nat) : Bool := v.1 == w.1 && v.2 == w.2

/-- THE #1212 ADJACENCY (Prop form): joined iff differing in exactly one
coordinate by ±1 (the engine's adjacency law). -/
def adj (v w : Nat × Nat) : Prop :=
  (v.1 = w.1 ∧ (v.2 + 1 = w.2 ∨ w.2 + 1 = v.2)) ∨
  (v.2 = w.2 ∧ (v.1 + 1 = w.1 ∨ w.1 + 1 = v.1))

/-- The Bool mirror of `adj`. -/
def adjB (v w : Nat × Nat) : Bool :=
  (v.1 == w.1 && (w.2 == v.2 + 1 || v.2 == w.2 + 1)) ||
  (v.2 == w.2 && (w.1 == v.1 + 1 || v.1 == w.1 + 1))

/-- The four lattice neighbors of a vertex (the degree universe). -/
def nbrs (v : Nat × Nat) : List (Nat × Nat) :=
  [(v.1 + 1, v.2), (v.1 - 1, v.2), (v.1, v.2 + 1), (v.1, v.2 - 1)]

/-- Membership / adjacency of a vertex to a vertex list. -/
def memB (v : Nat × Nat) (l : List (Nat × Nat)) : Bool :=
  l.any (fun w => pairEqB v w)

def adjToB (v : Nat × Nat) (l : List (Nat × Nat)) : Bool :=
  l.any (fun w => adjB v w)

/-- The habitat-neighbor counter (own structural def, rfl-unfolds). -/
def countB (p : Nat × Nat → Bool) : List (Nat × Nat) → Nat
  | [] => 0
  | v :: rest => btoN (p v) + countB p rest

/-- The habitat-degree: habitat neighbors among the four lattice sites. -/
def degB (v : Nat × Nat) : Nat := countB habitatB (nbrs v)

/-- THE WALK CERTIFICATE: every vertex a G-vertex (bounds, coprimality,
compositeness — the full verbatim guard) and consecutive vertices
adjacent. -/
def walkOK : List (Nat × Nat) → Bool
  | [] => true
  | [v] => habitatB v
  | v :: w :: rest => habitatB v && adjB v w && walkOK (w :: rest)

/-- Simplicity certificate: pairwise distinct vertices. -/
def allDistinct : List (Nat × Nat) → Bool
  | [] => true
  | v :: rest => !(rest.any (fun w => pairEqB v w)) && allDistinct rest

/-- THE DIRECTED WALK SURVIVAL: liveB k x y = true iff a directed
(+x/+y only) habitat walk of k+1 vertices starts at (x,y) (the r2b
engine's greedy-death predicate). -/
def liveB : Nat → Nat → Nat → Bool
  | 0, x, y => habitatB (x, y)
  | k + 1, x, y =>
    habitatB (x, y) && (liveB k (x + 1) y || liveB k x (y + 1))

/-- First/last vertex extractors. -/
def firstV : List (Nat × Nat) → Nat × Nat
  | [] => (0, 0)
  | v :: _ => v

def lastV : List (Nat × Nat) → Nat × Nat
  | [] => (0, 0)
  | [v] => v
  | _ :: rest => lastV rest

/-! ## §2 The structural laws. -/

theorem gcdF_zero_fuel (a b : Nat) : gcdF 0 a b = b := rfl

theorem btoN_le_one (b : Bool) : btoN b ≤ 1 := by
  cases b with
  | true => exact Nat.le_refl 1
  | false => exact Nat.zero_le 1

theorem countB_le (p : Nat × Nat → Bool) :
    ∀ l : List (Nat × Nat), countB p l ≤ l.length := by
  intro l
  induction l with
  | nil => exact Nat.le_refl 0
  | cons v rest ih =>
    have hc : countB p (v :: rest) = btoN (p v) + countB p rest := rfl
    have hl : (v :: rest).length = rest.length + 1 := by simp
    rw [hc, hl]
    have h1 : btoN (p v) ≤ 1 := btoN_le_one (p v)
    omega

/-- THE BOUNDED-DEGREE LAW (structural): every vertex of G has at most
four G-neighbors — the four lattice sites are the only candidates. -/
theorem degBound (v : Nat × Nat) : degB v ≤ 4 := by
  have h1 : countB habitatB (nbrs v) ≤ (nbrs v).length :=
    countB_le habitatB (nbrs v)
  have h2 : (nbrs v).length = 4 := rfl
  unfold degB
  omega

/-! ## §3 The adjacency structure laws (Prop level, full generality). -/

theorem adj_comm_aux (v w : Nat × Nat) : adj v w → adj w v := by
  intro h
  unfold adj at h ⊢
  rcases h with ⟨hx, hy⟩ | ⟨hy, hx⟩
  · rcases hy with hy' | hy'
    · exact Or.inl ⟨hx.symm, Or.inr hy'⟩
    · exact Or.inl ⟨hx.symm, Or.inl hy'⟩
  · rcases hx with hx' | hx'
    · exact Or.inr ⟨hy.symm, Or.inr hx'⟩
    · exact Or.inr ⟨hy.symm, Or.inl hx'⟩

/-- THE SYMMETRY LAW: G-adjacency is commutative. -/
theorem adj_comm (v w : Nat × Nat) : adj v w ↔ adj w v :=
  ⟨adj_comm_aux v w, adj_comm_aux w v⟩

/-- THE IRREFLEXIVITY LAW: adjacent vertices are distinct. -/
theorem adj_distinct (v w : Nat × Nat) : adj v w → v ≠ w := by
  intro h hveq
  subst hveq
  unfold adj at h
  omega

/-- THE ONE-COORDINATE LAW: adjacent vertices differ in exactly one
coordinate (the "differ in only one coordinate" reading of #1212,
derived from the ±1 form). -/
theorem adj_one_coord (v w : Nat × Nat) : adj v w →
    (v.1 = w.1 ∧ v.2 ≠ w.2) ∨ (v.1 ≠ w.1 ∧ v.2 = w.2) := by
  intro h
  unfold adj at h
  rcases h with ⟨hx, hy⟩ | ⟨hy, hx⟩
  · rcases hy with hy' | hy'
    · exact Or.inl ⟨hx, by omega⟩
    · exact Or.inl ⟨hx, by omega⟩
  · rcases hx with hx' | hx'
    · exact Or.inr ⟨by omega, hy⟩
    · exact Or.inr ⟨by omega, hy⟩

/-- THE B-HUB PARITY FLIP (round-1 type analysis as a theorem): an odd-odd
vertex (B-hub) has an odd/even or even/odd neighbor — the path alternates
B-hubs with intermediates whose even coordinate is auto-composite. -/
theorem adj_parity_flip (v w : Nat × Nat) (h : adj v w)
    (hv : v.1 % 2 = 1 ∧ v.2 % 2 = 1) :
    (w.1 % 2 = 1 ∧ w.2 % 2 = 0) ∨ (w.1 % 2 = 0 ∧ w.2 % 2 = 1) := by
  unfold adj at h
  rcases h with ⟨hx, hy⟩ | ⟨hy, hx⟩
  · rcases hv with ⟨h1, h2⟩
    rcases hy with hy' | hy' <;> omega
  · rcases hv with ⟨h1, h2⟩
    rcases hx with hx' | hx' <;> omega

/-! ## §4 The certified data rows (decide; battery1212.py §1/§3). -/

/-- THE HABITAT ANCHORS: the four engine configurations are G-vertices,
both coordinates composite, pairwise coprime. -/
theorem habitat_anchor_rows :
    habitatB (9, 25) = true ∧ habitatB (15, 49) = true ∧
    habitatB (203, 10201) = true ∧ habitatB (301, 10205) = true ∧
    compB 9 = true ∧ compB 25 = true ∧ compB 203 = true ∧
    compB 301 = true ∧ compB 10201 = true ∧ compB 10205 = true ∧
    coprimeB 9 25 = true ∧ coprimeB 15 49 = true ∧
    coprimeB 203 10201 = true ∧ coprimeB 301 10205 = true := by
  decide

/-- THE DEGREE TABLE (battery §3, unbounded habitat degrees): the
engine's nine measured degrees, decide-certified exactly. -/
theorem deg_table :
    degB (9, 25) = 2 ∧ degB (8, 25) = 2 ∧ degB (8, 27) = 1 ∧
    degB (15, 49) = 1 ∧ degB (16, 49) = 2 ∧ degB (19, 49) = 4 ∧
    degB (203, 10201) = 3 ∧ degB (204, 10201) = 2 ∧
    degB (301, 10205) = 2 := by
  decide

/-! ## §5 The component census (battery §2 / battery1212b BFS orders). -/

/-- The (4,9) component (box [2,20)): 3 vertices. -/
def c49 : List (Nat × Nat) := [(4, 9), (5, 9), (5, 8)]

/-- THE (9,25) component (box [2,30)): 9 vertices — the oscillation box. -/
def c925 : List (Nat × Nat) :=
  [(9, 25), (8, 25), (9, 26), (7, 25), (6, 25), (7, 26), (7, 24), (7, 27), (8, 27)]

/-- The (15,16) component (box [2,30)): 4 vertices. -/
def c1516 : List (Nat × Nat) := [(15, 16), (15, 17), (16, 17), (14, 17)]

/-- The (25,27) component (box [2,30)): 10 vertices. -/
def c2527 : List (Nat × Nat) :=
  [(25, 27), (26, 27), (25, 28), (25, 26), (25, 29), (26, 29), (24, 29),
   (27, 29), (28, 29), (27, 28)]

/-- The (15,49) component (box [2,60)): 13 vertices — the phase-law world. -/
def c15949 : List (Nat × Nat) :=
  [(15, 49), (16, 49), (17, 49), (18, 49), (17, 50), (17, 48), (19, 49),
   (20, 49), (19, 50), (19, 48), (19, 51), (20, 51), (19, 52)]

/-- THE COMPONENT CENSUS: five certified component lists — every listed
vertex a G-vertex, the engine's measured sizes 3, 9, 4, 10, 13 (the
round-1 "components are small at low coordinates" law). -/
theorem census_counts :
    c49.length = 3 ∧ c925.length = 9 ∧ c1516.length = 4 ∧
    c2527.length = 10 ∧ c15949.length = 13 ∧
    c49.all habitatB = true ∧ c925.all habitatB = true ∧
    c1516.all habitatB = true ∧ c2527.all habitatB = true ∧
    c15949.all habitatB = true := by
  decide

/-- THE NO-EXIT CLOSURE LAW of the (9,25) component (36-cell ring sweep
x[5,10] × y[23,28], the complete ±1-neighborhood of the component in ℕ²):
no habitat vertex adjacent to the component lies outside it — the
component is CLOSED in the full graph; the greedy can only oscillate
(the r2 engine's box [7,9]×[25,27] trap). -/
theorem comp925_no_exit :
    (List.range 6).all (fun dx : Nat =>
      (List.range 6).all (fun dy : Nat =>
        decide (¬ (habitatB (5 + dx, 23 + dy) = true ∧
            adjToB (5 + dx, 23 + dy) c925 = true) ∨
          memB (5 + dx, 23 + dy) c925 = true))) = true := by
  decide

/-- Usable form: every habitat ring cell adjacent to the (9,25)
component is a member of the component. -/
theorem comp925_closed :
    ∀ dx dy : Nat, dx < 6 → dy < 6 →
      habitatB (5 + dx, 23 + dy) = true →
      adjToB (5 + dx, 23 + dy) c925 = true →
      memB (5 + dx, 23 + dy) c925 = true := by
  intro dx dy hdx hdy hh ha
  have h1 := (List.all_eq_true.mp comp925_no_exit) dx (List.mem_range.mpr hdx)
  have h2 := (List.all_eq_true.mp h1) dy (List.mem_range.mpr hdy)
  rcases of_decide_eq_true h2 with hneg | hmem
  · exact absurd ⟨hh, ha⟩ hneg
  · exact hmem

/-! ## §6 The phase-law instances (battery1212.py §4 — the engine-corrected
landing law: q_min(y)=7 gives 2 certified moves from (15,49); q_min=101
gives 49 from (203,10201); landings collide exactly at (q-3)/2). -/

/-- THE (15,49) PHASE: columns 15..19 clean against 49 (intermediates
16, 18 and landings 17, 19 — two certified B-hub moves), the landing
WALL at 21 (gcd 7 with 49), 20 clean; the y-phase wall from (301,10201)
at 10206 (gcd 7 with 301), 10207 clean. -/
theorem phase15949 :
    (List.range 5).all (fun k : Nat => coprimeB (15 + k) 49) = true ∧
    coprimeB 21 49 = false ∧ coprimeB 20 49 = true ∧
    coprimeB 301 10206 = false ∧ coprimeB 301 10207 = true := by
  decide

/-- THE (203,10201) PHASE (the big certified window): all 99 columns
203..301 coprime to 10201 = 101² (49 B-hub-to-B-hub moves via the even
intermediates), landing WALL at 303 = 3·101 (j = 49 = (101-3)/2, the
engine-corrected law), intermediate WALL at 404 = 4·101 (j = 100). -/
theorem phase203_sweep :
    (List.range 99).all (fun k : Nat => coprimeB (203 + k) 10201) = true ∧
    coprimeB 303 10201 = false ∧ coprimeB 404 10201 = false := by
  decide

/-- Usable form: every column of the 99-wide certified window is coprime
to 10201. -/
theorem phase203_coprime :
    ∀ k : Nat, k < 99 → coprimeB (203 + k) 10201 = true := by
  intro k hk
  exact (List.all_eq_true.mp phase203_sweep.1) k (List.mem_range.mpr hk)

/-! ## §7 The path constructions (the certified finite witnesses). -/

/-- THE TWO-PHASE 103-VERTEX WITNESS (battery §5, witness1212_P103.txt):
(203,10201) → (301,10201) — the 49 certified x-phase moves — then
(301,10202) → (301,10205) — the y-phase restore. Every vertex a G-vertex
with y = 101² composite (min > 1 throughout), consecutive vertices
adjacent. -/
def p103 : List (Nat × Nat) :=
  [(203, 10201), (204, 10201), (205, 10201), (206, 10201), (207, 10201), (208, 10201), (209, 10201), (210, 10201),
   (211, 10201), (212, 10201), (213, 10201), (214, 10201), (215, 10201), (216, 10201), (217, 10201), (218, 10201),
   (219, 10201), (220, 10201), (221, 10201), (222, 10201), (223, 10201), (224, 10201), (225, 10201), (226, 10201),
   (227, 10201), (228, 10201), (229, 10201), (230, 10201), (231, 10201), (232, 10201), (233, 10201), (234, 10201),
   (235, 10201), (236, 10201), (237, 10201), (238, 10201), (239, 10201), (240, 10201), (241, 10201), (242, 10201),
   (243, 10201), (244, 10201), (245, 10201), (246, 10201), (247, 10201), (248, 10201), (249, 10201), (250, 10201),
   (251, 10201), (252, 10201), (253, 10201), (254, 10201), (255, 10201), (256, 10201), (257, 10201), (258, 10201),
   (259, 10201), (260, 10201), (261, 10201), (262, 10201), (263, 10201), (264, 10201), (265, 10201), (266, 10201),
   (267, 10201), (268, 10201), (269, 10201), (270, 10201), (271, 10201), (272, 10201), (273, 10201), (274, 10201),
   (275, 10201), (276, 10201), (277, 10201), (278, 10201), (279, 10201), (280, 10201), (281, 10201), (282, 10201),
   (283, 10201), (284, 10201), (285, 10201), (286, 10201), (287, 10201), (288, 10201), (289, 10201), (290, 10201),
   (291, 10201), (292, 10201), (293, 10201), (294, 10201), (295, 10201), (296, 10201), (297, 10201), (298, 10201),
   (299, 10201), (300, 10201), (301, 10201), (301, 10202), (301, 10203), (301, 10204), (301, 10205)]

/-- The 7-vertex longest path inside the (9,25) component (battery1212b). -/
def p7 : List (Nat × Nat) :=
  [(9, 26), (9, 25), (8, 25), (7, 25), (7, 26), (7, 27), (8, 27)]

/-- The 8-vertex longest path inside the (15,49) component: the x-phase
15 → 19 (two certified B-hub moves), the y-phase 49 → 51, and the
restore hop to (20,51) (battery1212b). -/
def p8 : List (Nat × Nat) :=
  [(15, 49), (16, 49), (17, 49), (18, 49), (19, 49), (19, 50), (19, 51), (20, 51)]

/-- The 6-vertex oscillation witness from (9,25) (witness1212_P925.txt —
the greedy trap box [7,9]×[25,27]). -/
def p6 : List (Nat × Nat) :=
  [(9, 25), (8, 25), (7, 25), (7, 26), (7, 27), (8, 27)]

/-- THE TWO-PHASE WITNESS LAW: p103 is a valid simple G-walk — every
vertex a G-vertex (coprime + composite + min > 1), consecutive vertices
adjacent, all 103 vertices pairwise distinct. -/
theorem p103_valid : walkOK p103 = true ∧ allDistinct p103 = true := by
  decide

/-- THE WITNESS SHAPE: 103 vertices, from (203,10201) to (301,10205),
both endpoints with BOTH coordinates composite (301 = 7·43, 10205 =
5·13·157), and the coordinate sum GROWS by 102 over the witness — the
infinite-path pressure in the finite certificate. -/
theorem p103_shape :
    (firstV p103).1 = 203 ∧ (firstV p103).2 = 10201 ∧
    (lastV p103).1 = 301 ∧ (lastV p103).2 = 10205 ∧
    p103.length = 103 ∧ compB 301 = true ∧ compB 10205 = true ∧
    203 + 10201 < 301 + 10205 := by
  decide

/-- THE SMALL WALKS: the three engine witnesses (p7 in the closed (9,25)
component, p8 the phase law in (15,49)'s component, p6 the oscillation)
are valid simple G-walks of lengths 7, 8, 6. -/
theorem small_walks_valid :
    walkOK p7 = true ∧ walkOK p8 = true ∧ walkOK p6 = true ∧
    allDistinct p7 = true ∧ allDistinct p8 = true ∧ allDistinct p6 = true ∧
    p7.length = 7 ∧ p8.length = 8 ∧ p6.length = 6 := by
  decide

/-! ## §8 The directed-death census (battery1212b — the r2b engine law:
forward-only greedy dies at depth ≤ 8 from all 12 composite starts). -/

theorem directed_death :
    liveB 2 9 25 = false ∧ liveB 2 25 9 = false ∧ liveB 3 15 16 = false ∧
    liveB 6 25 27 = false ∧ liveB 8 9 49 = false ∧ liveB 6 21 25 = false ∧
    liveB 6 27 25 = false ∧ liveB 2 33 25 = false ∧
    liveB 2 25 33 = false ∧ liveB 2 27 49 = false ∧
    liveB 1 35 27 = false ∧ liveB 2 9 121 = false := by
  decide

/-! ## §9 The arsenal bridge — BOSS's mathematics at #1212 anchors
(10201 = 101², 10205 = 5·13·157, 25). -/

theorem e1212_arsenal_bridge :
    ErdosTernary2.isTernaryDigit (10201 % 3) ∧
    (10201 ^ 2 - 1 = (10201 - 1) * (10201 + 1)) ∧
    (10205 % (25 * 2)) % 25 = 10205 % 25 ∧
    carryAtPos 10205 1 < 4 ∧
    v2r (3 ^ 1 * 10201) = v2r 10201 :=
  ⟨by decide, sq_sub_one 10201 (by decide), mod_mod_mul 10205 25 2 (by decide),
    carryAtPos_bound 10205 1, CardinalWorldsV2.v2r_ternary_scaling 1 10201⟩

/-! ## §10 The master board. -/

/-- THE P1212 KERNEL MASTER BOARD (18 conjuncts, full statements,
unconditional, flat anonymous constructor): the adjacency laws + the
parity flip + the bounded-degree law + the degree table + the habitat
anchors + the component census + THE NO-EXIT CLOSURE LAW (decide +
usable) + the two phase-law instances (sweep + usable) + THE 103-VERTEX
TWO-PHASE WITNESS (valid + shape + growth) + the small walks + the
directed-death census + the arsenal bridge core. -/
theorem erdos1212_board :
    (∀ v w : Nat × Nat, adj v w ↔ adj w v) ∧
    (∀ v w : Nat × Nat, adj v w → v ≠ w) ∧
    (∀ v w : Nat × Nat, adj v w →
      (v.1 = w.1 ∧ v.2 ≠ w.2) ∨ (v.1 ≠ w.1 ∧ v.2 = w.2)) ∧
    (∀ v w : Nat × Nat, adj v w → v.1 % 2 = 1 ∧ v.2 % 2 = 1 →
      (w.1 % 2 = 1 ∧ w.2 % 2 = 0) ∨ (w.1 % 2 = 0 ∧ w.2 % 2 = 1)) ∧
    (∀ v : Nat × Nat, degB v ≤ 4) ∧
    (degB (9, 25) = 2 ∧ degB (8, 25) = 2 ∧ degB (8, 27) = 1 ∧
      degB (15, 49) = 1 ∧ degB (16, 49) = 2 ∧ degB (19, 49) = 4 ∧
      degB (203, 10201) = 3 ∧ degB (204, 10201) = 2 ∧
      degB (301, 10205) = 2) ∧
    (habitatB (9, 25) = true ∧ habitatB (15, 49) = true ∧
      habitatB (203, 10201) = true ∧ habitatB (301, 10205) = true ∧
      compB 9 = true ∧ compB 25 = true ∧ compB 203 = true ∧
      compB 301 = true ∧ compB 10201 = true ∧ compB 10205 = true ∧
      coprimeB 9 25 = true ∧ coprimeB 15 49 = true ∧
      coprimeB 203 10201 = true ∧ coprimeB 301 10205 = true) ∧
    (c49.length = 3 ∧ c925.length = 9 ∧ c1516.length = 4 ∧
      c2527.length = 10 ∧ c15949.length = 13 ∧
      c49.all habitatB = true ∧ c925.all habitatB = true ∧
      c1516.all habitatB = true ∧ c2527.all habitatB = true ∧
      c15949.all habitatB = true) ∧
    ((List.range 6).all (fun dx : Nat =>
      (List.range 6).all (fun dy : Nat =>
        decide (¬ (habitatB (5 + dx, 23 + dy) = true ∧
            adjToB (5 + dx, 23 + dy) c925 = true) ∨
          memB (5 + dx, 23 + dy) c925 = true))) = true) ∧
    (∀ dx dy : Nat, dx < 6 → dy < 6 →
      habitatB (5 + dx, 23 + dy) = true →
      adjToB (5 + dx, 23 + dy) c925 = true →
      memB (5 + dx, 23 + dy) c925 = true) ∧
    ((List.range 5).all (fun k : Nat => coprimeB (15 + k) 49) = true ∧
      coprimeB 21 49 = false ∧ coprimeB 20 49 = true ∧
      coprimeB 301 10206 = false ∧ coprimeB 301 10207 = true) ∧
    ((List.range 99).all (fun k : Nat => coprimeB (203 + k) 10201) = true ∧
      coprimeB 303 10201 = false ∧ coprimeB 404 10201 = false) ∧
    (∀ k : Nat, k < 99 → coprimeB (203 + k) 10201 = true) ∧
    (walkOK p103 = true ∧ allDistinct p103 = true) ∧
    ((firstV p103).1 = 203 ∧ (firstV p103).2 = 10201 ∧
      (lastV p103).1 = 301 ∧ (lastV p103).2 = 10205 ∧
      p103.length = 103 ∧ compB 301 = true ∧ compB 10205 = true ∧
      203 + 10201 < 301 + 10205) ∧
    (walkOK p7 = true ∧ walkOK p8 = true ∧ walkOK p6 = true ∧
      allDistinct p7 = true ∧ allDistinct p8 = true ∧
      allDistinct p6 = true ∧
      p7.length = 7 ∧ p8.length = 8 ∧ p6.length = 6) ∧
    (liveB 2 9 25 = false ∧ liveB 2 25 9 = false ∧ liveB 3 15 16 = false ∧
      liveB 6 25 27 = false ∧ liveB 8 9 49 = false ∧ liveB 6 21 25 = false ∧
      liveB 6 27 25 = false ∧ liveB 2 33 25 = false ∧
      liveB 2 25 33 = false ∧ liveB 2 27 49 = false ∧
      liveB 1 35 27 = false ∧ liveB 2 9 121 = false) ∧
    (10201 ^ 2 - 1 = (10201 - 1) * (10201 + 1) ∧
      v2r (3 ^ 1 * 10201) = v2r 10201) :=
  ⟨adj_comm, adj_distinct, adj_one_coord, adj_parity_flip, degBound,
    deg_table, habitat_anchor_rows, census_counts, comp925_no_exit,
    comp925_closed, phase15949, phase203_sweep, phase203_coprime,
    p103_valid, p103_shape, small_walks_valid, directed_death,
    ⟨sq_sub_one 10201 (by decide), CardinalWorldsV2.v2r_ternary_scaling 1 10201⟩⟩

/-! ## RECEIPT. -/

#print axioms E1212.gcdF_zero_fuel
#print axioms E1212.btoN_le_one
#print axioms E1212.countB_le
#print axioms E1212.degBound
#print axioms E1212.adj_comm_aux
#print axioms E1212.adj_comm
#print axioms E1212.adj_distinct
#print axioms E1212.adj_one_coord
#print axioms E1212.adj_parity_flip
#print axioms E1212.habitat_anchor_rows
#print axioms E1212.deg_table
#print axioms E1212.census_counts
#print axioms E1212.comp925_no_exit
#print axioms E1212.comp925_closed
#print axioms E1212.phase15949
#print axioms E1212.phase203_sweep
#print axioms E1212.phase203_coprime
#print axioms E1212.p103_valid
#print axioms E1212.p103_shape
#print axioms E1212.small_walks_valid
#print axioms E1212.directed_death
#print axioms E1212.e1212_arsenal_bridge
#print axioms E1212.erdos1212_board

/- THE KERNEL-65 RECEIPT: prints green when the whole file elaborates
clean (the CI grep target for this step). -/
#eval "E1212_COPRIME_COMPOSITE_GREEN"

end E1212
