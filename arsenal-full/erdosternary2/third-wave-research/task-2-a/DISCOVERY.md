# DISCOVERY.md — Task 2-a: Wave Machinery Map

Inventory of the wave machinery extracted from the 17,041-line monolith
`ErdosTernary2.lean` (via `/home/z/agent-work/digest/WAVES.txt`, 2,365-line
digest of wave-machinery sections), plus the GST V2 six-adic universe files:

- `/home/z/agent-work/src/GSTGraphV2SixAdicSynchronizedShadows.lean` (228 lines)
- `/home/z/agent-work/src/GSTGraphV2SixAdicOntologicalGeometry.lean` (70 lines)

All line numbers below are **monolith line numbers** (`NNNN:` prefixes in
WAVES.txt). Statements are quoted/paraphrased exactly as they appear.
Names marked *(external)* are used inside WAVES.txt but their definitions live
outside the extracted sections — they are still loadable interfaces of the
machinery.

The mission target: kill the custom axiom
`gst_four_power_direct_existence_inline : GSTFourPowerDirectExistence.FourPowerDirectExistence`
(= `∀ K ≥ 5, K ≠ 7 → ∃ p ≥ 1, digit3 (4^K) p = 2 ∧ digit3 (4^(K+1)) p = 2`)
by deriving it as a theorem.

---

## 1. WAVE DEFINITIONS (state machines, coordinates, wave predicates)

### 1.1 The carry wave coordinates (wave 1 substrate) — *(external defs, used everywhere)*

| Name | Role |
|---|---|
| `gstDigit (R p)` *(external)* | ternary digit of `R` at position `p` (used as `R / 3^p % 3`, e.g. 4961, 5091, 15862) |
| `gstCarry (R p)` *(external)* | the GST carry coordinate at position `p` (used everywhere, e.g. 4953–4959) |
| `gstStepCarry (C d)` *(external)* | one-step carry transition (used 4982–4986, 5026, `simp [gstStepCarry]`) |
| `gstStep (C d)` *(external)* | one-step edge `(digit of 4R, carry at p+1)` (used 4990–4994) |
| `gstSpaceAt (R p)` *(external)* | space class of vertex: `.gstPlus` / `.null` / ALT− (used 5086–5093, 5120–5122) |
| `gstCarryS`, `gstDigitS`, `gstStepCarryS`, `gstAffineMulCarryS` *(external)* | scratch-coordinate twins of the above (used 9553–9560, 15222–15225, 1612–1617) |
| `GSTGraphWitness`, `gstGraphNode` *(external)* | graph packaging of a witness vertex (used 5100–5108, 5091–5098) |

The four-state carry automaton: **GST+ = carry 3, NULL = carry 0, ALT− = carry 1 or 2**
(evident from `GSTBadPair` 5008 and `gstBadPair_classifier` 5013).

The fundamental equation (comment block, monolith **4088–4097**, not a theorem):
```
C(R, 0) = 0
C(R, p+1) = floor((4·d_p + C(R, p)) / 3)
Φ(R, p) = (d_p + C(R, p)) % 3 = digit of 4*R at position p
```
i.e. the carry recurrence IS the multiplication-by-4 wave in base 3. Its
generalized provable forms in the file are `gst_affine_mul_digit_exact` (6821)
and `gst_seeded_output_digit_exactS` (12207).

### 1.2 The navigation / information wave (wave 2 substrate)

| Name | Statement | Line |
|---|---|---|
| `def gstNavigationConstant (s b : Nat) : Nat` | `4^(3^s * b) / 3^(s+1)` — "the exact ternary tail exposed after the forced `s+1` zero-carry prefix of `4^(3^s*b)`" | **5114** |
| `def GSTNavigationWitness (R : Nat) : Prop` | `∃ j, gstDigit R j = 2 ∧ (gstSpaceAt R j = .gstPlus ∨ gstSpaceAt R j = .null)` — the Happy Gate | **5120** |
| `def gstAffineMulCarry (A z T j : Nat) : Nat` | `(z + A * (T % 3^j)) / 3^j` — carry injected by the affine product `z + A*T` | **6803** |
| `def gstInfiniteParadoxEnergy (t T j : Nat) : Nat` | `1 + 3^(t+1+j) * (T / 3^j) + 3^(t+1) * (T % 3^j)` | **6853** |
| `GSTOmegaState` / `gstOmega` / `gstOmegaStep` *(external defs; fields seen)* | fields: `childCarry`, `childDigit`, `affineCarry`, `parentCarry`, `parentDigit`, `bridgeResidue`, `cascadeDepth`, `paradoxEnergy` | **6906–6912** |
| `def GSTOmegaGatePolynomial (w : GSTOmegaState) : Int` | `((w.parentDigit : Int) - 2)^2 + ((w.parentCarry : Int) * ((w.parentCarry : Int) - 3))^2` | **6965** |
| `def GSTOmegaDigitTwoSet (s k m)` | `{j | (gstOmega s k m j).parentDigit = 2}` | **7023** |
| `def GSTOmegaNullSet (s k m)` | `{j | (gstOmega s k m j).parentCarry = 0}` — "NULL exists because the wave carry is 0" | **7027** |
| `def GSTOmegaPlusSet (s k m)` | `{j | (gstOmega s k m j).parentCarry = 3}` | **7031** |
| `def GSTOmegaZeroSet (s k m)` | `{j | GSTOmegaGatePolynomial (gstOmega s k m j) = 0}` — Happy-Gate positions | **7035** |
| `def GSTOmegaBadSet (s k m)` | `{j | GSTOmegaGatePolynomial (gstOmega s k m j) ≠ 0}` — ALT−/bad | **7039** |
| `def GSTOmegaInfiniteBadTrace (s k m)` | `∀ j : Nat, j ∈ GSTOmegaBadSet s k m` — the forbidden `n → ∞` orbit | **7061** |

### 1.3 The Ω∞-interface predicates (residual wave frontier)

| Name | Statement | Line |
|---|---|---|
| `def GSTLargePrefixClosed (s k : Nat) : Prop` | `(s = 3 ∧ 8 ≤ k) ∨ (2 ≤ s ∧ s ≠ 3 ∧ 5 ≤ k)` — mature-prefix region | **5905** |
| `def GSTSmallShiftNavigationLift : Prop` | `∀ s k m, 1 ≤ s → 1 ≤ k → 1 ≤ m → m % 3 ≠ 0 → ¬GSTLargePrefixClosed s k → GSTNavigationWitness (gstNavigationConstant (s+k) m) → GSTNavigationWitness (gstNavigationConstant s (1+3^k*m))` | **5933** |
| `def GSTOriginClosed (s k r) : Prop` | 6 concrete closed origin states (mature prefix ∪ five cut states) | **5976** |
| `def GSTResidualBoundary (s k r) : Prop` | exact arithmetic shape of every origin state not already closed | **5986** |
| `def GSTResidualNavigationLift : Prop` | final young-wave constructor after certified origins erased | **6016** |
| `def GSTResidualOmegaTermination : Prop` | `∀ s k m, 1 ≤ s → 1 ≤ k → 1 ≤ m → m % 3 ≠ 0 → ¬GSTOriginClosed s k (m%3) → GSTNavigationWitness (gstNavigationConstant (s+k) m) → ¬GSTOmegaInfiniteBadTrace s k m` | **7084** |

### 1.4 The seeded/scratch wave coordinates (information-wave surgery)

| Name | Statement | Line |
|---|---|---|
| `def gstPrefixOneUPotentialTailS (s n : Nat) : Nat` | `c s / 3 + 4^(3^s) * gstNavigationConstant (s+1) n` — prefix-one affine tail | **9593** |
| `def gstInformationCarryAtS (S i : Nat) : Nat` | `S / 4^i % 4` — quaternary coordinate of the shared information word | **9793** |
| `def GSTSeededHappyS (D X j : Nat) : Prop` | `gstDigitS X j = 2 ∧ (gstAffineMulCarryS 4 D X j = 0 ∨ gstAffineMulCarryS 4 D X j = 3)` — Happy Gate in a seed-retaining child wave | **14107** |
| `GSTSeededBadTraceS` *(external)* | complete seeded bad trace (used 12238–12241, 14007, 14234) | used |
| `def gstLocalRotateS (x : Nat × Nat) : Nat × Nat` | `((x.1 + 4*x.2) / 3, (x.1 + 4*x.2) % 3)` — one legal GST cell re-coordinatization | **12255** |
| `def ternaryOriginDigitS (n k : Nat) : Nat` | `n / 3^k % 3` | **14055** |
| `def InfiniteTernarySupportS (n : Nat) : Prop` | `∀ K, ∃ k, K ≤ k ∧ ternaryOriginDigitS n k ≠ 0` | **14060** |
| `def gstBinaryEventWordValueS (R Y : Nat) : Nat` | `R + 3*Y` | **16544** |
| `def gstBinarySpaceChargeS (D : Nat) : Nat` | `D / 2 + 3 * (D % 2)` — binary bit-reversal space charge | **16567** |
| `def GSTCanonicalPhysicalTrapS (Q s n c z)` | two-boundary trap + pure-power rectangle + finite bridge certificate `S / 3^(2*N) = 0` | **15499** |

### 1.5 The consecutive-power two-wave family (the direct ancestors of the target)

| Name | Statement | Line |
|---|---|---|
| `def GSTPowerTwoWave (a : Nat) : Prop` | `hasTernaryTwo (4^a) = true ∨ GSTNavigationWitness (4^(a-1))` — "the two consecutive power waves overlap at a Happy Gate" | **16950** |
| `def GSTTwoWaveBadTrace (R : Nat) : Prop` | `∀ j, GSTBadPair (gstCarry R j) (gstDigit R j) ∧ GSTBadPair (gstCarry (4*R) j) (gstDigit (4*R) j)` | **16957** |
| `def GSTBadPair (C d : Nat) : Prop` | `¬ (d = 2 ∧ (C = 0 ∨ C = 3))` — bad-wave automaton acceptance | **5008** |

---

## 2. WAVE INTERACTION LAWS (how the waves act and combine)

### 2.1 The x4 multiplication wave (digit/carry transport)

| Name | Statement | Line |
|---|---|---|
| `div_add_of_dvd (a b c) (hpos) (hdvd)` | `(b + c) / a = b / a + c / a` | **3791** |
| `four_mul_mod3_eq (n)` | `(4 * n) % 3 = n % 3` | **3804** |
| `four_mul_d2_equation (X p) (hp) (hX_div : X / 3^p % 3 = 2)` | `(4 * X) / 3^p % 3 = (2 + (4 * (X % 3^p)) / 3^p) % 3` | **3807** |
| `four_mul_mod_eq (R p) (hp : 1 ≤ p)` | `(4 * R) % 3^p = (4 * (R % 3^p)) % 3^p` | **4045** |
| `carry_four_mul_eq (R p) (hp : 1 ≤ p)` | carry of `4*R` at `p` equals carry of `4*(R % 3^p)` at `p` | **4071** |
| `carry_four_mul_bound (R p) (hp : 1 ≤ p)` | `(4 * ((4 * R) % 3^p)) / 3^p < 4` | **4080** |
| `gst_residue_succ_exact (T j)` | `T % 3^(j+1) = T % 3^j + 3^j * gstDigit T j` | **6806** |
| `gst_affine_mul_digit_exact (A z T j)` | `gstDigit (z + A*T) j = (gstAffineMulCarry A z T j + A * gstDigit T j) % 3` — the provable Φ equation | **6821** |
| `gst_affine_mul_carry_forward (A z T j)` | `gstAffineMulCarry A z T (j+1) = (gstAffineMulCarry A z T j + A * gstDigit T j) / 3` | **6838** |
| `gst_seeded_output_digit_exactS (seed H q)` | `gstDigitS (seed + 4*H) q = (gstAffineMulCarryS 4 seed H q + gstDigitS H q) % 3` | **12207** |
| `gstCarry_forward_exact_all (R p)` *(also `gstCarry_forward_exact` (R p) (hp))* | `gstCarry R (p+1) = gstStepCarry (gstCarry R p) (gstDigit R p)` — including position 0 | **6069** |

### 2.2 The four-state carry automaton tables

| Name | Statement | Line |
|---|---|---|
| `gstStepCarry_table` | full 12-entry transition table for `gstStepCarry` | **4982** |
| `gstStep_table` | full 12-entry edge table for `gstStep` (digit of 4R, carry at p+1) | **4990** |
| `gstStepCarry_product_bounded (C d) (hC : C < 4) (hd : d < 3)` | `gstStepCarry C d < 4` | **5000** |
| `gstForward_from_null (R p) (hp : 1 ≤ p) (hC : gstCarry R p = 0)` | d=0→0, d=1→1, d=2→2 next carry | **5021** |
| `gstForward_from_gstPlus (R p) (hC : gstCarry R p = 3)` | d=0→1, d=1→2, d=2→3 | **5033** |
| `gstForward_from_altOne (R p) (hC : gstCarry R p = 1)` | d=0→0, d=1→1, d=2→3 | **5045** |
| `gstForward_from_altTwo (R p) (hC : gstCarry R p = 2)` | d=0→0, d=1→2, d=2→3 | **5057** |
| `gst_null_two_regenerates (R p) (hC : 0) (hd : d = 2)` | `gstCarry R (p+1) = 2` — NULL is not terminal | **7759** |
| `gst_plus_two_propagates (R p) (hC : 3) (hd : d = 2)` | `gstCarry R (p+1) = 3` | **7766** |

### 2.3 The two-wave surgical lift (THE survival law for consecutive powers)

| Name | Statement | Line |
|---|---|---|
| `gst_pure_lift_or_forced_cascade (R p) (hp : 1 ≤ p) (hd : gstDigit R p = 2) (hgood : gstCarry R p = 0 ∨ gstCarry R p = 3)` | `(gstDigit (4*R) p = 2 ∧ (gstCarry (4*R) p = 0 ∨ gstCarry (4*R) p = 3)) ∨ (gstDigit (4*R) p = 2 ∧ (gstCarry (4*R) p = 1 ∨ = 2) ∧ gstCarry (4*R) (p+1) = 3)` — **in BOTH branches `gstDigit (4*R) p = 2`** | **4952** |
| `gst_duality_carry0 (R p) (hp1) (hp_d2) (hcarry0)` | carry 0 at a d2 ⇒ `hasTernaryTwo (4 * R) = true` | **3828** |
| `gst_duality_carry1 (R p) (hp1) (hp_d2) (hcarry1) (hnext_d2)` | carry 1 + next digit 2 ⇒ `hasTernaryTwo (4 * R) = true` | **3838** |
| `gst_duality (R) (hR_mod3 : R % 3 = 1) (hR_has) (h_creation)` | full carry-wave duality (Infinite Paradox) | **3892** |
| `gst_four_pow_adjacent (a) (ha : 1 ≤ a)` | `4 * 4^(a-1) = 4^a` | **16973** |
| `gst_happy_big2_next_carry_two_or_threeS (T p) (hgate)` | after a seed-zero Happy cell, next carry is 2 or 3 | **15236** |
| `gst_child_gate_high_realisationS (C) (hC : C = 0 ∨ C = 3)` | `gstOutputDigitS C 2 = 2 ∧ (gstStepCarryS C 2 = 2 ∨ = 3)` | **14033** |

### 2.4 Seeded / affine / shared-information interaction laws

| Name | Statement | Line |
|---|---|---|
| `gst_omega_universal_equation (s k m j)` | `gstOmega s k m (j+1) = gstOmegaStep (4^(3^s)) (gstOmega s k m j)` | **6916** |
| `gst_infinite_paradox_energy_conservation (t T j)` | `gstInfiniteParadoxEnergy t T j = 1 + 3^(t+1) * T` | **6856** |
| `gst_navigation_constant_b1_recurrence (s m) (hs : 1 ≤ s)` | `gstNavigationConstant s (1+3*m) = c s + 3*4^(3^s) * gstNavigationConstant (s+1) m` | **5332** |
| `gst_navigation_constant_general_recurrence (s k m)` | `Q(s, 1+3^k m) = c s + 3^k 4^(3^s) Q(s+k, m)` | **5390** |
| `gst_affine_prefix_mod (c0 A T k j) (hj : j ≤ k)` | `(c0 + 3^k*A*T) % 3^j = c0 % 3^j` — tail invisible below its birth height | **5420** |
| `gst_affine_prefix_carry (c0 A T k j) (hj : j ≤ k)` | `gstCarry (c0 + 3^k*A*T) j = gstCarry c0 j` | **5428** |
| `gst_affine_prefix_digit (c0 A T k j) (hj : j < k)` | `gstDigit (c0 + 3^k*A*T) j = gstDigit c0 j` | **5432** |
| `gst_child_carry_reindex_seeded (T q j)` | `gstCarry T (q+j) = gstAffineMulCarry 4 (gstCarry T q) (T / 3^q) j` | **7774** |
| `gst_child_state_reindex_seeded (T q j)` | digit + carry reindexing under a ternary cut | **7782** |
| `gst_parent_state_reindex_seeded (D X q j)` | parent seeded-affine state reindexing | **7791** |
| `gst_child_gate_reindex_seeded (T q) (hgate)` | child Happy Gate survives reindexing | **7801** |
| `gst_affine_block_memory (A z T ...)` *(statement tail at 7818)* | block-memory identity `c*(T mod D)` in the affine carry | **7818** |
| `gst_shared_information_state_exactS (A z T q)` | `gstAffineMulCarryS (4*A) (1+4*z) T q = gstAffineMulCarryS 4 1 (z+A*T) q + 4 * gstAffineMulCarryS A z T q` | **9917** |
| `gst_shared_information_state_forwardS (A z T q)` | ternary vertical recurrence of one shared state | **9953** |
| `gst_seeded_shared_information_equationS (A B C C' z T q) (hcommute)` | the commuting-square information split law | **13539** |
| `gst_phase01_shared_informationS (A z T q)` | phase 0→1: seed zero becomes seed one | **13558** |
| `gst_phase12_shared_informationS (N c z T q)` | phase 1→2 seed advance | **13574** |
| `gst_coupled_bad_information_regeneratesS (A D Z W C Y)` | parent bad trace + endpoints regenerate after one child digit | **14006** |
| `gst_local_rotate_fiveS (C d) (hC : C < 4) (hd : d < 3)` | every legal cell returns after five re-coordinatizations; fixed states `(0,0)`, `(3,2)`; two five-cycles | **12261** |
| `gst_seed_zero_affine_carry_eq_physicalS (T p)` | `gstAffineMulCarryS 4 0 T p = gstCarryS T p` — seed-0 seeded carry IS the physical GST carry | **15222** |
| `gst_seed_zero_happy_is_physical_big2S (T p) (hgate)` | seed-zero Happy Gate = physical Happy BIG2 cell | **15228** |
| Binary layer laws: `gst_binary_seeded_event_valueS` (16547), `gst_binary_two_layer_event_chargeS` (16555), `gst_binary_space_charge_four_valuesS` (16570), `gst_binary_space_charge_ne_twoS` (16581), `gst_binary_good_space_charge_endpointsS` (16589), `gst_seeded_x4_event_chargeS` (16599), `gst_seeded_x4_binary_layers_exactS` (16611: `D % 2 + 2 * (D/2 + 2*R) = D + 4*R`), `gst_shared_x4_binary_factorS` (16640) | two binary x2 layers = one seeded x4 wave; NULL/GST+ = endpoints of the event charge, central charge 2 never legal | **16544–16657** |
| Information geometry: `gst_information_low_coordinatesS` (9767), `gst_information_high_coordinatesS` (9780), `gst_information_bottom_top_coordinatesS` (9798), `gst_information_word_boundS` (9820), `gst_information_bridge_nullS` (9902) | the two GST decompositions are bottom/top base-4 coordinates of one information word; aligned bridge depth has zero quotient `S / 3^(2*N) = 0` | **9766–9908** |

---

## 3. WAVE BOUNDARY / DISTINCTION THEOREMS

### 3.1 Happy Gate vs. bad trace (the distinction)

| Name | Statement | Line |
|---|---|---|
| `gstBadTrace_of_no_navigation_witness (R) (hno : ¬ GSTNavigationWitness R) (j)` | `GSTBadPair (gstCarry R j) (gstDigit R j)` | **5126** |
| `gstNavigationWitness_iff_not_badTrace (R)` | `GSTNavigationWitness R ↔ ¬ (∀ j, GSTBadPair (gstCarry R j) (gstDigit R j))` | **5139** |
| `gstBadPair_classifier (C d) (hC : C < 4) (hd : d < 3)` | `GSTBadPair C d ↔ (((C = 0 ∨ C = 3) ∧ (d = 0 ∨ d = 1)) ∨ ((C = 1 ∨ C = 2) ∧ (d = 0 ∨ d = 1 ∨ d = 2)))` | **5013** |
| `gst_omega_gate_polynomial_zero_iff (w)` | `GSTOmegaGatePolynomial w = 0 ↔ w.parentDigit = 2 ∧ (w.parentCarry = 0 ∨ w.parentCarry = 3)` | **6969** |
| `gst_omega_zeroSet_eq_subspaces (s k m)` | `GSTOmegaZeroSet = GSTOmegaDigitTwoSet ∩ (GSTOmegaNullSet ∪ GSTOmegaPlusSet)` | **7044** |
| `gst_omega_badSet_eq_compl (s k m)` | `GSTOmegaBadSet = (GSTOmegaZeroSet)ᶜ` | **7053** |
| `gst_omega_noInfiniteBadTrace_iff_zeroSet_nonempty (s k m)` | `¬ GSTOmegaInfiniteBadTrace ↔ (GSTOmegaZeroSet).Nonempty` | **7066** |
| `gst_twoWave_badTrace_of_no_navigation (R) (hR) (h4R)` | failure of both Navigation alternatives = complete two-wave bad trace | **16964** |
| `gst_seeded_happy_iff_common_twoS (seed H q) (hseed : seed < 4)` | `(gstDigitS H q = 2 ∧ (gstAffineMulCarryS 4 seed H q = 0 ∨ = 3)) ↔ (gstDigitS H q = 2 ∧ gstDigitS (seed + 4*H) q = 2)` — **a seeded Happy Gate IS a common digit-two between `H` and `seed+4H`** | **12215** |
| `gst_seeded_bad_iff_no_common_twoS (seed H) (hseed : seed < 4)` | `GSTSeededBadTraceS seed H ↔ ∀ q, ¬ (gstDigitS H q = 2 ∧ gstDigitS (seed + 4*H) q = 2)` | **12238** |
| `gstNavigationWitness_mul_three (R) (h)` | witness survives `×3` shift | **5158** |

### 3.2 The Ω∞ / residual boundary system

| Name | Statement | Line |
|---|---|---|
| `gst_orthogonal_badTrace_system (s b j) (hs) (hno)` | fingerprint equation + exact automaton state at each position | **5306** |
| `gst_omega_origin_exact (s k m j) (hs : 1 ≤ s)` | `(gstOmega s k m j).paradoxEnergy = 4^(3^(s+k)*m)` — origin retained | **6943** |
| `gst_omega_parent_projection (s k m j) (hs)` | residual parent graph = Ω∞ parent projection shifted by `k` | **6951** |
| `gst_omega_termination_s1 (k m) (hk) (hm) (hm3) (hboundary) (hchild)` | `¬ GSTOmegaInfiniteBadTrace 1 k m` — level-1 residual termination | **7377** |
| `gst_omega_termination_s3 (k m) ...` | `¬ GSTOmegaInfiniteBadTrace 3 k m` — level-3 residual termination | **7408** |
| `gst_origin_not_closed_boundary (s k r) ... (hnot : ¬ GSTOriginClosed s k r)` | `GSTResidualBoundary s k r` | **5992** |
| `gst_suffix_after_last_gate_is_badS (D X q) (hq) (hlast)` | after the globally last child gate the suffix is a complete seeded bad trace | **14188** |
| `gst_exists_global_last_seeded_gateS (D X) (hex)` | every seeded witness in a natural child has a globally last Happy Gate | **14166** |
| `gst_exists_last_seeded_gate_belowS (D X N) (hex)` | last gate in a finite interval | **14113** |
| `gst_digit_zero_above_self_ceilingS (X j) (hj : X + 1 ≤ j)` | `gstDigitS X j = 0` | **14144** |
| `gst_no_seeded_gate_above_self_ceilingS` | gates confined below the natural ceiling | **14156** |
| `gst_canonical_two_boundary_trapS (A z T) ...` | two-boundary trap packaging | **14230** |
| `gst_canonical_trap_is_physical_surgeryS (Q) (hQ) ...` | trap + exact pure-power rectangle certificate | **15523** |
| `gst_last_child_gate_right_chordS (T q) (hgate)` | THE LOCAL HAND-OFF: exactly two branches — GST+ 55_6 (event (5,5), seed 3) or BIG1 crossing NULL 42_6 (event (5,7), seed 2) | **15262** |

---

## 4. DIGIT-2 WITNESS PRODUCERS & EXPONENT-CLASS COVERERS

| Name | Statement | Line |
|---|---|---|
| `gstDecide (a K)` + `gstDecide_correct` | fast decision of `hasTwoInFirstKStruct (powMod 4 a (3^K)) K` ⇒ `hasTernaryTwo (4^a) = true` | **3557/3560** |
| `four_pow_mod27 (m)` | `4^m % 27 = 4^(m % 9) % 27` (period-9 lift) | **3580** |
| `hasTernaryTwo_first_pos (n) (h : hasTernaryTwo n = true)` | `∃ q, n / 3^q % 3 = 2 ∧ ∀ p < q, n / 3^p % 3 ≠ 2` — FIRST d2 with minimality | **4120** |
| `three_pow_mod2 (q)` | `3^q % 2 = 1` | **4151** |
| `mod_bound_all_digits_le_one (n q)` | `n % 3^q ≤ (3^q - 1) / 2` when digits ≤ 1 | **4158** |
| `h_creation_4pow_survive (k) (hk5 : 5 ≤ k) (hv3k : 1 ≤ v3 k) (hb3 : (k / 3^(v3 k)) % 3 = 2)` | `∃ p ≥ 1, 4^k / 3^p % 3 = 2 ∧ (carry = 0 ∨ (carry = 1 ∧ next digit 2))` — **the SURVIVE witness producer for `4^k` on the exponent class `v3(k) ≥ 1, b%3 = 2`** (uses `cascade_universal`) | **3910** |
| `gst_navigation_origin (s b) (hs : 1 ≤ s) (hb : 1 ≤ b) (hb3 : b % 3 ≠ 0)` | `gstDigit (4^(3^s*b)) (s+1) = b % 3 ∧ gstCarry (4^(3^s*b)) (s+1) = 0` — **universal origin: NULL carry, exposed digit `b % 3`** | **5179** |
| `gst_bridge_is_null (k) (hk : 2 ≤ k)` | `gstSpaceAt (4^k) (2*k) = .null` (via `bridge_carry_zero`) | **5086** |
| `gstNavigationWitness_of_digit_carry_zero / _three (R j)` | digit 2 + carry 0/3 ⇒ Navigation witness | **5167/5172** |
| `gstGraphWitness_of_null / _of_gstPlus (R N p)` | graph witness constructors | **5100/5105** |
| `gst_navigation_digit_shift (s b j)` | `gstDigit (4^(3^s*b)) (s+1+j) = gstDigit (gstNavigationConstant s b) j` | **6060** |
| `gst_navigation_carry_shift (s b j)` | carry transport along every forward edge | **6079** |
| `gst_affine_prefix_witness (c0 A T k j) (hj : j < k) (h)` | GST+/NULL digit-two vertex survives the generalized Navigation tail exactly | **5441** |
| `gst_navigation_constant_large_prefix_witness (s k m) (hlarge)` | infinite-family closure of the generalized `b ≡ 1` wave | **5911** |
| `gst_navigation_witness_all_of_small_shift (hsmall)` | full witness theorem given `GSTSmallShiftNavigationLift` | **5942** |
| `gst_navigation_witness_all_of_residual (hresidual)` | full witness theorem given `GSTResidualNavigationLift` | **6025** |
| `gst_navigation_constant_origin_closed_witness` | dispatch over the six closed origin classes | **6000** |
| `gst_navigation_constant_one_witness_all` *(used 5895, 5952, 6035)* | b = 1 terminal closure (with s = 2, s = 3 special waveforms) | used |
| `gst_power_two_wave_large (a) (ha : 500 < a)` | `GSTPowerTwoWave a` — via `gst_four_power_creation_master_inline` → `gst_four_power_ontological_navigation_of_master` → `gst_navigation_witness_of_standalone_navigation` | **16985** |
| `erdos_ternary_2_even_universal (a) (ha : 5 ≤ a)` | `hasTernaryTwo (4^a) = true` — small range via `modular_check_base`, large range via the two-wave lift **and the p=0 elimination `4^(a-1) % 3 = 1`** | **16997** |
| `erdos_ternary_2_universal (n) (hn : 9 ≤ n)` | `noTernaryTwo (2^n) = false` — the Erdős ternary-2 final theorem (odd route + even route) | **17030** |

### 4.1 The four-power creation chain (the theorem-shaped twin of the target axiom)

| Name | Statement | Line |
|---|---|---|
| `gst_four_power_creation_master_inline` | `GSTFourPowerOntologicalAdapter.FourPowerCreationMaster` — **proved as a theorem**, by `intro K hK5 hK7; simpa [GSTFourPowerOntologicalAdapter.CreationCertificate] using (gst_four_power_creation_certificate_inline K hK5 hK7)` — i.e. the master is `∀ K, 5 ≤ K → K ≠ 7 → CreationCertificate K`, supplied by "the independently kernel-checked width-three wave" | **16933** |
| `gst_four_power_creation_certificate_inline` *(external, used)* | the kernel-checked width-three wave certificate with hypotheses `hK5 : 5 ≤ K`, `hK7 : K ≠ 7` | used **16937** |
| `GSTFourPowerOntologicalAdapter.gst_four_power_ontological_navigation_of_master` *(external, used)* | master → `GSTCanonicalTailStateIso.Navigation (4^a)` (applied at 16989 with two `omega`-side conditions under `500 < a`) | used **16989** |
| `gst_navigation_witness_of_standalone_navigation` *(external, used)* | `GSTCanonicalTailStateIso.Navigation (4^a) → GSTNavigationWitness (4^a)` | used **16992** |
| `gst_prefix_one_navigation_lift_of_master_inline (hMaster)` | `GSTPrefixOneNavigationLift` from the master (child witness unused — POE proves the parent unconditionally) | **16925** |
| `gst_prefix_one_navigation_lift` | public prefix-one theorem: green width-three wave builds FP-NAV, POE constructs the parent Happy gate | **16941** |
| `gst_prefix_one_ontological_escape_of_master_inline` *(external, used 16931)* | the POE route | used |
| `modular_check_base` *(external, used 17000)* | `5 ≤ a → a ≤ 500 → hasTernaryTwo (4^a) = true` | used |
| `erdos_ternary_2_odd_universal` *(external, used 17033)* | odd-exponent route | used |
| `has_two_imp_not_no_two` *(external, used 17040)* | `hasTernaryTwo n = true → noTernaryTwo n = false` | used |

---

## 5. THE GST V2 SIX-ADIC UNIVERSE (the merge substrate for wave 3)

From `GSTGraphV2SixAdicOntologicalGeometry.lean` (namespace
`GSTGraphV2SixAdicOntologicalGeometry`, opens `GSTGraphV2NonEuclidean`):

| Name | Statement | File line |
|---|---|---|
| `def SixAdicIsoAt (k : Nat) (x y : Int) : Prop` | `∃ q : Int, x - y = (6 : Int)^k * q` | 23 |
| `def DyadicShadowAt (k : Nat) (x y : Int) : Prop` | `∃ q : Int, x - y = (2 : Int)^k * q` | 27 |
| `def TriadicShadowAt (k : Nat) (x y : Int) : Prop` | `∃ q : Int, x - y = (3 : Int)^k * q` | 31 |
| `def SixAdicBall (k : Nat) (c : Int) : Set Int` | `{x | SixAdicIsoAt k x c}` | 35 |
| `def sixChildCenter (k c j) : Int` | `c + j * (6 : Int)^k` — the six canonical refinement centers | 40 |
| `def GraphIsoAt (k) (G H : Graph)` | `SixAdicIsoAt k (G.energy : Int) (H.energy : Int)` — seven-axis ontology unchanged | 45 |
| `def physicalEnergy (P : PhysicalProjection) : Int` | `(4 : Int)^P.x4Phase * (P.sourceEnergy : Int)` — the physical `x4` chart | 50 |
| `def PhysicalProjectionIsoAt (k) (P Q)` | `SixAdicIsoAt k (physicalEnergy P) (physicalEnergy Q)` | 55 |
| `structure ResolvedGraph` | `ambient : Graph`, `resolution : Nat` — resolution is an overlay | 60 |
| `def resolvedVertex (G : ResolvedGraph) (p)` | `vertex G.ambient p` — resolving never changes the GST vertex | 66 |

From `GSTGraphV2SixAdicSynchronizedShadows.lean` (namespace
`GSTGraphV2SixAdicSynchronizedShadows`):

| Name | Statement | File line |
|---|---|---|
| `dyadic_triadic_to_six (h2 : DyadicShadowAt k x y) (h3 : TriadicShadowAt k x y)` | `SixAdicIsoAt k x y` (CRT synchronization) | 19 |
| `six_iso_iff_synchronized_shadows (k x y)` | `SixAdicIsoAt k x y ↔ DyadicShadowAt k x y ∧ TriadicShadowAt k x y` | 44 |
| `six_ball_membership_iff_shadows (k c x)` | ball = intersection of synchronized shadow balls | 56 |
| `triadic_shadow_mul_four_pow_iff (k t x y)` | `TriadicShadowAt k (4^t*x) (4^t*y) ↔ TriadicShadowAt k x y` — **multiplication by `4^t` is a genuine isometry of every triadic shadow** | 68 |
| `dyadic_shadow_mul_four_pow_iff (k t) (hkt : 2*t ≤ k) (x y)` | `DyadicShadowAt k (4^t*x) (4^t*y) ↔ DyadicShadowAt (k-2*t) x y` | 93 |
| `dyadic_shadow_zero (x y)` | `DyadicShadowAt 0 x y` | 140 |
| `dyadic_shadow_mul_four_pow_of_saturated (k t) (hkt : k ≤ 2*t) (x y)` | dyadic shadow saturated, no residual condition | 147 |
| `dyadic_shadow_mul_four_pow_iff_truncated (k t x y)` | `DyadicShadowAt k (4^t*x) (4^t*y) ↔ DyadicShadowAt (k-2*t) x y` (truncated subtraction, all cases) | 171 |
| `six_iso_mul_four_pow_iff_skew_shadows (k t) (hkt : 2*t ≤ k) (x y)` | `SixAdicIsoAt k (4^t*x) (4^t*y) ↔ DyadicShadowAt (k-2*t) x y ∧ TriadicShadowAt k x y` | 131 |
| `six_iso_mul_four_pow_iff_truncated_skew_shadows (k t x y)` | same, every exponent: full triadic depth + truncated dyadic shift | 188 |
| `six_pow_dvd_four_pow_mul_sub_iff_truncated (k t x y)` | `(6:Int)^k ∣ (4:Int)^t*(x-y) ↔ (3:Int)^k ∣ x-y ∧ (2:Int)^(k-2*t) ∣ x-y` | 199 |

Also seen in the monolith digest, graph-universe interfaces used by the wave
machinery (external): `GSTGraphV2InfiniteControl.graph`,
`GSTGraphV2CanonicalNWave.nWaveShift`, `GSTGraphV2PerfectPowerBlock.canonicalWidth`,
`GSTU2DEventTransport.HappyCell` (monolith 16802–16816),
`GSTCanonicalSevenAxisBridge.carry4` / `GSTCanonicalSevenAxisBridge.digit3`
(monolith 16864–16871 — **`digit3` is the target axiom's digit function**),
`GSTPrefixOneU2DCollisionProof.childTail / rightTail / childEnergy`
(16853–16860).

---

## 6. HOW WAVES 1/2 ARE STRUCTURED IN LEAN (synthesis)

The monolith's wave family is a three-layer erection:

1. **Wave 1 — the physical carry wave (the x4 chart).**
   Coordinates `gstCarry R p` / `gstDigit R p` with the kernel-checked
   four-state automaton `gstStepCarry`/`gstStep` (full tables at 4982/4990;
   closure at 5000). Spaces: GST+ = carry 3, NULL = carry 0, ALT− = carry 1/2.
   Forward laws per space: `gstForward_from_null/gstPlus/altOne/altTwo`
   (5021–5063); regeneration: `gst_null_two_regenerates` (7759),
   `gst_plus_two_propagates` (7766). The wave equation is Φ (4088–4097),
   proved as `gst_affine_mul_digit_exact` (6821) and
   `gstCarry_forward_exact_all` (6069).

2. **Wave 2 — the navigation / information wave (the perfect-power tail).**
   `gstNavigationConstant s b = 4^(3^s*b) / 3^(s+1)` (5114) with origin
   `gst_navigation_origin` (5179: NULL carry + digit `b % 3` at `s+1`);
   witness predicate `GSTNavigationWitness` (5120: digit-two in GST+/NULL);
   exact recurrences (5332, 5390); prefix-survival laws (5420–5441);
   the Ω∞ parent overlay `gstOmega` with conserved origin energy (6853–6947)
   and the gate polynomial (6965); boundary system
   `GSTOriginClosed`/`GSTResidualBoundary` (5976/5986) with the termination
   laws `gst_omega_termination_s1/s3` (7377/7408) and
   `GSTResidualOmegaTermination` (7084).

3. **The two-wave overlay on consecutive powers (the direct ancestor of the
   target).** `GSTPowerTwoWave a` (16950) = digit-two in `4^a` OR a
   Navigation witness in `4^(a-1)`; the obstruction language
   `GSTTwoWaveBadTrace` (16957); the surgical lift
   `gst_pure_lift_or_forced_cascade` (4952) — a Happy-Gate digit-two of `R`
   remains a digit-two of `4*R` in **both** branches; and the closure
   `gst_power_two_wave_large` (16985) → `erdos_ternary_2_even_universal`
   (16997) → `erdos_ternary_2_universal` (17030), with the four-power
   creation master (16933) as the theorem-grade source of witnesses for all
   `K ≥ 5, K ≠ 7`.

The **scratch (S-suffixed)** layer (9553–16657) is a parallel coordinate
system (`gstDigitS`, `gstCarryS`, `gstAffineMulCarryS`, `GSTSeededHappyS`,
binary event charges) for the same wave, used by the U-potential and
prefix-one attacks; its bridge back to the physical wave is
`gst_seed_zero_affine_carry_eq_physicalS` (15222).

**Key structural fact for this task:** the seed-zero Happy Gate is *literally*
a common digit-two of `H` and `4·H` (`gst_seeded_happy_iff_common_twoS`,
12215), and the physical lift law `gst_pure_lift_or_forced_cascade` (4952)
keeps the digit-two at the *same* position under the x4 edge whenever the
carry is aligned (0 or 3). The target axiom
(`∃ p ≥ 1, digit3 (4^K) p = 2 ∧ digit3 (4^(K+1)) p = 2`) is therefore exactly
a **Navigation-witness statement about `4^K`** — the third wave.

---

## 7. REFERENCED-BUT-EXTERNAL INTERFACES (names seen used, defined outside the extract)

`gstCarry`, `gstDigit`, `gstStepCarry`, `gstStep`, `gstSpaceAt`,
`gstOutputDigit`, `gstOutputDigit_forward_exact`, `gstCarry_forward_exact`,
`gstGoodSpace_carry_mod3_zero`, `gstCarry_lt_four`, `gstDigit_lt_three`,
`gstSpaceAt_of_carry_zero`, `gstSpaceAt_of_carry_three`,
`gstDigit_mul_three_shift`, `gstSpace_mul_three_shift`,
`nat_lt_four_cases`, `gst_carry_cases`, `gst_digit_cases`,
`carry_reset_after_d2`, `first_d2_carry_lt_two`, `gstGraphNode`,
`GSTGraphWitness`, `c`, `c_mod3`, `lte_identity`, `cascade_universal`,
`pow_v3_dvd`, `v3`, `mod_eq_one_of_sub_mod_zero`, `digit_identity`,
`gst_div_add_of_dvd`, `gst_navigation_decomposition`,
`gst_navigation_affine_product_state`, `gst_generalized_navigation_algebra`,
`generalized_cascade_terminates`, `gst_navigation_constant_one_witness`
(+ `_all`, `_s2`, `_s3`), `gstNavigationConstant_one`,
`gst_navigation_constant_b2_witness`, `gst_navigation_constant_cut_k2_b1`,
`gst_navigation_constant_s1_k2_b2`, `gst_navigation_constant_s1_cut_b2_large`,
`gst_navigation_constant_s3_k4_b1`, `gst_navigation_constant_s3_k6_b2`,
`gst_orthogonal_origin_fingerprint`,
`gst_omega_childZeroSet_nonempty_of_navigation_witness`,
`gst_residual_origin_descent_certificate`,
`gst_omega_infiniteBadTrace_iff_seededAffine`,
`gst_omega_infiniteBadTrace_blocks`, `GSTOmegaBadBlock`,
`GSTSeededAffineBadTrace`, `gst_omega_affine_tail_block_echo`,
`gst_bad_prefix_u_potential_boundS`,
`gst_complete_bad_u_potential_terminal_boundS`, `gstHandwrittenUChargeS`,
`gstBadPairS`, `gstAffineMulCarryS`, `gstDigitS`, `gstCarryS`,
`gstStepCarryS`, `gstOutputDigitS`, `GSTSeededBadTraceS`,
`gst_affine_carry_lt_multiplierS`, `gst_parent_digit_from_informationS`,
`gst_affine_tail_div_decompositionS`, `gst_seeded_affine_digit_shiftS`,
`gst_seeded_affine_carry_semigroupS`, `gstAffineS_forward_exact_all`,
`gst_relative_parent_bad_regeneratesS`, `gst_shared_two_endpoint_regeneratesS`,
`gst_shared_high_remainder_ltS`, `gst_canonical_origin_modulusS`,
`gst_canonical_Q_one_two_eq_455S`, `four_pow_succ_lt_three_pow_doubleS`,
`gst_information_bridge_boundS`, `GSTPhysicalTwoDigitBig1ClearS`,
`gstPhysicalMicroPairS`, `gstWideCarryS`, `GSTCanonicalOriginEnergyS`,
`GSTCanonicalTwoBoundaryTrapS`, `gst_canonical_phase0_energy_shape_surgeryS`,
`gst_shared_state_is_exact_power_rectangleS`,
`gst_navigation_constant_unit_prefixS`, `gstCanonicalPrefixOffsetS`,
`modular_check_base`, `erdos_ternary_2_odd_universal`,
`has_two_imp_not_no_two`, `hasTernaryTwo_of_digit`,
`hasTwoInFirstK*`, `powMod_correct`, `mod_has_two`, `hasTernaryTwo.eq_def`,
`GSTPrefixOneNavigationLift`, `gst_prefix_one_ontological_escape_of_master_inline`,
`gst_four_power_creation_certificate_inline`,
`GSTFourPowerOntologicalAdapter.*` (FourPowerCreationMaster, CreationCertificate,
gst_four_power_ontological_navigation_of_master),
`GSTCanonicalTailStateIso.Navigation`, `gst_navigation_witness_of_standalone_navigation`,
`GSTU2DEventTransport.HappyCell`, `GSTGraphV2InfiniteControl.graph`,
`GSTGraphV2CanonicalNWave.nWaveShift`, `GSTGraphV2PerfectPowerBlock.canonicalWidth`,
`GSTCanonicalSevenAxisBridge.carry4/digit3`, `GSTPrefixOneU2DCollisionProof.*`.

*(Plan only cites names that appear above; every additional name used in
PLAN.md is taken from §1–§7.)*
