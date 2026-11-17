import GSTWorldCosmology
import waves.GSTWaveCohomology
import waves.CardinalWorldsPostulateLaw
import GSTGraphV2Ontological
import GSTTailFFourthDimension
import GSTClimbInfiniteFamily

/-!
# Coherent GST cosmology: exact wave reconstruction and nonstationary towers

An additive extension of the existing GST laws. All observations are finite;
compatibility relates different resolutions. No terminal-boundary proposition
or unproved universal signature statement is used as a hypothesis.
-/

set_option maxHeartbeats 20000000
set_option maxRecDepth 1000000

namespace GSTCoherentCosmology

open GSTCanonicalSevenAxisBridge GST2DMixedEmergence
open GSTGraphV2Ontological GSTGraphV2OmegaWaveLaw

/-- The mixed wave and the pure ontological current, read together. -/
def dualCurrent (C d : Nat) : Int × Int :=
  (mixedDensity C d, ontDensity C d)

/-- The two existing currents jointly separate every physical cell. -/
theorem dual_current_finite_separation :
    ∀ C₁ : Fin 4, ∀ d₁ : Fin 3, ∀ C₂ : Fin 4, ∀ d₂ : Fin 3,
      dualCurrent C₁.val d₁.val = dualCurrent C₂.val d₂.val →
        C₁ = C₂ ∧ d₁ = d₂ := by decide

theorem dual_current_separation (C₁ d₁ C₂ d₂ : Nat)
    (hC₁ : C₁ < 4) (hd₁ : d₁ < 3) (hC₂ : C₂ < 4) (hd₂ : d₂ < 3)
    (h : dualCurrent C₁ d₁ = dualCurrent C₂ d₂) :
    C₁ = C₂ ∧ d₁ = d₂ := by
  have hs := dual_current_finite_separation
    ⟨C₁, hC₁⟩ ⟨d₁, hd₁⟩ ⟨C₂, hC₂⟩ ⟨d₂, hd₂⟩ h
  exact ⟨congrArg Fin.val hs.1, congrArg Fin.val hs.2⟩

/-- A concrete decoder, not an existential inverse. -/
def decodeCurrent (v : Int × Int) : Nat × Nat :=
  if v = (70, -54) then (0, 0) else
  if v = (112, -21) then (0, 1) else
  if v = (-56, 84) then (0, 2) else
  if v = (0, -21) then (1, 0) else
  if v = (210, 0) then (1, 1) else
  if v = (-112, -33) then (1, 2) else
  if v = (112, 0) then (2, 0) else
  if v = (42, -54) then (2, 1) else
  if v = (-56, 0) then (2, 2) else
  if v = (168, -33) then (3, 0) else
  if v = (0, 0) then (3, 1) else
  if v = (70, 42) then (3, 2) else (0, 0)

theorem decode_current_finite : ∀ C : Fin 4, ∀ d : Fin 3,
    decodeCurrent (dualCurrent C.val d.val) = (C.val, d.val) := by decide

theorem decode_current (C d : Nat) (hC : C < 4) (hd : d < 3) :
    decodeCurrent (dualCurrent C d) = (C, d) :=
  decode_current_finite ⟨C, hC⟩ ⟨d, hd⟩

/-- Mixed amplitude alone cannot even distinguish the two fixed-axis cells. -/
theorem mixed_current_alias : mixedDensity 0 0 = mixedDensity 3 2 := by decide

/-- This is the precise limitation of the previous controlled-tower structure. -/
theorem old_controlled_tower_stationary {α : Type}
    (T : CardinalWorldsPostulateLaw.ControlledTower α) (n : Nat) :
    T.level n = T.level 0 := by
  induction n with
  | zero => rfl
  | succ n ih => exact (T.ledger n).trans ((T.controller n).symm.trans ih)

/-- A world at resolution k is an actual finite residue. Refining resolution
preserves its lower window, while allowing new trits above that window. -/
structure WindowTower where
  level : Nat → Nat
  bounded : ∀ k, level k < 3^k
  coherent : ∀ k s, k ≤ s → level s % 3^k = level k

/-- A finite physical world, embedded into all resolutions. -/
def naturalTower (R : Nat) : WindowTower where
  level k := R % 3^k
  bounded k := Nat.mod_lt _ (Nat.pow_pos (by decide))
  coherent k s h := Nat.mod_mod_of_dvd R (Nat.pow_dvd_pow 3 h)

/-- The existing Omega frozen-window law constructs a tower in the new space. -/
def omegaTower (core : Nat) : WindowTower where
  level k := (omegaCutWord (k-1) 1 * core) % 3^k
  bounded k := Nat.mod_lt _ (Nat.pow_pos (by decide))
  coherent k s h := by
    rw [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 3 h)]
    exact GSTTailFFourthDimension.omega_tower_word_mod_chain core k (s-1) (by omega)

/-- The new space contains changing levels, witnessed by the repository's tower. -/
theorem omega_tower_nonstationary :
    (omegaTower 1).level 1 = 1 ∧ (omegaTower 1).level 2 = 7 ∧
      (omegaTower 1).level 3 = 16 := by decide

/-- Build a finite window from an arbitrary stream of legal trits. -/
def streamPrefix (a : Nat → Fin 3) : Nat → Nat
  | 0 => 0
  | n+1 => streamPrefix a n + 3^n * (a n).val

theorem stream_prefix_bound (a : Nat → Fin 3) (n : Nat) :
    streamPrefix a n < 3^n := by
  induction n with
  | zero => simp [streamPrefix]
  | succ n ih =>
    have ha := (a n).isLt
    have hp : 0 < (3:Nat)^n := Nat.pow_pos (by decide)
    simp only [streamPrefix, Nat.pow_succ]
    nlinarith

theorem stream_prefix_coherent (a : Nat → Fin 3) (k s : Nat) (h : k ≤ s) :
    streamPrefix a s % 3^k = streamPrefix a k := by
  induction s with
  | zero =>
    have hk : k = 0 := by omega
    subst k
    simp [streamPrefix]
  | succ s ih =>
    by_cases hks : k ≤ s
    · have hz : (3^s * (a s).val) % 3^k = 0 := by
        apply Nat.mod_eq_zero_of_dvd
        exact dvd_mul_of_dvd_left (Nat.pow_dvd_pow 3 hks) _
      rw [streamPrefix, Nat.add_mod, hz, Nat.add_zero, ih hks]
      exact Nat.mod_eq_of_lt (stream_prefix_bound a k)
    · have hk : k = s+1 := by omega
      subst k
      exact Nat.mod_eq_of_lt (stream_prefix_bound a (s+1))

def streamTower (a : Nat → Fin 3) : WindowTower where
  level := streamPrefix a
  bounded := stream_prefix_bound a
  coherent := stream_prefix_coherent a

/-- Distinct infinite innovation streams give distinct level families. -/
theorem stream_tower_injective : Function.Injective (fun a => (streamTower a).level) := by
  intro a b h
  funext n
  apply Fin.ext
  have h0 : streamPrefix a n = streamPrefix b n := congrFun h n
  have h1 : streamPrefix a (n+1) = streamPrefix b (n+1) := congrFun h (n+1)
  simp only [streamPrefix] at h1
  rw [h0] at h1
  have hm := Nat.add_left_cancel h1
  exact Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by decide)) hm

/-- Every finite world has all three distinct legal next-resolution branches. -/
theorem three_way_extension (k r : Nat) (hr : r < 3^k) :
    (∀ d : Fin 3, r + 3^k * d.val < 3^(k+1) ∧
      (r + 3^k * d.val) % 3^k = r) ∧
    Function.Injective (fun d : Fin 3 => r + 3^k * d.val) := by
  constructor
  · intro d
    constructor
    · have hd := d.isLt
      have hp : 0 < (3:Nat)^k := Nat.pow_pos (by decide)
      rw [Nat.pow_succ]
      nlinarith
    · simp [Nat.add_mod, Nat.mod_eq_of_lt hr]
  · intro a b h
    apply Fin.ext
    exact Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by decide)) (Nat.add_left_cancel h)

/-- Exact finite locality of both coordinates of a GST cell. -/
theorem cell_coordinates_local (R S p : Nat)
    (h : R % 3^(p+1) = S % 3^(p+1)) :
    carry4 R p = carry4 S p ∧ digit3 R p = digit3 S p := by
  have hlow : R % 3^p = S % 3^p := by
    have hdvd : 3^p ∣ 3^(p+1) := Nat.pow_dvd_pow 3 (by omega)
    rw [← Nat.mod_mod_of_dvd R hdvd, h, Nat.mod_mod_of_dvd S hdvd]
  refine ⟨?_, ?_⟩
  · simp only [carry4, hlow]
  · exact GSTFourPowerDirectResidue.digit3_eq_of_mod_next R S p h

/-- The entire infinite horizontal orbit below a fixed height is determined
by one finite tower level. The precision requirement does not grow with t. -/
theorem finite_realization (X : WindowTower) (K t p : Nat) (hp : p+1 ≤ K) :
    carry4 (4^t * X.level (p+1)) p = carry4 (4^t * X.level K) p ∧
    digit3 (4^t * X.level (p+1)) p = digit3 (4^t * X.level K) p := by
  apply cell_coordinates_local
  have hs := X.coherent (p+1) K hp
  have hl := Nat.mod_eq_of_lt (X.bounded (p+1))
  calc
    (4^t * X.level (p+1)) % 3^(p+1) =
        (4^t % 3^(p+1) * (X.level (p+1) % 3^(p+1))) % 3^(p+1) :=
      Nat.mul_mod _ _ _
    _ = (4^t % 3^(p+1) * (X.level K % 3^(p+1))) % 3^(p+1) := by
      rw [hl, hs]
    _ = (4^t * X.level K) % 3^(p+1) := (Nat.mul_mod _ _ _).symm

def towerCarry (X : WindowTower) (t p : Nat) : Nat :=
  carry4 (4^t * X.level (p+1)) p

def towerDigit (X : WindowTower) (t p : Nat) : Nat :=
  digit3 (4^t * X.level (p+1)) p

def towerCurrent (X : WindowTower) (t p : Nat) : Int × Int :=
  dualCurrent (towerCarry X t p) (towerDigit X t p)

theorem tower_carry_bound (X : WindowTower) (t p : Nat) : towerCarry X t p < 4 :=
  (GSTWaveCohomology.cellOf (4^t * X.level (p+1)) p).hcarry

theorem tower_digit_bound (X : WindowTower) (t p : Nat) : towerDigit X t p < 3 :=
  (GSTWaveCohomology.cellOf (4^t * X.level (p+1)) p).hdigit

/-- Both graph edge laws survive on the coherent infinite tower. -/
theorem tower_edge_laws (X : WindowTower) (t p : Nat) :
    outDigit (towerCarry X t p) (towerDigit X t p) = towerDigit X (t+1) p ∧
    nextCarry (towerCarry X t p) (towerDigit X t p) = towerCarry X t (p+1) := by
  constructor
  · unfold towerCarry towerDigit
    rw [show (4:Nat)^(t+1) * X.level (p+1) = 4 * (4^t * X.level (p+1)) by
      rw [Nat.pow_succ]; ring]
    exact (digit3_mul_four_exact _ p).symm
  · have h := finite_realization X (p+2) t p (by omega)
    unfold towerCarry towerDigit
    rw [h.1, h.2]
    exact (carry4_forward_exact (4^t * X.level (p+2)) p).symm

/-- New trit = the exact next-resolution innovation; this reconstructs levels. -/
theorem level_reconstruction (X : WindowTower) (p : Nat) :
    X.level (p+1) = X.level p + 3^p * towerDigit X 0 p := by
  have h := GSTClimbInfiniteFamily.mod_slice_up (X.level (p+1)) p
  rw [Nat.mod_eq_of_lt (X.bounded (p+1)), X.coherent p (p+1) (by omega)] at h
  simpa [towerDigit] using h

/-- Every level can be reconstructed from its wave-current trace, without
assuming any whole-number realization of the infinite tower. -/
theorem current_trace_reconstructs (X Y : WindowTower) (K : Nat)
    (h : ∀ p, p < K → towerCurrent X 0 p = towerCurrent Y 0 p) :
    X.level K = Y.level K := by
  induction K with
  | zero =>
    have hx := X.bounded 0
    have hy := Y.bounded 0
    norm_num at hx hy
    omega
  | succ K ih =>
    have hprev := ih (fun p hp => h p (by omega))
    have hd := (dual_current_separation _ _ _ _
      (tower_carry_bound X 0 K) (tower_digit_bound X 0 K)
      (tower_carry_bound Y 0 K) (tower_digit_bound Y 0 K) (h K (by omega))).2
    rw [level_reconstruction X K, level_reconstruction Y K, hprev, hd]

/-- Equality of finite worlds is exactly equality of their complete two-current
observations below that resolution, at every horizontal time. -/
theorem finite_observation_equivalence (X Y : WindowTower) (K : Nat) :
    X.level K = Y.level K ↔
      ∀ t p, p < K → towerCurrent X t p = towerCurrent Y t p := by
  constructor
  · intro h t p hp
    have hx := finite_realization X K t p (by omega)
    have hy := finite_realization Y K t p (by omega)
    unfold towerCurrent towerCarry towerDigit
    rw [hx.1, hx.2, hy.1, hy.2, h]
  · intro h
    exact current_trace_reconstructs X Y K (h 0)

/-- Arbitrary innovation streams remain distinguishable by wave observations. -/
theorem wave_stream_injective :
    Function.Injective (fun a => towerCurrent (streamTower a) 0) := by
  intro a b h
  apply stream_tower_injective
  funext K
  exact current_trace_reconstructs _ _ K (fun p _ => congrFun h p)

/-- Every observable depth-K signature has exactly one finite representative.
There are exactly 3^K possible representatives, each physically realized. -/
theorem unique_finite_signature (X : WindowTower) (K : Nat) :
    ∃! r : Fin (3^K), ∀ p, p < K →
      towerCurrent (naturalTower r.val) 0 p = towerCurrent X 0 p := by
  refine ⟨⟨X.level K, X.bounded K⟩, ?_, ?_⟩
  · have he : (naturalTower (X.level K)).level K = X.level K :=
      Nat.mod_eq_of_lt (X.bounded K)
    exact (finite_observation_equivalence _ _ K).mp he 0
  · intro r hr
    apply Fin.ext
    have he := current_trace_reconstructs (naturalTower r.val) X K hr
    change r.val % 3^K = X.level K at he
    simpa [Nat.mod_eq_of_lt r.isLt] using he

/-- Read the innovation stream back from a coherent tower. -/
def innovationStream (X : WindowTower) (p : Nat) : Fin 3 :=
  ⟨towerDigit X 0 p, tower_digit_bound X 0 p⟩

theorem innovation_reconstructs (X : WindowTower) (K : Nat) :
    streamPrefix (innovationStream X) K = X.level K := by
  induction K with
  | zero =>
    have h := X.bounded 0
    norm_num at h
    simpa [streamPrefix] using h.symm
  | succ K ih =>
    simp only [streamPrefix, innovationStream, ih]
    exact (level_reconstruction X K).symm

/-- Complete classification: every coherent tower has exactly one innovation
stream. This supplies both directions, not just examples of towers. -/
theorem unique_innovation_presentation (X : WindowTower) :
    ∃! a : Nat → Fin 3, (streamTower a).level = X.level := by
  refine ⟨innovationStream X, funext (innovation_reconstructs X), ?_⟩
  intro a ha
  apply stream_tower_injective
  exact ha.trans (funext (innovation_reconstructs X)).symm

/-- The innovation inserted at a level is exactly the trit later observed there. -/
theorem stream_digit_exact (a : Nat → Fin 3) (p : Nat) :
    towerDigit (streamTower a) 0 p = (a p).val := by
  have h := level_reconstruction (streamTower a) p
  change streamPrefix a (p+1) = streamPrefix a p +
    3^p * towerDigit (streamTower a) 0 p at h
  rw [streamPrefix] at h
  exact (Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by decide))
    (Nat.add_left_cancel h)).symm

/-- Controlled infinity is not a countable catalogue: any proposed natural-
indexed list of coherent worlds misses an explicitly constructed diagonal world. -/
theorem no_countable_catalogue (worlds : Nat → WindowTower) :
    ∃ X : WindowTower, ∀ n : Nat, X.level ≠ (worlds n).level := by
  let a : Nat → Fin 3 := fun n =>
    ⟨(towerDigit (worlds n) 0 n + 1) % 3, Nat.mod_lt _ (by decide)⟩
  refine ⟨streamTower a, ?_⟩
  intro n he
  have hl := congrFun he (n+1)
  have hd : towerDigit (streamTower a) 0 n = towerDigit (worlds n) 0 n := by
    unfold towerDigit
    rw [hl]
  rw [stream_digit_exact] at hd
  change (towerDigit (worlds n) 0 n + 1) % 3 = towerDigit (worlds n) 0 n at hd
  have hb := tower_digit_bound (worlds n) 0 n
  omega

/-- The all-two world is an explicit infinite inhabitant. -/
def allTwoTower : WindowTower := streamTower (fun _ => (2 : Fin 3))

theorem all_two_exact (K : Nat) : allTwoTower.level K + 1 = 3^K := by
  induction K with
  | zero => rfl
  | succ K ih =>
    change streamPrefix (fun _ => (2 : Fin 3)) (K+1) + 1 = _
    simp only [streamPrefix, Nat.pow_succ]
    change streamPrefix (fun _ => (2 : Fin 3)) K + 1 = 3^K at ih
    omega

private theorem depth_dominates (R : Nat) : R + 1 < 3^(R+2) := by
  induction R with
  | zero => decide
  | succ R ih =>
    have hp : 3^(R+1+2) = 3^(R+2) * 3 := by
      rw [show R+1+2 = (R+2)+1 by omega, Nat.pow_succ]
    rw [hp]
    omega

/-- This tower has no finite natural energy representing all of its windows. -/
theorem all_two_not_natural (R : Nat) :
    allTwoTower.level ≠ (naturalTower R).level := by
  intro h
  have he := congrFun h (R+2)
  have hc := all_two_exact (R+2)
  have hb : R % 3^(R+2) ≤ R := Nat.mod_le _ _
  have hg := depth_dominates R
  change allTwoTower.level (R+2) = R % 3^(R+2) at he
  omega

/-- Every GST finite rectangle law extends to every coherent tower. -/
theorem tower_rectangle_gauss (X : WindowTower) (N K : Nat) :
    (∑ p ∈ Finset.range K, (3:Int)^p * ∑ t ∈ Finset.range N,
      mixedDensity (towerCarry X t p) (towerDigit X t p)) =
    (∑ p ∈ Finset.range K, (3:Int)^p *
      (infoPotential (towerDigit X N p) - infoPotential (towerDigit X 0 p))) +
    7 * ((∑ t ∈ Finset.range N, carryPotential (towerCarry X t 0)) -
      (3:Int)^K * ∑ t ∈ Finset.range N, carryPotential (towerCarry X t K)) +
    56 * ∑ p ∈ Finset.range K, (3:Int)^p * ∑ t ∈ Finset.range N,
      surviveI (towerCarry X t p) (towerDigit X t p) := by
  apply mixed_rectangle_emergence
  intro t p _ _
  exact ⟨tower_carry_bound X t p, tower_digit_bound X t p,
    (tower_edge_laws X t p).1, (tower_edge_laws X t p).2⟩

/-- The existing no-erasure theorem now holds on every coherent tower,
including those with no finite natural-number representative. -/
theorem tower_no_erasure (X : WindowTower) (N q : Nat) (hN : 1 ≤ N)
    (h : GSTU2DEventTransport.HappyCell (towerCarry X 0 q) (towerDigit X 0 q)) :
    0 < weightedOntPrefix (towerCarry X) (towerDigit X) N (q+1) := by
  apply weightedOntPrefix_positive_of_top_leading_happy
  · exact hN
  · intro t p _ _
    exact tower_carry_bound X t p
  · intro t p _ _
    exact tower_digit_bound X t p
  · exact h

#print axioms dual_current_separation
#print axioms stream_tower_injective
#print axioms finite_observation_equivalence
#print axioms wave_stream_injective
#print axioms unique_finite_signature
#print axioms unique_innovation_presentation
#print axioms no_countable_catalogue
#print axioms all_two_not_natural
#print axioms tower_rectangle_gauss
#print axioms tower_no_erasure


/-! ## Completed spacetime cochains and their exact differential -/
open GSTWorldCosmology

def cosmicDeltaCarry (f : CompletedCosmos) : CompletedCosmos :=
  fun c => f (c.1+1,c.2) - f c

def cosmicDeltaDigit (f : CompletedCosmos) : CompletedCosmos :=
  fun c => f (c.1,c.2+1) - f c

theorem cosmic_differentials_commute (f : CompletedCosmos) :
    cosmicDeltaCarry (cosmicDeltaDigit f) =
      cosmicDeltaDigit (cosmicDeltaCarry f) := by
  funext c
  simp only [cosmicDeltaCarry, cosmicDeltaDigit]
  ring

def cosmicD0 (f : CompletedCosmos) : CompletedCosmos × CompletedCosmos :=
  (cosmicDeltaCarry f, cosmicDeltaDigit f)

def cosmicD1 (w : CompletedCosmos × CompletedCosmos) : CompletedCosmos :=
  cosmicDeltaCarry w.2 - cosmicDeltaDigit w.1

/-- No upper time or height is used in the completed cochain complex. -/
theorem cosmicD1_D0 (f : CompletedCosmos) : cosmicD1 (cosmicD0 f) = 0 := by
  unfold cosmicD1 cosmicD0
  rw [cosmic_differentials_commute, sub_self]

/-- A finite differential reads the next larger window, so no artificial
boundary value is silently inserted. -/
def windowDeltaCarry (A B : ℕ) (f : WorldCoef (A+1) (B+1)) : WorldCoef A B :=
  fun c => f (⟨c.1.val+1, by omega⟩,⟨c.2.val, by omega⟩) -
    f (⟨c.1.val, by omega⟩,⟨c.2.val, by omega⟩)

def windowDeltaDigit (A B : ℕ) (f : WorldCoef (A+1) (B+1)) : WorldCoef A B :=
  fun c => f (⟨c.1.val, by omega⟩,⟨c.2.val+1, by omega⟩) -
    f (⟨c.1.val, by omega⟩,⟨c.2.val, by omega⟩)

@[simp] theorem observe_deltaCarry (A B : ℕ) (f : CompletedCosmos) :
    observe A B (cosmicDeltaCarry f) =
      windowDeltaCarry A B (observe (A+1) (B+1) f) := rfl

@[simp] theorem observe_deltaDigit (A B : ℕ) (f : CompletedCosmos) :
    observe A B (cosmicDeltaDigit f) =
      windowDeltaDigit A B (observe (A+1) (B+1) f) := rfl

/-- The existing physical current is an actual completed spacetime field. -/
def completedTowerCurrent (X : WindowTower) : CompletedCosmos :=
  fun c => (towerCurrent X c.1 c.2).1

def completedTowerDualCurrent (X : WindowTower) : CompletedCosmos :=
  fun c => (towerCurrent X c.1 c.2).2

theorem tower_completed_currents_faithful {X Y : WindowTower}
    (h : completedTowerCurrent X = completedTowerCurrent Y)
    (hdual : completedTowerDualCurrent X = completedTowerDualCurrent Y) :
    X.level = Y.level := by
  funext K
  apply current_trace_reconstructs X Y K
  intro p hp
  apply Prod.ext
  · exact congrFun h (0,p)
  · exact congrFun hdual (0,p)


/-! ## Genuine completed and window cohomology quotients -/
def cosmicD0Linear : CompletedCosmos →ₗ[ℤ] (CompletedCosmos × CompletedCosmos) where
  toFun := cosmicD0
  map_add' := by
    intro f g
    apply Prod.ext <;> funext c <;>
      simp [cosmicD0, cosmicDeltaCarry, cosmicDeltaDigit] <;> ring
  map_smul' := by
    intro z f; apply Prod.ext <;> funext c <;>
      simp [cosmicD0, cosmicDeltaCarry, cosmicDeltaDigit, mul_sub]

def cosmicD1Linear : (CompletedCosmos × CompletedCosmos) →ₗ[ℤ] CompletedCosmos where
  toFun := cosmicD1
  map_add' := by
    intro f g
    funext c
    simp [cosmicD1, cosmicDeltaCarry, cosmicDeltaDigit] <;> ring
  map_smul' := by
    intro z f; funext c
    simp [cosmicD1, cosmicDeltaCarry, cosmicDeltaDigit, mul_sub]

def cosmicCoboundary : CompletedCosmos →ₗ[ℤ] LinearMap.ker cosmicD1Linear :=
  cosmicD0Linear.codRestrict _ (fun f => cosmicD1_D0 f)

abbrev CosmicH1 := (LinearMap.ker cosmicD1Linear) ⧸ LinearMap.range cosmicCoboundary

theorem windowDeltaCarry_add_exact (A B : ℕ)
    (f g : WorldCoef (A+1) (B+1)) :
    windowDeltaCarry A B (f + g) =
      windowDeltaCarry A B f + windowDeltaCarry A B g := by
  funext c
  change (f _ + g _) - (f _ + g _) = (f _ - f _) + (g _ - g _)
  ring

theorem windowDeltaDigit_add_exact (A B : ℕ)
    (f g : WorldCoef (A+1) (B+1)) :
    windowDeltaDigit A B (f + g) =
      windowDeltaDigit A B f + windowDeltaDigit A B g := by
  funext c
  change (f _ + g _) - (f _ + g _) = (f _ - f _) + (g _ - g _)
  ring

theorem windowDeltaCarry_smul_exact (A B : ℕ) (z : ℤ)
    (f : WorldCoef (A+1) (B+1)) :
    windowDeltaCarry A B (z • f) = z • windowDeltaCarry A B f := by
  funext c
  change z * f _ - z * f _ = z * (f _ - f _)
  ring

theorem windowDeltaDigit_smul_exact (A B : ℕ) (z : ℤ)
    (f : WorldCoef (A+1) (B+1)) :
    windowDeltaDigit A B (z • f) = z • windowDeltaDigit A B f := by
  funext c
  change z * f _ - z * f _ = z * (f _ - f _)
  ring

theorem window_differentials_commute_exact (A B : ℕ)
    (f : WorldCoef (A+2) (B+2)) :
    windowDeltaCarry A B (windowDeltaDigit (A+1) (B+1) f) =
      windowDeltaDigit A B (windowDeltaCarry (A+1) (B+1) f) := by
  funext c
  change (f _ - f _) - (f _ - f _) = (f _ - f _) - (f _ - f _)
  ring

def windowD0 (A B : ℕ) : WorldCoef (A+2) (B+2) →ₗ[ℤ]
    (WorldCoef (A+1) (B+1) × WorldCoef (A+1) (B+1)) where
  toFun := fun f => (windowDeltaCarry (A+1) (B+1) f, windowDeltaDigit (A+1) (B+1) f)
  map_add' := by
    intro f g
    apply Prod.ext
    · exact windowDeltaCarry_add_exact (A+1) (B+1) f g
    · exact windowDeltaDigit_add_exact (A+1) (B+1) f g
  map_smul' := by
    intro z f
    apply Prod.ext
    · exact windowDeltaCarry_smul_exact (A+1) (B+1) z f
    · exact windowDeltaDigit_smul_exact (A+1) (B+1) z f

def windowD1 (A B : ℕ) :
    (WorldCoef (A+1) (B+1) × WorldCoef (A+1) (B+1)) →ₗ[ℤ] WorldCoef A B where
  toFun := fun w => windowDeltaCarry A B w.2 - windowDeltaDigit A B w.1
  map_add' := by
    intro f g
    change windowDeltaCarry A B (f.2 + g.2) - windowDeltaDigit A B (f.1 + g.1) =
      (windowDeltaCarry A B f.2 - windowDeltaDigit A B f.1) +
        (windowDeltaCarry A B g.2 - windowDeltaDigit A B g.1)
    rw [windowDeltaCarry_add_exact, windowDeltaDigit_add_exact]
    abel
  map_smul' := by
    intro z f
    change windowDeltaCarry A B (z • f.2) - windowDeltaDigit A B (z • f.1) =
      z • (windowDeltaCarry A B f.2 - windowDeltaDigit A B f.1)
    rw [windowDeltaCarry_smul_exact, windowDeltaDigit_smul_exact]
    exact (smul_sub z _ _).symm

theorem windowD1_D0 (A B : ℕ) (f : WorldCoef (A+2) (B+2)) :
    windowD1 A B (windowD0 A B f)=0 := by
  change windowDeltaCarry A B (windowDeltaDigit (A+1) (B+1) f) -
    windowDeltaDigit A B (windowDeltaCarry (A+1) (B+1) f) = 0
  rw [window_differentials_commute_exact, sub_self]

def windowCoboundary (A B : ℕ) :
    WorldCoef (A+2) (B+2) →ₗ[ℤ] LinearMap.ker (windowD1 A B) :=
  (windowD0 A B).codRestrict _ (windowD1_D0 A B)

abbrev WindowH1 (A B : ℕ) :=
  (LinearMap.ker (windowD1 A B)) ⧸ LinearMap.range (windowCoboundary A B)

def observeClosed (A B : ℕ) :
    LinearMap.ker cosmicD1Linear →ₗ[ℤ] LinearMap.ker (windowD1 A B) where
  toFun := fun w => ⟨(observe (A+1) (B+1) w.val.1, observe (A+1) (B+1) w.val.2), by
    change windowD1 A B _ = 0
    have h := congrArg (observe A B) w.property
    exact h⟩
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

def observeH1 (A B : ℕ) : CosmicH1 →ₗ[ℤ] WindowH1 A B :=
  (LinearMap.range cosmicCoboundary).mapQ
    (LinearMap.range (windowCoboundary A B)) (observeClosed A B) (by
      rintro x ⟨f,rfl⟩
      exact ⟨observe (A+2) (B+2) f, rfl⟩)

def restrictClosed {A B C D : ℕ} (hA : A ≤ C) (hB : B ≤ D) :
    LinearMap.ker (windowD1 C D) →ₗ[ℤ] LinearMap.ker (windowD1 A B) where
  toFun := fun w => ⟨(restrictWindow (by omega) (by omega) w.val.1,
    restrictWindow (by omega) (by omega) w.val.2), by
      have h := congrArg (restrictWindow hA hB) w.property
      exact h⟩
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

def restrictH1 {A B C D : ℕ} (hA : A ≤ C) (hB : B ≤ D) :
    WindowH1 C D →ₗ[ℤ] WindowH1 A B :=
  (LinearMap.range (windowCoboundary C D)).mapQ
    (LinearMap.range (windowCoboundary A B)) (restrictClosed hA hB) (by
      rintro x ⟨f,rfl⟩
      exact ⟨restrictWindow (A:=A+2) (B:=B+2) (by omega) (by omega) f, rfl⟩)

theorem observeH1_natural {A B C D : ℕ} (hA : A ≤ C) (hB : B ≤ D)
    (x : CosmicH1) : restrictH1 hA hB (observeH1 C D x) = observeH1 A B x := by
  refine Quotient.inductionOn x ?_
  intro w
  rfl

theorem restrictH1_trans {A B C D E F : ℕ}
    (hAC : A ≤ C) (hBD : B ≤ D) (hCE : C ≤ E) (hDF : D ≤ F)
    (x : WindowH1 E F) :
    restrictH1 hAC hBD (restrictH1 hCE hDF x) =
      restrictH1 (hAC.trans hCE) (hBD.trans hDF) x := by
  refine Quotient.inductionOn x ?_
  intro w
  rfl

#print axioms windowD1_D0
#print axioms observeH1_natural
#print axioms restrictH1_trans

end GSTCoherentCosmology
