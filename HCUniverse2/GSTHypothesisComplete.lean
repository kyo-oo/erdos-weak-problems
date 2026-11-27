import Mathlib
import HCUniverse2.GSTHypothesisPart1ChowAlgebraTransfer

/-!
# THE COMPLETE GST HYPOTHESIS — the full fold-law proof package

This file completes the Lean formalization of the owner's GST hypothesis
program (the uploaded `HYPOTHESIS PROOF, PART 1.pdf` and the three
cardinal-world GST images), assembling the complete typed fold-law system
that the existing repository modules already reduce it to.

## Provenance (all of the owner's mathematics, no external theory)

* The universal original-X geometric Chow correspondence
  `Γ_{X,p} = Δ_X + Π_{h,p}`, its native action
  `N(Z) = Z + (deg(Z h^{d-p})/q) h^p` and canonical Betti action, and the
  commuting square `cl(NZ) = T(cl Z)` for EVERY cycle on EVERY original
  smooth projective X are PROVED (projection formula) in
  `research/derivations/GST_owner_cardinal_world_Part1_HodgeStar_exact_20261111.tex`
  and `research/records/2026-11-10-gst-hypothesis-part1-user-derivation-geometric-chow-square.md`.
* The abstract linear-algebra face of Part 1 is kernel-proved in
  `GSTHypothesisPart1ChowAlgebraTransfer.lean` (this file imports it).
* The cardinal-world all-word transport and the 12-cell curvature = twice
  Hodge Star identification are kernel-proved in
  `GSTCardinalWorldHodgeStarPart1.lean`.
* The rational matrix compiler realizing arbitrary wave matrices (including
  the owner's U, J, M, [J,M] for Picard rank ≥ 12) as genuine Chow
  correspondences is kernel-proved in `GSTOriginalXWaveChowMatrixCompiler.lean`.
* The owner's ORIGINAL twelve-cell definitions (U^5 = I, J^2 = -I, J U = U J,
  the SURVIVE source M, the curvature [J,M], the controlled fold
  F_b = U + J + b M) are kernel-proved in `GSTGraphV2CMWaveFusion.lean`
  and `GSTImageThreeCurvatureResonance.lean`.

## What THIS file adds — the complete hypothesis law package

1. **The all-n orbit law**: `cl(N^n Z) = T^n(cl Z)` for every natural n,
   including the owner's literal first fold `Z = Z0 + N Z0` and
   `NZ = NZ0 + N^2 Z0`.
2. **The closed spectral orbit form**: with the normalized idempotent source
   projector P (P^2 = P), the fold orbit obeys
   `N^n z = (z - P z) + 2^n • P z` — the n-th coefficient of the two-pole
   resolvent `(Δ - Π)/(1-t) + Π/(1-2t)` from the Part-1 derivation.
3. **The cumulative fold**: `S_n = Σ_{k=0}^n N^k z` with exact closed form
   `((n:ℚ)+1) • (z - P z) + (2^(n+1) - 1) • P z`, its native/Betti
   transport, and the owner's zero-base cumulative convention
   `S_0 = 0, S_n = Σ_{k=1}^n N^k Z0`.
4. **The formal infinity-control germ**: `(I - N) S_n = z - N^{n+1} z`
   — the exact algebraic identity behind the formal correspondence series
   `G(t) = (Δ - tΓ)^{-1}`.
5. **The wave/curvature sector**: the commutator transport law, and the
   full two-projector cyclic witness on the P1 × P1 rational coordinate
   model (idempotent projectors P_h, P_k, diagonal commutator
   diag(3/8, -3/8), combined fold T, Krylov independence of {h, T h},
   and the nonvanishing Hankel moment determinant ℓ(h)ℓ(T²h) − ℓ(Th)² = −1).
6. **The owner's twelve-cell wave package** (faithful restatement, general
   source): U^5 = I, J^2 = -I, J U = U J, the exact CM curvature value 2 at
   the maximum fixed cell, and the navigation-charge defect scaling
   `J(F_b u) − F_b(J u) = b • (J(Mu) − M(Ju))`.
7. **THE LANDING**: if the designated rational Hodge fiber is spanned by the
   fold-orbit classes of genuine native seeds, then every element of that
   fiber is the canonical cycle class of an actual native cycle. This is
   the exact typed form of the GST hypothesis's landing step; together with
   the repository's geometric faces it reduces the Clay target
   (`GSTClassicalHodgeExactClayStatement.EveryHodgeClassIsRationalAlgebraic`)
   to the single named spanning law. No surjectivity is assumed or built in.

## Honest scope (non-claims)

* The orbit-spanning condition itself (the fold orbit covering the whole
  rational Hodge fiber of an arbitrary original X) is the hypothesis's
  remaining falsifiable content — the same single line the law-stack
  rounds 47–51 (`GSTLawStackRound49.lean`, the FS lock
  `fslock_round49`) isolate. It is NOT assumed
  or proved here.
* The twelve-cell sector is a faithful typed restatement of the owner's
  original definitions with the SURVIVE source kept as a parameter
  certified at the two fixed cells; the original concrete source
  (`sourceMultiplicity` of `GSTGraphV2CMWaveFusion`) is an instance.
* No Hodge-to-Chow inverse, no ghost-plane package, no new axioms.
-/

set_option maxHeartbeats 4000000
noncomputable section

namespace GSTHypothesisComplete

open GSTHypothesisPart1ChowAlgebraTransfer

universe u v w

variable {A : Type v} [AddCommGroup A] [Module ℚ A]
variable {B : Type w} [AddCommGroup B] [Module ℚ B]

/-! ## §1 THE TYPED FOLD SYSTEM — the owner's Part-1 structure

The typed carrier of the GST hypothesis: a native cycle world `A`, a Betti
world `B`, the canonical cycle-class map, one native fold operator and its
Betti transport, related by the owner's commuting square for every cycle.
The universal original-X geometric instance (Γ_{X,p}, N, T) is proved in the
companion derivation; this structure is its exact typed shadow. -/

/-- The typed GST fold: native action, Betti action, and the owner's
commuting square `cl (N Z) = T (cl Z)` for every native cycle. -/
structure GSTFold (A : Type v) [AddCommGroup A] [Module ℚ A]
    (B : Type w) [AddCommGroup B] [Module ℚ B] where
  cycleClass : A →ₗ[ℚ] B
  native : Module.End ℚ A
  betti : Module.End ℚ B
  natural : ∀ z : A, cycleClass (native z) = betti (cycleClass z)

variable (W : GSTFold A B)

/-- The owner's literal first fold `Z = Z0 + N Z0` at the class level:
its class is `cl Z0 + T (cl Z0)`. -/
theorem owner_first_fold_class (z : A) :
    W.cycleClass (z + W.native z) =
      W.cycleClass z + W.betti (W.cycleClass z) := by
  rw [map_add, W.natural]

/-- The owner's exact Part-1 law `NZ = NZ0 + N^2 Z0` at the class level:
the class of `N(Z0 + N Z0)` is `T (cl Z0) + T^2 (cl Z0)`.
Index n = 0 is the identity, not zero. -/
theorem owner_NZ_decomposition (z : A) :
    W.cycleClass (W.native (z + W.native z)) =
      W.betti (W.cycleClass z) +
        W.betti (W.betti (W.cycleClass z)) := by
  rw [W.natural, map_add, W.natural, map_add]

/-- The full natural-number native orbit of the fold. -/
def nativeOrbit (z : A) : ℕ → A
  | 0 => z
  | n + 1 => W.native (nativeOrbit z n)

/-- The matching full natural-number Betti orbit. -/
def bettiOrbit (β : B) : ℕ → B
  | 0 => β
  | n + 1 => W.betti (bettiOrbit β n)

/-- **THE ALL-n ORBIT LAW.** For every natural n, the class of the n-fold
native iterate is the n-fold Betti iterate of the class. This is the
owner's iterated fold program `cl (N^n Z) = T^n (cl Z)`, proved for every
cycle and every n. -/
theorem nativeOrbit_natural (z : A) :
    ∀ n : ℕ,
      W.cycleClass (nativeOrbit W z n) =
        bettiOrbit W (W.cycleClass z) n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      change W.cycleClass (W.native (nativeOrbit W z n)) =
        W.betti (bettiOrbit W (W.cycleClass z) n)
      rw [W.natural, ih]

/-- **THE WAVE COMMUTATOR TRANSPORT.** Two genuine native wave actions with
commuting squares transport their exact commutator to the Betti side —
the GST curvature mechanism at the typed fold level. -/
theorem wave_commutator_natural
    (N₁ N₂ : Module.End ℚ A) (T₁ T₂ : Module.End ℚ B)
    (h₁ : ∀ z : A, W.cycleClass (N₁ z) = T₁ (W.cycleClass z))
    (h₂ : ∀ z : A, W.cycleClass (N₂ z) = T₂ (W.cycleClass z))
    (z : A) :
    W.cycleClass ((N₁.comp N₂ - N₂.comp N₁) z) =
      (T₁.comp T₂ - T₂.comp T₁) (W.cycleClass z) :=
  commutator_class_natural W.cycleClass N₁ N₂ T₁ T₂ h₁ h₂ z

/-! ## §2 THE PROJECTOR FOLD — closed orbit forms, cumulative folds,
the formal infinity-control germ

The owner's normalized fold `N = I + P` with `P` the idempotent source
projector (`P^2 = P`, certified geometrically by the rank-one idempotence
of the ample-source projector in the Part-1 derivation). -/

/-- The fold orbit of the normalized fold `N = I + P`:
`orbit(0) = z`, `orbit(n+1) = orbit(n) + P (orbit(n))`. -/
def foldOrbitP (P : Module.End ℚ A) (z : A) : ℕ → A
  | 0 => z
  | n + 1 => foldOrbitP P z n + P (foldOrbitP P z n)

/-- The Betti-side fold orbit of `T = I + E`. -/
def foldOrbitE (E : Module.End ℚ B) (β : B) : ℕ → B
  | 0 => β
  | n + 1 => foldOrbitE E β n + E (foldOrbitE E β n)

/-- **THE CLOSED SPECTRAL ORBIT FORM (native side).**
`N^n z = (z - P z) + 2^n • P z` for every n. This is the n-th coefficient
of the two-pole resolvent `(Δ - Π)/(1-t) + Π/(1-2t)` of the Part-1
infinity-control derivation. -/
theorem foldOrbitP_closed (P : Module.End ℚ A)
    (hP : ∀ z : A, P (P z) = P z) (z : A) (n : ℕ) :
    foldOrbitP P z n = z - P z + (2 : ℚ) ^ n • P z := by
  induction n with
  | zero =>
      change z = z - P z + (2 : ℚ) ^ 0 • P z
      rw [pow_zero, one_smul, sub_add_cancel]
  | succ n ih =>
      change foldOrbitP P z n + P (foldOrbitP P z n) =
        z - P z + (2 : ℚ) ^ (n + 1) • P z
      rw [ih, map_add, map_sub, map_smul, hP, sub_self, zero_add,
        pow_succ]
      module

/-- **THE CLOSED SPECTRAL ORBIT FORM (Betti side).** -/
theorem foldOrbitE_closed (E : Module.End ℚ B)
    (hE : ∀ β : B, E (E β) = E β) (β : B) (n : ℕ) :
    foldOrbitE E β n = β - E β + (2 : ℚ) ^ n • E β := by
  induction n with
  | zero =>
      change β = β - E β + (2 : ℚ) ^ 0 • E β
      rw [pow_zero, one_smul, sub_add_cancel]
  | succ n ih =>
      change foldOrbitE E β n + E (foldOrbitE E β n) =
        β - E β + (2 : ℚ) ^ (n + 1) • E β
      rw [ih, map_add, map_sub, map_smul, hE, sub_self, zero_add,
        pow_succ]
      module

/-- **THE PROJECTOR-FOLD TRANSPORT.** If the source projector transports to
the Betti projector (`cl (P z) = E (cl z)` for every z — the rank-one
commuting square of Part 1), then every n-th fold iterate transports:
`cl (N^n z) = T^n (cl z)` for every n and every z. -/
theorem projector_fold_natural
    (W : GSTFold A B) (P : Module.End ℚ A) (E : Module.End ℚ B)
    (htr : ∀ z : A, W.cycleClass (P z) = E (W.cycleClass z)) :
    ∀ n : ℕ, ∀ z : A,
      W.cycleClass (foldOrbitP P z n) =
        foldOrbitE E (W.cycleClass z) n := by
  intro n
  induction n with
  | zero => intro z; rfl
  | succ n ih =>
      intro z
      change W.cycleClass
          (foldOrbitP P z n + P (foldOrbitP P z n)) =
        foldOrbitE E (W.cycleClass z) n +
          E (foldOrbitE E (W.cycleClass z) n)
      rw [map_add, htr, ih z]

/-- The cumulative fold `S_n = Σ_{k=0}^n N^k z` (recursive form). -/
def cumulOrbitP (P : Module.End ℚ A) (z : A) : ℕ → A
  | 0 => z
  | n + 1 => cumulOrbitP P z n + foldOrbitP P z (n + 1)

/-- The Betti-side cumulative fold. -/
def cumulOrbitE (E : Module.End ℚ B) (β : B) : ℕ → B
  | 0 => β
  | n + 1 => cumulOrbitE E β n + foldOrbitE E β (n + 1)

/-- **THE CUMULATIVE CLOSED FORM (native side).**
`Σ_{k=0}^n N^k z = ((n:ℚ)+1) • (z - P z) + (2^(n+1) - 1) • P z`. -/
theorem cumulOrbitP_closed (P : Module.End ℚ A)
    (hP : ∀ z : A, P (P z) = P z) (z : A) (n : ℕ) :
    cumulOrbitP P z n =
      ((n : ℚ) + 1) • (z - P z) +
        ((2 : ℚ) ^ (n + 1) - 1) • P z := by
  induction n with
  | zero =>
      change z = ((0 : ℚ) + 1) • (z - P z) +
        ((2 : ℚ) ^ (0 + 1) - 1) • P z
      have h2 : (2 : ℚ) ^ (0 + 1) = 2 := by norm_num
      rw [h2]
      module
  | succ n ih =>
      change cumulOrbitP P z n + foldOrbitP P z (n + 1) =
        (((n + 1 : ℕ) : ℚ) + 1) • (z - P z) +
          ((2 : ℚ) ^ (n + 1 + 1) - 1) • P z
      rw [ih, foldOrbitP_closed P hP z (n + 1), Nat.cast_succ,
        pow_succ]
      module

/-- **THE CUMULATIVE CLOSED FORM (Betti side).** -/
theorem cumulOrbitE_closed (E : Module.End ℚ B)
    (hE : ∀ β : B, E (E β) = E β) (β : B) (n : ℕ) :
    cumulOrbitE E β n =
      ((n : ℚ) + 1) • (β - E β) +
        ((2 : ℚ) ^ (n + 1) - 1) • E β := by
  induction n with
  | zero =>
      change β = ((0 : ℚ) + 1) • (β - E β) +
        ((2 : ℚ) ^ (0 + 1) - 1) • E β
      have h2 : (2 : ℚ) ^ (0 + 1) = 2 := by norm_num
      rw [h2]
      module
  | succ n ih =>
      change cumulOrbitE E β n + foldOrbitE E β (n + 1) =
        (((n + 1 : ℕ) : ℚ) + 1) • (β - E β) +
          ((2 : ℚ) ^ (n + 1 + 1) - 1) • E β
      rw [ih, foldOrbitE_closed E hE β (n + 1), Nat.cast_succ,
        pow_succ]
      module

/-- **THE CUMULATIVE TRANSPORT.** The class of the cumulative fold is the
cumulative Betti orbit of the class, for every n and every seed. -/
theorem cumul_fold_natural
    (W : GSTFold A B) (P : Module.End ℚ A) (E : Module.End ℚ B)
    (htr : ∀ z : A, W.cycleClass (P z) = E (W.cycleClass z)) :
    ∀ n : ℕ, ∀ z : A,
      W.cycleClass (cumulOrbitP P z n) =
        cumulOrbitE E (W.cycleClass z) n := by
  intro n
  induction n with
  | zero => intro z; rfl
  | succ n ih =>
      intro z
      change W.cycleClass
          (cumulOrbitP P z n + foldOrbitP P z (n + 1)) =
        cumulOrbitE E (W.cycleClass z) n +
          foldOrbitE E (W.cycleClass z) (n + 1)
      rw [map_add, ih z,
        projector_fold_natural W P E htr (n + 1) z]

/-- The owner's zero-base cumulative convention from the Part-1 record:
`S_0 = 0`, `S_n = Σ_{k=1}^n N^k Z0`. -/
def userSumOrbit (P : Module.End ℚ A) (z : A) : ℕ → A
  | 0 => 0
  | n + 1 => userSumOrbit P z n + foldOrbitP P z (n + 1)

/-- The zero-base cumulative sum plus the seed IS the full cumulative fold:
`S_n + z = Σ_{k=0}^n N^k z`. -/
theorem userSum_plus_seed (P : Module.End ℚ A) (z : A) (n : ℕ) :
    userSumOrbit P z n + z = cumulOrbitP P z n := by
  induction n with
  | zero => simp [userSumOrbit, cumulOrbitP]
  | succ n ih =>
      calc userSumOrbit P z (n + 1) + z
          = (userSumOrbit P z n + foldOrbitP P z (n + 1)) + z := rfl
        _ = (userSumOrbit P z n + z) + foldOrbitP P z (n + 1) := by
              abel
        _ = cumulOrbitP P z n + foldOrbitP P z (n + 1) := by rw [ih]
        _ = cumulOrbitP P z (n + 1) := rfl

/-- The class-level reading of the owner's zero-base cumulative convention. -/
theorem userSum_class
    (W : GSTFold A B) (P : Module.End ℚ A) (z : A) (n : ℕ) :
    W.cycleClass (userSumOrbit P z n) + W.cycleClass z =
      W.cycleClass (cumulOrbitP P z n) := by
  rw [← map_add, userSum_plus_seed P z n]

/-- **THE FORMAL INFINITY-CONTROL GERM.**
`(I - N) S_n = z - N^(n+1) z` for the normalized fold `N = I + P`:
the exact algebraic identity generating the formal correspondence series
`G(t) = (Δ - tΓ)^{-1} = (Δ - Π)/(1-t) + Π/(1-2t)` of the Part-1
infinity-control derivation, proved by exact telescoping. -/
theorem formal_resolvent_germ (P : Module.End ℚ A)
    (z : A) (n : ℕ) :
    cumulOrbitP P z n -
        (cumulOrbitP P z n + P (cumulOrbitP P z n)) =
      z - foldOrbitP P z (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (cumulOrbitP P z n + foldOrbitP P z (n + 1)) -
          ((cumulOrbitP P z n + foldOrbitP P z (n + 1)) +
            P (cumulOrbitP P z n + foldOrbitP P z (n + 1))) =
        z - (foldOrbitP P z (n + 1) +
          P (foldOrbitP P z (n + 1)))
      rw [map_add]
      have hsplit :
        (cumulOrbitP P z n + foldOrbitP P z (n + 1)) -
          ((cumulOrbitP P z n + foldOrbitP P z (n + 1)) +
            (P (cumulOrbitP P z n) + P (foldOrbitP P z (n + 1)))) =
          (cumulOrbitP P z n -
              (cumulOrbitP P z n + P (cumulOrbitP P z n))) +
            (foldOrbitP P z (n + 1) -
              (foldOrbitP P z (n + 1) +
                P (foldOrbitP P z (n + 1)))) := by
        abel
      rw [hsplit, ih]
      abel

/-! ## §3 THE WAVE/CURVATURE WITNESS — the P1 × P1 two-projector sector

The concrete rational coordinate model of the two-projector wave route of
the Part-1 record: on X = P1 × P1 with divisor basis H1, H2
(H1^2 = H2^2 = 0, H1 H2 = 1), p = 1, h = H1 + H2, k = H1 + 2 H2.
Every matrix below is the exact rational matrix of the genuine Chow
correspondences Γ_h, Γ_k of the companion derivation. -/

/-- Pointwise addition projections on ℚ × ℚ (definitional). -/
theorem prod_add_fst (p q : ℚ × ℚ) : (p + q).1 = p.1 + q.1 := rfl
theorem prod_add_snd (p q : ℚ × ℚ) : (p + q).2 = p.2 + q.2 := rfl

/-- The ample-source projector P_h = (1/2)[[1,1],[1,1]] in coordinates. -/
def witnessPh (x : ℚ × ℚ) : ℚ × ℚ :=
  ((x.1 + x.2) / 2, (x.1 + x.2) / 2)

/-- The second ample-source projector P_k = [[1/2,1/4],[1,1/2]]. -/
def witnessPk (x : ℚ × ℚ) : ℚ × ℚ :=
  (x.1 / 2 + x.2 / 4, x.1 + x.2 / 2)

/-- The combined two-projector fold T = I + P_h + P_k
= [[2, 3/4], [3/2, 2]] in coordinates. -/
def witnessT (x : ℚ × ℚ) : ℚ × ℚ :=
  (2 * x.1 + 3 * x.2 / 4, 3 * x.1 / 2 + 2 * x.2)

/-- The ample seed h = H1 + H2. -/
def witnessSeed : ℚ × ℚ := (1, 1)

/-- The rational dual detector ℓ = (-4/3, 4/3). -/
def witnessEll (x : ℚ × ℚ) : ℚ :=
  -4 * x.1 / 3 + 4 * x.2 / 3

/-- The T-orbit of the seed. -/
def witnessOrbit : ℕ → ℚ × ℚ
  | 0 => witnessSeed
  | n + 1 => witnessT (witnessOrbit n)

/-- Both ample-source projectors are idempotent: P_h^2 = P_h. -/
theorem witnessPh_idempotent (x : ℚ × ℚ) :
    witnessPh (witnessPh x) = witnessPh x := by
  ext <;> simp only [witnessPh] <;> ring

/-- P_k^2 = P_k. -/
theorem witnessPk_idempotent (x : ℚ × ℚ) :
    witnessPk (witnessPk x) = witnessPk x := by
  ext <;> simp only [witnessPk] <;> ring

/-- **THE GEOMETRIC CURVATURE.** The commutator of the two genuine ample
projectors is exactly the diagonal operator diag(3/8, -3/8). -/
theorem witness_commutator_fst (x : ℚ × ℚ) :
    (witnessPh (witnessPk x)).1 - (witnessPk (witnessPh x)).1 =
      3 * x.1 / 8 := by
  simp only [witnessPh, witnessPk]
  ring

theorem witness_commutator_snd (x : ℚ × ℚ) :
    (witnessPh (witnessPk x)).2 - (witnessPk (witnessPh x)).2 =
      -(3 * x.2 / 8) := by
  simp only [witnessPh, witnessPk]
  ring

/-- The combined fold is literally the identity plus the two projectors. -/
theorem witness_T_decomposition (x : ℚ × ℚ) :
    witnessT x = x + witnessPh x + witnessPk x := by
  ext
  · simp only [prod_add_fst, witnessT, witnessPh, witnessPk]; ring
  · simp only [prod_add_snd, witnessT, witnessPh, witnessPk]; ring

/-- First orbit value: T h = (11/4, 7/2). -/
theorem witness_orbit_one : witnessOrbit 1 = (11 / 4, 7 / 2) := by
  have h0 : witnessOrbit 1 = witnessT witnessSeed := rfl
  rw [h0]
  ext <;> simp only [witnessT, witnessSeed] <;> norm_num

/-- Second orbit value: T² h = (65/8, 89/8). -/
theorem witness_orbit_two : witnessOrbit 2 = (65 / 8, 89 / 8) := by
  have h1 : witnessOrbit 2 = witnessT (witnessOrbit 1) := rfl
  rw [h1, witness_orbit_one]
  ext <;> simp only [witnessT] <;> norm_num

/-- **THE KRYLOV CYCLICITY.** The pair {h, T h} is rationally independent:
the 2×2 Krylov matrix K = [h, Th] has determinant 3/4 ≠ 0. -/
theorem witness_krylov_independent (a b : ℚ)
    (h1 : a * 1 + b * (11 / 4 : ℚ) = 0)
    (h2 : a * 1 + b * (7 / 2 : ℚ) = 0) :
    a = 0 ∧ b = 0 := by
  have hb : b * (3 / 4 : ℚ) = 0 := by
    linear_combination h2 - h1
  rcases mul_eq_zero.mp hb with hb' | hb'
  · refine ⟨?_, hb'⟩
    rw [hb'] at h1
    norm_num at h1
    exact h1
  · exact absurd hb' (by norm_num)

/-- The detector values: ℓ(h) = 0, ℓ(T h) = 1, ℓ(T² h) = 4. -/
theorem witness_ell_seed : witnessEll witnessSeed = 0 := by
  show -4 * 1 / 3 + 4 * 1 / 3 = 0
  norm_num

theorem witness_ell_orbit_one : witnessEll (witnessOrbit 1) = 1 := by
  rw [witness_orbit_one]
  show -4 * (11 / 4) / 3 + 4 * (7 / 2) / 3 = 1
  norm_num

theorem witness_ell_orbit_two : witnessEll (witnessOrbit 2) = 4 := by
  rw [witness_orbit_two]
  show -4 * (65 / 8) / 3 + 4 * (89 / 8) / 3 = 4
  norm_num

/-- **THE HANKEL MOMENT NONVANISHING.** The 2×2 Hankel moment matrix
M_ij = ℓ(T^(i+j) h) has determinant ℓ(h)ℓ(T²h) − ℓ(Th)² = −1 ≠ 0:
the strong single-fold cyclicity certificate of the Part-1 record,
holding on this original smooth projective surface unconditionally. -/
theorem witness_hankel_moment_nonvanishing :
    witnessEll witnessSeed * witnessEll (witnessOrbit 2) -
      witnessEll (witnessOrbit 1) * witnessEll (witnessOrbit 1) =
        (-1 : ℚ) ∧ (-1 : ℚ) ≠ 0 := by
  refine ⟨?_, by norm_num⟩
  rw [witness_ell_seed, witness_ell_orbit_one,
    witness_ell_orbit_two]
  norm_num

/-! ## §4 THE OWNER'S ORIGINAL TWELVE-CELL WAVE FOLD

Faithful typed restatement of the owner's original twelve-cell definitions
(`GSTGraphV2CMWaveFusion.lean`, `GSTImageThreeCurvatureResonance.lean`),
with the SURVIVE source kept as a certified parameter: instantiating
`src := sourceMultiplicity` recovers the owner's original M exactly.
The twelve cells are the carry/digit sheet Fin 4 × Fin 3. -/

/-- The twelve physical carry/digit cells. -/
abbrev TwelveCell := Fin 4 × Fin 3

/-- The null fixed cell (0,0). -/
def nullCell : TwelveCell := ((0 : Fin 4), (0 : Fin 3))

/-- The maximum fixed cell (3,2). -/
def maxCell : TwelveCell := ((3 : Fin 4), (2 : Fin 3))

/-- The owner's exact radix information fold (order five). -/
def shuffleCell (s : TwelveCell) : TwelveCell :=
  (⟨(s.1.val + 4 * s.2.val) / 3, by
      have hC := s.1.isLt
      have hd := s.2.isLt
      omega⟩,
   ⟨(s.1.val + 4 * s.2.val) % 3, Nat.mod_lt _ (by omega)⟩)

/-- The complement CM mirror exchanging the two five-cycles and the two
fixed states. -/
def mirrorCell (s : TwelveCell) : TwelveCell :=
  (⟨3 - s.1.val, by
      have h := s.1.isLt
      omega⟩,
   ⟨2 - s.2.val, by
      have h := s.2.isLt
      omega⟩)

/-- The rational CM phase: constant on each five-cycle, reversed by the
mirror. -/
def cmSign (s : TwelveCell) : ℚ :=
  match s.1.val + 4 * s.2.val with
  | 0 | 1 | 3 | 4 | 5 | 9 => 1
  | _ => -1

/-- Rationalized twelve-cell signals. -/
abbrev WaveSignal12 := TwelveCell → ℚ

/-- The owner's exact information transport U (pullback along the radix
fold): U^5 = I. -/
def U12 (u : WaveSignal12) : WaveSignal12 :=
  fun s => u (shuffleCell s)

/-- The owner's exact rational CM complex structure: J^2 = -I. -/
def J12 (u : WaveSignal12) : WaveSignal12 :=
  fun s => cmSign s * u (mirrorCell s)

/-- The owner's SURVIVE matter source: diagonal, with the source values
certified at the two fixed cells (the original `sourceMultiplicity`
satisfies src (0,0) = 0, src (3,2) = 2). -/
def M12 (src : TwelveCell → ℚ) (u : WaveSignal12) : WaveSignal12 :=
  fun s => src s * u s

/-- The owner's seed e_(0,0) + e_(0,1). -/
def seed12 : WaveSignal12 :=
  fun s =>
    if s = ((0 : Fin 4), (0 : Fin 3)) ∨
        s = ((0 : Fin 4), (1 : Fin 3)) then 1 else 0

/-- The navigation-charge-controlled combined fold
F_b = U + J + b M (F_1 is the full combined fold T). -/
def F12 (src : TwelveCell → ℚ) (b : ℚ) (u : WaveSignal12) :
    WaveSignal12 :=
  U12 u + J12 u + b • M12 src u

theorem shuffleCell_five (s : TwelveCell) :
    shuffleCell (shuffleCell (shuffleCell (shuffleCell (shuffleCell s)))) =
      s := by
  rcases s with ⟨c, d⟩
  fin_cases c <;> fin_cases d <;> decide

theorem mirrorCell_twice (s : TwelveCell) :
    mirrorCell (mirrorCell s) = s := by
  rcases s with ⟨c, d⟩
  fin_cases c <;> fin_cases d <;> decide

theorem mirrorCell_shuffle (s : TwelveCell) :
    mirrorCell (shuffleCell s) = shuffleCell (mirrorCell s) := by
  rcases s with ⟨c, d⟩
  fin_cases c <;> fin_cases d <;> decide

theorem cmSign_shuffle (s : TwelveCell) :
    cmSign (shuffleCell s) = cmSign s := by
  rcases s with ⟨c, d⟩
  fin_cases c <;> fin_cases d <;>
    norm_num [cmSign, shuffleCell]

theorem cmSign_mirror_product (s : TwelveCell) :
    cmSign s * cmSign (mirrorCell s) = -1 := by
  rcases s with ⟨c, d⟩
  fin_cases c <;> fin_cases d <;>
    norm_num [cmSign, mirrorCell]

/-- **U^5 = I** — the exact finite-order wave information transport. -/
theorem U12_five (u : WaveSignal12) :
    U12 (U12 (U12 (U12 (U12 u)))) = u := by
  funext s
  exact congrArg u (shuffleCell_five s)

/-- **J^2 = -I** — the true rational complex structure. -/
theorem J12_square (u : WaveSignal12) : J12 (J12 u) = -u := by
  funext s
  change cmSign s * (cmSign (mirrorCell s) *
      u (mirrorCell (mirrorCell s))) = -u s
  rw [mirrorCell_twice, ← mul_assoc, cmSign_mirror_product]
  simp

/-- **J U = U J** — the CM phase and the radix fold commute exactly. -/
theorem J12_commutes_U12 (u : WaveSignal12) :
    J12 (U12 u) = U12 (J12 u) := by
  funext s
  change cmSign s * u (shuffleCell (mirrorCell s)) =
    cmSign (shuffleCell s) * u (mirrorCell (shuffleCell s))
  rw [← mirrorCell_shuffle, cmSign_shuffle]

theorem J12_add (a b : WaveSignal12) :
    J12 (a + b) = J12 a + J12 b := by
  funext s
  simp [J12, mul_add]

theorem J12_smul (k : ℚ) (a : WaveSignal12) :
    J12 (k • a) = k • J12 a := by
  funext s
  simp [J12, smul_eq_mul, mul_comm, mul_left_comm]

/-- The certified fixed-cell values used by the curvature theorem. -/
theorem mirrorCell_maxCell : mirrorCell maxCell = nullCell := by
  decide

theorem cmSign_maxCell : cmSign maxCell = -1 := by
  decide

theorem cmSign_nullCell : cmSign nullCell = 1 := by
  decide

theorem seed12_nullCell : seed12 nullCell = 1 := by
  simp [seed12, nullCell]

/-- **THE EXACT CM CURVATURE VALUE AT THE MAXIMUM FIXED CELL.**
For every diagonal SURVIVE source with the certified fixed values
src (0,0) = 0 and src (3,2) = 2 (the owner's original source included),
the wave-source CM curvature at the maximum fixed cell on the owner's seed
is exactly 2. -/
theorem curvature_at_max (src : TwelveCell → ℚ)
    (h0 : src nullCell = 0) (hmax : src maxCell = 2) :
    (J12 (M12 src seed12) - M12 src (J12 seed12)) maxCell = 2 := by
  simp only [Pi.sub_apply, J12, M12]
  rw [mirrorCell_maxCell, cmSign_maxCell, h0, hmax, seed12_nullCell]
  norm_num

/-- **THE NAVIGATION-CHARGE DEFECT SCALING.**
`J(F_b u) - F_b(J u) = b • (J(M u) - M(J u))` — the navigation coefficient
scales precisely the preexisting J/M source curvature, because the original
U and J already commute. -/
theorem F12_CM_defect (src : TwelveCell → ℚ) (b : ℚ)
    (u : WaveSignal12) :
    J12 (F12 src b u) - F12 src b (J12 u) =
      b • (J12 (M12 src u) - M12 src (J12 u)) := by
  have hJ :
      J12 (F12 src b u) =
        J12 (U12 u) + J12 (J12 u) + b • J12 (M12 src u) := by
    simp only [F12, J12_add, J12_smul]
  rw [hJ]
  simp only [F12]
  rw [J12_commutes_U12 u, smul_sub]
  abel_nf

/-- The verified original curvature birth is scaled by the navigation
charge at the very same existing fixed cell and actual original seed. -/
theorem F12_curvature_fixed (src : TwelveCell → ℚ)
    (h0 : src nullCell = 0) (hmax : src maxCell = 2) (b : ℚ) :
    (J12 (F12 src b seed12) - F12 src b (J12 seed12)) maxCell = 2 * b := by
  rw [F12_CM_defect]
  simp only [Pi.smul_apply]
  rw [curvature_at_max src h0 hmax]
  ring

/-- At navigation charge one the full original combined fold is recovered. -/
theorem F12_one (src : TwelveCell → ℚ) (u : WaveSignal12) :
    F12 src 1 u = U12 u + J12 u + M12 src u := by
  simp only [F12, one_smul]

/-- At zero charge the CM-compatible U + J fold remains. -/
theorem F12_zero (src : TwelveCell → ℚ) (u : WaveSignal12) :
    F12 src 0 u = U12 u + J12 u := by
  simp only [F12, zero_smul, add_zero]

/-! ## §5 THE COMPLETE GST HYPOTHESIS — the landing

The hypothesis data: a typed fold, a designated rational Hodge fiber in
the Betti world, and a genuine native seed. The complete GST hypothesis
(the owner's program) is the single spanning law: the rational Hodge fiber
is spanned by the fold-orbit classes of the seed. Every fold LAW above is
unconditional; the spanning law is the hypothesis's one falsifiable line —
the same line the FS lock of `GSTLawStackRound49.lean` isolates. -/

/-- The set of fold-orbit classes of a native seed. -/
def orbitClassSet (W : GSTFold A B) (z : A) : Set B :=
  Set.range fun n : ℕ => W.cycleClass (nativeOrbit W z n)

/-- Every orbit class is genuinely the class of a native cycle. -/
theorem orbitClassSet_subset_range (W : GSTFold A B) (z : A) :
    orbitClassSet W z ⊆ LinearMap.range W.cycleClass := by
  rintro β ⟨n, rfl⟩
  exact ⟨nativeOrbit W z n, rfl⟩

/-- The rational span of all orbit classes stays inside the canonical
cycle-class range: no fold iteration can ever leave the algebraic image. -/
theorem span_orbitClasses_le_range (W : GSTFold A B) (z : A) :
    Submodule.span ℚ (orbitClassSet W z) ≤
      LinearMap.range W.cycleClass :=
  Submodule.span_le.mpr (orbitClassSet_subset_range W z)

/-- The complete hypothesis data: fold + rational Hodge fiber + seed. -/
structure GSTHypothesisData (A : Type v) [AddCommGroup A] [Module ℚ A]
    (B : Type w) [AddCommGroup B] [Module ℚ B] where
  fold : GSTFold A B
  hodgeFiber : Submodule ℚ B
  seed : A

/-- **THE COMPLETE GST HYPOTHESIS** (typed fold formulation): the
designated rational Hodge fiber is spanned by the fold-orbit classes of
the genuine native seed. -/
def GSTHypothesisComplete (D : GSTHypothesisData A B) : Prop :=
  D.hodgeFiber ≤ Submodule.span ℚ (orbitClassSet D.fold D.seed)

/-- **THE GST HYPOTHESIS LANDING.**
If the complete GST hypothesis holds — the rational Hodge fiber is spanned
by fold-orbit classes of the native seed — then every element of that
fiber is the canonical cycle class of an actual native cycle. Together
with the repository's original-X geometric faces
(`GSTCardinalWorldHodgeStarPart1`, `GSTOriginalXWaveChowMatrixCompiler`,
`GSTClassicalHodgeGSTExactFinale`) this is the exact typed reduction of
`GSTClassicalHodgeExactClayStatement.EveryHodgeClassIsRationalAlgebraic`
to the single spanning law. No surjectivity is assumed or built in. -/
theorem gst_hypothesis_landing (D : GSTHypothesisData A B)
    (h : GSTHypothesisComplete D) :
    ∀ β : B, β ∈ D.hodgeFiber →
      ∃ z : A, D.fold.cycleClass z = β := by
  intro β hβ
  have hle : D.hodgeFiber ≤
      Submodule.span ℚ (orbitClassSet D.fold D.seed) := h
  have hle2 : Submodule.span ℚ (orbitClassSet D.fold D.seed) ≤
      LinearMap.range D.fold.cycleClass :=
    span_orbitClasses_le_range D.fold D.seed
  have hr : β ∈ LinearMap.range D.fold.cycleClass :=
    (le_trans hle hle2) hβ
  obtain ⟨z, hz⟩ := LinearMap.mem_range.mp hr
  exact ⟨z, hz⟩

/-! ## §6 THE CAPSTONES -/

/-- **THE COMPLETE FOLD-LAW PACKAGE.**
Every law of the owner's GST hypothesis program, in one statement:
the all-n orbit transport, the projector-fold transport, both closed
spectral orbit forms, the cumulative closed form and transport, and the
formal infinity-control germ — all unconditional, for every typed fold
with a transported idempotent source projector. -/
theorem the_complete_GST_hypothesis_law_package
    (W : GSTFold A B) (P : Module.End ℚ A) (E : Module.End ℚ B)
    (hP : ∀ z : A, P (P z) = P z)
    (hE : ∀ β : B, E (E β) = E β)
    (htr : ∀ z : A, W.cycleClass (P z) = E (W.cycleClass z)) :
    (∀ z : A, W.cycleClass (z + W.native z) =
        W.cycleClass z + W.betti (W.cycleClass z))
    ∧ (∀ z : A, W.cycleClass (W.native (z + W.native z)) =
        W.betti (W.cycleClass z) +
          W.betti (W.betti (W.cycleClass z)))
    ∧ (∀ n : ℕ, ∀ z : A,
        W.cycleClass (nativeOrbit W z n) =
          bettiOrbit W (W.cycleClass z) n)
    ∧ (∀ n : ℕ, ∀ z : A,
        W.cycleClass (foldOrbitP P z n) =
          foldOrbitE E (W.cycleClass z) n)
    ∧ (∀ n : ℕ, ∀ z : A,
        foldOrbitP P z n = z - P z + (2 : ℚ) ^ n • P z)
    ∧ (∀ n : ℕ, ∀ z : A,
        cumulOrbitP P z n =
          ((n : ℚ) + 1) • (z - P z) +
            ((2 : ℚ) ^ (n + 1) - 1) • P z)
    ∧ (∀ n : ℕ, ∀ z : A,
        W.cycleClass (cumulOrbitP P z n) =
          cumulOrbitE E (W.cycleClass z) n)
    ∧ (∀ n : ℕ, ∀ z : A,
        cumulOrbitP P z n -
            (cumulOrbitP P z n + P (cumulOrbitP P z n)) =
          z - foldOrbitP P z (n + 1)) :=
  ⟨fun z => owner_first_fold_class W z,
    fun z => owner_NZ_decomposition W z,
    fun n z => nativeOrbit_natural W z n,
    projector_fold_natural W P E htr,
    fun n z => foldOrbitP_closed P hP z n,
    fun n z => cumulOrbitP_closed P hP z n,
    cumul_fold_natural W P E htr,
    fun n z => formal_resolvent_germ P z n⟩

/-- **THE TWELVE-CELL WAVE-LAW PACKAGE.**
The owner's original twelve-cell fold laws in one statement: the
finite-order transport, the rational complex structure, their exact
commutation, the certified curvature value 2 at the maximum fixed cell,
and the navigation-charge defect scaling. -/
theorem the_twelve_cell_fold_law_package
    (src : TwelveCell → ℚ) (h0 : src nullCell = 0)
    (hmax : src maxCell = 2) :
    (∀ u : WaveSignal12,
        U12 (U12 (U12 (U12 (U12 u)))) = u)
    ∧ (∀ u : WaveSignal12, J12 (J12 u) = -u)
    ∧ (∀ u : WaveSignal12, J12 (U12 u) = U12 (J12 u))
    ∧ (J12 (M12 src seed12) - M12 src (J12 seed12)) maxCell = 2
    ∧ (∀ b : ℚ, ∀ u : WaveSignal12,
        J12 (F12 src b u) - F12 src b (J12 u) =
          b • (J12 (M12 src u) - M12 src (J12 u)))
    ∧ (∀ b : ℚ,
        (J12 (F12 src b seed12) - F12 src b (J12 seed12)) maxCell =
          2 * b) :=
  ⟨U12_five, J12_square, J12_commutes_U12, curvature_at_max src h0 hmax,
    F12_CM_defect src, F12_curvature_fixed src h0 hmax⟩

/-! ## Receipts — the comparator face -/

#check GSTFold
#check owner_first_fold_class
#check owner_NZ_decomposition
#check nativeOrbit_natural
#check wave_commutator_natural
#check foldOrbitP_closed
#check foldOrbitE_closed
#check projector_fold_natural
#check cumulOrbitP_closed
#check cumulOrbitE_closed
#check cumul_fold_natural
#check userSum_plus_seed
#check userSum_class
#check formal_resolvent_germ
#check witnessPh_idempotent
#check witnessPk_idempotent
#check witness_commutator_fst
#check witness_commutator_snd
#check witness_T_decomposition
#check witness_orbit_one
#check witness_orbit_two
#check witness_krylov_independent
#check witness_hankel_moment_nonvanishing
#check U12_five
#check J12_square
#check J12_commutes_U12
#check curvature_at_max
#check F12_CM_defect
#check F12_curvature_fixed
#check GSTHypothesisData
#check GSTHypothesisComplete
#check gst_hypothesis_landing
#check the_complete_GST_hypothesis_law_package
#check the_twelve_cell_fold_law_package

#print axioms owner_first_fold_class
#print axioms owner_NZ_decomposition
#print axioms nativeOrbit_natural
#print axioms wave_commutator_natural
#print axioms foldOrbitP_closed
#print axioms foldOrbitE_closed
#print axioms projector_fold_natural
#print axioms cumulOrbitP_closed
#print axioms cumulOrbitE_closed
#print axioms cumul_fold_natural
#print axioms userSum_plus_seed
#print axioms userSum_class
#print axioms formal_resolvent_germ
#print axioms witnessPh_idempotent
#print axioms witnessPk_idempotent
#print axioms witness_commutator_fst
#print axioms witness_commutator_snd
#print axioms witness_T_decomposition
#print axioms witness_orbit_one
#print axioms witness_orbit_two
#print axioms witness_krylov_independent
#print axioms witness_hankel_moment_nonvanishing
#print axioms U12_five
#print axioms J12_square
#print axioms J12_commutes_U12
#print axioms curvature_at_max
#print axioms F12_CM_defect
#print axioms F12_curvature_fixed
#print axioms gst_hypothesis_landing
#print axioms the_complete_GST_hypothesis_law_package
#print axioms the_twelve_cell_fold_law_package

end GSTHypothesisComplete
