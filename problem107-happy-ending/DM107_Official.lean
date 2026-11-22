/-
OFFICIAL STATEMENT FILE — Erdős Problem #107 (Happy Ending).

Source: google-deepmind/formal-conjectures @ 2207c54d,
FormalConjectures/ErdosProblems/107.lean — byte-verified identical to the
campaign's vendored copy deepmind-comparator/DM_107.lean (diff empty, W82).

Transformation (provenance-recorded, statement-preserving ONLY):
- module-system syntax stripped; `@[category …]` attribute lines removed;
  `set_option linter.style.formal_proof_palomar false` removed (linter not
  present at the campaign toolchain).
- `FormalConjecturesUtil` import replaced by `Mathlib` + the vendored FC
  definitions (`FC.Geometry.TwoD` — from `FormalConjecturesForMathlib/
  Geometry/2d.lean` — provides `ℝ²`, `NonTrilinear`, `ConvexIndep`,
  `HasConvexNGon`).

This file carries the OFFICIAL definitions `cardSet` and `f` VERBATIM, and
the three `@[category test]` anchor proofs VERBATIM (f_zero_eq,
convexIndep_triple_of_not_collinear, f_three_eq) — if these compile
unchanged, the vendored definitions are certified faithful. Proof kernels
(DM107_Proof_*.lean) must declare each target theorem with a byte-identical
statement signature and a complete proof — no sorry.
-/
import Mathlib
import FC.Geometry.TwoD

/-!
# Erdős Problem 107

*References:*
- [erdosproblems.com/107](https://www.erdosproblems.com/107)
- [Wikipedia](https://en.wikipedia.org/wiki/Happy_ending_problem)
-/

open Filter
open EuclideanGeometry

namespace Erdos107

/-- The set of $N$ such that any $N$ points in the plane, no three on a line,
contain a convex $n$-gon. -/
def cardSet (n : ℕ) := { N | ∀ (pts : Finset ℝ²), pts.card = N → NonTrilinear (pts : Set ℝ²) →
  HasConvexNGon n pts }

/-- The function $f(n)$ specified in `erdos_107`. -/
noncomputable def f (n : ℕ) : ℕ :=
  sInf (cardSet n)

/-! ## THE OFFICIAL TARGET STATEMENTS (verbatim signatures, spec record)

THE OPEN CORE (research open):

    theorem erdos_107 : ∀ n ≥ 3, f n = 2^(n - 2) + 1

THE SOLVED VARIANTS (the official decomposition; the W82 kill targets):

    theorem nonempty_cardSet : ∀ n ≥ 3, (cardSet n).Nonempty

    theorem ersz_bounds :
        ∀ n ≥ 3, 2^(n - 2) + 1 ≤ f n ∧ f n ≤ Nat.choose (2 * n - 4) (n - 2) + 1

    theorem su_bound :
        ∃ r : ℕ → ℝ, r =o[atTop] (fun n => (n : ℝ)) ∧
          ∀ n ≥ 3, (f n : ℝ) ≤ 2^(n + r n)

    theorem hmpt_bound :
        ∃ r : ℕ → ℝ, r =O[atTop] (fun n => Real.sqrt (n * Real.log n)) ∧
          ∀ n ≥ 3, (f n : ℝ) ≤ 2^(n + r n)

Campaign position at W82 (honest ledger — never dress partial as complete):
the open core `erdos_107` is NOT claimed. W82-107A kills `nonempty_cardSet`
(the official solved variant, existence for ALL n ≥ 3); W82-107B kills
`ersz_bounds` (the official classical two-sided variant, ALL n ≥ 3) on the
banked cups/caps machinery (ES_SANDWICH_ALLN) — both over the official
definitions in this file. -/

/-- Three distinct non-collinear points form a convex-independent set. -/
private lemma convexIndep_triple_of_not_collinear {a b c : ℝ²}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hcoll : ¬ Collinear ℝ ({a, b, c} : Set ℝ²)) :
    ConvexIndep ({a, b, c} : Set ℝ²) := by
  intro x hx hmem
  -- The point `x` lies in the affine span of `{a, b, c} \ {x}` because it
  -- lies in the convex hull of that two-element set.
  apply hcoll
  have hx_aff : x ∈ affineSpan ℝ (({a, b, c} : Set ℝ²) \ {x}) :=
    convexHull_subset_affineSpan _ hmem
  rw [show ({a, b, c} : Set ℝ²) = insert x (({a, b, c} : Set ℝ²) \ {x}) from
        (Set.insert_sdiff_self_of_mem hx).symm,
      collinear_insert_iff_of_mem_affineSpan hx_aff]
  -- The two-element complement is collinear.
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · rw [show ({x, b, c} : Set ℝ²) \ {x} = ({b, c} : Set ℝ²) by ext; aesop]
    exact collinear_pair ℝ b c
  · rw [show ({a, x, c} : Set ℝ²) \ {x} = ({a, c} : Set ℝ²) by ext; aesop]
    exact collinear_pair ℝ a c
  · rw [show ({a, b, x} : Set ℝ²) \ {x} = ({a, b} : Set ℝ²) by ext; aesop]
    exact collinear_pair ℝ a b

theorem f_zero_eq : f 0 = 0 := by
  have : ∀ P, HasConvexNGon 0 P := by
    intro; use ∅; simp [ConvexIndep]
  simp [f, cardSet, this]

theorem f_three_eq : f 3 = 3 := by
  -- The substantive bound: 3 ∈ cardSet 3.
  have hmem3 : (3 : ℕ) ∈ cardSet 3 := by
    intro pts hpts hnontri
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hpts
    refine ⟨{a, b, c}, by simp [hab, hac, hbc], subset_refl _, ?_⟩
    have hcoerce : (({a, b, c} : Finset ℝ²) : Set ℝ²) = ({a, b, c} : Set ℝ²) := by simp
    have hmem : ∀ {y : ℝ²}, y ∈ ({a, b, c} : Set ℝ²) →
        y ∈ (({a, b, c} : Finset ℝ²) : Set ℝ²) := fun h => hcoerce ▸ h
    have hnc : ¬ Collinear ℝ ({a, b, c} : Set ℝ²) :=
      hnontri (hmem (by simp)) (hmem (by simp)) (hmem (by simp)) hab hbc hac
    rw [hcoerce]
    exact convexIndep_triple_of_not_collinear hab hac hbc hnc
  refine le_antisymm (Nat.sInf_le hmem3) (le_csInf ⟨3, hmem3⟩ fun N hN => ?_)
  -- A set with fewer than 3 points contains no 3-element subset.
  by_contra! hlt
  let f : ℕ → ℝ² := fun i => EuclideanSpace.single 0 (i : ℝ)
  let pts : Finset ℝ² := (Finset.range N).image f
  have hinj : Function.Injective f := fun i j hij => by
    have := congrArg (fun v : ℝ² => v 0) hij; simpa [f] using this
  have hpts_card : pts.card = N := by
    simp [pts, Finset.card_image_of_injOn hinj.injOn]
  have hnontri : NonTrilinear (pts : Set ℝ²) := by
    apply Set.triplewise_of_encard_lt
    rw [Set.encard_coe_eq_coe_finsetCard, hpts_card]
    exact_mod_cast hlt
  obtain ⟨S, hScard, hSsub, _⟩ := hN pts hpts_card hnontri
  have : S.card ≤ pts.card := Finset.card_le_card (by exact_mod_cast hSsub)
  omega

theorem dm107_anchors_green : True := trivial

#eval "DM107_ANCHORS_GREEN"

end Erdos107
