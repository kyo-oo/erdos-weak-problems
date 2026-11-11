import Erdos396_Base

/-! # Erdos396_Data — the k=2 exclusion chunks (S038)

Every n ∈ [1, 2480) fails the k=2 divisibility
∏_{i≤2}(n−i) ∣ C(2n,n) — certified in six chunk-decides under the
501-element NO-OOM discipline (480/480/480/480/480/79 elements). For
n ∈ {1, 2} the descending product binomP n 3 = 0 and 0 ∣ C is false
(x % 0 = x ≠ 0), so the uniform chunk predicate covers the whole range.
Engine cross-check: engine396_round2.py, exclusion replay [1,2480) = []. -/

set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

namespace Erdos396Data

/-- Chunk 1: n ∈ [1, 481). -/
theorem c1 :
    (List.range 480).all (fun off =>
      decide (binom (2*(1+off)) (1+off) % binomP (1+off) 3 ≠ 0)) = true := by
  decide

/-- Chunk 2: n ∈ [481, 961). -/
theorem c2 :
    (List.range 480).all (fun off =>
      decide (binom (2*(481+off)) (481+off) % binomP (481+off) 3 ≠ 0)) = true := by
  decide

/-- Chunk 3: n ∈ [961, 1441). -/
theorem c3 :
    (List.range 480).all (fun off =>
      decide (binom (2*(961+off)) (961+off) % binomP (961+off) 3 ≠ 0)) = true := by
  decide

/-- Chunk 4: n ∈ [1441, 1921). -/
theorem c4 :
    (List.range 480).all (fun off =>
      decide (binom (2*(1441+off)) (1441+off) % binomP (1441+off) 3 ≠ 0)) = true := by
  decide

/-- Chunk 5: n ∈ [1921, 2401). -/
theorem c5 :
    (List.range 480).all (fun off =>
      decide (binom (2*(1921+off)) (1921+off) % binomP (1921+off) 3 ≠ 0)) = true := by
  decide

/-- Chunk 6: n ∈ [2401, 2480). -/
theorem c6 :
    (List.range 79).all (fun off =>
      decide (binom (2*(2401+off)) (2401+off) % binomP (2401+off) 3 ≠ 0)) = true := by
  decide

end Erdos396Data
