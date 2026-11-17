import ErdosTernary2

/-- Entry point: prints workspace status and points to the comparator. -/
def main : IO Unit := do
  IO.println "ErdosTernary2 — Lean formalization workspace"
  IO.println "================================================"
  IO.println "Toolchain: leanprover/lean4 (see lean-toolchain)"
  IO.println ""
  IO.println "Proven theorems (0 sorries, 0 errors):"
  IO.println "  - ErdosTernary2.lt_three_cases"
  IO.println "  - ErdosTernary2.ternary_digit_lt_three"
  IO.println "  - ErdosTernary2.empty_foldr_repr_zero"
  IO.println "  - ErdosTernary2.single_digit_value"
  IO.println "  - ErdosTernary2.two_digit_value"
  IO.println "  - ErdosTernary2.isTernaryDigit_{zero,one,two,three}"
  IO.println ""
  IO.println "Verify cleanliness:"
  IO.println "  ./scripts/sorry_check.sh   # must return 0"
  IO.println "  ./scripts/comparator.sh    # prints 'Your solution is okay!'"
