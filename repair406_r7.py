#!/usr/bin/env python3
"""S085 r7 — THE FIVE-DEFECT REPAIR (the 406 lane's false-green exposure).
Applies the CI-verified defect fixes (run 45102521097, kernel-406b job log)
across all four kernel files. Fails loudly on any missing pattern.
"""
import sys

FILES = {
    'slim':  'problem406-ternary-powers/PiCollapse406.lean',
    'pins':  'problem406-ternary-powers/PiCollapse406Pins.lean',
    'ghost': 'problem406-ternary-powers/GhostExtinction406.lean',
    'tailf': 'problem406-ternary-powers/TailFDecomposition406.lean',
}

# Defect A: dead tactics after rw [hcube] auto-closed the goal (rfl).
A_OLD = "          rw [hcube]\n          simp only [lteCoeff]\n          try ring\n"
A_NEW = "          rw [hcube]\n"

# Defect B: rw [<- Nat.pow_add] pattern miss (parenthesized product, not pow*pow).
B_OLD = ("  have h2 : 3^(w+1) ∣ 3^(2*w+1) * (lteCoeff w)^3 := by\n"
         "    refine ⟨3^w * (lteCoeff w)^3, ?_⟩\n"
         "    rw [← Nat.pow_add]\n"
         "    congr 1\n"
         "    omega\n")
B_NEW = ("  have h2 : 3^(w+1) ∣ 3^(2*w+1) * (lteCoeff w)^3 := by\n"
         "    refine ⟨3^w * (lteCoeff w)^3, ?_⟩\n"
         "    have hpow : 3^((w+1)+w) = 3^(w+1) * 3^w := Nat.pow_add 3 (w+1) w\n"
         "    have hex : (w+1) + w = 2*w+1 := by omega\n"
         "    calc 3^(2*w+1) * (lteCoeff w)^3\n"
         "        = 3^((w+1)+w) * (lteCoeff w)^3 := by rw [hex]\n"
         "      _ = (3^(w+1) * 3^w) * (lteCoeff w)^3 := by rw [hpow]\n"
         "      _ = 3^(w+1) * (3^w * (lteCoeff w)^3) := by ring\n")

# Defect C: obtain <q, rfl> subst trap on a non-variable equality.
C_OLD = ("  obtain ⟨q, rfl⟩ := hsum\n"
         "  rw [Nat.add_assoc, Nat.add_mul_mod_self_left]\n")
C_NEW = ("  obtain ⟨q, hq⟩ := hsum\n"
         "  rw [Nat.add_assoc, hq, Nat.add_mul_mod_self_left]\n")

# Defect D: rw [hcancel] auto-closed the goal; the trailing '; ring' is dead.
D_OLD = "⟨e, by rw [hcancel]; ring⟩"
D_NEW = "⟨e, hcancel.symm⟩"

# Defect E: the rw-[hu] loop trap (hu's RHS contains u; rewriting inside u - u' diverges).
E_OLD = "    calc lteCoeff (k-1) * u = lteCoeff (k-1) * (u' + (u - u')) := by rw [hu]\n"
E_NEW = ("    have hsplit : u' + (u - u') = u := by omega\n"
         "    calc lteCoeff (k-1) * u = lteCoeff (k-1) * (u' + (u - u')) := by rw [hsplit]\n")

DEFFECTS = [('A', A_OLD, A_NEW), ('B', B_OLD, B_NEW), ('C', C_OLD, C_NEW),
            ('D', D_OLD, D_NEW), ('E', E_OLD, E_NEW)]

fail = False
for tag, path in FILES.items():
    txt = open(path, encoding='utf-8').read()
    report = []
    for name, old, new in DEFFECTS:
        n = txt.count(old)
        expected = 1
        if name == 'E' and tag == 'tailf':
            expected = 0  # tailf's collapse proof is independent (no calc-hu site)
        if n != expected:
            print(f"[{tag}] DEFECT {name}: expected {expected} occurrence(s), found {n} — ABORT")
            fail = True
            continue
        if expected == 1:
            txt = txt.replace(old, new, 1)
            report.append(name)
    if not fail:
        open(path, 'w', encoding='utf-8').write(txt)
        print(f"[{tag}] repaired: {', '.join(report)}")

if fail:
    sys.exit(1)
print("ALL REPAIRS APPLIED")
