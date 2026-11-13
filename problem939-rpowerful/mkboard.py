import io

AND = "\u2227"      # wedge
LE  = "\u2264"      # <=
DVD = "\u2223"      # divides
NE  = "\u2260"      # !=
ARR = "\u2192"      # ->
FOR = "\u2200"      # forall
LAN = "\u27e8"      # left angle
RAN = "\u27e9"      # right angle
DASH = "\u2014"     # em dash
IN = "\u2208"       # element
GE = "\u2265"       # >=

# read main file, extract the census statement
with io.open('Erdos939.lean', 'r', encoding='utf-8') as f:
    main = f.read()
i0 = main.index('theorem census_rows :')
i1 = main.index(':= by decide', i0)
census = main[i0 + len('theorem census_rows :'):i1]
# dedent by 4 spaces
census_lines = [l[4:] if l.startswith('    ') else l for l in census.split('\n')]
census_stmt = '\n'.join(census_lines).rstrip()

T = []
T.append('/-! ## ' + chr(167) + '8 THE ARSENAL BRIDGE + the master board. -/')
T.append('')
T.append('/-- THE ARSENAL BRIDGE (five conjuncts, one Arsenal lemma each, at #939-')
T.append('native anchor numbers ' + DASH + ' the witness cube base 919, the witness prime 271,')
T.append('the witness value 776151559 = 919^3 with the witness prime 73, and the')
T.append('census member 625 = 5^4 under the ternary scaling): erdosternary2\'s digit')
T.append('law on 919 % 3, HC-PROOF\'s difference-of-squares on 271, the mod-mod-mul')
T.append('law on 776151559 = 919^3 with 73, the carry bound at position 1, and')
T.append('CardinalWorldsV2\'s ternary scaling law at (4, 625). -/')
T.append('theorem e939_arsenal_bridge :')
T.append('    ErdosTernary2.isTernaryDigit (919 % 3) ' + AND)
T.append('    (271 ^ 2 - 1 = (271 - 1) * (271 + 1)) ' + AND)
T.append('    (776151559 % (73 * 2)) % 73 = 776151559 % 73 ' + AND)
T.append('    carryAtPos 919 1 < 4 ' + AND)
T.append('    v2r (3 ^ 4 * 625) = v2r 625 :=')
T.append('  ' + LAN + 'by decide, sq_sub_one 271 (by decide),')
T.append('    mod_mod_mul 776151559 73 2 (by decide),')
T.append('    carryAtPos_bound 919 1, CardinalWorldsV2.v2r_ternary_scaling 4 625' + RAN)
T.append('')
T.append('/-- THE E939 KERNEL MASTER BOARD (11 conjuncts, full statements,')
T.append('unconditional, flat anonymous constructor): the census rows + the')
T.append('beyond-FLT row + the r = 2 witness + both r = 3 Nitaj witnesses + the')
T.append('class residues + the T-case kills + the hunt bound + the bounded')
T.append('no-solution master + the T-case decomposition + the arsenal bridge. -/')
T.append('theorem e939_board :')
T.append('    ' + census_stmt + ' ' + AND)
T.append('    (rpow 4 32 = true ' + AND + ' ' + FOR + ' m < 4, m ^ 4 ' + NE + ' 32) ' + AND)
T.append('    (rpow 2 1 = true ' + AND + ' rpow 2 8 = true ' + AND + ' rpow 2 9 = true ' + AND)
T.append('      Nat.gcd 1 8 = 1 ' + AND + ' 1 + 8 = 9) ' + AND)
T.append('    (rpow 3 (271 ^ 3) = true ' + AND)
T.append('      rpow 3 (2 ^ 3 * 3 ^ 5 * 73 ^ 3) = true ' + AND)
T.append('      rpow 3 (919 ^ 3) = true ' + AND)
T.append('      Nat.gcd (271 ^ 3) (2 ^ 3 * 3 ^ 5 * 73 ^ 3) = 1 ' + AND)
T.append('      271 ^ 3 + 2 ^ 3 * 3 ^ 5 * 73 ^ 3 = 919 ^ 3) ' + AND)
T.append('    (rpow 3 (3 ^ 4 * 29 ^ 3 * 89 ^ 3) = true ' + AND)
T.append('      rpow 3 (7 ^ 3 * 11 ^ 3 * 167 ^ 3) = true ' + AND)
T.append('      rpow 3 (2 ^ 7 * 5 ^ 4 * 353 ^ 3) = true ' + AND)
T.append('      Nat.gcd (3 ^ 4 * 29 ^ 3 * 89 ^ 3) (7 ^ 3 * 11 ^ 3 * 167 ^ 3) = 1 ' + AND)
T.append('      3 ^ 4 * 29 ^ 3 * 89 ^ 3 + 7 ^ 3 * 11 ^ 3 * 167 ^ 3')
T.append('        = 2 ^ 7 * 5 ^ 4 * 353 ^ 3) ' + AND)
T.append('    ((e16.all (fun z => z % 16 == 0)) = true ' + AND)
T.append('      (odd9.all (fun z => z % 2 == 1)) = true) ' + AND)
T.append('    ((odd9.all (fun x => odd9.all (fun y => !(e16.any (fun z => z == x + y))))) = true ' + AND)
T.append('      (e16.all (fun x => odd9.all (fun y => !(odd9.any (fun z => z == x + y))))) = true ' + AND)
T.append('      (odd9.all (fun x => e16.all (fun y => !(odd9.any (fun z => z == x + y))))) = true) ' + AND)
T.append('    (5623 ^ 4 ' + LE + ' 10 ^ 15 ' + AND + ' 10 ^ 15 < 5624 ^ 4) ' + AND)
T.append('    (' + FOR + ' a < 1500, ' + FOR + ' b < 1500, rpow 4 a = true ' + ARR + ' rpow 4 b = true ' + ARR)
T.append('      Nat.gcd a b = 1 ' + ARR + ' rpow 4 (a + b) = false) ' + AND)
T.append('    (' + FOR + ' a b : Nat, rpow 4 a = true ' + ARR + ' rpow 4 b = true ' + ARR)
T.append('      rpow 4 (a + b) = true ' + ARR + ' Nat.gcd a b = 1 ' + ARR)
T.append('      (a % 2 = 1 ' + AND + ' b % 2 = 1 ' + AND + ' 2 ^ 4 ' + DVD + ' a + b) ' + ORR)
T.append('      (a % 2 = 0 ' + AND + ' 2 ^ 4 ' + DVD + ' a ' + AND + ' b % 2 = 1 ' + AND)
T.append('        (a + b) % 2 = 1) ' + ORR)
T.append('      (b % 2 = 0 ' + AND + ' 2 ^ 4 ' + DVD + ' b ' + AND + ' a % 2 = 1 ' + AND)
T.append('        (a + b) % 2 = 1)) ' + AND)
T.append('    (ErdosTernary2.isTernaryDigit (919 % 3) ' + AND)
T.append('      (271 ^ 2 - 1 = (271 - 1) * (271 + 1)) ' + AND)
T.append('      (776151559 % (73 * 2)) % 73 = 776151559 % 73 ' + AND)
T.append('      carryAtPos 919 1 < 4 ' + AND)
T.append('      v2r (3 ^ 4 * 625) = v2r 625) :=')
T.append('  ' + LAN + 'census_rows, beyond_flt_row, witness_r2_row, r3_witness1,')
T.append('    r3_witness2, class_residues, tcase_kills, hunt939b_bound,')
T.append('    e939_no_small_sum_1500, tc_shape, e939_arsenal_bridge' + RAN)
T.append('')
T.append('end E939')
T.append('')

with io.open('tail2.lean', 'w', encoding='utf-8') as f:
    f.write('\n'.join(T))
print('tail2.lean written', len(T), 'lines')
