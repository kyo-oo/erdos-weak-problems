#!/usr/bin/env python3
"""S038 ROULETTE — corpus scan for NEW admissions.
Triage set = every problem mentioned in THE_LIST v8 (killed/queue/OUT) +
THE_CORE addenda queues. Untriaged open corpus problems ranked by
weapon-territory keywords (the arsenal's strengths)."""
import yaml, re

with open('/home/z/my-project/corpus-erdos/data/problems.yaml') as f:
    data = yaml.safe_load(f)

triaged = set()
# Killed / closed / banned
triaged |= {404, 271, 406, 260, 700, 727, 686, 1108, 1063, 451, 1072, 394, 711, 961, 1074, 954, 282, 261, 317}
# §C queue
triaged |= {374, 289, 396, 306, 348, 288, 1212, 389, 708}
# §D witness lanes
triaged |= {1056, 939, 203, 273, 885, 677, 850, 274}
# §F volley
triaged |= {124, 243}
# Doubter-killed S026
triaged |= {508, 188, 212, 1135, 918, 919, 376, 377, 386, 936, 137, 373, 930, 931, 291, 264, 1049, 1160, 1159, 849, 1003, 985}
triaged |= set(range(1167, 1222))
# S028 OUT
triaged |= {3, 5, 233, 455, 68, 249, 251, 252, 257, 263, 267, 269, 385, 413, 572, 573, 634, 684, 685, 1095, 805, 942, 952, 1199, 1206, 495, 276}
# S029 OUT
triaged |= {1113, 940, 1093, 675, 177, 1188, 1189, 912, 393, 400, 478, 1094, 278, 293, 295, 301, 302, 304, 311, 313, 319, 327, 450, 693, 886, 887, 893, 945, 975, 1054, 1100, 470, 9, 11, 28, 33, 40, 66, 870, 881, 1145, 1192, 1194, 338, 683, 731, 156, 472, 695, 701, 970, 978, 983, 996, 1151, 256, 1035, 595, 602, 61, 75, 159, 174, 500, 563, 564, 712, 827, 837, 838}
# S030 OUT
triaged |= {422, 456, 913, 1065, 1059, 1142, 324, 826, 1055, 1110, 689, 312, 326, 431, 892, 1101}
# 271-status residue front is internal
triaged |= {820}  # named deep front S022

WEAPONS = {
    'factorial': 10, 'binomial': 10, 'powerful': 9, 'divisor': 8, 'divides': 8,
    'unit fraction': 9, 'egyptian': 9, 'covering': 9, 'primitive': 7,
    'pell': 10, 'square': 7, 'residue': 8, 'digit': 8, 'base': 6,
    'gcd': 8, 'lcm': 8, 'consecutive': 7, 'greedy': 8, 'sylvester': 9,
    'smooth': 9, 'wilson': 10, 'prime': 5, 'modular': 6, 'congruence': 7,
    'arithmetic progression': 6, 'multiplicative': 7, 'coprime': 7,
    'perfect power': 9, 'ternary': 10, 'representation': 6, 'pillai': 10,
    'reciprocal': 8, 'harmonic': 8, 'complete sequence': 9, 'power': 4,
}

open_probs = []
for p in data:
    st = (p.get('status') or {}).get('state', '')
    if 'open' not in st:
        continue
    num = int(p['number'])
    if num in triaged:
        continue
    open_probs.append((num, p))

print(f"open + untriaged: {len(open_probs)} problems")
print(f"numbers: {[n for n,_ in open_probs]}")
