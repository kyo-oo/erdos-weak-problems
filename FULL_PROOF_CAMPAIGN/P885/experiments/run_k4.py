import sys, json
sys.path.insert(0, '/home/z/my-project/erdos-weak-problems/FULL_PROOF_CAMPAIGN/P885/experiments')
import biclique_engine as E

s1_max = int(sys.argv[1]) if len(sys.argv) > 1 else 1000
tau_min = int(sys.argv[2]) if len(sys.argv) > 2 else 24
hits = E.hunt(4, s1_max, tau_min)
print('TOTAL k4 hits:', len(hits))
json.dump([[list(map(int, r)), list(map(int, c))] for r, c in hits[:200]],
          open(f'k4_hits_s{s1_max}_t{tau_min}.json', 'w'))
