# W64-D P885 CI VERDICT — THE k=4 CASE THEOREM CERTIFIED GREEN ON CI

Run 43599544505 (branch w63-b5-p885, commit 6dacf35 = guard-sync push, 2026-11-14T13:23:45Z):
kernel-a: success | kernel-c: SUCCESS (job 132461141736) | kernel-b: in_progress at capture.

## THE RECEIPTS (kernel-c job log, verbatim)
[36;1mgrep -F "E885_K4_GREEN" kernel50b.log[0m
[36;1mgrep -E "E885K4.(dset_mem_iff|dset_witness|k4_witness|k4_distinct_sorted|e885_k4_arsenal_bridge|e885_k4_board)' (does not depend on any axioms|depends on axioms)" kernel50b.log[0m
[36;1mecho KERNEL50B_GREEN=1[0m
'E885K4.dset_mem_iff' depends on axioms: [propext]
'E885K4.dset_witness' depends on axioms: [propext]
'E885K4.k4_witness' depends on axioms: [propext]
'E885K4.k4_distinct_sorted' does not depend on any axioms
'E885K4.e885_k4_arsenal_bridge' depends on axioms: [propext, Classical.choice, Quot.sound]
'E885K4.e885_k4_board' depends on axioms: [propext, Quot.sound]
"E885_K4_GREEN"
"E885_K4_GREEN"
'E885K4.dset_mem_iff' depends on axioms: [propext]
'E885K4.dset_witness' depends on axioms: [propext]
'E885K4.k4_witness' depends on axioms: [propext]
'E885K4.k4_distinct_sorted' does not depend on any axioms
'E885K4.e885_k4_arsenal_bridge' depends on axioms: [propext, Classical.choice, Quot.sound]
'E885K4.e885_k4_board' depends on axioms: [propext, Quot.sound]
KERNEL50B_GREEN=1
[36;1mecho KERNEL61_GREEN=1[0m
'Erdos411.table_bounds' depends on axioms: [propext]
'Erdos411.table_bounds' depends on axioms: [propext]
KERNEL61_GREEN=1

## WHAT THIS CERTIFIES
THE Erdos #885 k=4 CASE THEOREM (Erdos885K4.lean, Kernel 50b):
N = 2254336 < 9945936 < 29904336 < 779175936 share exactly D = {534, 3216, 8016, 9840};
E885K4.k4_witness depends on axioms: [propext] ONLY (no sorryAx, no Classical.choice).
The ex-master-blocker (kernel61 CI guard E411. vs namespace Erdos411) is dead:
KERNEL61_GREEN=1 in the same green job.

## THE W64-D round also running (k=5 escalation hunt)
k5hunt_w64.py (extension pass over the K_{6,2} pool; exact big-n factorization
patch: sympy.factorint fallback for Delta > 1.6e9) + engine885_r5_k5.py
(full-u-window K_{6,2} harvest, u=501..2236, tau(Delta)>=16, C<=1e8, seeded
from the W63-B5 u<=501 harvest of 12761 K_{6,2}s).
Census so far: extension over ALL 12761 pairs — ZERO third columns sharing
>= 6 rows at C <= 1e8 AND at C <= 1e9 (2.5M rich columns cached per pass).
