#!/usr/bin/env python3
# hunt939e.py — Erdős #939 r=4, W62 Task 1-b: THE TRUE BOX TO 10^19 (background run).
# Same validated engine as hunt939d.py (bucketed EO/OO lanes, numpy uint64 —
# sums <= 1e19 < 2^64, exact). Run via nohup; writes hunt939e_output.txt.
import os, sys
sys.path.insert(0, '/home/z/erdos-weak-problems/problem939-rpowerful')
os.environ['QUIETFILE'] = '/home/z/erdos-weak-problems/problem939-rpowerful/hunt939e_output.txt'
import hunt939d as H

H.main.__wrapped__ if False else None
# open the dedicated log and run the box
H.LOG = open('/home/z/erdos-weak-problems/problem939-rpowerful/hunt939e_output.txt', 'w')
H.log('hunt939e: the TRUE exhaustive box to 1e19 (engine = hunt939d.box_npy, '
      'validated vs Lean census + brute-force cross-check at 1e7)')
H.box_npy(10 ** 19, '19')
H.log('hunt939e done.')
H.LOG.close()
