# OFFICIAL PROVENANCE — fresh comparator downloads (S071, BOSS order)

Downloaded fresh from GitHub on 2026-11-17 (this round; NOT reused from any
prior campaign artifact):

| Repo | Clone URL | HEAD at clone | License | Role |
|---|---|---|---|---|
| FunSearch | https://github.com/google-deepmind/funsearch.git | cc53f274237d7ab05c19df939edbc1f9616a7c19 | Apache-2.0 | Official evaluators: cap_set (F_3^n AP-free/cap sets — #142), cyclic_graphs (independent sets in cyclic graph powers — #61), implementation/ (official Evaluator engine — program evaluation lane for #107) |
| Code Contests | https://github.com/google-deepmind/code_contests.git | fa7a4f8139aab08362503f3344778eb86901709a | Apache-2.0 | Official AlphaCode challenge+solution execution harness (format reference; C++/Bazel — consulted, not executed) |

Verbatim official code extracts live in `challenges/<pid>/official_code/`
with per-file provenance headers (source path + commit). The official
notebook code (cap_set.ipynb cells 2–14, cyclic_graphs.ipynb cells 2–14) is
copied byte-for-byte where used, with the cell number recorded.

The verdict protocol: the gate prints `YOUR SOLUTION IS OKAY` when every
official check, every solution-claim check, and every negative control
(corruption correctly rejected) passes. See PROTOCOL.md.
