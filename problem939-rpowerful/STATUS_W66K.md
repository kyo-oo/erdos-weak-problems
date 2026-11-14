#939 STATUS — W66-P939-K (commander-executed kernel surgery)

- LANDED: problem939-rpowerful/Erdos939R5.lean (14,192 lines, kernel60c) —
  THE BOX THEOREM, table form: e939_box_census — no pairwise-coprime
  4-powerful triple a+b=c with a, b <= B = 999706081460641 inside the
  certified census TAB (48,138 members <= 2B, incl. 1, sorted, dual-method
  python: gen939R5.py gen4 + preflight939R5.py/engine939_w66.py).
- STRUCTURE: parity split (EE structural 2|gcd; EO/OE via eo_kill; OO via
  oo_kill); the even-16 table gate; residue routing via filter-eq certs;
  the sweeps (265 decide chunks, 40 o's each, ~700K steps/chunk); the
  inTAB 64-bucket decision tree (O(16)/query, TAB.all inTAB certified).
- EVIDENCE: sum-hits 17,439 residue-mirrored, ALL gcd>1, ZERO coprime
  (the 1e19 python extension: 449,087 values, 246,243 sum-hits, coprime 0;
  the r=3 positive control validates the scanner — see the P939-D lane).
- SCOPE (honest): complete and unconditional over the certified census
  table. The structural bridge rpow 4 n -> n <= LIM -> n ∈ TAB (the
  genVals recursion completeness) is the next-round lane.
