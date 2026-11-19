# W75-61K NEW CLAIMS (for comparator-official/challenges/61/solution.json integration)

## C61-PAW
"THEOREM PAW (W75, in-package, zero premises): every paw-free graph (no induced paw = triangle with pendant edge) on n >= 1 vertices satisfies alpha(G) >= sqrt(n)/2. Proof: connected paw-free components are triangle-free (alpha >= sqrt(m)/2 by the max-degree/Caro-Wei split, in-package) or complete multipartite (Olariu structure theorem re-derived in-package: every vertex adjacent to >= 2 of any triangle, non-adjacency is transitive via the paw exclusion); alpha sums over components with sqrt-concavity. The 1/2 exponent is optimal (m x m block-twin witnesses). Engine: receipts61four.txt 14/14 GREEN + 731K-graph census addendum."

## C61-P3K1
"Corollary P3+K1 (complement transfer of THEOREM PAW): every (P3+K1)-free graph (no induced P3 + isolated vertex) satisfies omega(G) >= sqrt(n)/2. The complement of a paw is P3+K1; max(alpha,omega) is complement-invariant."

## C61-DIAMOND
"THEOREM DIAMOND (W75, in-package, zero premises): every diamond-free graph (no induced K4 - e) on n >= 1 vertices satisfies max(alpha, omega) >= n^(1/3)/2. Proof: in a diamond-free graph every open neighborhood N(v) is P3-free (else v,x,y,z with x~y, x~z, y!~z forms the diamond), hence a disjoint union of cliques; the max-degree vertex splits into r cliques of max size s with alpha >= r, omega >= s+1, r*s >= Delta; the case split at Delta = n^(2/3) closes with Caro-Wei. Engine: receipts61four.txt."

## C61-K2-2K1
"Corollary K2+2K1 (complement transfer of THEOREM DIAMOND): every (K2+2K1)-free graph (no induced edge + two isolated vertices) satisfies max(alpha,omega) >= n^(1/3)/2 (complement of diamond = K2+2K1)."

## C61-2K2-STRUCTURE
"THE 2K2 STRUCTURE PACKAGE (W75, in-package): (i) THEOREM 2K2-TF: every triangle-free 2K2-free graph satisfies alpha >= sqrt(n)/2. (ii) THEOREM 2K2-DEC: the complete eight-class attachment decomposition of a 2K2-free graph around any triangle, with the proved laws: S_empty independent; S_x x S_y fully non-adjacent (x != y exactly-one classes); at most one of S_a,S_b,S_c carries an edge; omega(S_ab) <= omega-2, omega(S_abc) <= omega-3. (iii) CENSUS-2K2 (exhaustive): every 2K2-free graph on n <= 7 vertices (731,523 graphs, complete enumeration) satisfies alpha*omega >= 4n/5, equality exactly at C5; complement transfer carries all of it to induced-C4-free graphs. (iv) The C5-attachment 17-type law (proved). The full-n alpha*omega >= 4n/5 closure is the named immediate lane (the pairwise-constraint matrix of the eight classes)."

## C61-FOURVERTEX-CLASSIFICATION
"THE 4-VERTEX CLASSIFICATION (status exact): 9 of the 11 unlabeled 4-vertex graphs are EH-closed in-package with explicit unconditional exponents (P4 and paw/P3+K1 at the optimal 1/2; K4/K4bar every c<1/3; claw/K3+K1, diamond/K2+2K1 at 1/3); C4/2K2 carry the complete triangle-free half (alpha >= sqrt(n)/2), the complete triangle-decomposition structure theorem, and the exhaustive sharp-form census alpha*omega >= 4n/5 through n=7. All claims engine-certified (receipts61four.txt 14/14 + the 731K census addendum)."
