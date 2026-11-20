# Erdős Problem #61 — THE ERDŐS–HAJNAL CONJECTURE (verbatim, erdosproblems.com/61)

> For any graph $H$ is there some $c=c(H)>0$ such that every graph $G$ on $n$
> vertices that does not contain $H$ as an induced subgraph contains either a
> complete graph or independent set on $\geq n^c$ vertices?

Tags: graph theory. Sources: [ErHa89] [Er90] [Er93,p.346] [Er97f] [Va99,3.52].

Corpus context (verbatim comments):
- Conjectured by Erdős and Hajnal [ErHa89], who proved a clique or independent set of size
  >= exp(c_H sqrt(log n)) must exist.
- Improved by Bucić, Nguyen, Scott, Seymour [BNSS23] to >= exp(c_H sqrt(log n log log n)).
- PROVED for: any H with <= 4 vertices [ErHa89]; the bull graph [ChSa08]; C_5 [CSSS23];
  all paths [NSS26, Nguyen]; closed under vertex substitution [APS01] => all H on 5 vertices.

DeepMind comparator (google-deepmind/formal-conjectures, ErdosProblems/61.lean):
- IsErdosHajnalLowerBound H f := forall^f n in atTop, forall G : SimpleGraph (Fin n),
    (not exists g : alpha -> Fin n, H = G.comap g) -> G.indepNum >= f n \/ G.cliqueNum >= f n
- erdos_61 (research open): forall H, exists c > 0, IsErdosHajnalLowerBound H (n => n^c)
- variants.erha89 (solved): exp (c * sqrt (log n))
- variants.bnss23 (solved): exp (c * sqrt (log n * log (log n)))
- variants.p5 (solved): pathGraph 5 with n^c
- variants.c5 (solved): cycleGraph 5 with n^c
