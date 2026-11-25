# Fidelity note: what the Lean proof checks

This note says in words what each Lean statement means. It compares the statements with the wording of the conjectures in
the literature. It also lists the consequences that have a paper proof only.

Notation. For a finite simple graph G: |V(G)| is the number of vertices, α(G) the independence number, ω(G) the clique
number, χ(G) the chromatic number, h(G) the Hadwiger number and cm(G) the connected-matching number. Section 1 defines them.

## 1. The definitions, as built

The file `Challenge/Statement.lean` imports Mathlib and nothing else. It copies four definitions word for word from OpenAI's
comparator file `lean/ComparatorChallenges/HadwigerCounterexample.lean` (openai/math, commit
3344da59991ed94f9ba711217b29c1d760badfa6). The proofs in `lean/OAI/Combinatorics/HadwigerScaled/Main.lean` use the same
four definitions from OpenAI's library. A check printed the four definitions and the three theorem statements in full
(`pp.all`) in both environments. The two outputs are byte-identical (8,820 bytes; `logs/p3-clean-4-chal.txt`, `logs/p3-clean-4-sol.txt`).

- **Graph.** `G : SimpleGraph (Fin m)`. A Mathlib simple graph on the vertex set {0, 1, ..., m-1}. Edges are undirected.
  There are no loops and no multiple edges.
- **Independence number.** `G.indepNum` (Mathlib). It is the supremum of the sizes of the sets of pairwise non-adjacent
  vertices. For a finite vertex set this supremum is a maximum. So `G.indepNum ≤ 2` means: among any three distinct
  vertices, at least two are adjacent.
- **Connected matching.** `IsTouchingMatching G M`, where `M` is a finite set of vertex sets. It holds when
  (a) each member of `M` has exactly two vertices and these two vertices are adjacent, so each member is an edge;
  (b) two different members have no common vertex;
  (c) for two different members `e` and `f`, some vertex of `e` is adjacent to some vertex of `f`.
  `connectedMatchingNumber G` is the supremum of the sizes of such `M`. The empty `M` qualifies, and a matching has at most
  m/2 edges. So the supremum is the largest size of a connected matching.
- **Clique minor.** `HasCliqueMinor G t` holds when there are t vertex sets B_1, ..., B_t (the branch sets) such that each
  B_i induces a connected subgraph, two different B_i have no common vertex, and two different B_i are joined by at least
  one edge. In Mathlib a connected graph is not empty, so each B_i has at least one vertex. This is the usual definition of
  a K_t minor (a "K_t model"). `hadwigerNumber G` is the supremum of such t. The value t = 0 qualifies, and t ≤ m. So it is
  the largest t such that G has a K_t minor.

Literature check of the definitions:

- Connected matching. Costa, Luu, Wood and Yip (arXiv:2512.17114v2, Section 1): a matching M is connected "if for every two
  edges e, f ∈ M, V(e) and V(f) are adjacent", where two disjoint vertex sets are adjacent when some vertex of one is
  adjacent to some vertex of the other. Conlon, Fox and Sudakov (arXiv:1910.08661, Section 7) give the same definition in
  words. Conditions (a) to (c) above say exactly this.
- Hadwiger number. The largest t such that K_t is a minor of G (Seymour's survey, Section 4; had(G) in Costa et al.).
- Independence number. The size of the largest stable set (Seymour calls it the stability number).

## 2. The five Lean theorems

All five are in namespace `OAI.HadwigerCounterexample`, module `OAI.Combinatorics.HadwigerScaled.Main`. For each one,
`#print axioms` lists exactly `propext`, `Classical.choice` and `Quot.sound` (`logs/p3-clean-3-axioms.txt`). Theorems 3, 4 and 5 are
the three statements of `Challenge/Statement.lean`. Theorems 1 and 2 are steps of the proof. The same-statement check does
not cover theorems 1 and 2.

1. `exists_graphs_div (hQ : 0 < Q) (M : ℕ)`. For every positive integer Q and every M, there is an integer m ≥ max(M, 5)
   and a graph G on m vertices with α(G) ≤ 2 and cm(G) < m/Q.
2. `exists_graphs_beta (β : ℚ) (hβ : 0 < β) (M : ℕ)`. For every rational β > 0 and every M, there is m ≥ M and a graph G
   on m vertices with α(G) ≤ 2 and cm(G) < βm.
3. `exists_small_hadwiger (β : ℚ) (hβ : 0 < β) (M : ℕ)`. For every rational β > 0 and every M, there is m ≥ M and a graph
   G on m vertices with α(G) ≤ 2, cm(G) < βm and h(G) < (1/3 + 2β)m + 2/3.
4. `not_linear_cm`. There are no rational c > 0 and no M such that every graph G with m ≥ M vertices and α(G) ≤ 2 has
   cm(G) ≥ cm.
5. `not_hc_eps`. There are no rational ε > 0 and no M such that every graph G with m ≥ M vertices and α(G) ≤ 2 has
   h(G) ≥ (1/3 + ε)m.

Theorem 3 has the form that the claim needs: for every rational β > 0 and every M there is m ≥ M and a graph G on
`Fin m` with `G.indepNum ≤ 2` and cm(G) < βm (and the bound on h(G)).

The constants are rational in Lean. This loses nothing: below every real number c > 0 there is a rational number in (0, c).

The proof of theorem 1 is OpenAI's proof of their theorem `exists_graphs` (cm(G) < m/100) with two changes. The marginal cap
2^1000 of the parameter lemma becomes 2^(12Q+1), and the final sampling step uses the threshold m/Q. OpenAI's
supersaturation theorem `eventual_conflict_lower_bound` is used unchanged. It holds for every value of the cap. The exact
changes are in `lean/provenance.diff`.

## 3. Quantifier order

For each β > 0 and each bound M, theorem 3 gives one order m ≥ M. So for each β there are infinitely many orders m with
such a graph. The theorems do not give a graph of every large order. The proof builds graphs only of the orders
m = 2^(1000 g N) with g = 10^9 + 1 and N a multiple of a number that depends on β (Lean `ord p.g N`).

This is enough for the conjectures in Section 4. Each of them says "there is a constant such that every graph (or every
large graph) with α(G) = 2 satisfies a linear bound". Counterexamples of arbitrarily large orders refute such a statement.

The theorems say nothing about the function m ↦ min{cm(G)/m : |V(G)| = m, α(G) ≤ 2} at orders m outside the sequence above.
So they show that its lower limit is 0. They do not show that its limit is 0.

## 4. The conjectures in the literature and how the Lean theorems settle them

(a) **The weak (linear) connected-matching conjecture of Füredi, Gyárfás and Simonyi.** Their paper (Combin. Probab.
Comput. 14 (2005) 435-438, author copy read on 2026-11-25) defines a connected matching exactly as in Section 1 and states
Conjecture 1.4: there is a constant c such that every graph with ct vertices and α(G) = 2 has a connected matching of size
t. OpenAI restates it (Hadwiger paper, `01-history.tex` lines 79 to 81): there is an absolute c_0 > 0 with
cm(G) ≥ c_0|V(G)| "for all sufficiently large graphs with α(G) ≤ 2". Theorem 4 is the negation of OpenAI's sentence. (Lean
states it for graphs on the vertex set {0, ..., m-1}. Every finite graph is isomorphic to such a graph, and α and cm do not
change under isomorphism.) Theorem 4 also refutes Conjecture 1.4 as written, by a short step that is not in Lean. Suppose
Conjecture 1.4 holds with constant c (then c ≥ 4, because two disjoint copies of K_{2t-1} have no connected matching of
size t). Let G have n ≥ c vertices and α(G) ≤ 2, and put t = ⌊n/c⌋ ≥ 1. An induced subgraph H of G on ct vertices has
α(H) ≤ 2. If α(H) = 2, Conjecture 1.4 gives a connected matching of size t in H. If α(H) ≤ 1, H is complete and has one of
size ⌊ct/2⌋ ≥ t. A connected matching of H is one of G. So cm(G) ≥ ⌊n/c⌋ ≥ n/(2c) for all such G, which theorem 4 (with a
rational constant at most 1/(2c) and M = c) says is false.

(b) **Linear-CM, Conjecture 1.8 of Costa, Luu, Wood and Yip** (arXiv:2512.17114v2; attributed there to Füredi, Gyárfás and
Simonyi): there is c > 0 such that every graph G with α(G) = 2 has a connected matching of size at least c|V(G)|. The same
statement is Conjecture 7.1 of Conlon, Fox and Sudakov (arXiv:1910.08661). Two differences from theorem 4: it is about every
graph, not only large graphs, and it asks α(G) = 2, not α(G) ≤ 2. Theorem 4 refutes it by a one-line step that is not in
Lean. Suppose the conjecture holds with constant c. A graph with α(G) ≤ 1 and m ≥ 2 vertices is complete, and the complete
graph K_m has a connected matching of size ⌊m/2⌋ ≥ m/3. So every graph with α(G) ≤ 2 and m ≥ 2 vertices has
cm(G) ≥ min(c, 1/3) m. Theorem 4 with a rational constant in (0, min(c, 1/3)] and M = 2 says this is false.

(c) **Seymour's question** (survey "Hadwiger's conjecture", Section 4, Open question 4.8) asks whether some constant
c > 1/3 gives every graph G with α(G) = 2 a K_t minor with t ≥ c|V(G)|. The same question is HC_ε, Conjecture 1.7 of Costa et
al. (attributed to Seymour), and Conjecture 1.3 of Füredi, Gyárfás and Simonyi (attributed to Seymour, unpublished).
Conlon, Fox and Sudakov write that Seymour and Mader have both asked it. Theorem 5 answers
it in the negative by the same one-line step: K_m has h = m, so the question with constant c would give
h(G) ≥ min(c, 1) m for every graph with α(G) ≤ 2, and theorem 5 with ε rational in (0, min(c, 1) - 1/3] says this is false.

(d) **Equivalence.** Thomassé observed that (b) and (c) are equivalent. Füredi, Gyárfás and Simonyi report this (citing
Thomassé's note in the problem list of a 2002 meeting in Odense) and refer to Kawarabayashi, Plummer and Toft for a
proof. The Lean proof does not use the equivalence. It derives theorem 5 from
theorem 3, and theorem 3 uses only OpenAI's Lean form of the easy direction: h(G) ≤ (|V(G)| + 4 cm(G) + 2)/3 for every
finite graph (`full_matching_minor_proposition`).

## 5. Consequences with a paper proof only (not in Lean)

- **inf h(G)/|V(G)| = 1/3 over nonempty graphs with α(G) ≤ 2.** Theorem 3 gives the upper bound: values below
  1/3 + 2β + 2/(3m).
  The lower bound h(G) ≥ |V(G)|/3 is the theorem of Duchet and Meyniel (1982). It is not formalized here.
- **sup χ(G)/h(G) = 3/2 over nonempty graphs with α(G) ≤ 2, and the same for the fractional chromatic number.** For the
  graphs of theorem 3: ω(G) ≤ 2 cm(G) + 1 (pair up the vertices of a largest clique) and χ(G) ≤ (m + ω(G))/2, so
  χ/h → 3/2 along witnesses with β → 0 and m → ∞.
  The bound χ(G) < (3/2) h(G) for every graph with α(G) ≤ 2 comes from Lemmas 2.1 and 2.3 of Böhme, Kostochka and Thomason
  (Combin. Probab. Comput. 20 (2011) 513-518): h ≥ (4χ - n)/3 and, for n ≥ 5, h ≥ 1 + n/3; adding them gives
  χ ≤ (3/2)h - 3/4. So 3/2 is the supremum and no graph attains it. None of this is in Lean.
- **The clique threshold n/4 of Chudnovsky and Seymour is sharp.** Chudnovsky and Seymour (Combinatorica 32 (2012)) proved
  that a graph with α(G) ≤ 2 has a K_t minor with t = ⌈|V(G)|/2⌉ when it has a clique of at least |V(G)|/4 vertices
  (|V(G)| even) or at least (|V(G)| + 3)/4 vertices (|V(G)| odd) (Theorem 1.3, as stated by OpenAI). Join a graph
  G_0 of theorem 3 (n_0 vertices) to a complete graph K_q: every vertex of G_0 becomes adjacent to every vertex of K_q. Then
  α stays at most 2, ω = ω(G_0) + q, and h ≤ h(G_0) + q, because deleting one vertex lowers h by at most 1. With q just below
  n_0 - 2h(G_0) ≥ (1/3 - 4β)n_0 - 4/3 the joined graph has h < n/2 and ω/n → 1/4 as β → 0. So the constant 1/4 cannot be
  lowered. This is a paper remark (Section 5 of the paper). It is not in Lean. (OpenAI's own Lean bound
  h(G_0) < 26n_0/75 + 2/3 alone gives such graphs with ω/n up to about 23/98.)
- **Open Problem (3) of Kawarabayashi, Wood and Yip** (arXiv:2611.11205v2, 10 Nov 2026, Sections 1.1 and 7). They put
  ρ := inf had(G)/χ(G) and ρ_d := inf had_d(G)/χ(G) over non-empty claw-free graphs (had_d is the dominating-model
  version, had_d ≤ had), record 2/3 ≤ ρ_d ≤ ρ ≤ 2/3 + 2/75 and ask: "What are the constants ρ and ρ_d?" A graph with
  α(G) ≤ 2 is claw-free. For the graphs of theorem 3, χ(G) ≥ m/2 (a colour class has at most two vertices), so
  h(G)/χ(G) < 2/3 + 4β + 4/(3m). Hence ρ ≤ 2/3, and with their lower bound ρ = ρ_d = 2/3. The bound on h is in Lean;
  χ ≥ m/2 and the lower bound 2/3 (Kawarabayashi-Wood-Yip Theorem 5, which generalizes Chudnovsky and Fradkin, J. Graph
  Theory 63 (2010)) are not.
- **The conflict form is the same statement.** The paper's Theorem 1.2 also says that every matching with at least βm
  edges contains two conflicting edges (two edges with no edge between them). A matching without such a pair is a
  connected matching, so this sentence says exactly cm(G) < βm, which is in Lean. Paper only is the probability estimate
  for the random construction (Lemma 4.3 of the paper: the bound holds with probability 1 - exp(-Ω(m))).

- **Further consequences** (Section 6 of the paper): the inequality 3 h_f(G) ≤ n + 4 cm(G) + 2 and the failure of
  Conjectures 23 and 24 of Harvey and Wood, the lower bound on cm for the triangle-free process, and three remarks
  checked by one reader (inflations, dense minors, strongly odd dominating models). All are paper only.

## 6. What the Lean proof depends on

- Mathlib at commit d13f23b723b8a846827a245b89c10fc7d3f11612 and Lean 4.34.1.
- 288 unchanged files of OpenAI's Lean library at commit 3344da59991ed94f9ba711217b29c1d760badfa6 (list in
  `lean/oai_files.txt`, SHA-256 sums in `lean/OAI-SHA256SUMS`). They contain OpenAI's formal proof of the supersaturation
  theorem. That proof is part of the checked closure. It is not an assumption.
- The axioms propext, Classical.choice and Quot.sound. No other axiom and no `sorry` occur in the closure. The only `sorry`
  in the project is in `Challenge/Statement.lean`, whose role is to state the theorems.

Kernel checks of the closure: the Lean kernel during the build; `leanchecker` replayed 292 modules (288 of OpenAI and our
4); `lean4lean` (an independent kernel written in Lean) checked the export of the five theorems with all their dependencies
(39,086 declarations). All exited with code 0 in a build of the published files from an empty folder (`logs/`).
