# The Duchet-Meyniel bound is asymptotically sharp for graphs with independence number two

Research driven, orchestrated and reviewed by Jack Ryan. Claude (by Anthropic), GPT-6.2 Astra (by OpenAI) and Gemini 4 Neon (by Google) collaborated in finding and writing the proofs. The main theorems are formalized in Lean 4.

No professional mathematician has refereed this repository.

## The claim

The section "Terms" below defines every term and symbol.

For every c > 0 there are arbitrarily large graphs G with independence number at most 2 in which every connected matching
has fewer than c|V(G)| edges, and the Hadwiger number of these graphs is less than (1/3 + 2c)|V(G)| + 2/3.

So the bound h(G) ≥ |V(G)|/3 of Duchet and Meyniel (1982) for graphs with independence number at most 2 cannot be improved
to (1/3 + ε)|V(G)| for any ε > 0. The bound is asymptotically sharp: the ratio h(G)/|V(G)| comes arbitrarily close to 1/3,
and no graph with α(G) ≤ 2 and at least 5 vertices reaches 1/3 (Böhme, Kostochka and Thomason 2011: h(G) ≥ 1 + |V(G)|/3).
This answers Seymour's Open question 4.8 (survey "Hadwiger's conjecture", 2016) in the
negative: no constant c > 1/3 gives every graph G with α(G) = 2 a K_t minor with t ≥ c|V(G)|.

In the table, n is the number of vertices.

| Year | Statement about connected matchings in graphs with α(G) ≤ 2 | Status |
|---|---|---|
| 2005 | Füredi, Gyárfás and Simonyi, Conjecture 1.5: every such graph on 4t - 1 vertices has a connected matching of size t, so cm(G) is at least about n/4 | conjecture; checked for t ≤ 17 (2005) and t ≤ 22 (Chen and Deng, 2025) |
| 2005 | Weak form, their Conjecture 1.4: cm(G) ≥ cn for some c > 0 | conjecture |
| 2026 | OpenAI (manuscript dated 23 September, public in October): graphs with cm(G) < n/100 | disproves Conjecture 1.5 and Hadwiger's conjecture; leaves the weak form open |
| 2026 | This repository (November): graphs with cm(G) < εn for every ε > 0 | disproves the weak form; machine-checked in Lean 4 |

## Terms

- A **graph** here is finite and simple: no loops and no multiple edges. |V(G)| is its number of vertices.
- The **independence number** α(G) is the largest number of vertices with no edge between any two of them. If α(G) ≤ 2,
  then among any three vertices at least two are joined by an edge.
- A **matching** is a set of edges with no common vertex. A matching is **connected** if for any two of its edges, some
  endpoint of the first edge is joined by an edge to some endpoint of the second. cm(G) is the largest number of edges in a
  connected matching.
- G has a **K_t minor** if there are t disjoint, non-empty vertex sets, each of which induces a connected subgraph, with at
  least one edge between any two of them. The **Hadwiger number** h(G) is the largest such t.
- The **chromatic number** χ(G) is the least number of colours for the vertices such that the two ends of every edge get
  different colours.
- A graph is **claw-free** if no vertex has three neighbours with no edge between any two of them. Every graph with
  α(G) ≤ 2 is claw-free.

## What is machine-checked

The file `Challenge/Statement.lean` states three theorems. It imports Mathlib and nothing else. The four definitions in it
(connected matching, connected-matching number, clique minor, Hadwiger number) are copied unchanged from OpenAI's own
statement file for their Hadwiger counterexample.

1. `exists_small_hadwiger`: for every rational β > 0 and every M there is m ≥ M and a graph on m vertices with α ≤ 2,
   cm < βm and h < (1/3 + 2β)m + 2/3.
2. `not_linear_cm`: no rational c > 0 and no M make cm(G) ≥ c|V(G)| true for every graph G with α(G) ≤ 2 and at least M
   vertices.
3. `not_hc_eps`: no rational ε > 0 and no M make h(G) ≥ (1/3 + ε)|V(G)| true for every graph G with α(G) ≤ 2 and at least M
   vertices.

The proofs are in `lean/OAI/Combinatorics/HadwigerScaled/Main.lean`, together with two intermediate theorems
(`exists_graphs_div`, `exists_graphs_beta`). The checks, all on 25 November 2026:

- The project builds with exit code 0. The only `sorry` is in the statement file, which states the theorems.
- `#print axioms` gives exactly `propext`, `Classical.choice` and `Quot.sound` for all five theorems.
- The definitions and the three statements, printed in full, are byte-identical in the statement file and in the proof.
- `leanchecker` replays 292 modules with exit code 0.
- `lean4lean`, a second kernel, checks the five theorems and all their dependencies (39,086 declarations) with exit code 0.
- A second build from an empty folder, with the files of this repository and OpenAI's files fetched by `lean/assemble.sh`,
  repeated all these checks with the same results.

`FIDELITY.md` says in words what each Lean statement means and compares it with the conjectures in the literature. The
logs are in `logs/`.

### How to rebuild

The proof imports 288 files of OpenAI's Lean library. They are not copied here. `lean/assemble.sh` copies them from a
checkout of github.com/openai/math and checks their SHA-256 sums.

    cd lean
    git clone https://github.com/openai/math openai-math
    git -C openai-math checkout 3344da59991ed94f9ba711217b29c1d760badfa6
    sh assemble.sh openai-math
    lake exe cache get
    ulimit -n 8192
    LEAN_NUM_THREADS=4 lake build OAI.Combinatorics.HadwigerScaled.Main ComparatorChallenge.HadwigerScaled

The checks and their expected output are in `lean/README.md`. The build ran on a machine with 128 GB of memory.

## What it depends on

- **OpenAI's Lean library**, github.com/openai/math at commit 3344da59991ed94f9ba711217b29c1d760badfa6 (Apache License
  2.0). It contains OpenAI's formal proof of their counterexample to Hadwiger's conjecture, including their supersaturation
  theorem. That proof is part of the checked closure. It is not an assumption.
- Mathlib at commit d13f23b723b8a846827a245b89c10fc7d3f11612, and Lean 4.34.1.

The result is a parametric extension of OpenAI's proof. OpenAI's graphs have independence number at most 2 and cm(G) <
|V(G)|/100. Their proof fixes one parameter, a marginal cap equal to 2^1000. With this cap fixed, the final step of their
proof cannot reach thresholds below a fixed positive constant. Their formal supersaturation theorem holds for every value of
the cap. We changed two places: the cap 2^1000 became 2^(12Q+1), and the threshold m/100 became m/Q, for any positive
integer Q. `lean/provenance.diff` shows the changes.
OpenAI wrote that their fixed coefficient "leaves the weaker conjecture for smaller positive coefficients unresolved"
(A counterexample to Hadwiger's conjecture, manuscript dated 23 September 2026, section "Historical context").

## Relation to the literature

- **Duchet and Meyniel (1982)** proved h(G) ≥ |V(G)|/(2α(G) - 1), so h(G) ≥ |V(G)|/3 when α(G) ≤ 2. The constant 1/3 is
  now known to be optimal.
- **Seymour**, survey "Hadwiger's conjecture" (2016), Open question 4.8, asks whether some c > 1/3 gives a K_t minor with
  t ≥ c|V(G)| in every graph with α(G) = 2. The answer is no. Costa, Luu, Wood and Yip (arXiv:2512.17114) call this
  statement HC_ε (their Conjecture 1.7). Conlon, Fox and Sudakov (arXiv:1910.08661) write that Seymour and Mader both asked
  it.
- **Füredi, Gyárfás and Simonyi (Combin. Probab. Comput. 14 (2005) 435-438)**: their Conjecture 1.4 is the weak (linear)
  form: some constant c gives every graph with ct vertices and α(G) = 2 a connected matching of size t. It is false.
  Costa, Luu, Wood and Yip call it Linear-CM (Conjecture 1.8); Conlon, Fox and Sudakov state it as their Conjecture 7.1.
  The same paper states Seymour's problem as Conjecture 1.3 and the sharp form (4t - 1 vertices) as Conjecture 1.5, and
  reports Thomassé's observation that Conjectures 1.3 and 1.4 are equivalent. The Lean proof does not need this
  equivalence.
- **OpenAI** (manuscript dated 23 September 2026, made public in October 2026) proved cm(G) < |V(G)|/100 and
  h(G) < 26|V(G)|/75 + 2/3 for their graphs. This disproved Hadwiger's conjecture and the sharp conjecture of Füredi,
  Gyárfás and Simonyi. The repository github.com/EdouardBonnet/hadwiger-counterexample ports OpenAI's Lean proof of that
  fixed-coefficient construction (with its 288 upstream modules) and reports a kernel replay dated 11 October 2026.
- **Consequences with paper proofs only** (see `paper/alpha2-third.tex` and `FIDELITY.md`, section 5):
  - inf h(G)/|V(G)| = 1/3 over nonempty graphs with α(G) ≤ 2 (the lower bound is the theorem of Duchet and Meyniel);
  - sup χ(G)/h(G) = 3/2 over nonempty graphs with α(G) ≤ 2, not attained (with Böhme, Kostochka and Thomason 2011);
  - the clique bound |V(G)|/4 in the theorem of Chudnovsky and Seymour (2012) cannot be lowered;
  - the constants ρ and ρ_d of Kawarabayashi, Wood and Yip (arXiv:2611.11205, Open problem 3) both equal 2/3. Here ρ is
    the infimum of h(G)/χ(G) over claw-free graphs, and ρ_d is the same infimum for their dominating clique models.
- **Searches for earlier work** on 25 November 2026 found no earlier statement of this result in the sources searched:
  arXiv (including the math.CO listings of 19 to 25 November), papers that cite the 2005 paper and the papers of Fox and
  of Kawarabayashi, Plummer and Toft, hexagonmath.org (full texts of 1550 of its 1560 works), nilradical.ai, proofatlas.ai,
  the Palomar registry, vibemathed.com, Zenodo, GitHub, MathOverflow. Such searches cannot be complete. Kawarabayashi, Wood
  and Yip (10 November 2026) still describe the question for 1/3 as open.

## Limits

- The graphs are very large: the proof gives graphs only with 2^(1000·g·N) vertices, where g = 10^9 + 1. There is no
  explicit construction, and no rate at which cm(G)/|V(G)| tends to 0.
- For each c the proof gives infinitely many orders |V(G)|, not every large order.
- Lean checks the statements about cm and h. The consequences about χ, ρ, ρ_d and the clique bound |V(G)|/4 are short
  paper arguments that use published theorems. The paper's estimate of the probability that a random sample works is
  also paper only.
- The paper also gives a second proof route through OpenAI's Colin de Verdière paper. That route has no formal proof and
  depends on unrefereed lemmas of that paper.
- The Lean result is as good as Lean's kernel, Mathlib's definitions and the four copied definitions. `FIDELITY.md`
  explains these definitions.

## Files

- `Challenge/Statement.lean`: the three main statements in Mathlib terms.
- `lean/`: our four Lean modules, the project configuration, `assemble.sh`, the SHA-256 lists and `provenance.diff`.
- `logs/`: build and check logs.
- `paper/alpha2-third.tex`: the paper (LaTeX source).
- `FIDELITY.md`: what the Lean statements mean.
- `LICENSE`, `NOTICE`: Apache License 2.0; the files that contain code from OpenAI's library.

## License

Apache License 2.0 (file `LICENSE`). Our four Lean modules and the statement file contain code copied or adapted from
OpenAI's library, which has the same license; `NOTICE` lists them and the changes. These files are not OpenAI's work, and OpenAI has not reviewed
them. They use the Lean namespace `OAI` only so that they compile next to OpenAI's library.
