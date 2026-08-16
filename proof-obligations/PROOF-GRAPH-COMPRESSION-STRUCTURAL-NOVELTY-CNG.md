# Proof Obligations: proof graph compression, structural novelty, and CNG

Task id: `PROOF-GRAPH-COMPRESSION-STRUCTURAL-NOVELTY-CNG`

| Node | Target | Dependencies | Proof route | Regularity/faithfulness contract | Status |
| --- | --- | --- | --- | --- | --- |
| `ENV-EXPORT` | exact project-owned direct type/value dependency graph | compiled `BanditRLProof.olean`; Lean `Environment` | traverse constants and expression occurrences; deterministic JSON | environment-extracted, not an elaborator trace or kernel trace | compiled |
| `COST-VECTOR` | library-aware nonnegative Pareto cost record | exact graph; fixed roots | shared fixed charge once; reuse separate; semantic SCC DAG | correctness and target faithfulness are hard gates | prototype |
| `ZDD-SUPPORT` | compressed family of minimal supports | fixed declaration universe | explicit baseline then zero-suppressed unique table | dependent proof state stays outside | prototype |
| `HYPERGRAPH-LB` | concrete completion mapping and admissible LB | support alternatives; nonnegative charges | enumerate mapping; max-single/disjoint-pack lower bounds | call pruning safe only if `LB(s) <= OPT_remaining(s)` | prototype |
| `NOVELTY-VECTOR` | five-part non-scalar structural audit | frozen library; fixed canonicalization | residual, backward, Pareto, held-out, target/proof split | raw node count forbidden as innovation metric | prototype, no result |
| `TANGENT-QUOTIENT` | constant shifts vanish on zero-sum directions | `Finset.sum_add_distrib`, `mul_sum` | finite algebra | zero-sum direction explicit | compiled |
| `MIN-SHIFT` | weighted center, completion of square, minimum, uniqueness | `sum_sub_distrib`, `sum_mul`, field/ring algebra | weighted residual then exact decomposition | nonzero/positive total weight explicit; nonnegative weights where needed | compiled |
| `SIGNAL-NOISE` | exact interaction identity and two-term energy bound | ring identity; `sq_nonneg`; `sum_le_sum` | pointwise algebra then finite sum | nonnegative weight required only for inequality | compiled |
| `CONSTRAINED-COMETRIC` | reusable quotient/cometric interface | compiled finite algebra | freeze exact operator and positivity target before proof | finite dimensionality, definiteness, and interiority unresolved | planned |
| `ROUTE-REPLACEMENT` | replace several frozen route-specific subgraphs | constrained cometric; audited consumers | reversible before/after proof graph comparison | no target weakening or hidden assumption strengthening | planned |
| `HELDOUT-TRANSFER` | lower proof cost for a frozen held-out theorem family | route replacement; OFUL held out from design | reconstruct without using held-out result during design | disclose all cost dimensions and open obligations | planned |

## Safe-Lower-Bound Argument

Every concrete completion chooses at least one support alternative for each
obligation.  Mapping the union vertices and the chosen alternatives to one
satisfies the relaxed cover/link constraints.  With nonnegative fixed charges,
each per-obligation minimum bundle is no larger than any completion; their
maximum is admissible.  Minimum bundles may be summed only for obligations
whose complete alternative universes are pairwise disjoint.  Focused tests
enumerate this mapping and check both reported lower bounds against the exact
small optimum.

## Novelty Failure Classification

- No residual signature: `coverage extension` may still have target value.
- Backward compression only: candidate may be `library consolidation`.
- New irreducible route without held-out reuse: `new proof route`.
- Backward and held-out gains after review: candidate may be `reusable abstraction`.
- Cross-family backward and held-out compression: candidate may be
  `cross-family conceptual compression`.

These are neutral audit labels, not quality judgements about authors or peers.

## Evidence Boundary

The finite CNG algebra is compiled.  The full calculus, constrained cometric,
route replacement, Pareto shift, held-out transfer, Tsallis-INF, and any new
bandit theorem are not complete.  No Chapter 13--17 or lower-bound artifact is
owned or mutated by this task.

