# Proof graph compression, structural novelty audit, and CNG geometry

Task id: `PROOF-GRAPH-COMPRESSION-STRUCTURAL-NOVELTY-CNG`
Kind: `lean-infrastructure`
Status: `partial`
Harness: `hierarchical`

## Goal

Build an auditable environment-extracted proof-dependency graph, conservative
library-aware proof-cost vectors, minimal-support ZDD and proof-hypergraph/MIP
prototypes, and a falsifiable proof-structural novelty protocol.  Validate the
observation layer on unchanged compiled EXP3, half-Tsallis, and OFUL terminals.
Then compile only the route-independent finite algebraic leaves of a candidate
Curvature--Noise--Gap (CNG) abstraction.

This task asks whether target-faithful normalization and compression expose
irreducible proof structure, backward library compression, a Pareto-frontier
shift, and held-out transfer.  Raw new-node count is never an innovation score.

## Frozen Baseline And Source

- Baseline: `origin/main` commit
  `cb5d50be148c691cc595ed9fd2f535c42506fada`.
- Exact frozen graph hash:
  `177233bc84b7f18928f66b1bf95545095d7dd1373f32d7dd2ed286c46bc520c9`.
- Local compiled precursors:
  `TsallisConstrainedQuadraticOptimization`, `TsallisFTRLStationarity`, and
  `TsallisConjugatePotentialStability`.
- Retrieval cards: `MLIB-FINSET-SUMS`, `MLIB-ORDER-ALGEBRA`,
  `MLIB-CONVEX-LINALG`, `MLIB-REAL-RPOW-TSALLIS`.
- External tools are interface/license evidence only; they are not theorem
  evidence.  No source was copied from Lean Atlas or import-graph.

## Exact Lean Target

Target file: `BanditRLProof/CurvatureNoiseGapGeometry.lean`.

Compiled finite-algebra layer:

```lean
CurvatureNoiseGap.tangentPairing_add_const_of_isSimplexTangent
CurvatureNoiseGap.sum_weight_mul_sub_weightedCenter_eq_zero
CurvatureNoiseGap.weightedShiftEnergy_decomposition_of_centered
CurvatureNoiseGap.weightedShiftEnergy_decomposition
CurvatureNoiseGap.weightedShiftEnergy_center_le
CurvatureNoiseGap.weightedShiftEnergy_eq_center_iff
CurvatureNoiseGap.weightedShiftEnergy_add_decomposition
CurvatureNoiseGap.weightedShiftEnergy_add_le_two
```

The target is deliberately not “formalize CNG”, “prove Tsallis-INF”, or “prove
a new bandit theorem”.  It is the finite weighted-shift quotient,
minimizing-shift characterization, and signal--noise algebra needed to test a
future reusable interface.

## Assumption Fence

| Contract | Assumptions | Status |
| --- | --- | --- |
| tangent quotient | finite support and zero-sum direction | compiled |
| weighted residual/decomposition | nonzero total weight | compiled |
| minimizing shift | coordinatewise nonnegative weights and strictly positive total weight | compiled |
| unique minimizing shift | strictly positive total weight | compiled |
| signal--noise identity | finite support only | compiled |
| two-term energy bound | coordinatewise nonnegative weights | compiled |
| full constrained cometric | positive-definiteness/interiority/finite-dimensional chart still to be frozen | planned |

No hidden stochastic, measurability, simplex-interiority, or bandit-model
premise is introduced in the compiled algebra layer.

## Structural-Novelty Contract

The novelty result is a vector, not a scalar:

1. conditional residual motif/hyperedge/obligation/composition signatures;
2. backward compression of frozen proof routes;
3. a non-scalar proof-cost Pareto relation;
4. transfer to a theorem family held out from abstraction design;
5. target novelty reported separately from proof novelty.

The protocol freezes the library at `t`, freezes theorem statements and
assumptions, applies fixed canonicalization/compression, includes retrospective
landmark-versus-incremental cases, held-out transfer, compression and ordering
ablations, and independent human interpretability review.  Neutral grades are
`coverage extension`, `library consolidation`, `new proof route`, `reusable
abstraction`, and `cross-family conceptual compression`.

## Evidence And Status

| Layer | Evidence | Status |
| --- | --- | --- |
| environment type/value dependency export | deterministic Lean exporter and strict validator | compiled exporter / observed graph |
| proof-cost, ZDD, hypergraph, admissible LB, MIP planner | executable Python with focused tests | prototype |
| novelty-vector operations | executable dimension-wise operations with focused tests | prototype |
| EXP3/half-Tsallis/OFUL frozen roots | loaded compiled declarations, theorem bodies unchanged | compiled benchmark roots |
| CNG finite geometry | source plus external focused canary compile | compiled leaves / partial route |
| route-specific subgraph replacement | candidate graph has zero existing-to-CNG dependency edges | not demonstrated; replacement planned |
| backward compression | all three frozen route structural supports remain exactly unchanged | prototype observed no gain |
| proof-cost Pareto shift | structural support is equal, but candidate check time and open obligations were not remeasured | full-vector relation not assessed |
| OFUL held-out transfer | OFUL was held out; its closure contains zero CNG declarations and no obligation was unlocked | prototype observed no transfer |
| CNG proof-structural novelty | criteria not met | proposed, not established |

## Falsifiable CNG Upgrade Rule

CNG counts as evidence for a reusable abstraction only if a compiled,
target-faithful interface replaces multiple audited route-specific subgraphs,
improves the declared library-aware cost vector with a disclosed Pareto
relation, and reduces cost or unlocks an obligation in a frozen held-out theorem
family.  It must survive canonicalization, compression, and ordering ablations
and independent interpretability review.  Merely rephrasing the half-Tsallis
derivation, adding helpers, or helping only design-set routes fails this test.

## Strict Non-Overlap

Do not edit or advance Lattimore--Szepesvari Chapters 13--17, finite-arm lower
bounds, Bernoulli-KL/change-of-measure/minimax/asymptotic lower-bound
declarations, their task/blueprint/retrieval cards, the Textbook Spine pages, or
the other task's active frontier.  If a future candidate file overlaps that
scope, stop writing that file and continue only with orthogonal infrastructure.

## Gates

- [x] Baseline fetched and frozen before mutation.
- [x] Current declaration scanner, teaching dependencies, imports, lifecycle,
  blueprints, Lean environment APIs, tests, CI, and website graph audited.
- [x] Deterministic type/value exporter, strict tests, and documentation exist.
- [x] Fixed EXP3/half-Tsallis/OFUL benchmark, ZDD orders, hypergraph mapping,
  admissible lower bounds, and planning-only MIP contract exist.
- [x] Non-scalar structural-novelty protocol and executable vector operations exist.
- [x] CNG finite algebra and external canary compile without placeholders.
- [x] The current additive-only CNG candidate is compared to the frozen graph and correctly rejected as structural-discovery evidence.
- [ ] Multiple route-specific subgraphs are replaced by CNG.
- [ ] Backward compression and Pareto-frontier shifts are measured.
- [ ] Held-out OFUL transfer is demonstrated.
- [ ] Human interpretability review is complete.
