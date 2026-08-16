# Conversion Window: CNG finite geometry and structural audit

Task id: `PROOF-GRAPH-COMPRESSION-STRUCTURAL-NOVELTY-CNG`

## Natural-Language Target

On a finite support, signals modulo a common scalar shift pair identically with
simplex-tangent directions.  A nondegenerate weighted quadratic energy has the
weighted mean as its unique minimizing common shift, and an additive
signal--noise split has an exact interaction decomposition and a conservative
two-term bound.

This is a candidate reusable algebraic interface.  It becomes structural
discovery evidence only after audited route replacement, non-scalar cost
improvement, and held-out transfer.

## Lean Mapping

| Mathematical object | Lean object | Status |
| --- | --- | --- |
| simplex tangent direction | `CurvatureNoiseGap.IsSimplexTangent` | compiled |
| tangent pairing modulo constants | `tangentPairing`; `tangentPairing_add_const_of_isSimplexTangent` | compiled |
| weighted quadratic after common shift | `weightedShiftEnergy` | compiled |
| optimal common shift | `weightedCenter` | compiled |
| completed square and minimum | `weightedShiftEnergy_decomposition`; `weightedShiftEnergy_center_le` | compiled |
| uniqueness | `weightedShiftEnergy_eq_center_iff` | compiled |
| signal--noise interaction | `weightedShiftEnergy_add_decomposition` | compiled |
| two-term signal--noise bound | `weightedShiftEnergy_add_le_two` | compiled |
| constrained cometric/quotient operator | exact interface not frozen | planned |

## Assumption Ledger

| Assumption | Location | Hidden? |
| --- | --- | --- |
| finite support and decidable equality | all finite-sum declarations | no |
| zero-sum direction | tangent invariance | no |
| nonzero total weight | center residual/decomposition | no |
| positive total weight | minimum uniqueness | no |
| coordinatewise nonnegative weights | minimum and two-term inequality | no |
| probability simplex/interiority | not used in these leaves | no |
| positive-definite constrained cometric | future interface only | unresolved/planned |
| stochastic law/measurability | absent from this algebra layer | no |

## Local Retrieval And Pivot Rule

`TsallisConstrainedQuadraticOptimization` proves route-specific scalar
quadratic bounds; `TsallisFTRLStationarity` uses zero-sum simplex differences;
`TsallisConjugatePotentialStability` contains a route-specific potential
argument.  These are precursors and later candidate consumers, not evidence
that the generic CNG interface already compresses them.

Mathlib supplies `Finset.sum_sub_distrib`, `Finset.sum_mul`,
`Finset.mul_sum`, `Finset.sum_le_sum`, and `sq_nonneg`.  If a future constrained
cometric target requires stronger definiteness or interiority than the source
mathematics, stop and refreeze the target instead of adding an implicit premise.

## Proof DAG And Status

| Node | Dependencies | Gate | Status |
| --- | --- | --- | --- |
| tangent constant invariance | zero-sum direction; finite distributivity | focused source/test | compiled |
| weighted residual | nonzero total weight; field algebra | focused source/test | compiled |
| square completion | weighted residual; ring algebra | focused source/test | compiled |
| minimum/uniqueness | completion; positive total weight | focused source/test | compiled |
| signal--noise identity/bound | ring identity; nonnegative weights | focused source/test | compiled |
| constrained cometric | target/API review | none | planned |
| route replacement | multiple audited consumers | graph before/after | planned |
| held-out transfer | frozen OFUL consumer family | graph/cost/human review | planned |

## Non-Overlap

This window does not own Chapter 13--17, finite-arm lower bounds,
Bernoulli-KL/change-of-measure/minimax/asymptotic lower bounds, their cards,
blueprints, pages, or active frontier.

