# Proof Obligations: Book Map Chapters 7--8 canonical completion

Task id: `BOOKMAP-CHAPTERS-7-8-CANONICAL-COMPLETION`

| Node | Target | Local APIs/imports | Regularity | Gate | Status |
| --- | --- | --- | --- | --- | --- |
| `CH7-POTENTIAL-MOMENTS` | potential/Hedge, IW support, conditional first/second moments, generated trajectory and predictable transport | `Exp3HedgeRegret`, `Exp3ImportanceWeighted`, `Exp3PredictableMoments` | finite nonempty decidable actions; positive `eta,gamma`; probability prior; predictable unit loss | named checks and axioms | accepted |
| `CH7-TUNED-FIXED-WINDOW` | tuned expected and per-horizon best-arm realized tail with each law kept explicit | `Exp3ExpectedRegret`, `Exp3MixedSquareBernsteinRealizedBestArmAllHorizon` | `K>=2`; positive horizon; scale and delta contracts; comparator membership | full-conclusion typed applications | accepted |
| `CH7-SAME-PROCESS-SPARSE` | exact decomposition plus predictable/deviation/all-regret geometric events; separately sparse terminal | `Exp3PredictableRegretAllTime`, `Exp3RealizedDeviationAllTime`, `Exp3RealizedRegretAllTime`, sparse all-horizon module | fixed `eta,gamma,loss,comparator` across prefixes; explicit sparse-failure probability | full-conclusion typed applications | accepted |
| `CH7-EXP3-CANONICAL-COMPLETION` | all 12 scoped nodes and public import graph | three nodes above | no horizon-free/tuned-CS overclaim | full repository/site gates | accepted |
| `CH8-FTRL-REGULARITY` | finite-simplex half-Tsallis minimizer existence/interiority/uniqueness/measurability and one-step stability | `TsallisFTRLMinimizer*`, `TsallisFTRLOneStepStability` | finite nonempty decidable actions; positive rate; unit losses | named checks and axioms | accepted |
| `CH8-GENERATED-STABILITY` | scheduled generated action law, score alignment, stability/penalty, all-rate expected regret, self-bound | `TsallisScheduledRecursiveTrajectory`, `TsallisScheduledScoreAlignment`, `TsallisScheduledExpectedRegret`, `TsallisScheduledFixedGapSelfBounding` | Standard Borel probability environment; positive nonincreasing schedule; predictable unit loss; supported comparator | exact generated-law checks and typed terminal | accepted |
| `CH8-IID-FINAL` | concrete bounded finite-arm IID reward-law generated logarithmic regret | `TsallisFiniteArmIIDRewardLaw` | positive finite model; probability laws; a.e. unit support; exact means; positive non-best gaps; nonnegative corruption allowance | nondegenerate `Fin 2` full-conclusion typed application | accepted |
| `CH8-TSALLIS-FTRL-CANONICAL-COMPLETION` | all 14 scoped nodes and public import graph | three nodes above | no paper-sharp/BOBW/dynamic overclaim | full repository/site gates | accepted |
| `ROOT` | both independent child gates plus review/lifecycle/site/GitHub synchronization | repository harness | one child cannot discharge the other | every local acceptance command; remote delivery verified externally | accepted |

## Reviewer checklist

- The EXP3 tuned and fixed-window statements visibly rebuild their law from the
  queried horizon; neither is described as a fixed-policy anytime theorem.
- The EXP3 all-positive-prefix terminal preserves one exact
  `sampledImportanceWeightedTrajectoryKernel` and one comparator.
- The sparse theorem retains `epsilon` and the sparsity-failure premise.
- The Tsallis selector and action law are those used by the regret terminal's
  exact `let` chain; no independent sample model is substituted.
- The IID reward-law producer supplies probability, support, and mean/gap
  transport; the canary does not assume the regret conclusion.
- Corruption/drift/restart, paper-sharp constants, and refined-obstruction
  branches remain extensions rather than hidden completion premises.
- Audited terminals use no `sorry`, `admit`, or new axioms.

## Failure classification

Record the first exact failure as stale declaration/import, source/measure
misalignment, missing measurability/support/integrability contract, theorem
target drift, website overclaim, review rejection, or full-gate failure.  Do
not weaken either child target.
