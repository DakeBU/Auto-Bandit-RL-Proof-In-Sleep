# Proof Obligations: Book Map Chapters 5--6 canonical completion

Task id: `BOOKMAP-CHAPTERS-5-6-CANONICAL-COMPLETION`

| Node | Target | Local APIs/imports | Regularity | Gate | Status |
| --- | --- | --- | --- | --- | --- |
| `CH5-GEOMETRY-CONFIDENCE` | elliptical potential through self-normalized ridge confidence | `OFULEllipticalPotential`, `OFULSelfNormalizedConfidence`, `OFULConfidenceEllipsoid` | finite features, positive ridge/noise scale, conditional MGF/adaptation contracts | required declarations and axiom report | compiled canary |
| `CH5-GENERATED-ALL-HORIZON` | one horizon-free policy, producer-generated all-time confidence, all-horizon regret on identical trajectory measure | `OFULScheduledAllTimeConfidence`, `OFULScheduledAllHorizonHighProbabilityRegretRate` | finite actions/features, centered sub-Gaussian environment law, feature bound and optimal arm | full-conclusion typed applications | compiled canary |
| `CH5-EXPECTED-STOPPING` | separate horizon-indexed fixed-model expected consistency plus bounded and square-integrable finite stopping consumers for the horizon-free telescoping policy | `OFULExpectedRegretConsistency`, `OFULScheduledBoundedStoppingTimeExpectedRegret`, `OFULScheduledUnboundedStoppingTimeExpectedRegretExactMoment` | expected consistency uses confidence `1/(horizon+1)^2`; both stopping consumers use the telescoping policy/source; canonical filtration; bounded horizon or a.e. finite, integrable rounds, finite second moment | full-conclusion typed applications | compiled canary |
| `CH5-OFUL-CANONICAL-COMPLETION` | all 18 scoped nodes and public import graph | three nodes above plus existing finite expected/bounded stopping modules | no scope inflation | full repository and website gates | accepted |
| `CH6-POSTERIOR-PROBABILITY-MATCHING` | successor action conditioned on its own generated finite history equals posterior-best action law | `PosteriorKernel`, `ThompsonCanonicalSampler`, `ThompsonRecursiveSampler` | probability prior, Standard Borel/nonempty types, finite nonempty arms, measurable selector | actual-history typed application | compiled canary |
| `CH6-DECOMPOSITION-CONCENTRATION` | Bayes decomposition, clipped bridge, latent-stream support and two confidence integrals | `ThompsonBayesRegretDecomposition`, `ThompsonClippedUCBScore`, `ThompsonStationaryReward` | measurable bounded mean, Markov source, centered sub-Gaussian MGF, nonzero proxy | declarations and axiom report | compiled canary |
| `CH6-STATIONARY-FINAL` | concrete stationary generated-trajectory Bayesian regret endpoint | `IsOptimalMeanSelector`, `stationaryLatentArmStreamCanonicalTrajectoryMeasure_integral_trajectoryBayesMeanRegret_le` | one-arm Unit environment, `gaussianReal 0 1`, Markov const kernel, zero mean, explicitly proved pointwise mean-optimal selector | concrete theorem application | compiled canary |
| `CH6-THOMPSON-STATIONARY-CANONICAL-COMPLETION` | all 15 scoped nodes and public import graph | three nodes above | no universal/posterior/LML overclaim | full repository and website gates | accepted |
| `ROOT` | both independent child gates plus review/lifecycle/site synchronization | repository harness | one child cannot discharge the other | all acceptance commands | accepted |

## Reviewer checklist

- `finiteHistoryTelescopingScalarRidgeOptimisticAlgorithm` has no horizon
  parameter, and the exact same constructor arguments feed confidence,
  all-horizon regret, and stopping measures.
- `CanonicalLinearSubgaussianEnvironmentLaw` is a real kernel-law producer,
  not a proposition that stores the desired tail/regret conclusion.
- The stopping canary retains `IsStoppingTime` and
  `SquareIntegrableFiniteStoppingTime`; docs name the a.e.-finite,
  integrability, and second-moment content.
- Thompson matching conditions the actual successor action on the finite
  history extracted from the actual recursive trajectory measure.
- The concrete stationary example builds a Markov Gaussian kernel and proves
  its centered MGF; it does not assume the terminal conclusion.
- The final bound and all assumptions match the Lean signature exactly.
- `trajectoryBayesMeanRegret` is comparator-relative algebra in isolation; the
  stationary Bayesian-regret terminal additionally requires the explicit
  pointwise `IsOptimalMeanSelector` contract.
- No theorem card, proof weapon, local reconstruction, or nearby `#check` is
  described as literal LML declaration identity.

## Failure classification

Record the first exact failure as a stale declaration/import, source/measure
misalignment, missing measurability/Markov/MGF/finite-stopping contract,
concrete-kernel typeclass bridge, theorem target drift, website overclaim,
review rejection, or full-gate failure.  Do not weaken either child target.
