# Book Map Chapters 5--6 canonical completion

Task id: `BOOKMAP-CHAPTERS-5-6-CANONICAL-COMPLETION`  
Kind: `lean`  
Status: `accepted`  
Harness: `hierarchical`

## Goal

Promote two independent Book Map gates only after an external typed canary and
the full repository gate verify their exact local textbook scopes:

- `CH5-OFUL-CANONICAL-COMPLETION`;
- `CH6-THOMPSON-STATIONARY-CANONICAL-COMPLETION`.

One gate never implies the other.  The joint task is accepted only when both
are accepted.

## Source placement

- Chapter 5: `TXT-LATTIMORE-SZEPESVARI-2020`,
  `PPR-ABBASI-YADKORI-2011-SELF-NORMALIZED`,
  `PPR-LI-CHU-LANGFORD-SCHAPIRE-2010-LINUCB`, `SCN-LINEAR-GLM`, and
  inspiration-only `WEAPON-SELF-NORMALIZED-OFUL`.
- Chapter 6: `TXT-SLIVKINS-2019-2024`,
  `TXT-LATTIMORE-SZEPESVARI-2020`, `PPR-AGRAWAL-GOYAL-2011-TS`,
  `SCN-STOCHASTIC-FINITE`, `SCN-BAYESIAN-POSTERIOR`, and
  inspiration-only `WEAPON-POSTERIOR-SAMPLING`.
- LML cards `LML-TS-POSTERIOR-ACTION` and `LML-TS-BAYES-REGRET` are source
  evidence only.  No upstream symbol is imported by this task.

## Chapter 5 completion definition

The scoped canonical model has finite nonempty actions, finite-dimensional
real features, scalar rewards, a linear mean, positive ridge regularization,
and an explicit centered conditional sub-Gaussian reward law.  Completion
requires the traceable local chain:

1. regularized Gram matrix, positive definiteness, and inverse interfaces;
2. rank-one determinant update;
3. log-determinant telescope;
4. elliptical-potential inequality;
5. fixed-direction conditional MGF;
6. Gaussian-mixture/self-normalized confidence;
7. ridge confidence ellipsoid;
8. regularization bias;
9. finite-action optimistic score;
10. measurable strict-fold optimistic selection;
11. concrete generated history policy and trajectory law;
12. `CanonicalLinearSubgaussianEnvironmentLaw` producing the residual law;
13. one horizon-free telescoping policy with all-time confidence;
14. all-horizon high-probability pseudo-regret on that trajectory measure;
15. finite-horizon expected pseudo-regret;
16. fixed-model expected-average consistency;
17. bounded stopping-time consumption;
18. square-integrable finite, possibly unbounded, stopping-time expected regret.

The key terminal surface is
`OFUL.telescopingCanonicalStandardHighProbabilityPseudoRegret_nonneg_and_allHorizon_tail_le_explicitBound_of_linearSubgaussianEnvironment_of_featureBound_le_regularization`.
The all-time, all-horizon, bounded-stopping, and square-integrable stopping
endpoints use the same horizon-free telescoping policy.  The expected-average
endpoint is also typed in the canary but is explicitly a separate
horizon-indexed fixed-model policy family whose confidence level is scheduled
as a function of the queried horizon.

## Chapter 6 completion definition

The scoped canonical model has a probability prior, Standard Borel nonempty
environment, finite nonempty actions, stationary Markov real reward kernel,
measurable best-action selector with the explicit pointwise contract
`IsOptimalMeanSelector mean bestAction`, a bounded mean surface, centered
sub-Gaussian rewards, and nonzero variance proxy.  Completion requires:

1. prior/likelihood posterior kernel;
2. posterior equals the environment conditional law;
3. posterior best-action pushforward;
4. canonical one-step sampler;
5. action conditional-law identity;
6. non-circular recursive Thompson history algorithm;
7. successor action probability matching on its actual generated history;
8. finite-history score expectation transport;
9. Bayesian mean-regret decomposition;
10. measurable bounded clipped-UCB score;
11. stationary latent arm-stream producer;
12. a.e. generated-reward/stream support identity;
13. upper and lower empirical-mean confidence events;
14. selected- and best-action clipped-score expectation bounds;
15. the stationary generated-trajectory terminal

`E[R_n^Bayes] <= (2K + 1)(u - l) + 8 sqrt(sigma^2 K n log n)`.

The dedicated canary instantiates this endpoint with a concrete one-arm
stationary Gaussian Markov reward kernel, rather than only printing its type.

## Acceptance checklist

- [x] Required local declarations exist on the current Lean 4.29.1 toolchain.
- [x] `Tests/BookMapChaptersFiveAndSixCanary.lean` contains all six requested groups.
- [x] Chapter 5 all-time/all-horizon/expected/stopping terminals have typed applications.
- [x] Chapter 6 probability matching is typed on the actual recursive generated history.
- [x] Chapter 6 final stationary regret is concretely instantiated.
- [x] Chapter 6 terminal requires and the concrete canary proves pointwise mean optimality.
- [x] Focused dedicated canary build passes; audited axioms are baseline only.
- [x] Independent review record has no unresolved P0--P3.
- [x] Chapter, result, highlight, diagram, README, and overview surfaces are synchronized.
- [x] Lifecycle/retrieval/frontier/manifest surfaces are synchronized.
- [x] Full `python3 tools/bandit.py check` and website gates pass.

## Nonclaims and extensions

Chapter 5 completion does not include contextual/time-varying action sets,
dynamic linear bandits, sharp/minimax constants, uniform-over-parameter or
infinite-dimensional results, arbitrary history environments without a
centered conditional-MGF producer, pathwise/almost-sure/universal optional
stopping, or a full BwK theorem.  Forced-budget schedules are not called BwK.

Chapter 6 completion does not include nonstationary, contextual, or linear
Thompson sampling; PSRL; arbitrary user-supplied posteriors without law
producers; sharp problem-dependent/asymptotic constants; or literal upstream
LML identity.  `BRL-TS-BAYES-001` remains separate.

## Failure policy

If either child gate fails, keep that chapter partial and record the exact
declaration, current compiler goal, regularity contract, retrieval evidence,
and next smallest bridge.  Do not add a hypothesis equivalent to the target,
weaken the terminal, substitute an independent trajectory, or promote an LML
card/proof weapon as a local proof.
