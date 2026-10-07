# OpenAI Math assimilation protocol for BanditRLlib / ABRL

Status: active intake protocol, 2026-10-07.

This protocol governs the use of `openai/math` inside BanditRLlib. It is
deliberately conservative: the current OpenAI Math snapshot contains no direct
Lean cluster whose primary subject is multi-armed bandits or reinforcement
learning. Therefore this intake must strengthen ABRL's shared mathematics and
adjacent online-decision routes without relabelling unrelated theorems as
bandit/RL results.

## 1. Pinned upstream and negative-scope fact

Reviewed snapshot:

- repository: `openai/math`;
- commit: `adc7f1241b42e322a6451854ab7e4b4c146bf78a`;
- release date: 2026-10-06;
- upstream formalization license: Apache-2.0.

Searches of this snapshot find no direct `bandit` or `reinforcement learning`
Lean route. This absence is part of the intake record. Do not manufacture a
mapping from a keyword match such as “regret” to ABRL.

In particular, the edit-distance approximation files containing the word
`Regret` are not online-learning regret and are `out-of-scope` unless a
specific source-independent lemma is later shown to have a genuine ABRL
consumer.

## 2. Intake classes

Every candidate is classified as one of:

- `canonical-leaf`: generic probability, information, optimisation, martingale,
  matrix, or measurable-policy lemma with real ABRL consumers;
- `adapter-backed`: reusable theorem stated in a different experiment/kernel/
  information model and admitted through an explicit semantic adapter;
- `adjacent-route`: prophet/secretary/online-selection or game-theoretic route
  that is worth teaching/formalizing but is not called a bandit theorem;
- `benchmark-only`: useful source for future lower-bound or information
  machinery;
- `out-of-scope`.

Default: `benchmark-only`.

## 3. Core semantic rule

For every promoted item record separately:

1. source/preprint statement;
2. exact upstream Lean statement;
3. local ABRL statement;
4. source-blind reconstruction;
5. independent source review.

The adapter audit must identify the experiment:

- what is latent;
- what is observed and when;
- what the learner may adapt to;
- which randomness belongs to the environment versus learner;
- filtration/history semantics;
- stopping/horizon convention;
- loss/reward sign convention;
- information available before action selection;
- budget/resource constraint;
- performance criterion and comparator.

A theorem about a static Gaussian experiment, secretary arrival model, memory
stream, or Boolean channel cannot silently become a sequential bandit theorem.

The repository-wide invariant remains:

> proof ingredient = dependency edge; source hypothesis = theorem binder.

## 4. Priority A: online selection — Matroid Prophet and Matroid Secretary

### Matroid Prophet

Upstream:
`OAI/Probability/MatroidProphet`, with
`Main.lean` blob SHA `cfd8c1eb2df52f9085b7dbeb8d3f3f49726e66e1`.

The current source-facing endpoint includes a hidden-vector guarantee and a
one-sample challenge theorem built from matroid feasibility, rounding,
thinning/filtering, conditional payoff analysis, and randomized seed laws.

This should be an **adjacent online-decision route**. It can share with ABRL:

- measurable randomized decision rules;
- product/random-seed models;
- conditional expectations and payoff accounting;
- stopping/selection feasibility;
- comparison to an offline optimum;
- one-sample versus hidden-vector reductions.

Do not call its competitive ratio “bandit regret”. If a shared lemma is reused,
its local name and statement should avoid source-specific prophet terminology.

### Matroid Secretary

Upstream:
`OAI/Probability/MatroidSecretary`.

Its graph contains precommitted sampling kernels, finite seed theorems,
integrability, replay/relabelling, thinning, independence/accounting, hidden
vectors, density comparison, and secretary selection structure.

Admit it as a separate secretary/online-selection textbook route. Shared
measurability, finite-seed, conditional-law, and accounting primitives may move
to a technical layer when they have ABRL consumers.

## 5. Priority B: information contraction and noisy observations

### BooleanNoise / SoftChannel

OpenAI's Boolean-noise and soft-channel developments contain finite-channel
mutual information, noise kernels, information contraction/attainment, entropy
production, and sharp Boolean information inequalities.

These are promising substrates for:

- information-theoretic bandit lower bounds;
- noisy-feedback models;
- data-processing/contraction steps;
- information-ratio analyses;
- observation-channel comparisons.

They are **not** automatically ABRL lower bounds. To become one, add a local
adapter from the ABRL history/observation kernel to the precise finite channel
and prove the information quantity is the same one used by the target theorem.

When the same primitive is useful to QuantumComputinglib, prefer a
source-independent mathematical statement or an explicitly owned cross-library
adapter rather than three duplicated definitions.

## 6. Priority B: Gaussian experiment and memory lower-bound machinery

Candidate clusters include:

- `OAI/Probability/GaussianInformation`;
- `OAI/Probability/GaussianRegression`;
- `OAI/Probability/MemoryPrecision`;
- related Gaussian replacement/projection/posterior-replica modules after
  individual audit.

The Gaussian-regression main route proves memory lower bounds for a sequential
observation/learner model. The memory-precision route contains kernel-policy,
success-probability, Gaussian/spherical geometry, measurable-test, density, and
stream lower-bound machinery.

Potential ABRL consumers:

- linear-bandit lower-bound infrastructure;
- finite-information/memory-constrained learners;
- adaptive experiment lower bounds;
- transcript compression and indistinguishability;
- Gaussian design/observation models.

Admission must be **lemma-first**. Do not port an entire regression theorem and
rename it a linear-bandit lower bound. The missing step is generally the
experiment reduction; that reduction must itself be a proved ABRL edge.

A natural local target is a future shared technical layer for
`experiment -> transcript -> test/information -> success/regret lower bound`,
with each application supplying its own reduction.

## 7. Priority C: stochastic games and RL-adjacent sources

OpenAI Math includes current work on stochastic/game-theoretic problems,
including a turn-based stochastic mean-payoff-games preprint. These are
`benchmark-only` until the following are matched to the ABRL RL API:

- state/action spaces;
- transition kernels;
- policy class;
- reward/mean-payoff objective;
- finite versus infinite horizon;
- discounted versus average reward;
- adversarial player semantics;
- measurability and strategy randomization.

A stochastic game is not an MDP merely because both have states and
transitions. Any bridge must expose exactly which player or adversary is fixed,
optimized, or quantified over.

## 8. Explicitly rejected lexical mappings

The following patterns must not create graph nodes by keyword alone:

- edit-distance `Regret` files -> bandit regret;
- generic `Policy` -> RL policy;
- generic `Reward` -> bandit reward;
- Markov-chain mixing -> RL convergence;
- information-theory contraction -> regret bound;
- optimisation theorem -> online-learning theorem.

Such material may still contribute a canonical leaf after a real consumer and
semantic proof are identified.

## 9. Cross-library ownership

### Quantum bandits / quantum RL

Follow `docs/quantum-bandit-cross-library-protocol.md`.

Quantum states, channels, POVMs, circuit/oracle semantics, and quantum query
notions are owned by QuantumComputinglib/ASPBE and its audited adapters.
BanditRLlib owns the sequential decision/regret skeleton. An OpenAI quantum
theorem should first be assimilated on the quantum side, then consumed through a
reviewed cross-library boundary.

### Sampling and MCMC

Samplinglib owns generic sampling/mixing/SDE foundations. ABRL may reuse a
source-independent Markov/probability lemma, but should not import a sampling
paper route merely because an RL algorithm contains a Markov chain.

## 10. Graph contract

OpenAI-derived ABRL additions must distinguish:

- local compiled Lean dependencies;
- source correspondence;
- proved adapters/reductions;
- adjacent routes;
- dashed conceptual mirrors.

Candidate conceptual families:

- `family:online-selection-vs-offline-optimum`;
- `family:information-contraction-under-observation`;
- `family:experiment-transcript-test-lower-bound`;
- `family:finite-random-seed-policy`;
- `family:resource-constrained-learning`.

A family is not a theorem. Every bridge records hypothesis map, conclusion map,
source IDs, candidate Lean substrates, and failure boundary.

## 11. Recommended local placement

When implementation begins:

- generic source-independent leaves should live in a small technical module with
  at least two genuine consumers;
- prophet/secretary statements should live in clearly named adjacent-route
  modules rather than under classical bandit algorithms;
- information-channel adapters should sit next to the ABRL observation/history
  models they connect;
- Gaussian/memory lower-bound machinery should be factored below application
  theorems;
- cross-library quantum adapters should remain explicit boundary modules.

Do not create a large `OpenAIMath.lean` import surface.

## 12. CI and publication gate

An OpenAI-derived ABRL contribution is publishable only with:

- pinned upstream commit/path/SHA and license record;
- source anchor;
- upstream statement seal;
- local statement seal;
- experiment/feedback-model diff;
- reuse decision;
- local Lean evidence;
- source-blind reconstruction and independent review;
- route classification (`bandit`, `RL`, or explicitly `adjacent`);
- Lean/Overview/Functor graph deltas;
- reader-facing natural-language + formula + Lean correspondence;
- remaining red boundary.

The contribution manifest must make it impossible for an adjacent theorem to
silently count toward a bandit/RL route completion badge.

## 13. Upstream updates

Do not track OpenAI `main` implicitly. A newer upstream commit requires a diff
against this pin, semantic-change classification, and re-audit of every admitted
adapter or source statement whose dependency closure changed.
