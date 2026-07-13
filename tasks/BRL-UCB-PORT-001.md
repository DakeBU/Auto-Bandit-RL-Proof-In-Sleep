# Port the UCB regret proof route

Task id: `BRL-UCB-PORT-001`
Kind: `literaturePort`
Status: `activePort`
Harness: `hierarchical`

## Goal

Build a local ABRL route for the finite stochastic UCB regret theorem, starting
from theorem cards and ending in either a compiled local theorem, a documented
import route, or a precise blocked ledger.

## Source

- Repository: [LeanMachineLearning/LML](https://github.com/LeanMachineLearning/LML)
- Upstream declaration: `Bandits.UCB.regret_le`
- Upstream module: `LeanMachineLearning.Online.Bandit.Algorithms.UCB`
- Local surface: `BanditRLProof/Algorithms/UCB.lean`
- Textbook/source cards: `TXT-BUBECK-CESABIANCHI-2012`, `TXT-LATTIMORE-SZEPESVARI-2020`
- Scenario card: `SCN-STOCHASTIC-FINITE`
- Mathlib cards: `MLIB-FINSET-SUMS`, `MLIB-ORDER-ALGEBRA`, `MLIB-REAL-LOG-SQRT`, `MLIB-PROBABILITY-INDEPENDENCE`

## Lean Target

```lean
-- staged targets:
-- BanditRLProof.UCB.obligationNames
-- future local theorem compatible with Bandits.UCB.regret_le
```

## Proof Obligations

- [x] Decide `card-only`, `port`, or `dependency` route: local port with pinned
  LML source evidence; direct LML import remains cross-toolchain work.
- [x] Map UCB index, width, empirical mean, and pull-count definitions through
  `UCB-NATIVE-REAL-HISTORY-INDEX`.
- [x] Record sub-Gaussian tail dependencies and the fixed-sample-count peeling
  law transport used by the pinned theorem.
- [ ] Record expected pull-count bound dependencies.
- [ ] Keep proof export clear that LML is theorem-card status until local closure.

## Mathlib-Ready Leaf Contract

Current leaf classes are recorded in
`proof-obligations/BRL-UCB-PORT-001.md`.  Generic order, algebra, positivity,
summability, and concentration infrastructure should be prepared as Mathlib
candidates.  UCB-specific wrappers should remain thin and should point to
those reusable leaves.  Do not change the proof route without a reviewer-visible
statement, hypothesis, or counterexample audit.

## Build Gate

```bash
python3 tools/bandit.py check
```

## Native Real History Index Leaf

- Leaf id: `UCB-NATIVE-REAL-HISTORY-INDEX`.
- Lean statements: `UCB.realEmpiricalMean`, `UCB.realWidth`, `UCB.realIndex`,
  `UCB.realHistoryWidth`, `UCB.realHistoryIndex`, `UCB.realIndexAction`,
  `UCB.realHistoryIndexAction`, their measurability/maximality theorems, and
  the four finite-pair-history/trace alignment theorems.
- Local APIs/imports: `BanditRLProof.Algorithms.UCB`, `ETCRealHistoryScore`,
  `ETCRealArgmaxTie`, `History.finitePairHistoryOfTrace`,
  `measurable_sumRewards`, `measurable_natCast_pullCount`, Mathlib
  `Real.log`, `Real.sqrt`, and measurable division.
- Proof route: define the actual path-dependent score from
  `sumRewards/pullCount + sqrt(2*c*log(n+1)/pullCount)`; use the inclusive
  history count/sum wrappers with the source's `n+2` convention; transport
  each score coordinate to trace time `n+1`; reuse the least-encoded finite
  argmax for maximality and measurability.
- Regularity contracts: `0 < K` for selector construction, canonical finite
  measurable space for `Fin K`, and timewise measurable action/reward
  coordinates for measurability. No measure, reward law, MGF, independence,
  filtration, count positivity, or tail theorem is assumed.
- Retrieval evidence: pinned LML commit
  `19dc3ab132c2a7539f5944503d1114eac4c5bb74`, `ucbWidth'`, `ucbWidth`,
  `empMean'`, `empMean`, `nextArm`, `measurableArgmax`, and
  `Bandits.UCB.regret_le`; local Mathlib cards `MLIB-REAL-LOG-SQRT`,
  `MLIB-FINSET-SUMS`, and `MLIB-MEASURE-INTEGRAL`.
- Status: `leanCompiled`; focused module and external alignment/measurability
  canaries pass.
- Failure policy: concrete empirical means, the random pull-count width,
  history/trace mapping, least-encoded maximization, and measurability are
  closed. Fixed-count peeling now compiles separately; the next faithful
  blocker is an actual generated-UCB source and canonical stationary arm-stream
  law, followed by one-sided sub-Gaussian tails and expected pull-count
  assembly. Do not force this sample-dependent radius through the older
  deterministic `proxy : Nat -> Arm -> NNReal` interface.

## Fixed-Count Peeling And Stream-Law Leaf

- Leaf id: `UCB-FIXED-COUNT-PEELING-LAW` (`UCB-PEELING-LAW`).
- Lean statements: `UCB.ArmRewardStream`, `UCB.armPrefixSum`,
  `UCB.FixedArmPrefixSource`, its stream/prefix measurability theorems,
  `UCB.measure_pullCount_prod_sumRewards_mem_le_of_fixedArmPrefixSource`, and
  the `_identDistrib` law-transport endpoint.
- Local APIs/imports: `UCBFixedCountPeeling`, `UCBRealHistoryIndex`,
  `pullCount_le_time`, `ProbabilityUnionBound.measure_biUnion_finset_le`,
  `Finset.range`/`filter`/`sum`, `measurable_pi_apply`,
  `Finset.measurable_sum`, and Mathlib `ProbabilityTheory.IdentDistrib`.
- Proof route: record the pathwise identity saying selected rewards from an arm
  are the first `pullCount` values of its latent stream; cover the adaptive
  pair event by the finite union over `k <= n`; apply the outer-measure union
  bound; compose one complete-stream `IdentDistrib` law with each measurable
  fixed prefix sum and rewrite the event measures.
- Regularity contracts: measurable source and canonical spaces, measurable
  latent-stream coordinates, measurable `s : Set (Nat x Real)`, and a
  `DecidablePred` for the projected count filter. No probability-measure,
  independence, MGF, filtration, or positive-count premise is required.
- Retrieval evidence: pinned LML commit
  `19dc3ab132c2a7539f5944503d1114eac4c5bb74`,
  `SumRewards.identDistrib_sum_range_snd`,
  `prob_pullCount_prod_sumRewards_mem_le`, and the two UCB index-tail uses;
  local cards `MLIB-PROBABILITY-INDEPENDENCE`, `MLIB-MEASURE-INTEGRAL`, and
  `MLIB-FINSET-SUMS`.
- Status: `leanCompiled`; focused module build and two external canaries pass.
- Failure policy: generic adaptive-count peeling and complete-stream law
  transport are closed. Do not claim source-faithful UCB tails until the actual
  generated UCB process provides `FixedArmPrefixSource` and an
  `IdentDistrib` law to a canonical stationary/product arm stream, or an
  explicitly recorded conditional-MGF substitute of equivalent strength.
