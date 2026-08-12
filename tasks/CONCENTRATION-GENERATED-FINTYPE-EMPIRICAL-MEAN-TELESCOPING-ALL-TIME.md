# Generated finite-arm empirical-mean telescoping all-time confidence

Task id: `CONCENTRATION-GENERATED-FINTYPE-EMPIRICAL-MEAN-TELESCOPING-ALL-TIME`
Kind: `lean`
Status: `accepted`
Harness: `hierarchical`

## Goal

On one canonical generated action/reward trajectory, control simultaneously
every positive successor horizon and every arm by replacing the accepted
geometric confidence share with the regret-compatible telescoping share
`delta / ((n+1)*(n+2))`.  This is a Probability producer for a later
horizon-free UCB policy; it is not itself a policy, pull-count, regret, or
anytime-consistency theorem.

## Source

- Paper route: `PPR-AUER-CBF-2002-UCB1`, tail summability spine.
- Existing Lean producers:
  `actionRewardHistoryStepKernelFamily_successorArmEmpiricalMean_abs_tail_random_pullCount_ennreal_delta_trajMeasure_on_horizon`
  and the accepted geometric all-time wrapper.
- Existing schedule precedent: `OFUL.allTimeTelescopingDelta` and
  `OFUL.tsum_ofReal_allTimeTelescopingDelta`; these are local compiled
  precedents, not dependencies of the generic concentration layer.
- Textbook/source cards: `TXT-LATTIMORE-SZEPESVARI-2020`,
  `TXT-BUBECK-CESABIANCHI-2012`.
- Scenario card: `SCN-STOCHASTIC-FINITE`.
- Proof weapons considered: `WEAPON-UCB-OPTIMISM` and
  `WEAPON-TAIL-INEQUALITIES`, inspiration only.

## Lean Target

```lean
Concentration.telescopingConfidenceShare
Concentration.tsum_ofReal_telescopingConfidenceShare
Concentration.measure_iUnion_iUnion_fintype_le_delta_of_telescopingConfidenceShare
ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_successorArmEmpiricalMean_simultaneous_fintype_telescopingAllTime_abs_tail_ennreal_delta_trajMeasure
```

Target file: `BanditRLProof/ConditionalRewardPartialTrajectoryTelescopingAllTime.lean`.

## Proof Obligations

- [x] Natural-language statement is mapped to Lean symbols.
- [x] Required model assumptions are explicit.
- [x] Probability, measurability, concentration, and stopping-time contracts are recorded.
- [x] Reusable theorem cards are identified before proof search.
- [x] Each active leaf has local APIs, intended proof route, and regularity contracts.
- [x] General leaves are classified as `mathlib-candidate`, `project-local`, or `theorem-card-only`.
- [x] `lake build && lake build Tests` passes in the final repository gate.

Accepted status: the schedule module, finite-index adapter, generated terminal,
dedicated conclusion-typed canary, and public Book Map canary compile;
SafeVerify preserves terminal hash `0084164a...f24855`. Independent read-only
review reports no P0--P3, the full repository gate passes, and verified memory
`mem-bf2d4d618cb0e53d` records the exact evidence and assumptions. The
Lean-verified site passes with 531 modules, 6855 declarations, zero
placeholders, 34 highlights, and 36 milestones.

## Mathlib-Ready Leaf Contract

| Leaf | Local APIs/imports | Intended proof route | Regularity contracts | Mathlib status |
| --- | --- | --- | --- | --- |
| telescoping schedule | `Mathlib.Analysis.SpecificLimits.Basic`; existing OFUL schedule proof as precedent | reciprocal telescope, convert `HasSum` through `NNReal` to `ENNReal` | `0 <= delta` for exact sum; `0 < delta` for positive shares | project-local reusable concentration infrastructure |
| finite-arm/countable union | `MeasureTheory.measure_iUnion_le`, `ENNReal.tsum_le_tsum`, existing uniform finite union | specialize generic finite-index scheduled union then rewrite exact tsum | measurable ambient space, finite nonempty index; no event measurability or probability measure | project-local thin wrapper |
| generated producer | accepted random-pull-count empirical-mean fixed-horizon tail | instantiate at horizon `n+1` and share `delta_n/card`, then apply union wrapper on identical `trajMeasure` | probability initial law, finite nonempty Standard Borel arms, measurable context/state/mean, centered kernel law, global variance ceiling, stationary arm means, positive proxy/delta | project-local |

## Retrieval Cards

- LML cards: none used as proof terms.
- Mathlib cards: `MLIB-MEASURE-INTEGRAL`, `MLIB-ORDER-ALGEBRA`,
  `MLIB-ASYMPTOTICS` (placement only for the later consumer).
- Textbook cards: `TXT-LATTIMORE-SZEPESVARI-2020`,
  `TXT-BUBECK-CESABIANCHI-2012`.
- Paper cards: `PPR-AUER-CBF-2002-UCB1`.
- Scenario cards: `SCN-STOCHASTIC-FINITE`.

## Failure Policy

If the reciprocal telescope or ENNReal coercion fails, repair the deterministic
schedule proof without changing the share. If the generated terminal fails,
audit only horizon indexing, positive share/card algebra, or same-measure
unfolding. Do not return to a geometric share, weaken the event, add
independence/event-measurability assumptions, or claim a UCB consumer.

## Trial Logging

```bash
python3 tools/bandit.py trial-log --task CONCENTRATION-GENERATED-FINTYPE-EMPIRICAL-MEAN-TELESCOPING-ALL-TIME --role lower --kind attempt --status running --notes "..."
python3 tools/bandit.py trial-summary
```
