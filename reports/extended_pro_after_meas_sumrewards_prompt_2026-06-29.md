# Extended Pro review request after MEAS-SUMREWARDS

Repository: `D:\code\Auto-Bandit-RL-Proof-In-Sleep-main\Auto-Bandit-RL-Proof-In-Sleep-main`

Please review the current ABRL Lean formalization state after the local `sumRewards` measurability bridge and recommend exactly one next executable leaf.

## Current goal

Advance the project from deterministic bandit/regret algebra into Mathlib-backed probability foundations, then toward concentration inequalities and complete UCB/ETC/Thompson/EXP3/Tsallis-INF/OFUL/RL theorem routes.

Policy:

- Do not treat theorem cards as local Lean proofs.
- Do not start from broad algorithm theorem statements.
- Pick exactly one executable unfinished/local leaf.
- Prefer a small Mathlib-backed leaf that compiles locally.
- Avoid probability measures, expectation, filtration, or concentration unless the next leaf genuinely needs them.

## New work completed since your last review

Your last recommendation was:

- accept `MEAS-SELECTED-REWARD-FINITE-SUM` as-is;
- implement `MEAS-SUMREWARDS`;
- use a new file `BanditRLProof/MeasurableLocalQuantities.lean`;
- connect `measurable_finset_sum_indicator_reward` to the local recursive quantity `sumRewards`;
- use `sumRewards_eq_finset_filter_sum` and `Finset.sum_indicator_eq_sum_filter`;
- do not move yet to `MEAS-REGRET`, expectation, probability measures, or filtration.

I implemented it.

New file:

```lean
import Mathlib.Algebra.BigOperators.Group.Finset.Indicator
import BanditRLProof.MeasurableSums
import BanditRLProof.MathlibWrappers
```

Important implementation detail:

- The theorem uses `{Action : Type v} {Reward : Type v}` rather than separate universes.
- This is intentional because the existing compiled wrapper `sumRewards_eq_finset_filter_sum` currently has `Action` and `Reward` in the same universe.

New theorem:

```lean
theorem measurable_sumRewards
    {Omega : Type u} {Action : Type v} {Reward : Type v}
    [MeasurableSpace Omega] [MeasurableSpace Action]
    [MeasurableSingletonClass Action]
    [MeasurableSpace Reward] [AddCommMonoid Reward] [MeasurableAdd₂ Reward]
    [DecidableEq Action]
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Reward)
    (haction : forall t : Nat, Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat, Measurable (fun omega : Omega => reward omega t))
    (a : Action) (n : Nat) :
    Measurable
      (fun omega : Omega => sumRewards (action omega) (reward omega) a n)
```

The proof:

1. Uses `measurable_finset_sum_indicator_reward` on `Finset.range n`.
2. Uses a private helper:

```lean
sumRewards_eq_finset_range_indicator_reward
```

to prove pointwise equality from:

```lean
sumRewards_eq_finset_filter_sum
Finset.sum_indicator_eq_sum_filter
```

3. Rewrites the local recursive `sumRewards` function to the measurable selected-reward indicator finite sum.

Root import:

```lean
import BanditRLProof.MeasurableLocalQuantities
```

Consumer test added in `Tests/Basic.lean`.

Verification:

```text
lake build BanditRLProof.MeasurableLocalQuantities
lake build Tests.Basic
python3 -m py_compile tools\bandit.py
python3 tools\bandit.py reference-index
python3 tools\bandit.py memory-refresh BRL-UCB-PORT-001
python3 tools\bandit.py memory-refresh BRL-ETC-PORT-001
python3 tools\bandit.py check
```

All passed. Full check:

```text
Build completed successfully (1703 jobs).
check passed
```

Local retrieval index:

```text
local declarations: 95
LOCAL-LEAF-MEASURE-FOUNDATION:
- measurableSet_actionTrace_eval_eq
- measurable_actionTrace_eval_eq_indicator_const
- measurable_actionTrace_eval_eq_indicator_reward

LOCAL-LEAF-MEASURABLE-SUMS:
- measurable_finset_sum_indicator_reward

LOCAL-LEAF-MEASURABLE-LOCAL-QUANTITIES:
- measurable_sumRewards
```

`python3 tools\bandit.py unfinished --status missing-leaf --status theorem-card` no longer lists `MEAS-SUMREWARDS`.

Remaining unfinished/theorem-card rows include:

- `MEAS-HISTORY`
- `MEAS-POLICY`
- `MEAS-REGRET`
- `EXP-INDICATOR-PULL`
- `EXP-REGRET-PULLCOUNT` theorem-card only
- `KERNEL-POLICY-BIND`
- `COND-EXPECT-REWARD`
- `POSTERIOR-KERNEL`
- `TS-PROB-MATCH` theorem-card only
- `FILTRATION-HISTORY`
- `ADAPTED-ACTION`
- `MART-DIFF-REWARD`
- `STOPPING-TIME-BUDGET`
- `TAIL-SUMMABILITY-UCB`
- FTRL/EXP3/Tsallis/OFUL leaves

## Existing compiled foundation

- deterministic finite-prefix/list bridges;
- `PULLCOUNT-FINSET`;
- `SUMREWARDS-FINSET`;
- `PSEUDOREGRET-FINSET`;
- `REGRET-PULLCOUNT`;
- `PULLCOUNT-SUM-TIME`;
- `MEAS-FIN-ACTION`;
- `MEAS-PULL-INDICATOR`;
- `MEAS-REWARD`;
- `MEAS-SELECTED-REWARD-FINITE-SUM`;
- `MEAS-SUMREWARDS`.

## Questions

1. Is `MEAS-SUMREWARDS` reasonable as implemented, especially the same-universe `Action`/`Reward` contract inherited from `MathlibWrappers`?
2. What is the single best next executable leaf now?
3. Should the next step be `MEAS-REGRET`, a pseudo-regret measurability bridge, `EXP-INDICATOR-PULL`, or a first expectation canary?
4. Please provide the exact Lean-facing statement shape, imports/APIs to probe, proof route, regularity contracts, status classification, and failure policy.

Please keep the recommendation focused on one local Lean leaf and a minimal batch before asking again.
