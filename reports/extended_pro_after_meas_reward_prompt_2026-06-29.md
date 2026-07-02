# Extended Pro review request after MEAS-REWARD

Repository: `D:\code\Auto-Bandit-RL-Proof-In-Sleep-main\Auto-Bandit-RL-Proof-In-Sleep-main`

Please review the current ABRL Lean formalization state after the `MEAS-REWARD` leaf and recommend exactly one next executable leaf.

## Current goal

Advance the project from deterministic bandit/regret algebra into Mathlib-backed probability foundations, then toward concentration inequalities and complete UCB/ETC/Thompson/EXP3/Tsallis-INF/OFUL/RL theorem routes.

Policy:

- Do not treat theorem cards as local Lean proofs.
- Do not start from broad algorithm theorem statements.
- Pick exactly one executable unfinished leaf.
- Prefer a small Mathlib-backed leaf that compiles locally.
- Avoid importing integration/probability/filtration unless the next leaf genuinely requires it.

## New work completed since your last review

Your last recommendation was:

- keep `MEAS-PULL-INDICATOR` as-is;
- implement `MEAS-REWARD`, specifically selected-reward indicator measurability;
- do not move yet to `EXP-INDICATOR-PULL`, `MEAS-REGRET`, concentration, or UCB/ETC.

I implemented `MEAS-REWARD` in `BanditRLProof/MeasureFoundation.lean`.

Imports remain:

```lean
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import BanditRLProof.Core
```

New theorem:

```lean
theorem measurable_actionTrace_eval_eq_indicator_reward
    {Omega : Type u} {Action : Type v} {Reward : Type w}
    [MeasurableSpace Omega] [MeasurableSpace Action]
    [MeasurableSingletonClass Action]
    [MeasurableSpace Reward] [Zero Reward]
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Reward)
    (haction : forall t : Nat, Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat, Measurable (fun omega : Omega => reward omega t))
    (a : Action) (t : Nat) :
    Measurable
      (({omega : Omega | action omega t = a} : Set Omega).indicator
        (fun omega : Omega => reward omega t)) := by
  exact Measurable.indicator (hreward t)
    (measurableSet_actionTrace_eval_eq action haction a t)
```

Consumer test was added in `Tests/Basic.lean`.

Verification:

```text
lake build BanditRLProof.MeasureFoundation
lake build Tests.Basic
python3 -m py_compile tools\bandit.py
python3 tools\bandit.py reference-index
python3 tools\bandit.py memory-refresh BRL-UCB-PORT-001
python3 tools\bandit.py memory-refresh BRL-ETC-PORT-001
python3 tools\bandit.py check
```

All passed. Full check:

```text
Build completed successfully (837 jobs).
check passed
```

Local retrieval index now reports:

```text
local declarations: 93
LOCAL-LEAF-MEASURE-FOUNDATION declarations:
- measurableSet_actionTrace_eval_eq
- measurable_actionTrace_eval_eq_indicator_const
- measurable_actionTrace_eval_eq_indicator_reward
```

`python3 tools\bandit.py unfinished --status missing-leaf --status theorem-card` no longer lists `MEAS-REWARD`.

Remaining missing/theorem-card leaves include:

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
- `MEAS-REWARD`.

## Questions

1. Is `MEAS-REWARD` reasonable as implemented, or should its statement be adjusted before building on it?
2. What is the single best next executable leaf now?
3. Should the next move be a finite-sum measurability leaf for selected reward sums, `MEAS-REGRET`, `EXP-INDICATOR-PULL`, or a history/policy measurability leaf?
4. Please provide the exact Lean-facing statement shape, imports/APIs to probe, proof route, regularity contracts, status classification, and failure policy.

Please keep the recommendation focused on one local Lean leaf and a minimal batch before asking again.
