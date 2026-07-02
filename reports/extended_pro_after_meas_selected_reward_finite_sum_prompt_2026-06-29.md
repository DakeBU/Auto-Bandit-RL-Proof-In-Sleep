# Extended Pro review request after MEAS-SELECTED-REWARD-FINITE-SUM

Repository: `D:\code\Auto-Bandit-RL-Proof-In-Sleep-main\Auto-Bandit-RL-Proof-In-Sleep-main`

Please review the current ABRL Lean formalization state after the finite-sum measurability leaf and recommend exactly one next executable leaf.

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

- accept `MEAS-REWARD` as-is;
- implement `MEAS-SELECTED-REWARD-FINITE-SUM`;
- use a new file `BanditRLProof/MeasurableSums.lean`;
- keep the statement over arbitrary `s : Finset Nat`;
- use `Measurable.add`, `Finset.induction_on`, and `Finset.sum_insert`;
- do not move yet to `MEAS-REGRET`, `EXP-INDICATOR-PULL`, history/policy, or concentration.

I implemented it as follows.

New file:

```lean
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.MeasureTheory.Group.Arithmetic
import BanditRLProof.MeasureFoundation
```

New theorem:

```lean
theorem measurable_finset_sum_indicator_reward
    {Omega : Type u} {Action : Type v} {Reward : Type w}
    [MeasurableSpace Omega] [MeasurableSpace Action]
    [MeasurableSingletonClass Action]
    [MeasurableSpace Reward] [AddCommMonoid Reward] [MeasurableAdd₂ Reward]
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Reward)
    (haction : forall t : Nat, Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat, Measurable (fun omega : Omega => reward omega t))
    (a : Action) (s : Finset Nat) :
    Measurable
      (fun omega : Omega =>
        s.sum
          (fun t : Nat =>
            (({omega' : Omega | action omega' t = a} : Set Omega).indicator
              (fun omega' : Omega => reward omega' t)) omega)) := by
  refine Finset.induction_on s ?h_empty ?h_insert
  · simp
  · intro t s ht ih
    have hterm :
        Measurable
          (fun omega : Omega =>
            (({omega' : Omega | action omega' t = a} : Set Omega).indicator
              (fun omega' : Omega => reward omega' t)) omega) := by
      exact measurable_actionTrace_eval_eq_indicator_reward
        action reward haction hreward a t
    simpa [Finset.sum_insert, ht] using hterm.add ih
```

Root import:

```lean
import BanditRLProof.MeasurableSums
```

Consumer test was added in `Tests/Basic.lean`.

Verification:

```text
lake build BanditRLProof.MeasurableSums
lake build Tests.Basic
python3 -m py_compile tools\bandit.py
python3 tools\bandit.py reference-index
python3 tools\bandit.py memory-refresh BRL-UCB-PORT-001
python3 tools\bandit.py memory-refresh BRL-ETC-PORT-001
python3 tools\bandit.py check
```

All passed. Full check:

```text
Build completed successfully (1702 jobs).
check passed
```

Local retrieval index:

```text
local declarations: 94
LOCAL-LEAF-MEASURE-FOUNDATION:
- measurableSet_actionTrace_eval_eq
- measurable_actionTrace_eval_eq_indicator_const
- measurable_actionTrace_eval_eq_indicator_reward

LOCAL-LEAF-MEASURABLE-SUMS:
- measurable_finset_sum_indicator_reward
```

`python3 tools\bandit.py unfinished --status missing-leaf --status theorem-card` no longer lists this finite-sum leaf.

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
- `MEAS-SELECTED-REWARD-FINITE-SUM`.

## Questions

1. Is `MEAS-SELECTED-REWARD-FINITE-SUM` reasonable as implemented, or should the statement/import boundary be adjusted before building on it?
2. What is the single best next executable leaf now?
3. Should the next step be a `sumRewards`-specific measurability corollary, `MEAS-REGRET`, `EXP-INDICATOR-PULL`, or the first expectation canary?
4. Please provide the exact Lean-facing statement shape, imports/APIs to probe, proof route, regularity contracts, status classification, and failure policy.

Please keep the recommendation focused on one local Lean leaf and a minimal batch before asking again.
