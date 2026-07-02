# Extended Pro review request after MEAS-PULLCOUNT

Repository: `D:\code\Auto-Bandit-RL-Proof-In-Sleep-main\Auto-Bandit-RL-Proof-In-Sleep-main`

Please review the current ABRL Lean formalization state after the pull-count measurability leaf and recommend exactly one next executable leaf.

## Current goal

Advance the project from deterministic bandit/regret algebra into Mathlib-backed probability foundations, then toward concentration inequalities and complete UCB/ETC/Thompson/EXP3/Tsallis-INF/OFUL/RL theorem routes.

Policy:

- Do not treat theorem cards as local Lean proofs.
- Do not start from broad algorithm theorem statements.
- Pick exactly one executable unfinished/local leaf.
- Prefer a small Mathlib-backed leaf that compiles locally.
- Avoid probability measures, expectation, filtration, or concentration unless the next leaf genuinely needs them.

## New work completed since your last review

Your final recommendation after `MEAS-REGRET` was:

- accept `MEAS-REGRET / measurable_pseudoRegret` as-is;
- implement `MEAS-PULLCOUNT` before expectation;
- use induction over the recursive `pullCount`;
- use `measurableSet_actionTrace_eval_eq`, `Measurable.ite`, `Measurable.add`, and `pullCount_succ`;
- do not introduce probability measures, expectation, scalar casts, filtration, or concentration yet.

I implemented it.

New file:

```lean
import Mathlib.MeasureTheory.Group.Arithmetic
import BanditRLProof.MeasureFoundation
import BanditRLProof.LeafLemmas
```

New theorem:

```lean
theorem measurable_pullCount
    {Omega : Type u} {Action : Type v}
    [MeasurableSpace Omega] [MeasurableSpace Action]
    [MeasurableSingletonClass Action]
    [MeasurableSpace Nat] [MeasurableAdd₂ Nat]
    [DecidableEq Action]
    (action : Omega -> ActionTrace Action)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (a : Action) (n : Nat) :
    Measurable
      (fun omega : Omega => pullCount (action omega) a n) := by
  induction n with
  | zero =>
      simp [pullCount]
  | succ n ih =>
      have hevent :
          MeasurableSet {omega : Omega | action omega n = a} :=
        measurableSet_actionTrace_eval_eq action haction a n
      have hind :
          Measurable
            (fun omega : Omega =>
              if action omega n = a then (1 : Nat) else 0) :=
        Measurable.ite hevent measurable_const measurable_const
      have hadd :
          Measurable
            (fun omega : Omega =>
              pullCount (action omega) a n
                + if action omega n = a then (1 : Nat) else 0) :=
        ih.add hind
      simpa [pullCount_succ] using hadd
```

Root import:

```lean
import BanditRLProof.MeasurablePullCount
```

Consumer test added in `Tests/Basic.lean`.

Verification:

```text
lake build BanditRLProof.MeasurablePullCount
lake build Tests.Basic
python3 -m py_compile tools\bandit.py
python3 tools\bandit.py reference-index
python3 tools\bandit.py memory-refresh BRL-UCB-PORT-001
python3 tools\bandit.py memory-refresh BRL-ETC-PORT-001
python3 tools\bandit.py check
```

All passed. Full check:

```text
Build completed successfully (1705 jobs).
check passed
```

Local retrieval index:

```text
local declarations: 97
LOCAL-LEAF-MEASURABLE-PULLCOUNT:
- measurable_pullCount
```

`python3 tools\bandit.py unfinished --status missing-leaf --status theorem-card` still lists no `MEAS-REGRET` and now no `MEAS-PULLCOUNT` row.

Remaining unfinished/theorem-card rows include:

- `MEAS-HISTORY`
- `MEAS-POLICY`
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
- `MEAS-SUMREWARDS`;
- `MEAS-REGRET`;
- `MEAS-PULLCOUNT`.

## Questions

1. Is `MEAS-PULLCOUNT / measurable_pullCount` reasonable as implemented?
2. What is the single best next executable leaf now?
3. Should the next step be scalar-casted pull-count measurability, `EXP-INDICATOR-PULL`, a first expectation canary, or a history/policy measurability leaf?
4. Please provide the exact Lean-facing statement shape, imports/APIs to probe, proof route, regularity contracts, status classification, and failure policy.

Please keep the recommendation focused on one local Lean leaf and a minimal batch before asking again.
