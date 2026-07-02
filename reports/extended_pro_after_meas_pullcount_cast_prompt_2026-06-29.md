# Extended Pro review request after MEAS-PULLCOUNT-CAST

Repository: `D:\code\Auto-Bandit-RL-Proof-In-Sleep-main\Auto-Bandit-RL-Proof-In-Sleep-main`

Please review the current ABRL Lean formalization state after the scalar-casted
pull-count measurability leaf and recommend exactly one next executable leaf.

## Current goal

Advance the project from deterministic bandit/regret algebra into
Mathlib-backed probability foundations, then toward concentration inequalities
and complete UCB/ETC/Thompson/EXP3/Tsallis-INF/OFUL/RL theorem routes.

Policy:

- Do not treat theorem cards as local Lean proofs.
- Do not start from broad algorithm theorem statements.
- Pick exactly one executable unfinished or local leaf.
- Prefer a small Mathlib-backed leaf that compiles locally.
- Avoid filtration or concentration unless the next leaf genuinely needs them.

## New work completed since your last review

Your recommendation after `MEAS-PULLCOUNT` was:

- accept `MEAS-PULLCOUNT / measurable_pullCount` as-is;
- implement scalar-casted pull-count measurability next;
- use direct scalar induction instead of composing Nat-valued measurability with
  a cast;
- keep the statement generic in the scalar type, so later consumers can use
  `Beta := Rat`;
- do not introduce probability measures, expectation, filtration,
  concentration, `Real`, or `Rat` yet.

I implemented it.

New file:

```lean
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.MeasureTheory.Group.Arithmetic
import BanditRLProof.MeasurablePullCount
```

New theorem:

```lean
theorem measurable_natCast_pullCount
    {Omega : Type u} {Action : Type v} {Beta : Type w}
    [MeasurableSpace Omega] [MeasurableSpace Action]
    [MeasurableSingletonClass Action]
    [MeasurableSpace Beta] [AddCommMonoidWithOne Beta] [MeasurableAdd₂ Beta]
    [DecidableEq Action]
    (action : Omega -> ActionTrace Action)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (a : Action) (n : Nat) :
    Measurable
      (fun omega : Omega =>
        ((pullCount (action omega) a n : Nat) : Beta)) := by
  induction n with
  | zero =>
      simp [pullCount]
  | succ n ih =>
      have hevent :
          MeasurableSet {omega : Omega | action omega n = a} :=
        measurableSet_actionTrace_eval_eq action haction a n
      have hinc :
          Measurable
            (fun omega : Omega =>
              if action omega n = a then (1 : Beta) else 0) :=
        Measurable.ite hevent measurable_const measurable_const
      have hadd :
          Measurable
            (fun omega : Omega =>
              ((pullCount (action omega) a n : Nat) : Beta)
                + (if action omega n = a then (1 : Beta) else 0)) :=
        ih.add hinc
      have hfun :
          (fun omega : Omega =>
              ((pullCount (action omega) a (Nat.succ n) : Nat) : Beta))
            =
          (fun omega : Omega =>
              ((pullCount (action omega) a n : Nat) : Beta)
                + (if action omega n = a then (1 : Beta) else 0)) := by
        funext omega
        by_cases h : action omega n = a
        · simp [pullCount_succ, h]
        · simp [pullCount_succ, h]
      rw [hfun]
      exact hadd
```

Root import:

```lean
import BanditRLProof.MeasurablePullCountCast
```

Consumer test added in `Tests/Basic.lean`.

Documentation and harness updates:

- added `LOCAL-LEAF-MEASURABLE-PULLCOUNT-CAST`;
- added `MEAS-PULLCOUNT-CAST` as compiled-local in the Mathlib foundation
  leaf map;
- updated README, completion-gap audit, collaborator guide, project overview,
  theory tree, and the UCB/ETC proof-obligation ledgers;
- refreshed retrieval indexes and UCB/ETC memory packets.

Verification:

```text
lake build BanditRLProof.MeasurablePullCountCast
lake build Tests.Basic
python3 -m py_compile tools\bandit.py
python3 tools\bandit.py list-lean-decls measurable_natCast_pullCount --statement
python3 tools\bandit.py reference-index
python3 tools\bandit.py memory-refresh BRL-UCB-PORT-001
python3 tools\bandit.py memory-refresh BRL-ETC-PORT-001
python3 tools\bandit.py check
```

All passed. Final check:

```text
Build completed successfully (1704 jobs).
Build completed successfully (1706 jobs).
$ lake build
$ lake build Tests
check passed
```

Local retrieval index:

```text
local declarations: 98
measurable_pseudoRegret 1 BanditRLProof/MeasurableRegret.lean
measurable_pullCount 1 BanditRLProof/MeasurablePullCount.lean
measurable_natCast_pullCount 1 BanditRLProof/MeasurablePullCountCast.lean
```

`python3 tools\bandit.py unfinished --status missing-leaf --status theorem-card`
still lists:

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
- `MEAS-PULLCOUNT`;
- `MEAS-PULLCOUNT-CAST`.

## Questions

1. Is `MEAS-PULLCOUNT-CAST / measurable_natCast_pullCount` reasonable as
   implemented?
2. What is the single best next executable leaf now?
3. Should the next step be `EXP-INDICATOR-PULL`, a smaller expectation canary,
   `MEAS-HISTORY`, `MEAS-POLICY`, or a Rat-specific expected-regret interface?
4. Please provide the exact Lean-facing statement shape, imports/APIs to probe,
   proof route, regularity contracts, status classification, and failure policy.

Please keep the recommendation focused on one local Lean leaf and a minimal
batch before asking again.
