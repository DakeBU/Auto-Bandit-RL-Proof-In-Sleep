# Extended Pro review request after EXP-INDICATOR-PULL

Repository: `D:\code\Auto-Bandit-RL-Proof-In-Sleep-main\Auto-Bandit-RL-Proof-In-Sleep-main`

Please review the current ABRL Lean formalization state after the first
expectation/integration canary and recommend exactly one next executable leaf.

## Current goal

Advance the project from deterministic bandit/regret algebra into
Mathlib-backed probability foundations, then toward concentration inequalities
and complete UCB/ETC/Thompson/EXP3/Tsallis-INF/OFUL/RL theorem routes.

Policy:

- Do not treat theorem cards as local Lean proofs.
- Do not start from broad algorithm theorem statements.
- Pick exactly one executable unfinished or local leaf.
- Prefer a small Mathlib-backed leaf that compiles locally.
- Avoid Bochner expected regret, conditional expectation, filtration, kernels,
  and concentration unless the next leaf genuinely needs them.

## New work completed since your last review

Your recommendation after `MEAS-PULLCOUNT-CAST` was:

- accept `MEAS-PULLCOUNT-CAST / measurable_natCast_pullCount` as-is;
- start the first expectation/integration canary;
- implement `EXP-INDICATOR-PULL` as an `ENNReal` lower-Lebesgue-integral
  statement;
- use an arbitrary measure, not a probability measure;
- use `MeasureTheory.lintegral_indicator_one` and
  `measurableSet_actionTrace_eval_eq`;
- do not introduce Bochner expectation, `Real`, `Rat`, conditional
  expectation, filtrations, kernels, or concentration.

I implemented it.

New file:

```lean
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import BanditRLProof.MeasureFoundation
```

New theorem:

```lean
theorem lintegral_actionTrace_eval_eq_indicator_one
    {Omega : Type u} {Action : Type v}
    [MeasurableSpace Omega] [MeasurableSpace Action]
    [MeasurableSingletonClass Action]
    (mu : Measure Omega)
    (action : Omega -> ActionTrace Action)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (a : Action) (t : Nat) :
    MeasureTheory.lintegral mu
      (fun omega : Omega =>
        (({omega' : Omega | action omega' t = a} : Set Omega).indicator
          (1 : Omega -> ENNReal)) omega)
      =
    mu {omega : Omega | action omega t = a} := by
  simpa using
    (@MeasureTheory.lintegral_indicator_one
      Omega _ mu {omega : Omega | action omega t = a}
      (measurableSet_actionTrace_eval_eq action haction a t))
```

Implementation note:

- The local Mathlib version did not expose
  `MeasureTheory.lintegral_indicator_fun_one`.
- It did expose `MeasureTheory.lintegral_indicator_one`, so I used the
  non-eta-expanded `s.indicator 1` form.
- I also used `MeasureTheory.lintegral` in the statement rather than `∫⁻`
  notation to keep the source robust in this Windows/PowerShell workflow.

Root import:

```lean
import BanditRLProof.ExpectationFoundation
```

Consumer test added in `Tests/Basic.lean`.

Documentation and harness updates:

- added `LOCAL-LEAF-EXPECTATION-FOUNDATION`;
- changed `EXP-INDICATOR-PULL` from `missing-leaf` to `compiled-local` in the
  Mathlib foundation leaf map;
- updated README, completion-gap audit, collaborator guide, project overview,
  theory tree, and UCB/ETC proof-obligation ledgers;
- refreshed retrieval indexes and UCB/ETC memory packets.

Verification:

```text
lake build BanditRLProof.ExpectationFoundation
lake build Tests.Basic
python3 -m py_compile tools\bandit.py
python3 tools\bandit.py list-lean-decls lintegral_actionTrace_eval_eq_indicator_one --statement
python3 tools\bandit.py reference-index
python3 tools\bandit.py memory-refresh BRL-UCB-PORT-001
python3 tools\bandit.py memory-refresh BRL-ETC-PORT-001
python3 tools\bandit.py check
```

All passed. Final check:

```text
Build completed successfully (1717 jobs).
Build completed successfully (1719 jobs).
$ lake build
$ lake build Tests
check passed
```

Local retrieval index:

```text
local declarations: 99
measurable_natCast_pullCount 1 BanditRLProof/MeasurablePullCountCast.lean
lintegral_actionTrace_eval_eq_indicator_one 1 BanditRLProof/ExpectationFoundation.lean
```

`python3 tools\bandit.py unfinished --status missing-leaf --status theorem-card`
no longer lists `EXP-INDICATOR-PULL`.

Remaining unfinished/theorem-card rows include:

- `MEAS-HISTORY`
- `MEAS-POLICY`
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
- `MEAS-PULLCOUNT-CAST`;
- `EXP-INDICATOR-PULL`.

## Questions

1. Is `EXP-INDICATOR-PULL / lintegral_actionTrace_eval_eq_indicator_one`
   reasonable as implemented?
2. What is the single best next executable leaf now?
3. Should the next step be an `ENNReal` finite-sum expectation bridge, a
   measure-theoretic pull-count identity, `MEAS-HISTORY`, `MEAS-POLICY`, or a
   Rat/Real Bochner expectation canary?
4. Please provide the exact Lean-facing statement shape, imports/APIs to probe,
   proof route, regularity contracts, status classification, and failure
   policy.

Please keep the recommendation focused on one local Lean leaf and a minimal
batch before asking again.
