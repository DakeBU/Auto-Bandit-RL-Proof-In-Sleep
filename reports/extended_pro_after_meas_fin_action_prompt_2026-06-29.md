# Extended Pro Prompt: After MEAS-FIN-ACTION Closure

You are reviewing ABRL, a Lean 4 repository for bandit/RL proof engineering.

The previous recommendation was to start the probability/measure foundation
with exactly one small canary, `MEAS-FIN-ACTION`, then stop and ask again.

That leaf is now compiled locally:

```lean
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import BanditRLProof.Core

namespace BanditRLProof

theorem measurableSet_actionTrace_eval_eq
    {Omega : Type u} {Action : Type v}
    [MeasurableSpace Omega] [MeasurableSpace Action]
    [MeasurableSingletonClass Action]
    (action : Omega -> ActionTrace Action)
    (hmeas : forall t : Nat, Measurable (fun omega : Omega => action omega t))
    (a : Action) (t : Nat) :
    MeasurableSet {omega : Omega | action omega t = a}

end BanditRLProof
```

The proof uses:

- `MeasurableSet.singleton`;
- measurable preimages from `hmeas t`;
- `simpa [Set.preimage]`.

The file is:

```text
BanditRLProof/MeasureFoundation.lean
```

and it is imported by:

```text
BanditRLProof.lean
```

There is a test consumer in `Tests/Basic.lean`.

The local card/index/docs were refreshed:

- `LOCAL-LEAF-MEASURE-FOUNDATION`;
- `research-wiki/theory-tree/mathlib-foundation-leaf-map.md`;
- `docs/completion_gap_audit.md`;
- `docs/collaborator_unfinished_work_guide.md`;
- `docs/project_overview_next_plan.md`;
- UCB/ETC proof-obligation ledgers;
- `research-wiki/mathlib/theorem-cards.md`;
- retrieval indexes.

The full local gate passes:

```bash
python3 tools/bandit.py check
```

with:

```text
lake build
lake build Tests
check passed
```

Current compiled layer:

- dependency-light finite bookkeeping and `List.range` bridges;
- Mathlib `Finset.range` wrappers for pull count, reward sum, and pseudo-regret;
- deterministic regret decomposition:
  `pseudoRegret_eq_finset_sum_gap_mul_pullCount`;
- deterministic finite-action count partition:
  `finset_sum_pullCount_eq_time`;
- first probability/measure canary:
  `measurableSet_actionTrace_eval_eq`.

Current unfinished rows still include:

- `MEAS-HISTORY`, `MEAS-POLICY`, `MEAS-REWARD`, `MEAS-REGRET`;
- `EXP-INDICATOR-PULL`, `EXP-REGRET-PULLCOUNT`;
- filtration/martingale leaves;
- concentration/tail leaves;
- final UCB/ETC/TS/contextual/RL/EXP3/Tsallis theorem cards.

Please review:

1. Was this `MEAS-FIN-ACTION` closure reasonable as the first
   probability/measure canary?
2. What exactly should be the next single executable leaf?
   - `MEAS-REGRET`?
   - `MEAS-REWARD`?
   - a pull-count event/indicator measurability leaf before
     `EXP-INDICATOR-PULL`?
   - `MEAS-POLICY` or `MEAS-HISTORY`?
   - something else?
3. Give the exact Lean-facing statement shape, minimal imports, local APIs to
   reuse, regularity/typeclass contracts, proof route, and failure policy.
4. How much should be completed before asking you again?

Keep the answer focused on one next executable leaf and a minimal batch.
