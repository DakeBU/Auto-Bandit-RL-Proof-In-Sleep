# Extended Pro Prompt: After PULLCOUNT-SUM-TIME Closure

You are reviewing ABRL, a Lean 4 repository for bandit/RL proof engineering.

The previous recommendation was to complete exactly one deterministic
count-prep leaf, `PULLCOUNT-SUM-TIME`, then stop and ask again before
entering probability/measure/concentration work.

That leaf is now compiled locally, in a slightly more general form than the
`Fin K`-specific sketch:

```lean
import Mathlib.Data.Fintype.Basic
import BanditRLProof.MathlibWrappers

namespace BanditRLProof

theorem finset_sum_pullCount_eq_time
    {Action : Type u} [Fintype Action] [DecidableEq Action]
    (action : ActionTrace Action) (t : Nat) :
    (Finset.univ : Finset Action).sum
      (fun a : Action => pullCount action a t) = t

end BanditRLProof
```

The proof uses:

- `pullCount_eq_finset_filter_card`;
- `Finset.card_eq_sum_card_fiberwise`;
- simplification of `(Finset.range t).card = t`.

The theorem was added in:

```text
BanditRLProof/PullCountDecomposition.lean
```

and imported by:

```text
BanditRLProof.lean
```

There is a test consumer in `Tests/Basic.lean`, and the local card/index/docs
were refreshed:

- `LOCAL-LEAF-PULLCOUNT-DECOMPOSITION`;
- `research-wiki/theory-tree/mathlib-foundation-leaf-map.md`;
- `docs/completion_gap_audit.md`;
- `docs/collaborator_unfinished_work_guide.md`;
- `docs/project_overview_next_plan.md`;
- UCB/ETC proof-obligation ledgers.

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

The Windows Unicode crash in:

```bash
python3 tools/bandit.py list-lean-decls QUERY --statement
```

was also fixed by configuring stdout/stderr as UTF-8 with replacement.
The command now finds:

```lean
theorem finset_sum_pullCount_eq_time :
  (Finset.univ : Finset Action).sum
    (fun a : Action => pullCount action a t) = t
```

Current compiled deterministic layer:

- dependency-light `List.range` bridges for pull count, reward sum, filtered
  reward sum, and pseudo-regret;
- Mathlib `Finset.range` wrappers for pull count, reward sum, and pseudo-regret;
- deterministic regret decomposition:
  `pseudoRegret_eq_finset_sum_gap_mul_pullCount`;
- deterministic finite-action count partition:
  `finset_sum_pullCount_eq_time`.

Current unfinished rows still include:

- measure/probability leaves such as `MEAS-FIN-ACTION`, `MEAS-HISTORY`,
  `MEAS-POLICY`, `MEAS-REWARD`, `MEAS-REGRET`;
- integrability/expectation routes such as `INT-FINITE-SUM`,
  `EXP-FINITE-SUM`, `EXP-INDICATOR-PULL`,
  `EXP-REGRET-PULLCOUNT`;
- filtration/martingale leaves such as `FILTRATION-HISTORY`,
  `ADAPTED-ACTION`, `MART-DIFF-REWARD`;
- tail/concentration leaves;
- algorithm theorem cards for UCB, ETC, Thompson sampling, contextual bandits,
  RL, EXP3, and Tsallis-INF.

Please review:

1. Was generalizing `PULLCOUNT-SUM-TIME` from `Fin K` to arbitrary finite
   `[Fintype Action] [DecidableEq Action]` reasonable?
2. What exactly should be the next single executable leaf?
   - probability/measure foundation contract?
   - expected pull count as event probabilities?
   - expected regret equals gaps times expected pull counts?
   - one more deterministic corollary such as `pullCount_le_time` via Finset?
   - something else?
3. Give the exact Lean-facing statement shape, imports, local APIs to reuse,
   regularity/typeclass contracts, proof route, and failure policy.
4. How much should be completed before asking you again?

Keep the answer focused on one next executable leaf and a minimal batch.
