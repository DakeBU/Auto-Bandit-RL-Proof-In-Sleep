# Extended Pro Prompt: After Three Finset Wrappers

You are reviewing ABRL, a Lean 4 repository for bandit/RL proof engineering.

A meaningful batch is now complete.  The full local gate passes:

```bash
python3 tools/bandit.py check
```

with:

```text
lake build
lake build Tests
check passed
```

The deterministic Mathlib wrapper layer now has three compiled declarations:

```lean
theorem pullCount_eq_finset_filter_card :
    pullCount action a t =
      ((Finset.range t).filter (fun s : Nat => action s = a)).card

theorem sumRewards_eq_finset_filter_sum :
    sumRewards action reward a t =
      ((Finset.range t).filter (fun s : Nat => action s = a)).sum
        (fun s : Nat => reward s)

theorem pseudoRegret_eq_finset_sum :
    pseudoRegret model action t =
      (Finset.range t).sum (fun s : Nat => model.gap (action s))
```

Actual wrapper imports:

```lean
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.Rat
import Mathlib.Data.Finset.Card
import BanditRLProof.LeafLemmas
```

Local notes:

- `SUMREWARDS-FINSET` uses `[AddCommMonoid Reward]`.
- `PSEUDOREGRET-FINSET` uses the `Rat` additive instance from
  `Mathlib.Algebra.Field.Rat`.
- `PULLCOUNT-FINSET`, `SUMREWARDS-FINSET`, and `PSEUDOREGRET-FINSET` no
  longer appear in `python3 tools/bandit.py unfinished`.
- `python3 tools/bandit.py list-lean-decls finset --statement` finds all
  three theorem declarations.

Current unfinished rows still include measure/probability/filtration/tail
leaves, plus theorem-card backlog for UCB/ETC/Thompson/contextual/RL.

Please review the next execution choice:

1. Should the next immediate target be a deterministic consumer leaf, such as
   `REGRET-PULLCOUNT`, an ETC/UCB count-prep lemma, or a finite-action
   reindexing statement?
2. Or is it now time to start the probability/measure foundation layer?
3. Give exactly one recommended next leaf row, with:
   - exact Lean-facing statement shape;
   - minimal imports;
   - local APIs/declarations to reuse;
   - regularity/typeclass contracts;
   - proof route;
   - failure policy.
4. How much should be completed before asking you again?

Keep the answer focused on execution order and one exact next Lean leaf.
