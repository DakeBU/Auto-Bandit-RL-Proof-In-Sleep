# Extended Pro Prompt: After REGRET-PULLCOUNT Closure

You are reviewing ABRL, a Lean 4 repository for bandit/RL proof engineering.

The last recommendation was to complete exactly one deterministic consumer
leaf, `REGRET-PULLCOUNT`, then stop and ask again before proceeding.

That leaf is now compiled locally:

```lean
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Nat.Cast.Basic
import BanditRLProof.MathlibWrappers

theorem pseudoRegret_eq_finset_sum_gap_mul_pullCount
    (model : FiniteBanditModel K) (action : Nat -> Fin K) (t : Nat) :
    pseudoRegret model action t =
      (Finset.univ : Finset (Fin K)).sum
        (fun a : Fin K => model.gap a * (pullCount action a t : Rat))
```

The proof uses:

- `pseudoRegret_eq_finset_sum`;
- `pullCount_eq_finset_filter_card`;
- `Finset.sum_fiberwise'`;
- `Finset.sum_const`;
- `nsmul_eq_mul'`.

The full gate passes:

```bash
python3 tools/bandit.py check
```

with:

```text
lake build
lake build Tests
check passed
```

Current compiled deterministic layer:

- dependency-light `List.range` bridges for pull count, reward sum, filtered
  reward sum, and pseudo-regret;
- Mathlib `Finset.range` wrappers for pull count, reward sum, and pseudo-regret;
- deterministic regret decomposition `REGRET-PULLCOUNT`.

Please review:

1. Was this `REGRET-PULLCOUNT` closure reasonable as the first consumer leaf?
2. What exactly should be the next single leaf?
   - probability/measure foundation contract?
   - ETC/UCB count-prep lemma?
   - expected-regret/pull-count identity?
   - something else?
3. Give the exact Lean-facing statement shape, imports, local APIs to reuse,
   regularity/typeclass contracts, proof route, and failure policy.
4. How much should be completed before asking again?

Keep the answer focused on one next executable leaf.
