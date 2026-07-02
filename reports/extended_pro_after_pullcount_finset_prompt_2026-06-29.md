# Extended Pro Prompt: After PULLCOUNT-FINSET Closure

You are reviewing ABRL, a Lean 4 repository for bandit/RL proof engineering.

Current environment:

- Lean/Lake: Lean 4.29.1 through elan.
- Mathlib is now pinned in `lakefile.lean`:
  `leanprover-community/mathlib4 @ v4.29.1`.
- Full gate passes:

```bash
python3 tools/bandit.py check
```

with:

```text
lake build
lake build Tests
check passed
```

The prior recommendation was to treat `PULLCOUNT-FINSET` as the first
Mathlib dependency canary before probability/concentration work.

What was completed:

```lean
import Mathlib.Data.Finset.Card
import BanditRLProof.LeafLemmas

namespace BanditRLProof

theorem pullCount_eq_finset_filter_card
    {Action : Type u} [DecidableEq Action]
    (action : ActionTrace Action) (a : Action) (t : Nat) :
    pullCount action a t =
      ((Finset.range t).filter (fun s : Nat => action s = a)).card := by
  induction t with
  | zero =>
      simp [pullCount]
  | succ t ih =>
      rw [pullCount_succ, ih]
      by_cases h : action t = a
      · have ht :
            Not (Membership.mem
              ((Finset.range t).filter (fun s : Nat => action s = a)) t) := by
          simp [Finset.mem_range]
        simp [Finset.range_add_one, Finset.filter_insert, h, ht]
      · simp [Finset.range_add_one, Finset.filter_insert, h]

end BanditRLProof
```

Notes:

- The attempted one-line bridge through `pullCount_eq_list_filter_length` was
  not used, because the direct induction was shorter and stable in local Lean.
- `Mathlib.Data.Finset.Basic` alone was insufficient for `.card`; the minimal
  import that worked was `Mathlib.Data.Finset.Card`.
- The successor API was `Finset.range_add_one`, not `Finset.range_succ`.
- `python3 tools/bandit.py unfinished --status missing-leaf` no longer lists
  `PULLCOUNT-FINSET`.
- Current unfinished finite wrappers are:
  - `SUMREWARDS-FINSET`;
  - `PSEUDOREGRET-FINSET`.

Repository updates made:

- added `BanditRLProof/MathlibWrappers.lean`;
- imported it from `BanditRLProof.lean`;
- added a test consumer in `Tests/Basic.lean`;
- updated `research-wiki/theory-tree/mathlib-foundation-leaf-map.md`;
- updated `docs/completion_gap_audit.md`;
- updated `docs/collaborator_unfinished_work_guide.md`;
- updated `docs/project_overview_next_plan.md`;
- refreshed `research-wiki/retrieval-index/*`;
- added a local card `LOCAL-LEAF-MATHLIB-FINSET-WRAPPERS`.

Please review:

1. Was it reasonable to close `PULLCOUNT-FINSET` by direct induction rather
   than forcing reuse of the `List.range` bridge?
2. Is `Mathlib.Data.Finset.Card` the right import boundary for this wrapper
   layer?
3. Should the next immediate leaf be `PSEUDOREGRET-FINSET` or
   `SUMREWARDS-FINSET`?
4. Give the exact next Lean-facing statement, minimal imports, intended proof
   route, and regularity/typeclass contracts for that next leaf.
5. What failure policy should be used if the next finite-sum wrapper reveals
   typeclass or big-operator friction?
6. How much more work should be done before asking you again?

Keep the answer focused on execution order and exact next Lean leaf design.
