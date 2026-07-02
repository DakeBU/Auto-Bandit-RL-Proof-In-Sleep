# Extended Pro Review Prompt: After OFREAL-FINSET-WEIGHTED-NAT-FAITHFULNESS

We are working in the Lean 4 repository `Auto-Bandit-RL-Proof-In-Sleep`.

Following your previous recommendation, I completed exactly one leaf:

```text
OFREAL-FINSET-WEIGHTED-NAT-FAITHFULNESS
```

New compiled file:

```text
BanditRLProof/ScalarENNReal.lean
```

New theorem:

```lean
theorem BanditRLProof.ENNReal.ofReal_finset_sum_mul_natCast_of_nonneg
    {I : Type u}
    (s : Finset I) (gap : I -> Real) (count : I -> Nat)
    (hgap : forall i : I, i ∈ s -> 0 <= gap i) :
    ENNReal.ofReal
      (s.sum (fun i : I => gap i * ((count i : Nat) : Real)))
      =
    s.sum
      (fun i : I =>
        ENNReal.ofReal (gap i) * ((count i : Nat) : ENNReal))
```

Imports used:

```lean
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.Nat.Cast.Basic
```

Proof route actually used:

1. Prove each real summand is nonnegative:
   `0 <= gap i * ((count i : Nat) : Real)`.
2. Use `ENNReal.ofReal_sum_of_nonneg` to move `ofReal` through the finite sum.
3. Use `ENNReal.ofReal_mul'` plus `ENNReal.ofReal_natCast` to rewrite each
   weighted count.

Verification passed:

```text
python3 tools/bandit.py check
Build completed successfully (1772 jobs).
Build completed successfully (1774 jobs).
check passed
```

I also updated:

- root import in `BanditRLProof.lean`;
- a consumer test in `Tests/Basic.lean`;
- `tools/bandit.py` local leaf cards and recommendation output;
- `research-wiki/theory-tree/mathlib-foundation-leaf-map.md`;
- `docs/completion_gap_audit.md`;
- `docs/project_overview_next_plan.md`;
- `docs/collaborator_unfinished_work_guide.md`;
- `README.md`;
- `research-wiki/theory-tree/bandit-theory-tree.md`;
- UCB/ETC proof-obligation ledgers.

Current relevant compiled bridge chain:

```text
PULLCOUNT-FINSET
SUMREWARDS-FINSET
PSEUDOREGRET-FINSET
REGRET-PULLCOUNT
PULLCOUNT-SUM-TIME
MEAS-FIN-ACTION
MEAS-PULL-INDICATOR
MEAS-REWARD
MEAS-SELECTED-REWARD-FINITE-SUM
MEAS-SUMREWARDS
MEAS-REGRET
MEAS-PULLCOUNT
MEAS-PULLCOUNT-CAST
EXP-INDICATOR-PULL
EXP-FINSET-INDICATOR-PULL
EXP-PULLCOUNT-LINTEGRAL
EXP-WEIGHTED-PULLCOUNT-LINTEGRAL
EXP-PULLCOUNT-LE-TIME
EXP-WEIGHTED-PULLCOUNT-LE-TIME
EXP-WEIGHTED-PULLCOUNT-LE-TIME-FIN
EXP-MODEL-GAP-OFREAL-BOUND
OFREAL-FINSET-WEIGHTED-NAT-FAITHFULNESS
```

Important boundary:

- I have not claimed Rat-valued expected regret.
- I have not started Bochner expectation.
- I have not introduced filtrations, kernels, conditional expectation, or
  concentration.
- The new theorem is scalar algebra only.

Please review whether this latest scalar leaf is the right bridge and recommend
the next single executable Lean leaf.

Questions:

1. Is `OFREAL-FINSET-WEIGHTED-NAT-FAITHFULNESS` reasonable as implemented and
   classified as scalar algebra only?
2. Should the next leaf prove nonnegativity of `FiniteBanditModel.gap`, or a
   model-specific corollary using the scalar lemma, or should we stop and move
   to Bochner/integrability route design?
3. Please give exactly one next executable leaf, with:
   - exact Lean-facing statement;
   - local APIs/imports;
   - intended proof route;
   - regularity contracts;
   - retrieval evidence from Mathlib/local declarations;
   - status classification;
   - failure policy.
4. How much should be completed before I ask you again?
