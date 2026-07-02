# Extended Pro Review: After EXP-MODEL-GAP-OFREAL-BOUND

Extended Pro accepted `EXP-MODEL-GAP-OFREAL-BOUND` as an `ENNReal.ofReal`
surrogate only.  It advised not to treat that theorem as faithful
Rat-valued expected regret.

Recommended next single executable leaf:

```text
OFREAL-FINSET-WEIGHTED-NAT-FAITHFULNESS
```

Recommended theorem:

```lean
theorem ENNReal.ofReal_finset_sum_mul_natCast_of_nonneg
    {ι : Type u}
    (s : Finset ι) (gap : ι -> Real) (count : ι -> Nat)
    (hgap : forall i : ι, i ∈ s -> 0 <= gap i) :
    ENNReal.ofReal
      (s.sum (fun i : ι => gap i * ((count i : Nat) : Real)))
      =
    s.sum
      (fun i : ι =>
        ENNReal.ofReal (gap i) * ((count i : Nat) : ENNReal))
```

Recommended file:

```text
BanditRLProof/ScalarENNReal.lean
```

Recommended imports:

```lean
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.Nat.Cast.Basic
```

Proof route:

1. Prove each real summand is nonnegative:
   `0 <= gap i * (count i : Real)`.
2. Use `ENNReal.ofReal_sum_of_nonneg` to move `ofReal` through the finite sum.
3. Use `ENNReal.ofReal_mul'` on each summand with nonnegativity of the Nat
   cast.
4. Simplify `ENNReal.ofReal (((count i : Nat) : Real))` to
   `((count i : Nat) : ENNReal)`.

Classification:

- scalar algebra only, not expectation;
- prerequisite for model-specific gap faithfulness and Rat/Real-to-ENNReal
  regret bridges;
- does not close `EXP-REGRET-PULLCOUNT`.

Failure policy:

- Keep `Mathlib.Data.ENNReal.BigOperators` for
  `ENNReal.ofReal_sum_of_nonneg`.
- Keep `Mathlib.Data.ENNReal.Real` for `ENNReal.ofReal_mul'` and related
  conversion facts.
- Do not add `FiniteBanditModel`, `Rat`, probability imports, Bochner
  integration, filtrations, kernels, concentration, or broad imports.
- Do not weaken equality to an inequality.
- Mark complete only after `python3 tools/bandit.py check` passes.
