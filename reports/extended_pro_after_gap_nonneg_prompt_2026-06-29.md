# Extended Pro Review Prompt: After FINITE-BANDIT-GAP-NONNEG

We are working in the ABRL Lean 4 repository for formalizing bandit/RL theory.

Following your previous recommendation, I completed exactly one additional
model-invariant leaf:

```text
FINITE-BANDIT-GAP-NONNEG
```

New compiled theorem, in `BanditRLProof/FiniteBanditModelInvariants.lean`:

```lean
theorem FiniteBanditModel.gap_nonneg
    {K : Nat}
    (model : FiniteBanditModel K) (a : Fin K) :
    (0 : Rat) <= model.gap a
```

Implementation route:

- `gap` is defined with an `if arm = model.bestArm then 0 else ...`, so the
  proof splits on `a = model.bestArm`.
- best-arm case: `simp [gap, h]`.
- non-best case: `simp [gap, h, bestMean,
  sub_nonneg.mpr (mean_le_bestArm_mean model a)]`.
- No probability, expectation, ENNReal, filtration, concentration, or algorithm
  theorem imports were added.

Updated:

- `Tests/Basic.lean` smoke example:

```lean
example {K : Nat} (model : FiniteBanditModel K) (a : Fin K) :
    (0 : Rat) <= model.gap a := by
  exact FiniteBanditModel.gap_nonneg model a
```

- `tools/bandit.py` local leaf card and `unfinished` recommendation output.
- README, completion gap audit, project overview, collaborator guide,
  Mathlib foundation leaf map, theory tree.
- Retrieval indexes and UCB/ETC memory refresh JSON.
- Local declaration scan is now 112 declarations.

Verification:

```text
python3 tools/bandit.py check
Build completed successfully (1776 jobs).
Build completed successfully (1778 jobs).
$ lake build
$ lake build Tests
check passed
```

Current boundary:

- `FINITE-BANDIT-BESTARM-DOMINATES` and `FINITE-BANDIT-GAP-NONNEG` are now
  compiled model-invariant leaves.
- `EXP-OFREAL-PSEUDOREGRET-BOUND-OF-RAT-GAP-NONNEG` still requires an explicit
  `hgap : forall a, (0 : Rat) <= model.gap a`.
- We have not yet added the adapter that calls `FiniteBanditModel.gap_nonneg`
  to remove that explicit `hgap` argument.
- We still have not claimed Rat-valued expectation, Bochner expectation,
  filtration, concentration, UCB/ETC regret, Thompson sampling, EXP3,
  Tsallis-INF, OFUL, or RL/MDP theorem work.

Candidate next leaf:

```lean
theorem lintegral_ofReal_pseudoRegret_le_sum_model_gap_ofReal_mul_time
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    [MeasurableSpace (Fin K)] [MeasurableSingletonClass (Fin K)]
    (mu : Measure Omega) [MeasureTheory.IsProbabilityMeasure mu]
    (model : FiniteBanditModel K)
    (action : Omega -> ActionTrace (Fin K))
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (n : Nat) :
    MeasureTheory.lintegral mu
      (fun omega : Omega =>
        ENNReal.ofReal
          (((pseudoRegret model (action omega) n : Rat) : Real)))
      <=
    (Finset.univ : Finset (Fin K)).sum
      (fun a : Fin K =>
        ENNReal.ofReal (((model.gap a : Rat) : Real)) *
          (n : ENNReal))
```

Expected route:

```lean
exact
  lintegral_ofReal_pseudoRegret_le_sum_model_gap_ofReal_mul_time_of_rat_gap_nonneg
    mu model action haction (fun a => FiniteBanditModel.gap_nonneg model a) n
```

Questions:

1. Is this adapter now the right next single leaf?
2. Is the theorem name and statement above the exact Lean-facing form you
   recommend?
3. Should it live in `BanditRLProof.ExpectationPseudoRegretRatBounds` or a new
   file?
4. What should its status be: compiled local expectation adapter, or still just
   lower-integral `ENNReal.ofReal` surrogate?
5. After this adapter, should the next step be another review before
   Rat-valued expected regret/Bochner expectation, or is there a smaller
   non-probabilistic leaf to do first?
