# Extended Pro Review Prompt: After EXP-OFREAL-PSEUDOREGRET-BOUND-MODEL-GAP

We are working in the ABRL Lean 4 repository for formalizing bandit/RL theory.

Following your previous recommendation, I completed exactly one additional
adapter leaf:

```text
EXP-OFREAL-PSEUDOREGRET-BOUND-MODEL-GAP
```

New compiled theorem, in `BanditRLProof/ExpectationPseudoRegretRatBounds.lean`:

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

Implementation route:

```lean
exact
  lintegral_ofReal_pseudoRegret_le_sum_model_gap_ofReal_mul_time_of_rat_gap_nonneg
    (mu := mu)
    (model := model)
    (action := action)
    (haction := haction)
    (hgap := fun a => FiniteBanditModel.gap_nonneg model a)
    (n := n)
```

Updated:

- one consumer test in `Tests/Basic.lean`;
- `tools/bandit.py` local leaf card and `unfinished` recommendation output;
- README, completion gap audit, project overview, collaborator guide,
  Mathlib foundation leaf map, theory tree;
- retrieval indexes and UCB/ETC memory refresh JSON.

Verification:

```text
python3 tools/bandit.py check
Build completed successfully (1776 jobs).
Build completed successfully (1778 jobs).
$ lake build
$ lake build Tests
check passed
```

Current completed chain:

```text
PULLCOUNT/SUMREWARDS/PSEUDOREGRET finite wrappers
REGRET-PULLCOUNT
PULLCOUNT-SUM-TIME
MEAS-* measurability canaries
EXP-* ENNReal lower-integral pull-count/weighted bounds
OFREAL-FINSET-WEIGHTED-NAT-FAITHFULNESS
OFREAL-PSEUDOREGRET-PULLCOUNT-FAITHFULNESS
EXP-OFREAL-PSEUDOREGRET-BOUND
EXP-OFREAL-PSEUDOREGRET-BOUND-OF-RAT-GAP-NONNEG
FINITE-BANDIT-BESTARM-DOMINATES
FINITE-BANDIT-GAP-NONNEG
EXP-OFREAL-PSEUDOREGRET-BOUND-MODEL-GAP
```

Boundary:

- This is still only an `ENNReal.ofReal` lower-integral surrogate.
- We have not proved Rat-valued expected regret, Bochner expectation,
  integrability contracts, filtrations, conditional expectation, concentration,
  UCB/ETC final regret, Thompson sampling, EXP3, Tsallis-INF, OFUL, or RL/MDP.

Questions:

1. What is the right next single executable leaf now?
2. Should the next direction be a Bochner/integrability canary, or a
   non-probabilistic UCB/ETC deterministic scaffold?
3. What exact Lean-facing statement should be attempted next?
4. What imports/local APIs should it use?
5. What should the failure policy be?
