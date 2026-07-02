# Extended Pro Review Prompt: After ETC-ACTION-WITH-COMMIT-EXPLORE-PHASE

We are working in the ABRL Lean 4 repository for formalizing bandit/RL theory.

Following your previous recommendation, I completed exactly one project-local
ETC trace-boundary leaf:

```text
ETC-ACTION-WITH-COMMIT-EXPLORE-PHASE
```

New compiled file:

```text
BanditRLProof/Algorithms/ETCTrace.lean
```

New compiled definition and theorem:

```lean
def ETC.actionWithCommit
    {K : Nat} (spec : ETC.Spec K) (commitArm : Fin K) :
    ActionTrace (Fin K) :=
  fun t : Nat =>
    if t < spec.explorationPulls * K then
      ETC.exploreArm spec t
    else
      commitArm

@[simp] theorem ETC.actionWithCommit_eq_exploreArm_of_lt
    {K : Nat} (spec : ETC.Spec K) (commitArm : Fin K) {t : Nat}
    (h : t < spec.explorationPulls * K) :
    ETC.actionWithCommit spec commitArm t = ETC.exploreArm spec t
```

Implementation route:

- imports only `BanditRLProof.Core` and `BanditRLProof.Algorithms.ETC`;
- keeps `commitArm : Fin K` explicit;
- proves only the exploration-prefix agreement by simplifying the `if`;
- does not prove the commit-phase theorem;
- does not prove pull-count or regret facts about `actionWithCommit`;
- does not introduce empirical means, argmax, probability, concentration,
  filtration, conditional expectation, or final ETC regret.

Verification from the current worktree:

```text
python3 tools/bandit.py list-lean-decls actionWithCommit --statement
BanditRLProof.ETC.actionWithCommit [def] BanditRLProof/Algorithms/ETCTrace.lean:17
  def actionWithCommit {K : Nat} (spec : ETC.Spec K) (commitArm : Fin K) : ActionTrace (Fin K) :=
BanditRLProof.ETC.actionWithCommit_eq_exploreArm_of_lt [theorem] BanditRLProof/Algorithms/ETCTrace.lean:32
  @[simp] theorem actionWithCommit_eq_exploreArm_of_lt {K : Nat} (spec : ETC.Spec K) (commitArm : Fin K) {t : Nat} (h : t < spec.explorationPulls * K) : ETC.actionWithCommit spec commitArm t = ETC.exploreArm spec t

python3 tools/bandit.py check
Build completed successfully (1780 jobs).
Build completed successfully (1782 jobs).
$ lake build
$ lake build Tests
check passed
```

Updated:

- root import in `BanditRLProof.lean`;
- one consumer test in `Tests/Basic.lean`;
- `tools/bandit.py` local leaf card and `unfinished` recommendation output;
- `README.md`, completion gap audit, project overview, collaborator guide,
  Mathlib foundation leaf map, bandit theory tree;
- retrieval indexes and UCB/ETC memory refresh JSON.

Current local ETC surface now includes:

```lean
ETC.exploreArm
ETC.exploreArm_eq_iff_mod_eq_val
ETC.pullCount_exploreArm_explorationPulls_mul_K_eq
ETC.pseudoRegret_exploreArm_explorationPulls_mul_K_le_sum_gap_mul_explorationPulls
ETC.actionWithCommit
ETC.actionWithCommit_eq_exploreArm_of_lt
```

Questions:

1. Is the next single executable leaf the complementary commit-phase theorem?
2. If yes, should the statement use `¬ t < spec.explorationPulls * K` or
   `spec.explorationPulls * K <= t`?
3. What exact Lean-facing statement should be attempted next?
4. What imports/local APIs should it use?
5. What regularity contracts should it require?
6. How should it be classified: imported, port candidate, Mathlib candidate,
   project-local, or theorem-card-only?
7. What should the failure policy be?

Please keep the recommendation to one small compiled Lean leaf. Do not
recommend pull-count facts, regret facts, empirical means, commit argmax,
probability, concentration, filtration, conditional expectation, or a final ETC
regret theorem in this batch.
