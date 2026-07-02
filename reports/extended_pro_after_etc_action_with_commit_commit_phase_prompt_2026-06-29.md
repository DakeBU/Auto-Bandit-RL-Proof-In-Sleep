# Extended Pro Review Prompt: After ETC-ACTION-WITH-COMMIT-COMMIT-PHASE

We are working in the ABRL Lean 4 repository for formalizing bandit/RL theory.

Following your previous recommendation, I completed exactly one additional
project-local ETC trace-boundary leaf:

```text
ETC-ACTION-WITH-COMMIT-COMMIT-PHASE
```

The existing trace file is now:

```text
BanditRLProof/Algorithms/ETCTrace.lean
```

Compiled definition and phase-boundary theorems:

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

@[simp] theorem ETC.actionWithCommit_eq_commitArm_of_ge
    {K : Nat} (spec : ETC.Spec K) (commitArm : Fin K) {t : Nat}
    (h : spec.explorationPulls * K <= t) :
    ETC.actionWithCommit spec commitArm t = commitArm
```

Implementation route for the commit-phase theorem:

- no new imports beyond `BanditRLProof.Core` and
  `BanditRLProof.Algorithms.ETC`;
- public condition is `spec.explorationPulls * K <= t`;
- proof uses `Nat.not_lt_of_ge h` to simplify the inactive exploration branch;
- no `not_lt` companion theorem;
- no pull-count transfer, regret fact, empirical mean, argmax, probability,
  concentration, filtration, conditional expectation, or final theorem.

Verification from the current worktree:

```text
python3 tools/bandit.py list-lean-decls actionWithCommit --statement
BanditRLProof.ETC.actionWithCommit [def] BanditRLProof/Algorithms/ETCTrace.lean:17
  def actionWithCommit {K : Nat} (spec : ETC.Spec K) (commitArm : Fin K) : ActionTrace (Fin K) :=
BanditRLProof.ETC.actionWithCommit_eq_exploreArm_of_lt [theorem] BanditRLProof/Algorithms/ETCTrace.lean:32
  @[simp] theorem actionWithCommit_eq_exploreArm_of_lt {K : Nat} (spec : ETC.Spec K) (commitArm : Fin K) {t : Nat} (h : t < spec.explorationPulls * K) : ETC.actionWithCommit spec commitArm t = ETC.exploreArm spec t
BanditRLProof.ETC.actionWithCommit_eq_commitArm_of_ge [theorem] BanditRLProof/Algorithms/ETCTrace.lean:45
  @[simp] theorem actionWithCommit_eq_commitArm_of_ge {K : Nat} (spec : ETC.Spec K) (commitArm : Fin K) {t : Nat} (h : spec.explorationPulls * K <= t) : ETC.actionWithCommit spec commitArm t = commitArm

python3 tools/bandit.py check
Build completed successfully (1780 jobs).
Build completed successfully (1782 jobs).
$ lake build
$ lake build Tests
check passed
```

Updated:

- one consumer test in `Tests/Basic.lean`;
- `tools/bandit.py` local leaf card and `unfinished` recommendation output;
- `README.md`, completion gap audit, project overview, collaborator guide,
  Mathlib foundation leaf map, bandit theory tree;
- retrieval indexes and UCB/ETC memory refresh JSON.

Current boundary:

- The basic fixed-commit ETC phase API is now available.
- No pull-count or regret facts about `ETC.actionWithCommit` exist yet.
- No empirical mean or commit argmax theorem.
- No probability, concentration, filtration, conditional expectation, or final
  ETC regret theorem.

Questions:

1. What is the next single executable leaf?
2. Should it be an exploration-prefix pull-count transfer for
   `ETC.actionWithCommit`, or a generic phase-splitting helper?
3. What exact Lean-facing statement should be attempted next?
4. What imports/local APIs should it use?
5. What regularity contracts should it require?
6. How should it be classified: imported, port candidate, Mathlib candidate,
   project-local, or theorem-card-only?
7. What should the failure policy be?

Please keep the recommendation to one small compiled Lean leaf. Do not
recommend regret facts, empirical means, commit argmax, probability,
concentration, filtration, conditional expectation, or a final ETC regret
theorem in this batch.
