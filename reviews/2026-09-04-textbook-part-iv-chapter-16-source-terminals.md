# Chapter 16 source-terminal review and handoff

Date: 2026-09-05

Task: `TEXTBOOK-PART-IV-CHAPTER-16-INSTANCE-DEPENDENT-LOWER-BOUNDS-SPINE`

## Source audit and compiled result

Definition 16.1, the finite-mean source mean-to-gap producer, Theorem 16.2,
Lemma 16.3, and Theorem 16.4 compile in
`BanditRLProof/LowerBounds/InstanceDependent.lean`. The Chapter 16 canary
passes with only `propext`, `Classical.choice`, and `Quot.sound`.

The audit used physical pages 216--219 of the official author PDF:
<https://tor-lattimore.com/downloads/book/book.pdf>.

- Definition 16.1 retains one policy, every environment, and every real p>0.
- Theorem 16.2 retains arbitrary unstructured finite-mean probability-law
  component classes, strict mean improvement, original-to-alternative KL,
  and original-law expected pulls. Exact n-pull sequences include n=0.
  Inverse-infimum aggregation keeps empty, zero, finite, and infinite
  information cases. Finite-count Fatou proves the sum/liminf direction.
- Lemma 16.3 retains the exact minimum, 1/4, both regrets, and KL direction.
  Zero KL contradicts distinct finite means; infinite KL is explicit.
- Theorem 16.4 retains unrestricted real unit-Gaussian means, nonempty N,
  C>0, p in (0,1), epsilon in (0,1], the local coordinate box, 8C,
  2/(1+epsilon)^2, and the positive part of the entire per-gap quotient.

No per-arm liminf conclusion was substituted for source consistency.
Optional exercises and other Table 16.1 distribution families are outside
the requested four-item main-text scope.

## Exact declarations

- `LowerBounds.IsConsistentPolicyOver`
- `LowerBounds.oneArmMeanChange_produces_gap_contract`
- `LowerBounds.consistentPolicy_liminf_expectedPull_div_log_ge_inv_dInf`
- `LowerBounds.consistentPolicy_liminf_expectedRegret_div_log_ge`
- `LowerBounds.expectedPullCount_ge_log_regret_changeOfMeasure`
- `LowerBounds.gaussianExpectedRegret_ge_finiteTimeInstanceDependent`

## Verification

- Focused module: passed, 3584 jobs.
- Updated Chapter 16 canary: passed; standard axiom set only.
- Full library/test build within harness: passed, 8852/8894 jobs.
- Full Python harness suite: passed, 400 tests, 7 skipped; `check passed`.
- Site build and check: passed, 658 HTML pages, 604 modules, 8266 declarations,
  9035 Lean source links; internal links and anchors valid.
- Browser: desktop 1280x800 and mobile 390x844 inspected. Mobile reload
  resolved the transient cropped capture; title, body, source links, and
  compiled status display correctly. No whole-page horizontal overflow or
  broken images. Temporary viewport override reset.
- Final commit/PR and current-main comparison: pending.

Windows validation temporarily used `buildDir := "E:/abrl16-build"`, a
junction to this worktree's `.lake/build`, to avoid a pre-existing long RL
module output-path limit. The override and junction were removed after the
passing full gate; `lakefile.lean` matches the original tracked configuration.

## Reusable continuation prompt

Finish the delivery audit for this Chapter 16 task. The exact three source
theorems and Definition 16.1 compile; do not redo or weaken them. Read the
current verification logs, finish the full harness run, refresh index,
Blueprint, memory, frontier-shadow and trial summary after final edits,
ensure all current docs/site/export statuses agree, remove the temporary
Windows buildDir workaround, inspect the diff, and create the authorized
commit and PR. Preserve the exact paper title:
ABRL: A Target-Faithful Autoformalization Harness and Lean 4 Library for
Bandit and Reinforcement Learning Theory.
Do not merge this PR.

Primary isolated worktree:
`E:\CodexWorktrees\61cf\Auto-Bandit-RL-Proof-In-Sleep-github-sync`

Secondary authoritative checkout (inspect before use):
`E:\code\Auto-Bandit-RL-Proof-In-Sleep-github-sync`
