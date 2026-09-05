# Chapter 16 source-terminal review and handoff

Date: 2026-09-05

Task: `TEXTBOOK-PART-IV-CHAPTER-16-INSTANCE-DEPENDENT-LOWER-BOUNDS-SPINE`

## Integration follow-up (2026-09-05)

The follow-up authorizes merging PR #104 after Chapter 15 PR #102, then
verifying Pages. This supersedes the earlier no-merge handoff below.
Main through `102c5cd` (accepted Chapter 13/14 updates) is integrated in
`94574c8`. Ch16 source and canary are unchanged from the CI-passing version.
Generated indexes were rebuilt; website conflicts preserve both mainline
chapter acceptance and the five-declaration Ch16 gate.

This intermediate integration passed the full harness: Lean library 8909
jobs, Tests 8984 jobs, 400 Python tests in 190.980 seconds, 7 skipped.
The verified site passed: 715 pages, 661 modules, 8721 declarations, and
9552 source links. Temporary Windows short-path configuration and junction
were removed. PR #102 was still open at this check; final post-#102
integration, PR #104 merge, and deployed Pages verification remain pending.

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

- Focused module: passed after rebase, 3590 jobs.
- Updated Chapter 16 canary: passed; standard axiom set only.
- Full library/test build within harness: passed, 8852/8894 jobs.
- Full Python harness suite: passed after rebase, 400 tests, 7 skipped;
  `check passed` (250.530 seconds for Python tests).
- Site build and check: passed after rebase, 658 HTML pages, 604 modules,
  8279 declarations, 9051 Lean source links; internal links and anchors valid.
- Browser: desktop 1280x800 and mobile 390x844 inspected. Mobile reload
  resolved the transient cropped capture; title, body, source links, and
  compiled status display correctly. No whole-page horizontal overflow or
  broken images. Temporary viewport override reset.
- Rebased on main `5c0ba47`, including Chapter 14 PR #103. Source changes
  merged cleanly; generated indexes were regenerated from both chapters.
  Delivery PR: <https://github.com/DakeBU/Auto-Bandit-RL-Proof-In-Sleep/pull/104>.
  Remote CI status is tracked on the PR; no merge is authorized here.

Windows validation temporarily used `buildDir := "E:/abrl16-build"`, a
junction to this worktree's `.lake/build`, to avoid a pre-existing long RL
module output-path limit. The override and junction were removed after the
passing full gate; `lakefile.lean` matches the original tracked configuration.

## Reusable continuation prompt

Review PR #104 for this Chapter 16 task. The exact three source theorems and
Definition 16.1 compile; do not redo or weaken them. The post-rebase full
harness, site, and desktop/mobile checks passed; the temporary Windows
buildDir workaround was removed. Inspect remote CI and the exact statements,
especially inverse-infimum branches and finite-count Fatou. Preserve the
exact paper title:
ABRL: A Target-Faithful Autoformalization Harness and Lean 4 Library for
Bandit and Reinforcement Learning Theory.
Do not merge this PR.

Primary isolated worktree:
`E:\CodexWorktrees\61cf\Auto-Bandit-RL-Proof-In-Sleep-github-sync`

Secondary authoritative checkout (inspect before use):
`E:\code\Auto-Bandit-RL-Proof-In-Sleep-github-sync`
