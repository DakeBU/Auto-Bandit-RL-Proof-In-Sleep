# Chapter 13 exact Mills-ratio integration audit — 2026-09-05

Scope: committed Lean extension at `1203c63`, plus source/evidence updates.
This is an in-branch self-review, not an independent-agent review.

## Verified

- Both exact Eq. (13.4) integral bounds and printed Eq. (13.1) compiled in
  focused builds and the full-statement canary. The source probability
  theorem requires n>0 and Delta>0; denominator constants are 16 and 32/pi.
- Full root library build passed in `C:\abrl13-d9682b8` at `1203c63`:
  8,854 jobs. Full Tests build passed: 8,896 jobs.
- `tools/ProofGraphExport.lean` passed. The Python unit-test stage of
  `python tools/bandit.py check` is still running; do not report the whole
  harness as passed until its final exit status is collected.
- Maintained task, conversion window, proof obligations, Markdown/LaTeX
  export, textbook/Mathlib cards, theory tree, README and website records
  now distinguish compiled exact Mills bounds from the open MOSS dependency.
- Blueprint, reference index and task memory regenerated.
- Website build with `--lean-verified` passed following the root Lean gate.
  `check_site.py` passed: 660 pages, 606 modules, 8,262 declarations, no
  placeholders, internal links/anchors valid. This is a local dirty-source
  build, not a remote deployment or authoritative-main gate.
- Desktop browser preview at 1280x720 shows the new status and separate
  compiled-route / partial-chapter labels.

## Remaining checks and findings

- Mobile 390x844 DOM measurements show no document horizontal overflow;
  main width is about 343 px and sampled paragraph line rectangles end
  before x=357. However, screenshots appear to clip text at the right edge
  despite these measurements (devicePixelRatio=1.5). Mobile visual QA is
  inconclusive, not passed; resolve the capture/layout discrepancy before
  claiming a clean mobile preview. Temporary viewport overrides were reset.
- Full harness Python tests, final clean-commit site rebuild, PR/remote
  gates and deployment checks remain pending.
- Mathematical completion still requires Algorithm 7 / Theorem 9.1's
  broader-class MOSS upper side. Its exact source target, assumptions,
  no-extra-log concentration route and next deterministic leaf are recorded
  in `open-problem-proposals/CH13-MOSS-UPPER.md`. The open-problem skill
  was used to preserve this dependency explicitly, not to weaken the target.
- Chapter 13 stays `partial`. Notes and exercises are optional; they are
  not the reason for the incomplete main-text contract.
