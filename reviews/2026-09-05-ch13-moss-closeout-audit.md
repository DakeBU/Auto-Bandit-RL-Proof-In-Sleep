# Chapter 13 MOSS evidence closeout audit

This is an in-branch self-audit, not an independent review or completion
certificate. Lean baseline: cdc3a51. Chapter status remains partial.

## Current evidence

- MOSSHistoryRegret compiles exact constant 39 on the common finite-history
  regret functional; SubgaussianMinimax compiles the broad gaps-in-[0,1]
  class, regret-preserving Gaussian embedding, constants 1/54 and 40 and
  universal near-minimax factor 2160. Typed canaries report only propext,
  Classical.choice and Quot.sound.
- No bounded absolute-mean assumption was added to the broad class. The
  policy is fixed-horizon Algorithm 7, not an anytime variant.
- Initialization uses the corrected T<=1+kappa. Sharp count integration
  preserves exactly one gap sum. This correction is stated in both exports.
- Full check at ad51f89 passed: root 8879 jobs, Tests 8925 jobs,
  ProofGraphExport, 400 Python tests in 187.815s, 7 skipped. This precedes
  the broad-class consumer; it does not certify cdc3a51.
- Full check at cdc3a51 is running in C:/abrl13-d9682b8 (session 65140).
- Markdown/LaTeX exports, task/window/obligations, README, theory tree and
  site content now describe the compiled broad-class consumer. The public
  anytime MOSS source card retains its distinct unformalized status.
- Unverified local site build succeeded: 632 modules, 8440 declarations,
  zero placeholders. check_site rejected the unverified label and derived
  SGB compiled labels. Do not weaken these checks: rebuild with
  --lean-verified after validating the current Lean tree, then recheck.

## Remaining completion evidence

### Rendered proof-export gate

Added a reproducible preview.tex wrapper alongside latest.tex. TeX Live
latexmk compiled the two-page export. First rendering exposed an overfull
Theorem 13.1 declaration name; putting that unchanged name in its own
breakable quote resolved the defect. Final log has no overfull/underfull
boxes. Both pages were rendered with pdftoppm and visually inspected:
equations, constants, margins and declaration names are legible, with no
clipping. The preview is QA output, not a chapter-completion certificate.

### Main-text coverage reconciliation

| Frozen requirement | Current mathematical evidence | Boundary |
| --- | --- | --- |
| Worst-case, minimax, optimality | BasicIdeas definitions and IsMinimaxOptimal | explicit same classes and horizon; no assumed attainment |
| Theorem 13.1 | GaussianMinimax unitGaussianMinimaxExpectedPseudoRegret_ge_one_div_fiftyFour_sqrt | unit variance, means [0,1], k>1, n>=k |
| iid Gaussian sample mean and test | GaussianHypothesisTesting gaussianIIDSampleMeanLaw and both midpoint error-event identities | canonical finite iid product, n>0 |
| Exact Eq. (13.1) / (13.4) | gaussianSampleMeanZeroErrorProbability_source_bounds and both gaussianMills integral bounds | printed constants; not discharged by Chernoff |
| Competition/similarity and Eqs. (13.2)--(13.3) | BasicIdeas algebra plus GaussianMinimax common-policy history construction and tuning | informal discussion mapped to precise downstream proof, not assumed cross-law equality |
| Broader-class Algorithm 7 claim | MOSSHistoryRegret plus SubgaussianMinimax.moss_nearMinimax (namespace LowerBounds) | gaps [0,1], not bounded means; fixed horizon; actual arm-law means |
| Notes/exercises | explicitly optional under frozen contract | not claimed formalized |

This reconciliation finds no remaining named main-text mathematical node
in the frozen contract without a compiled route. It does not discharge
merged-tree validation, final review findings, mobile visual verification,
or PR/main/deployment/live gates. In particular the earlier self-review's
scope and old build evidence cannot substitute for these current gates.

### Website verification follow-up

At clean commit 9fc6054, verified site build/check passed: 686 HTML pages,
632 modules, 8440 declarations, zero placeholders, valid internal links and
formula fallbacks. Lean sources are identical to cdc3a51, whose library
build passed and full Tests/Python run continues. The browser rendered the
new MOSS declarations and separate compiled-route / partial-chapter labels.

Visual review nevertheless caught a stale MOSS-open sentence in the page's
bottom gaps list, missed by the static checker. The sentence is corrected,
the dependency nodes now include MOSS and broad-class near-minimax, and the
checker has regression guards for the three terminal correspondences and
three obsolete boundary phrases. Negative test on the old generated page
failed specifically with `Chapter 13 contains stale proof boundary`.
The corrected verified rebuild/check passed with the same 686 pages,
632 modules and 8440 declarations. The regression guard's negative and
positive cases both behaved as intended; py_compile also passed.

Desktop 1280x720 screenshot is readable. Mobile 390x844 remains inconclusive:
document scroll width 375, main bounds x=16..358.667 and paragraph width
342.667 show no horizontal overflow, but the screenshot clips right-edge
text even after reload. No CSS change is justified by the present evidence;
do not mark mobile visual QA passed. Temporary viewport override was reset.

Remote refresh finds main at 5c0ba47 (merged Chapter 14 PR #103), five
commits ahead of this branch's base. Shared changes include InformationTheory,
Chapter 14 canary, generated indexes and website records. Integrate these
without overwriting Chapter 14 progress, then validate the merged tree before
PR/deployment closure. cdc3a51 full Tests passed (8927 jobs); Python tests
continue. This remains distinct from current-main integration.

- Current-commit full harness and verified site build/check.
- Follow-up: cdc3a51 full check passed (Tests 8927 jobs, ProofGraphExport,
  400 Python tests in 239.188s, 7 skipped). Merged main 5c0ba47 into
  e218fc8, preserving its InformationTheory and Chapter 14 canary byte for
  byte. Shared prose retains both chapters; indexes regenerated. Draft
  PR #105 is open at e218fc8. Lean/documentation run 33951321752 is in
  progress; lifecycle 33951321759 and preflight 33951321751 passed.
  Merged-tree full check now runs in the clean short validation worktree.
  The primary long-path canary build encountered the known unrelated RL
  .olean path-length write failure, not a Chapter 13 proof error.
- Rendered export verification and exact source/declaration coverage audit.
- Structured final review; this self-audit does not substitute for a
  separately required independent review.
- Desktop/mobile visual checks; earlier mobile capture was inconclusive.
- PR and authoritative-main Actions, Pages deployment and live-page checks.
- Reconcile all completion checkboxes against current evidence before any
  chapter status promotion. Optional Notes/Exercises remain outside scope.
