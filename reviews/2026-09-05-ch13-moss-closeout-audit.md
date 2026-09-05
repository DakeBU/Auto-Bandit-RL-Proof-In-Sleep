# Chapter 13 MOSS evidence closeout audit

This is an in-branch self-audit, not an independent review or completion
certificate. Current PR-validated tree: 90b1c07, merged as b38630c.
Chapter status remains partial pending main/deployment/live acceptance.

## PR acceptance

### Authoritative-main and deployed-page acceptance

Main run 33953476610 completed successfully on b38630c. Build job
101272447506 passed library 8880 jobs, Tests 8927 jobs, ProofGraphExport,
400 Python tests in 70.266 seconds (3 skipped), result-free protocol
validation, public-snapshot site build/check and Pages artifact upload.
Deployment job 101275173069 also passed. Live site-manifest.json reports
source_commit b38630cb18c9724252432647443cfe3c031da4e5, source_dirty false,
lean_verified true, public_snapshot true, 632 modules, 8453 declarations,
zero placeholders, and generation time 2026-09-05T08:08:56+00:00.

The deployed Chapter 13 page was inspected at desktop 1280x720 and mobile
390x844. Desktop text is legible with zero broken images and document width
1265. Mobile text and the minimax formula are legible after reload resolved
the transient screenshot/layout scaling discrepancy; document width is 375,
with zero broken images. The Lean correspondence region has client width
341, content width 704 and overflow-x:auto. Actual horizontal scrolling
moved scrollLeft from 0 to 350 and exposed the role/type columns without
document-level overflow. The three MOSS/common-history/broad-class terminal
links are present. Temporary viewport overrides were reset.

The live page correctly retains its pre-promotion Partial main-text label
and explicitly optional Notes/Exercises. This acceptance closes the
publication gate for the mathematical extension; it does not claim that
the subsequent status-summary edits or completion labels are deployed.
Those final synchronized records still require publication and verification.

PR #105 was marked ready after the local source/consumer/export/mobile
review and merged at b38630cb18c9724252432647443cfe3c031da4e5. Its head
90b1c0742cbfd3783dbf7cdf99c1f3b9d82f4223 passed all three workflows:
Lean/documentation 33952076777, lifecycle 33952076768 and pinned-source
preflight 33952076771. Build job 101268669875 completed the full harness,
result-free protocol validation, verified website build and site checks.
Logs confirm Tests 8927 jobs, 400 Python tests in 90.845 seconds with
3 skipped, and 686 pages / 8453 declarations / 118 highlights. The Linux
skip count is distinct from the local Windows run's 7 skips.

No submitted reviews or inline review threads were present at the final
pre-merge check. The in-branch structured review above is not represented
as an independent approval. Git diff between the PR head and merge tree
is empty. PR artifact upload and deployment were skipped by workflow
design, so PR success is not deployment evidence.

Authoritative-main run 33953476610 is now active on b38630c (build job
101272447506). Its outcome, Pages deployment and live desktop/mobile
verification remain unverified. Do not promote the chapter yet.

## Latest merged-tree verdict

Publication follow-up: the primary textbook banner now derives the count
of compiled chapter contracts from chapter status records, rather than
hard-coding that Chapters 13--17 all remain partial. The site checker
requires this derived count. An in-memory regression exercise verified
both zero and one compiled contracts without changing the source JSON;
all five chapter records remain partial at this stage. Python syntax
checks passed. This prepares consistent status reporting, not an early
promotion or proof-status change. The verified local rebuild and full
site check passed (686 pages, 632 modules, 8453 declarations, 118 highlights,
valid internal links and formula fallbacks); Lean sources were unchanged.

Full `python tools/bandit.py check` at e218fc8 completed successfully in
the clean short validation worktree C:/abrl13-d9682b8 (session 5092,
exit 0): library 8880 jobs, Tests 8927 jobs, ProofGraphExport and 400 Python
tests in 214.613 seconds, with 7 skipped. The target-drift template's
UNSET fields are expected result-free evaluation placeholders, not a
Chapter 13 proof failure. No evaluation outcome is claimed.

The subsequent commits through 3c0dc07 change only evidence, the export
preview and the old MOSS packet; `git diff e218fc8 3c0dc07` is empty for
Lean sources, Tests, tools and website scripts. This establishes the
unchanged executable proof baseline, not a claim that remote CI tested
3c0dc07. Local rendered-export and desktop/mobile site QA pass as detailed
below. PR #105 is open, draft and currently mergeable; its Lean/documentation
run remains in progress. Main, deployment and live verification remain open.

Structured consumer recheck: MOSSHistoryRegret explicitly transports the
finite-history law and counts through t+1 before applying constant 39.
SubgaussianMinimax quantifies over all history algorithms and stationary
unit-subgaussian arm kernels; its gap restriction does not bound absolute
means. Gaussian inclusion preserves exactly the policy and regret
functional. The upper bound uses gap sum <= k <= sqrt(k*(t+1)); multiplying
the lower constant 1/54 by 2160 recovers 40. The policy depends on k and
the horizon, not the environment mean. Typed endpoint canaries are part
of the passing Tests build. A source scan of these two consumer modules
finds no sorry, admit, added axiom or opaque declaration. No new blocking
consumer issue was found in this self-review; it is not an independent
review and does not certify the remaining publication gates.

The following sections retain the chronological audit trail. Later explicit
passing verdicts supersede earlier running/inconclusive observations.

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

Mobile follow-up resolves the earlier visual discrepancy: resetting browser
zoom with Ctrl+0 restored consistent screenshot scaling (devicePixelRatio
1.5). At viewport 390x844, fresh normal screenshots now show complete body
text and the minimax formula without right-edge clipping. Document scroll
width is 375. The declaration table intentionally has a 341px viewport and
704px content with overflow-x:auto; an actual horizontal scroll moved its
scrollLeft to 350. This verifies access to the hidden columns without
document-level overflow. No CSS change was made. Temporary viewport override
was reset. Local mobile layout QA passes; post-deployment live QA remains
a distinct gate.

Merged-tree verified website build/check also passed: 686 pages, 632
modules, 8453 declarations, 118 highlights, zero placeholders and valid
internal links. The additional Chapter 14 declarations are present; this
supersedes the pre-merge 8440-declaration site count. The old MOSS open-
dependency packet is now marked mathematically compiled and explicitly
retains integration/publication gates.

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
