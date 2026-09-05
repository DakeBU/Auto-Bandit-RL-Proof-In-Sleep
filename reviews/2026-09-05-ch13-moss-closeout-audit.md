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

- Current-commit full harness and verified site build/check.
- Rendered export verification and exact source/declaration coverage audit.
- Structured final review; this self-audit does not substitute for a
  separately required independent review.
- Desktop/mobile visual checks; earlier mobile capture was inconclusive.
- PR and authoritative-main Actions, Pages deployment and live-page checks.
- Reconcile all completion checkboxes against current evidence before any
  chapter status promotion. Optional Notes/Exercises remain outside scope.
