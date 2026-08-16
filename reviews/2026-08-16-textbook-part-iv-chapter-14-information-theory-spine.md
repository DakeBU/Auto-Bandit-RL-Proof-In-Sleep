# Evidence review: Textbook Part IV Chapter 14 information-theory spine

Task: `TEXTBOOK-PART-IV-CHAPTER-14-INFORMATION-THEORY-SPINE`

Date: 2026-08-16

Mode: independent read-only Codex review of `origin/main...5a84d26`, covering
the maintained Chapter 14 source contract, Lean module, typed canary, proof
obligations, proof export, and website data. This is an independent model
review, not a human review.

## Decision

`ACCEPT`. P0: none. P1: none. P2: none. P3: none unresolved.

The accepted scope is the source-faithful Chapter 14 §14.2 lower-bound
foundation: extended-real relative entropy, its absolute-continuity and
integrability branches, Bernoulli KL including singular endpoints, the
event-level binary data-processing leaf, and the exact unconditional
Bretagnolle--Huber event inequality. Chapter 14 remains `partial` at the
chapter-page level because §14.1 coding results and the full Exercise 14.10
are mapped but not formalized.

## Review trail

Read-only review session: `01a00a9a-8d8b-7440-aac3-ad45d1a634f6`.

The reviewer reported: "No actionable P0-P3 findings." It independently
checked that:

- relative entropy and event data processing preserve the direction
  `D(P,Q)`;
- the testing terminal is `P(A) + Q(Aᶜ)`, with the complement evaluated
  under `Q`;
- Theorem 14.2 remains unconditional through the explicit zero scale at
  infinite KL;
- absolute continuity and log-likelihood integrability are visible exactly
  where the finite branch needs them;
- Bernoulli endpoint and support-mismatch cases follow the existing
  extended-real convention; and
- no adaptive same-policy history KL theorem is promoted in Chapter 14.

The reviewer made no edits.

## Statement fence

- `relativeEntropy` is an alias of Mathlib's extended-real `klDiv`; the local
  adapters do not redefine measure KL.
- `relativeEntropy_ne_top_iff` exposes both `P ≪ Q` and integrability of the
  log likelihood ratio rather than hiding a regularity premise.
- `bernoulliRelativeEntropy_event_le` is the event/binary specialization of
  data processing. It is not presented as the full sub-sigma-algebra result
  in Exercise 14.10.
- `bretagnolleHuberScale` explicitly implements `exp(-∞)=0`, so
  `bretagnolleHuber` has no finite-KL or mutual-AC premise.
- The Chapter 15 kernel/history construction, policy consistency, and
  pull-count decomposition remain planned consumers.

## Deterministic evidence

- Commit `5a84d26` was checked from the detached short-path worktree
  `C:\abrl-p4-ch14-final-5a84d26` to avoid Windows path-length artifact
  failures.
- `python3 tools/bandit.py check` passed completely: the root library built in
  3,690 jobs, `Tests` built in 3,703 jobs, and 42 Python tests passed with one
  expected skip.
- The root-import typed canary covers finite and singular cases and prints
  axioms for the public Chapter 14 declarations. The reports contain only
  `propext`, `Classical.choice`, and `Quot.sound`.
- `python3 website/scripts/build_site.py --lean-verified` and
  `python3 website/scripts/check_site.py` passed with 560 modules, 7,383
  declarations, zero placeholders, and 588 checked pages.
- Desktop and 390-pixel mobile browser inspections found no broken images or
  document-level horizontal overflow; MathJax rendered the Chapter 14
  formulas, and the long table remained locally scrollable.

## Remote evidence

- PR #11 passed the required `Lean and documentation / build` check in run
  `31948234489`, job `95167560544`, and was merged without a direct push to
  `main`.
- Merge commit: `194aca91b5d9b50c26fffaf5b02c610112a7daa7`.
- Authoritative-main run `31949303227` passed. Build job `95170181038`
  completed Lean, Tests, the lean-verified site, site checks, and Pages
  artifact upload in 20m56s. Deployment job `95172626370` passed in 10s.
- Live page:
  <https://dakebu.github.io/Auto-Bandit-RL-Proof-In-Sleep/textbook-spine/chapter-14-information-theory/>.
  Desktop 1280px and 390x844 mobile inspection confirmed the verified banner,
  `PARTIAL` chapter status, compiled Theorem 14.2 correspondence, the Chapter
  15 adaptive-history boundary, five rendered MathJax containers, zero broken
  images, and no document-level horizontal overflow.

This evidence promotes the scoped Chapter 14 task to `accepted`; the chapter
page remains `partial` because §14.1 coding, full Exercise 14.10, and adaptive
history KL are not local compiled declarations.
