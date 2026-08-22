# Independent review: Chapter 16 event-to-regret extension

Date: 2026-08-22

Scope: the fifteen-declaration Chapter 16 gap-event/regret extension in
`BanditRLProof/LowerBounds/InstanceDependent.lean`, its root-import canary,
task/conversion/obligation and generated retrieval artifacts, anonymous
claim-ledger validator, and desktop/mobile textbook page. The reviewer was
read-only: it did not edit files or start a Lean build.

## Verdict

No Blocking, High, or Medium finding remains in this scoped extension. The
review accepts the fifteen declarations as a compiled conditional consumer;
it does not promote source Lemma 16.3 or Theorems 16.2/16.4.

## Mathematical checks

- `finiteHistoryGapPseudoRegret` is the inclusive-horizon sum of
  `gap arm * pullCount arm` in `ENNReal`; its canonical expectation uses the
  exact randomized `HistoryAlgorithm` and Markov arm environment.
- `oneArmMajorityPullEvent` is `2 * T_i > lastRound + 1`, matching the source
  event `T_i(n) > n/2` under `n = lastRound + 1`.
- Under the original environment, the event is charged using the changed
  arm's original gap. Under the one-arm alternative, its complement is charged
  using the stated uniform lower bound on every non-changed arm gap. Both laws
  use the same nonanticipating randomized history policy.
- The history KL direction is original to alternative,
  `D(P_i, P_i')`, and the pull-count multiplier is the original-environment
  expectation `E_P[T_i(n)]`.
- Bretagnolle--Huber contributes the source factor `1/2`; the two exact
  half-horizon pseudo-regret charges contribute the second factor `1/2`, so the
  combined lower bound retains factor `1/4`.
- The logarithmic conclusion assumes an explicit finite positive arm KL and a
  nonnegative gap vector. It does not construct the textbook finite-mean
  arm-law-to-gap interface and therefore is not source Lemma 16.3.

## Evidence checks

- The generated declaration index contains exactly the predecessor twenty
  Chapter 16 declarations plus the fifteen new public declarations, all with
  unique fully qualified names.
- The website exposes separate `compiled/20` and `compiled/15` records while
  the source-terminal record remains `blocked` with zero declarations.
- The anonymous supplement validator requires the exact frozen sets of twenty
  and fifteen unique declarations and separately requires the source-terminal
  record to remain blocked and empty. Negative tests cover all three drifts.
- The task, conversion window, obligation table, README, Blueprint, result,
  highlight, and textbook-spine records keep the whole chapter `partial` and
  keep the finite-mean bridge, asymptotic extraction, Lemma 16.3, Theorem 16.2,
  and Theorem 16.4 open.

The source comparison used Lattimore--Szepesvari, *Bandit Algorithms* (2020),
official author PDF, Section 16.2, author-online pp. 207--210 and physical PDF
pp. 216--219: <https://tor-lattimore.com/downloads/book/book.pdf>.

## Local verification evidence

- `lake build BanditRLProof.LowerBounds.InstanceDependent`: passed (3,584
  jobs).
- `lake build Tests.TextbookPartIVChapter16Canary`: passed (8,828 jobs);
  representative axiom reports contain only `propext`, `Classical.choice`, and
  `Quot.sound`.
- `python tools/bandit.py check`: passed after full Lean and Tests builds (8,848
  jobs), proof-graph export, and 198 Python tests with four platform skips.
- `python website/scripts/build_site.py --lean-verified`: passed with 580
  modules, 7,754 scanner declarations, 91 highlights, 74 milestones, and zero
  placeholders.
- `python website/scripts/check_site.py`: passed with 609 pages and 16,759
  Lean source links.
- Browser checks at 1280x720 and 390x844 found no document-level overflow. The
  mobile correspondence table scrolls only inside its labelled focusable
  region, and the drawer preserves inert/ARIA, focus trapping, Escape closure,
  and focus return.
- All 15 anonymous-supplement builder tests passed.

## Residual and remote boundary

The finite arm-law mean/optimal-arm-to-gap producer, the full source-general
Lemma 16.3 statement, Theorem 16.2's extended-real and liminf branches, and
Theorem 16.4 remain blocked. The current extension has not yet passed a PR,
authoritative-main Actions, Pages deployment, or live-page check; those remote
gates must be recorded only after the branch is merged.
