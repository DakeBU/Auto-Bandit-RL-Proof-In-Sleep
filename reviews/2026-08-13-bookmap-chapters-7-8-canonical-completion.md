# Evidence review: Book Map Chapters 7--8 canonical completion

Task: `BOOKMAP-CHAPTERS-7-8-CANONICAL-COMPLETION`

Date: 2026-08-13

Mode: local read-only statement/source review plus compiler and deterministic
gates; no separate reviewer agent was invoked in this run.

## Decision

`ACCEPT`.  P0: none.  P1: none.  P2: none.  P3: none.

The two decisions are independent:

- `CH7-EXP3-CANONICAL-COMPLETION`: accepted under the scoped canonical
  definition in the task packet;
- `CH8-TSALLIS-FTRL-CANONICAL-COMPLETION`: accepted under its separate scoped
  canonical definition.

Neither decision is used as evidence for the other.

## Chapter 7 findings

- The expected theorem and fixed-window best-supported-arm theorem rebuild
  tuned `eta`, `gamma`, and the generated trajectory law from the supplied
  horizon.  They are not a fixed-policy anytime result.
- The all-positive-prefix terminal fixes one prior, arms set, predictable loss,
  `eta`, `gamma`, comparator, and generated trajectory law.  It consumes the
  predictable-regret parent, realized-deviation parent, and exact pathwise
  decomposition through geometric countable outer-measure control.
- The sparse/variance-sensitive theorem retains its explicit sparsity-failure
  probability.  It is an extension, not a premise silently inserted into the
  canonical expected or all-prefix route.
- The dedicated canary gives full-conclusion applications of the expected,
  fixed-window, all-prefix, and sparse terminals and checks their named parent
  declarations.

## Chapter 8 findings

- The checked selector, conditional action law, observed-score alignment,
  stability, self-bound, and expected-regret consumers use the canonical
  scheduled half-Tsallis generated trajectory surface.
- The final IID theorem constructs the loss state, selector,
  `Measure.infinitePi` prior, trajectory kernel, and trajectory measure in one
  exact `let` chain; no detached sample model is substituted.
- The dedicated concrete application uses `Fin 2` with IID Dirac arm laws of
  means `3/4` and `1/4`.  It proves the selected best arm, probability laws,
  a.e. `[0,1]` support, exact means, and the positive non-best gap before
  applying the terminal with corruption allowance zero.
- The result remains a finite-horizon expected logarithmic reciprocal-gap
  theorem.  It is not labelled paper-sharp/minimax Tsallis-INF, complete
  best-of-both-worlds, high-probability/realized regret, or an observed-reward
  restart theorem.

## Deterministic evidence

- Focused command:
  `lake env lean Tests/BookMapChaptersSevenAndEightCanary.lean` -- exit 0.
- Statement fences:
  - Chapter 7: `34d6b6dd7518f9b531186f8db39ab7f52a67b685605a43cc8c5871d3fa295702`;
  - Chapter 8: `32fd5bce5e128e8c002665a9d6344b82cfdaf9727ba20a08b57223b758eb0bc8`.
  Both final `safe-verify` runs report exact hash equality, assumptions
  preserved, and no findings.
- Six representative `#print axioms` reports contain only `propext`,
  `Classical.choice`, and `Quot.sound`.
- Final full command: `python3 tools/bandit.py check` -- exit 0; 3675 Lake
  jobs completed; 42 Python tests passed with one skipped.
- Website build/check is rerun after final lifecycle synchronization; its exact
  counts are recorded in the final handoff.

This review is an evidence audit, not a claim of independent human or
sub-agent review.  Lean elaboration, exact statement fences, the repository
gate, and remote GitHub Actions are the independent machine checks used for
acceptance.
