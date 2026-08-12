# Independent Review: Book Map Chapters 5--6 canonical completion

Date: 2026-08-12  
Task: `BOOKMAP-CHAPTERS-5-6-CANONICAL-COMPLETION`  
Mode: evidence-only review of the external canary, theorem signatures, source
modules, synchronized ledgers, and website claims.  The review does not supply
or modify any theorem proof.

## Final verdict

- P0: none.
- P1: none.
- P2: none after the concrete-kernel canary repair described below.
- P3: none.
- Chapter 5 canonical scope: accepted.
- Chapter 6 stationary canonical scope: accepted.

## Chapter 5 findings

The all-time producer, all-horizon regret theorem, bounded stopping theorem,
and square-integrable stopping theorem all expose the same horizon-free
`finiteHistoryTelescopingScalarRidgeOptimisticAlgorithm` arguments and the
same `canonicalHistoryTrajectoryMeasure`.  Expected consistency is correctly
recorded as a separate horizon-indexed family.  The producer structure contains
only the theta-norm bound and centered sub-Gaussian laws for the initial and
successor reward kernels.  It does not contain a confidence or regret result.

The stopping terminal preserves the canonical all-round filtration,
`IsStoppingTime`, and `SquareIntegrableFiniteStoppingTime`; its conclusion
retains the exact second-moment and bad-event terms.  No pathwise,
almost-sure, universal optional-stopping, minimax, contextual, dynamic, or BwK
claim follows.

## Chapter 6 findings

The probability-matching canary restates the complete `let` chain: recursive
uniform-reference Thompson algorithm, canonical trajectory kernel, actual
joint measure, actual generated finite history, and successor action.  Thus it
does not test a separately adjoined sampler.

The final canary instantiates the stationary theorem using `Unit`, `Fin 1`, a
constant Markov kernel with `gaussianReal 0 1`, zero measurable mean, and an
explicit proof of centered `HasSubgaussianMGF` with proxy one.  The first
compile exposed only a missing reducibility/typeclass bridge for the wrapped
constant kernel; adding a local `IsMarkovKernel` instance and normalizing the
two casts closed it without changing any theorem target.

The exact terminal is
`(2*K+1)*(u-l) + 8*sqrt(sigma2*K*n*log n)` under the explicit prior,
Standard-Borel, Markov, measurability, bounded-mean, sub-Gaussian, and nonzero
proxy assumptions.  It is not a universal Thompson, contextual/linear TS,
PSRL, sharp asymptotic, or literal LML identity theorem.

The first independent review found that the earlier terminal admitted any
measurable selector.  The repair adds `Thompson.IsOptimalMeanSelector`, threads
it through both stationary terminals, and proves it in the concrete canary.
The decomposition itself is now documented honestly as comparator-relative.

## Canary and axiom evidence

- `lake build Tests.BookMapChaptersFiveAndSixCanary` completes successfully
  with 3231 jobs.
- The six requested canary groups are present.
- Axiom reports for the four OFUL terminal layers, recursive Thompson
  matching, and final stationary regret contain only `propext`,
  `Classical.choice`, and `Quot.sound`.
- No new library theorem or axiom was added; the only new Lean object is the
  external typed/concrete test module.

## Final-gate addendum

- Independent read-only delta review: P0/P1/P2/P3 all none.
- `python3 tools/bandit.py check`: passed; 3664 Lean jobs and 42 Python tests
  with one intentional skip.
- Lean-backed site: 535 modules, 7023 declarations, 51 teaching
  highlights/milestones.
- Site check: 557 HTML pages, 13 Mermaid blocks, 15167 Lean source links;
  internal links, declaration anchors, README links, MathJax, and Pages
  workflow checks all pass.
- JSON parsing and `git diff --check`: pass.
