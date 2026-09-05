# Review: Textbook Part IV Chapter 13 source-faithful closure

Date: 2026-09-04

Scope: Chapter 13 source inventory, production Lean, the root-import typed
canary, lifecycle artifacts, proof export, evidence indexes, and the local
Part IV website. This is a structured in-branch audit, not an independent
external review.

## Findings

### P0--P2

No actionable finding.

### P3: unsupported website section-status value

The first lean-verified website build rejected `optional` as a section status.
The repository's status vocabulary has no such enum value. Sections 13.2 and
13.4 now use the supported `source` status, while their scope text still says
that Notes and Exercises are optional, indexed, and unformalized. The website
build and strict site check pass after the correction.

## Source and mathematical checks

- The official author PDF was audited at physical pp. 189--194, corresponding
  to author-online pp. 180--185 and CUP print pp. 155--159.
- The required main-text inventory distinguishes the chapter opening and
  Theorem 13.1, Section 13.1 and Eqs. (13.1)--(13.3), and the broader
  Algorithm 7 / Theorem 9.1 near-minimax statement from optional Notes and
  Exercises.
- Theorem 13.1 remains the compiled Chapter 15 consumer with explicit constant
  `1/54`; it is not re-proved or relabeled as local Chapter 13 algebra.
- `IsMinimaxOptimal` packages membership in the fixed policy class and exact
  attainment of the corresponding fixed-class minimax value. It does not
  claim that such a policy always exists.
- `gaussianIIDObservationLaw` is the canonical finite product of unit-variance
  Gaussian coordinate laws. Characteristic-function factorization proves its
  coordinate sum has law `N(n*mu,n)`, and the positive-size scaling theorem
  identifies the arithmetic-mean pushforward with `N(mu,1/n)`.
- Both midpoint decision error sets have the intended orientation. The
  compiled maximum-risk bound is the honest Chernoff companion
  `exp(-n*Delta^2/8)`, not either side of source Eq. (13.1).
- The exact two-sided Mills-ratio Eq. (13.1), whose analytic source is Eq.
  (13.4), remains blocked. The broader finite-arm 1-subgaussian statement also
  remains partial until a compiled MOSS/Algorithm 7 upper theorem exists.
- No changed-environment expectation is identified definitionally with a base
  expectation, and the Chapter 13 deterministic algebra retains its explicit
  cross-law discrepancy premise.

## Lean and evidence checks

- The focused `BasicIdeas` and `GaussianHypothesisTesting` modules compile.
- The external Chapter 13 canary compiles through the root import, including a
  concrete eight-sample iid mean-law application and both Gaussian error
  branches.
- Public axiom reports are baseline-only: `propext`, `Classical.choice`, and
  `Quot.sound`.
- The production module and canary contain no proof placeholders.
- On the short-path exact-commit worktree, `python tools/bandit.py check`
  passes: root build 8853 jobs, Tests build 8895 jobs, proof-graph export, 400
  Python tests with seven skips, and the harness checks.
- The original long-path worktree reaches the known Windows path-length
  failure when creating an unrelated very-long RL `.olean`; the same target
  and complete gate pass in the short-path worktree, so this is classified as
  a Windows path-length/build-artifact failure rather than a Lean regression.
- `build_site.py --lean-verified` and `check_site.py` pass. Browser inspection
  at 1280x720 and 390x844 finds no broken images or document-level horizontal
  overflow, and visibly preserves the Compiled theorem-route / Partial whole-
  chapter distinction.

## Verdict

The current dependency extension is source-faithful and gate-clean with no
unresolved P0--P3 finding. It closes the explicit iid empirical-mean bridge,
fixed-class minimax-optimality interface, midpoint error events, and weaker
Chernoff testing companion. It does not satisfy the frozen whole-chapter
completion contract: Chapter 13 must remain `partial` until exact Eq. (13.1)
and the broader-class MOSS upper consequence compile.
