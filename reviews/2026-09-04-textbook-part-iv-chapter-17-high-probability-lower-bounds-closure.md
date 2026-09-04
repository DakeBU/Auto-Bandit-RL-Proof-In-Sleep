# Chapter 17 high-probability lower-bounds closure review

Date: 2026-09-04

Scope: `BanditRLProof/LowerBounds/HighProbability.lean`, the Chapter 17
canary, exact-source task/obligation/export artifacts, retrieval and blueprint
surfaces, and the generated Chapter 17 website.

Verdict: **partial, submit-ready for the compiled slice**. No unresolved
P0--P2 issue was found in the declarations claimed as compiled. The chapter
must not be called complete: Corollary 17.3, Claims 17.6--17.7, the
policy-coupled pushed-forward hard law, and Theorem 17.4 remain open.

## Source and semantic audit

- Theorem 17.1 preserves one possibly randomized history policy, a premise
  quantified over the full gap-at-most-one unit-variance Gaussian class,
  original-to-alternative history KL, original-law expected pull counts, the
  outer `1/4`, and `log (1 / (4 * delta))`. Its constructed witness lies in
  the unit-cube subfamily and therefore in the source class.
- Corollary 17.2 keeps Eq. (17.6), derives the necessary `delta < 1/4`, and
  uses `B = sqrt (2 * log (1 / (4 * delta)))`, with the factor `1/2` inside
  the final square root and `1/4` outside the minimum.
- Stochastic random pseudo-regret, deterministic expected pseudo-regret, and
  adversarial random regret remain different definitions. No expected-regret
  statement is substituted for a random tail event.
- The adversarial construction uses one shared centered Gaussian noise
  coordinate per round, adds the source shifts before clipping, and is IID
  only across time. It does not introduce false within-round arm
  independence.
- `adversarialRandomRegret_ge_eq17_8` is a construction-level pathwise
  theorem for the maximum over fixed-arm comparators, rather than only the
  older conditional quarter-horizon algebra consumer.

## Compiled evidence boundary

The following new or strengthened public surfaces are within the compiled
claim boundary:

- `GapOneGaussianBanditEnvironment` and the full-class expected-regret premise;
- `gaussianRandomPseudoRegret_ge_theorem17_1`;
- `gaussianRandomPseudoRegret_ge_corollary17_2`;
- `integral_exp_neg_rpow_inv_le_one`, an analytic leaf for the still-open
  Corollary 17.3;
- `adversarialCenteredNoiseLaw`, `adversarialClaim17_6Gap`, the clipped
  shared-noise path, and its shift/clipping lemmas;
- `adversarialRandomRegret_ge_eq17_8`.

The exact terminal names for Corollary 17.3, Claims 17.6--17.7, and Theorem
17.4 are absent and remain explicitly blocked. No `sorry`, `admit`, `axiom`,
or `postulate` occurs in the scoped Lean module or canary.

## Verification

- Focused Chapter 17 module build: passed (`3588/3588`).
- A focused external canary checks the six new public surfaces. Nine axiom
  reports contain only `propext`, `Classical.choice`, and `Quot.sound`.
- Lean-verified website build: passed with 604 modules, 8259 declarations,
  zero placeholders, and 447 foundations.
- Website checker: passed for 658 HTML pages, 113 highlights, 18 Mermaid
  blocks, 9026 Lean source links, internal links/anchors, README links,
  MathJax fallbacks, and the Pages workflow.
- The proof-graph exporter compiles. The full Python harness regression suite
  passes 400 tests with seven expected skips.
- Chrome desktop visual check: the updated partial-status summary, source map,
  navigation, and Chapter 17 title render correctly at 1280×900.
- Chrome device-emulation check at 390×844: `clientWidth = scrollWidth = 390`,
  seven MathJax containers render after load, the Theorem 17.1 and Eq. (17.8)
  correspondence rows show `COMPILED`, and there are zero broken images.
- The Codex in-app browser page container timed out while attaching. The
  Chrome checks above are the browser evidence; the attach timeout is not
  represented as a site pass or failure.
- The native full root/Tests harness reaches one pre-existing unrelated RL
  module and then hits Windows `MAX_PATH` while creating its long-named
  `.olean`. This is an environment gate; authoritative Linux PR CI remains
  required before merge.

## Remaining blockers

1. Corollary 17.3 still needs the one-policy/all-horizon/all-confidence tail
   rescaling and a calibrated `(n, delta)` contradiction using the compiled
   Gamma integral leaf.
2. Claim 17.6 still needs the same-policy interaction law for the pushed-forward
   clipped hard distribution and the exact relative-entropy/pull-count bound.
3. Claim 17.7 still needs the source-constant Gaussian clipping-count
   concentration argument.
4. Theorem 17.4 still needs those two claims, the random-matrix CDF interface,
   and Claim 17.5's deterministic-witness extraction.

Recommendation: merge only after the PR's Linux Lean/Tests/harness job passes.
Keep the task and public chapter status `partial` until all four blockers are
closed with the exact frozen contracts.
