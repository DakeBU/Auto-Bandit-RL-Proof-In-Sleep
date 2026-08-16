# Textbook Part IV Chapter 17 high-probability lower-bounds spine

Task id: `TEXTBOOK-PART-IV-CHAPTER-17-HIGH-PROBABILITY-LOWER-BOUNDS-SPINE`

Kind: `theoremFormalization`

Status: `accepted`

Harness: `hierarchical`

## Goal

Formalize the source-faithful stochastic and adversarial high-probability
lower-bound routes in Lattimore--Szepesvari, *Bandit Algorithms* (2020),
Chapter 17. The exact source terminals are Theorem 17.1, Corollaries 17.2 and
17.3, Theorem 17.4, and Claims 17.5--17.7. The compiled first slice freezes all
three threshold surfaces, the tail-event direction, Claim 17.5's
first-moment argument, the probability subtraction that combines Claims
17.6--17.7, and the deterministic quarter-horizon algebra after Eq. (17.8).
It must not be reported as any blocked source terminal.

## Source

- Authors: Tor Lattimore and Csaba Szepesvari.
- Book: *Bandit Algorithms*, Cambridge University Press, 2020.
- Book DOI: <https://doi.org/10.1017/9781108571401>.
- Chapter DOI: <https://doi.org/10.1017/9781108571401.022>.
- CUP chapter page:
  <https://www.cambridge.org/core/books/abs/bandit-algorithms/highprobability-lower-bounds/CDC23AC2BB673E4D5FDBD05D3BD3AB9E>.
- Official author PDF: <https://tor-lattimore.com/downloads/book/book.pdf>.
- Placement: Part IV, Chapter 17, CUP print pp. 185--190; author-online
  page labels 215--221; physical PDF pp. 224--230.
- Chapter opening: CUP p. 185; author-online p. 215; physical PDF p. 224.
- Section 17.1 Stochastic Bandits: CUP pp. 186--188; author-online pp.
  216--218; physical PDF pp. 225--227. Theorem 17.1 and Corollaries
  17.2--17.3.
- Section 17.2 Adversarial Bandits: CUP pp. 188--190; author-online pp.
  218--220; physical PDF pp. 227--229. Theorem 17.4 and Claims 17.5--17.7.
- Section 17.3 Notes: CUP p. 190; author-online p. 220; physical PDF p. 229.
- Section 17.4 Bibliographic Remarks: CUP p. 190; author-online p. 220;
  physical PDF p. 229.
- Section 17.5 Exercises: CUP p. 190; author-online p. 221; physical PDF
  p. 230.
- Textbook card: `TXT-LATTIMORE-SZEPESVARI-2020` plus Chapter 17 cards below.
- Scenario cards: `SCN-STOCHASTIC-FINITE` and `SCN-ADVERSARIAL-FINITE`.
- Detailed adversarial route evidence only: Gerchinovitz--Lattimore,
  *Refined Lower Bounds for Adversarial Bandits*, NeurIPS 2016,
  <https://proceedings.neurips.cc/paper/2016/hash/2f37d10131f2a483a8dd005b3d14b0d9-Abstract.html>.

The CUP print pagination, author-online page labels, and physical PDF pages are
edition-specific fields. The author PDF explicitly warns that its pagination
does not match the print edition, so no constant page offset is inferred.

## Frozen source targets

The chapter opening defines adversarial random regret and expected regret as

```text
Rhat_n = max_{i in [k]} sum_{t=1}^n (x_ti - x_t,A_t),
R_n = E[Rhat_n].
```

Section 17.1 defines stochastic random pseudo-regret by

```text
Rbar_n = sum_{i=1}^k T_i(n) Delta_i.
```

Let `E^k` be the class of `k`-armed Gaussian bandits whose suboptimality gaps
are bounded by one. The source writes `mu in [0,1]^d` when introducing
`nu_mu`; the surrounding `k`-armed context indicates a dimensional typo.
The Lean target records a `k`-indexed mean vector and does not silently retain
an unrelated `d`.

Theorem 17.1: let `n>=1`, `k>=2`, `B>0`, and let one policy `pi` satisfy for
every `nu in E^k`

```text
R_n(pi,nu) <= B sqrt((k-1)n).                              (17.4)
```

For every `delta in (0,1)`, there exists `nu in E^k` such that

```text
P_nu^pi(
  Rbar_n(pi,nu) >=
    (1/4) min { n,
      (1/B) sqrt((k-1)n) log(1/(4 delta)) }) >= delta.
```

The factor `1/4` is outside the whole minimum. The proof chooses

```text
Delta = min { 1/2,
  (1/(2B)) sqrt((k-1)/n) log(1/(4 delta)) },
```

uses the least-pulled arm among arms `i>1`, changes that arm's mean by
`2 Delta`, and applies Bretagnolle--Huber and Lemma 15.1 in the original-law
to alternative-law KL direction.

Corollary 17.2: if `n>=1`, `k>=2`, `delta in (0,1)`, and

```text
n delta <= sqrt(n(k-1) log(1/(4 delta))),                 (17.6)
```

then for every policy there exists `nu in E^k` such that

```text
P_nu^pi(
  Rbar_n(pi,nu) >=
    (1/4) min { n,
      sqrt((n(k-1)/2) log(1/(4 delta))) }) >= delta.      (17.7)
```

Corollary 17.3: for `k>=2`, `p in (0,1)`, and `B>0`, there does not exist one
policy `pi` such that for all `n>=1`, all `delta in (0,1)`, and all
`nu in E^k`,

```text
P_nu^pi(
  Rbar_n(pi,nu) >=
    B sqrt((k-1)n) log(1/delta)^p) < delta.
```

The strict `< delta`, every-horizon/every-confidence quantifiers, and single
policy are essential.

Theorem 17.4: there exist sufficiently small/large universal constants
`c,C>0` such that for `k>=2`, `n>=1`, `delta in (0,1)`, and

```text
n >= C k log(1/(2 delta)),
```

there exists a deterministic reward sequence `x in [0,1]^(n x k)` whose
random-regret CDF `F_x` satisfies

```text
1 - F_x(c sqrt(n k log(1/(2 delta)))) >= delta.
```

Claim 17.5: for a probability law `Q` on bounded reward matrices, if

```text
E_Q[1 - F_X(u)] >= delta,
```

then some deterministic `x` satisfies `1-F_x(u)>=delta`. Lean makes the
suppressed integrability of `x |-> 1-F_x(u)` explicit.

Claim 17.6 uses a correlated-across-arms, IID-across-time clipped-normal hard
family. For `sigma>0` and

```text
Delta = sigma sqrt(((k-1)/(2n)) log(1/(8 delta))),
```

some arm `i` satisfies `P_Qi(T_i(n)<n/2)>=2 delta`.

Equation (17.8) is

```text
Rhat_n >= Delta (
  n - T_i(n)
    - sum_{t=1}^n I{exists j in [k] : X_tj in {0,1}}).   (17.8)
```

Claim 17.7: for `sigma=1/10`, `Delta<1/8`, and
`n>=32 log(1/delta)`, the probability that the clipping-count sum is at least
`n/4` is at most `delta`.

## Lean target and status fence

Target file: `BanditRLProof/LowerBounds/HighProbability.lean`.

Compiled public declarations:

```lean
LowerBounds.tailAtLeast
LowerBounds.stochasticHighProbabilityThreshold
LowerBounds.stochasticMinimaxHighProbabilityThreshold
LowerBounds.adversarialHighProbabilityThreshold
LowerBounds.exists_tailMass_ge_of_integral_ge
LowerBounds.exists_cdfTail_ge_of_integral_ge
LowerBounds.measureReal_diff_ge_delta
LowerBounds.adversarialRegretLowerExpression
LowerBounds.adversarialRegretLowerExpression_ge_quarter
LowerBounds.randomRegret_ge_quarter_of_clippingDecomposition
```

`exists_cdfTail_ge_of_integral_ge` is the exact first-moment content of Claim
17.5, with the textbook-suppressed integrability assumption made explicit.
The threshold declarations and remaining theorems are dependency leaves.

Reserved source terminals, with no declaration claimed:

```lean
LowerBounds.gaussianRandomPseudoRegret_ge_theorem17_1
LowerBounds.gaussianRandomPseudoRegret_ge_corollary17_2
LowerBounds.noUniformGaussianRandomPseudoRegretTail_corollary17_3
LowerBounds.adversarialRandomRegret_ge_theorem17_4
LowerBounds.clippedGaussian_pullCount_lt_half_claim17_6
LowerBounds.clippingCount_ge_quarter_le_claim17_7
```

The chapter stays `partial`. Claim 17.5 is compiled; Theorem 17.1,
Corollaries 17.2--17.3, Theorem 17.4, and Claims 17.6--17.7 are blocked.

## Exact regularity contract

- Stochastic random pseudo-regret and adversarial random regret are distinct
  random variables and must not be interchanged.
- `E^k` contains `k`-armed Gaussian bandits with gaps bounded by one. The
  source construction uses unit-variance Gaussian laws and mean vectors in
  the unit cube.
- Expected regret in Eq. (17.4) is deterministic; `Rbar_n` is random through
  pull counts. Every probability is under the history law induced by the same
  possibly randomized nonanticipating policy.
- Theorem 17.1 uses `n>=1`, `k>=2`, `B>0`, and `delta in (0,1)`. Its uniform
  expected-regret premise quantifies over every environment in `E^k`.
- KL direction is original history law to changed-environment history law;
  expected pull counts are under the original law.
- Corollary 17.2 retains its horizon-confidence side condition, the factor
  `1/2` inside the square root, and the outer factor `1/4`.
- Corollary 17.3 uses one policy for all horizons, confidence levels, and
  environments. Its exponent is a real `p in (0,1)` on `log(1/delta)` and the
  upper-tail probability is strictly less than `delta`.
- Theorem 17.4 is adversarial, concerns random regret, and produces a
  deterministic reward matrix in `[0,1]^(n x k)`. The universal constants and
  horizon condition remain explicit.
- Claim 17.5 needs a probability law on reward matrices, the Borel sigma
  algebra, and integrability of `x |-> 1-F_x(u)`. The compiled generic theorem
  does not assert that a future bandit CDF construction supplies integrability.
- Claim 17.6's reward coordinates are correlated across arms at a fixed time,
  but each arm is IID across time. The policy interaction law must preserve
  the source conditional policy kernel.
- Claim 17.7 needs the exact clipping map, Gaussian tails, a union/count
  argument, `sigma=1/10`, `Delta<1/8`, and `n>=32 log(1/delta)`.
- Equation (17.8) is a pathwise construction-specific inequality. The
  compiled quarter-horizon theorem assumes this missing lower comparison
  rather than claiming it.

## Current semantic and analytic blockers

Theorem 17.1 and its corollaries inherit Lemma 15.1's missing same-policy
adaptive-history divergence decomposition. Installed Mathlib exposes a
composition-product KL chain rule but not the conditional integral of
pointwise kernel KL, and the repository still lacks a canonical possibly
randomized policy-kernel history law.

Theorem 17.4 is described only at a high level in the textbook and delegates
details to Gerchinovitz--Lattimore (2016). A source-faithful proof needs the
clipped-normal reward-matrix law, the associated policy-history law, the
relative-entropy calculation of Claim 17.6, the clipping concentration of
Claim 17.7, and the pathwise reward comparison in Eq. (17.8). The external
paper is route evidence, not a local theorem.

These are two explicit open-problem proposals. They are not reasons to
replace randomized policies by deterministic maps, assume armwise
independence in the adversarial hard family, reverse KL, change random
pseudo-regret into expected regret, or weaken a probability/constant.

## Proof obligations

- [x] Official edition, book/chapter DOI, stable author PDF, section titles,
  and three-way pagination are recorded.
- [x] Theorem 17.1, Corollaries 17.2--17.3, Theorem 17.4, Claims 17.5--17.7,
  and Eq. (17.8) are frozen with exact quantifiers, event directions,
  constants, and threshold placement.
- [x] Existing Chapters 14--16 and Mathlib first-moment/outer-measure APIs are
  audited.
- [x] Exact tail-event and stochastic/adversarial threshold interfaces compile.
- [x] Claim 17.5's first-moment content compiles with integrability explicit.
- [x] The probability subtraction combining Claims 17.6--17.7 compiles.
- [x] The quarter-horizon algebra following Eq. (17.8) compiles.
- [ ] Lemma 15.1 or an equivalent source-faithful stochastic history
  information constraint compiles.
- [ ] Theorem 17.1 and Corollaries 17.2--17.3 compile.
- [ ] The clipped-normal hard family, Claim 17.6, Eq. (17.8), Claim 17.7, and
  Theorem 17.4 compile.
- [x] Root import, focused module, expanded typed canary, axiom reports,
  placeholder scan, exports, retrieval indexes, site build/check, desktop
  browser, and independent read-only review pass locally.
- [ ] Native Windows full `lake build` / `Tests` / harness pass. The current
  local run is blocked only by MAX_PATH while creating an existing unrelated
  long-named RL `.olean`; authoritative Linux PR CI is the required full gate.
- [x] Authoritative Linux PR and main full Lean/Tests/harness gates pass.
- [x] Actual 390px mobile browser review passes. Synthetic local viewport
  injection was rejected by browser security policy, so this remains a
  remote/live result rather than a claimed local pass.
- [x] PR, authoritative-main Actions, Pages deployment, and live checks pass.

## Local verification evidence

- `lake build BanditRLProof.LowerBounds.HighProbability`: passed, 2654 jobs.
- The public `BanditRLProof` root and expanded Chapter 17 canary compile through
  the worktree's `X:` short-path mapping. Axiom reports contain only `propext`,
  `Classical.choice`, and `Quot.sound`.
- `python3 tools/bandit.py check` reaches the full root build but Windows fails
  to create an existing unrelated long-named RL object file because of
  MAX_PATH. No Chapter 17 target fails; authoritative Linux CI passed below.
- `python3 website/scripts/build_site.py --lean-verified`: passed with 563
  modules, 7415 declarations, and zero placeholders.
- `python3 website/scripts/check_site.py`: passed with 591 pages, 14 Mermaid
  blocks, and 16037 Lean source links.
- Desktop browser QA at 1280x720 found `PARTIAL`, all seven MathJax displays,
  the complete Part IV navigation, no document-level horizontal overflow,
  and local scrolling on long formula/table/code containers.
- Independent read-only review initially found two P3 evidence/canary gaps;
  both were corrected, and re-review found no unresolved P0--P3. See
  `reviews/2026-08-17-textbook-part-iv-chapter-17-high-probability-lower-bounds-spine.md`.

## Remote verification evidence

- PR #17 passed `Lean and documentation / build` in run `31975031469`, job
  `95233089033` (23m13s), and was merged without a direct push to `main`.
- Merge commit: `eb41d9607cc5a46aa208572e3a6f05f291c82798`.
- Authoritative-main run `31976153611` passed: build job `95235875154`
  completed Lean, Tests, the lean-verified site, site checks, and Pages
  artifact upload in 22m24s; deployment job `95238317293` passed in 12s.
- Live page:
  <https://dakebu.github.io/Auto-Bandit-RL-Proof-In-Sleep/textbook-spine/chapter-17-high-probability/>.
  Desktop 1280x720 and native mobile 390x844 inspections confirmed the
  `2026-08-16T22:44:25+00:00` build, overall `PARTIAL` chapter status, CUP
  print pp. 185--190 and physical-PDF pp. 224--230, all seven MathJax
  displays, the compiled Claim 17.5/threshold/event-subtraction/Eq. (17.8)
  algebra slice, the blocked Theorem 17.1 / Corollaries 17.2--17.3 / Theorem
  17.4 terminals, and zero broken images. Browser metrics found no
  document-level horizontal overflow at 390x844 (`375/375` client/scroll
  width); the mobile TOC/sidebar and long MathJax displays retain intentional
  local horizontal scrolling.

Remote acceptance applies only to the scoped dependency slice. The chapter
remains `partial`; the stochastic history-information route and the
clipped-normal adversarial construction retain their recorded blocked status.

## Mathlib-ready leaf contract

| Leaf | Local APIs/imports | Intended proof route | Regularity contracts | Mathlib status |
| --- | --- | --- | --- | --- |
| exact threshold surfaces | `Real.sqrt`, `Real.log`, `min`, natural casts | transcribe all constants and grouping before later tuning algebra | positivity remains terminal-side; `alternativeArms=k-1` at consumer | compiled project-local definitions |
| Claim 17.5 | `MeasureTheory.exists_integral_le` | first-moment method on `x |-> 1-F_x(u)` | probability measure and integrability | compiled exact source claim |
| good-event subtraction | `le_measureReal_diff`, real linear arithmetic | subtract the clipping-bad event from the pull-small event | finite measure; outer-measure sets need not be measurable | compiled project-local |
| Eq. (17.8) quarter algebra | ordered-field multiplication | `T_i<=n/2` and clipping count `<=n/4` leave at least `n/4` rounds | nonnegative gap; Eq. (17.8) itself remains a premise | compiled project-local |
| stochastic terminal | Chapter 14 BH plus Chapter 15 history KL | least-pulled arm, one-coordinate Gaussian change, exact tuning | same stochastic policy and original-law pulls | connected blocker |
| Corollary 17.3 tail integration | layer-cake/tail integral and Gamma-type integral | integrate the proposed all-confidence tail, then contradict Theorem 17.1 | measurable/integrable random pseudo-regret; real `p in (0,1)` | open Mathlib/project leaf |
| clipped-normal law | probability kernels, Gaussian map/clipping | construct the correlated-across-arm reward matrix and policy interaction law | Borel measurability; IID across time only | open project semantic interface |
| Claim 17.6 | relative entropy and history law | least-pulled arm plus changed law and source entropy calculation | exact `Delta`, same policy, finite KL | connected blocker |
| Claim 17.7 | Gaussian tail/concentration and finite unions | bound each clipping indicator and its count | `sigma=1/10`, `Delta<1/8`, exact horizon condition | open concentration leaf |
| Theorem 17.4 | Claims 17.5--17.7 and Eq. (17.8) | combine good event, calibrate `Delta`, then first moment | deterministic witness matrix and CDF law | blocked source terminal |

## Retrieval cards

- Mathlib: `MLIB-MEASURE-INTEGRAL`, `MLIB-ORDER-ALGEBRA`,
  `MLIB-REAL-LOG-SQRT`, `MLIB-PROBABILITY-KERNEL`,
  `MLIB-PROBABILITY-INDEPENDENCE`, and `MLIB-PROBABILITY-SUBGAUSSIAN`.
- Local compiled dependencies: Chapter 14 `bretagnolleHuber`; Chapter 15
  `klDiv_gaussianReal_one`; Chapter 13 `exists_leastExploredAlternative`.
- Textbook: `TXT-LATTIMORE-SZEPESVARI-2020`,
  `TXT-LS-2020-THM-17-1-STOCHASTIC-TAIL`,
  `TXT-LS-2020-COR-17-2-STOCHASTIC-MINIMAX-TAIL`,
  `TXT-LS-2020-COR-17-3-UNIFORM-TAIL-IMPOSSIBILITY`,
  `TXT-LS-2020-THM-17-4-ADVERSARIAL-TAIL`, and
  `TXT-LS-2020-CLAIMS-17-5-17-7`.
- Scenario: `SCN-STOCHASTIC-FINITE`, `SCN-ADVERSARIAL-FINITE`.
- Paper route evidence only: `PPR-GERCHINOVITZ-LATTIMORE-2016-REFINED-LOWER-BOUNDS`.
- LML: none promoted.
- Proof weapon route evidence only: `WEAPON-KL-CHANGE-OF-MEASURE`.

## Nonclaims and failure policy

- A threshold definition is not a tail lower-bound theorem.
- The compiled Claim 17.5 adapter does not construct the reward-matrix law,
  the policy interaction law, or its CDF.
- Probability subtraction and quarter-horizon algebra do not prove Claims
  17.6--17.7 or Eq. (17.8).
- The stochastic random pseudo-regret is not adversarial random regret and is
  not deterministic expected regret.
- Theorem cards, open-problem proposals, and the NeurIPS paper remain route
  evidence only.
- If the terminals remain blocked, preserve their exact contracts and publish
  only Claim 17.5 plus reusable compiled leaves and explicit blockers.
