# Conversion Window: Textbook Part IV Chapter 17 high-probability lower bounds

Task id: `TEXTBOOK-PART-IV-CHAPTER-17-HIGH-PROBABILITY-LOWER-BOUNDS-SPINE`

Source card: `TXT-LATTIMORE-SZEPESVARI-2020`

Scenario cards: `SCN-STOCHASTIC-FINITE`, `SCN-ADVERSARIAL-FINITE`

## Source placement and status fence

Canonical source: Lattimore--Szepesvari, *Bandit Algorithms*, CUP 2020,
Part IV, Chapter 17, chapter DOI
<https://doi.org/10.1017/9781108571401.022>. The chapter is CUP print
pp. 185--190 / author-online labels 215--221 / physical PDF pp. 224--230.
Section 17.1 contains Theorem 17.1 and Corollaries 17.2--17.3. Section 17.2
contains Theorem 17.4 and Claims 17.5--17.7. Edition-specific pagination is
not converted by an offset.

The current compiled window contains the exact threshold surfaces, tail-event
direction, Claim 17.5's first-moment content, the Claims 17.6--17.7 event
subtraction, and the deterministic quarter-horizon consequence of Eq. (17.8).
Theorem 17.1, Corollaries 17.2--17.3, Theorem 17.4, and Claims 17.6--17.7
remain uncompiled and blocked. The website chapter must remain `partial`.

## Precise restatement

For stochastic Gaussian bandits with gaps bounded by one, Theorem 17.1 says a
policy with uniform expected regret at most `B sqrt((k-1)n)` has, on some
environment, random pseudo-regret at least

```text
(1/4) min {n, (1/B)sqrt((k-1)n)log(1/(4delta))}
```

with probability at least `delta`. Corollary 17.2 removes the expected-regret
premise under its explicit horizon-confidence side condition. Corollary 17.3
rules out one policy whose tail is strictly below every `delta` for every
horizon, environment, and threshold of order
`sqrt((k-1)n) log(1/delta)^p`, `p in (0,1)`.

For adversarial bandits, Theorem 17.4 produces a deterministic bounded reward
matrix whose random-regret tail at
`c sqrt(nk log(1/(2delta)))` is at least `delta`. Claim 17.5 is the exact
first-moment witness extraction. Claims 17.6--17.7 build and control a
clipped-normal hard distribution, while Eq. (17.8) turns pull and clipping
counts into random regret.

## Lean mapping

| Source symbol | Meaning | Lean declaration | Type / role | Status |
| --- | --- | --- | --- | --- |
| `{R>=u}` | lower-tail obstruction event | `tailAtLeast` | set-valued definition | compiled |
| Theorem 17.1 threshold | outer quarter times exact minimum | `stochasticHighProbabilityThreshold` | real definition | compiled |
| Eq. (17.7) threshold | minimax stochastic tail threshold | `stochasticMinimaxHighProbabilityThreshold` | real definition | compiled |
| Theorem 17.4 threshold | adversarial random-regret threshold | `adversarialHighProbabilityThreshold` | real definition | compiled |
| first-moment witness | average tail implies one instance | `exists_tailMass_ge_of_integral_ge` | generic probability theorem | compiled |
| Claim 17.5 | `E_Q[1-F_X(u)]>=delta` | `exists_cdfTail_ge_of_integral_ge` | exact source claim with explicit integrability | compiled |
| Claims 17.6--17.7 combination | `2delta` minus `delta` leaves `delta` | `measureReal_diff_ge_delta` | outer-measure probability leaf | compiled |
| Eq. (17.8) RHS | gap times unclipped non-arm rounds | `adversarialRegretLowerExpression` | real definition | compiled |
| quarter consequence | count bounds leave `Delta n/4` | `adversarialRegretLowerExpression_ge_quarter` | deterministic algebra | compiled |
| Eq. (17.8) transfer | construction lower bound implies regret threshold | `randomRegret_ge_quarter_of_clippingDecomposition` | conditional algebra | compiled |
| Theorem 17.1 | exact stochastic Gaussian tail | reserved terminal | bandit theorem | blocked |
| Corollaries 17.2--17.3 | minimax tail and all-confidence impossibility | reserved terminals | bandit theorems | blocked |
| Claim 17.6 | clipped-Gaussian pull-small event | reserved terminal | adversarial information theorem | blocked |
| Claim 17.7 | clipping count tail | reserved terminal | concentration theorem | blocked |
| Theorem 17.4 | deterministic adversarial witness | reserved terminal | bandit theorem | blocked |

## Semantic signature

```text
stochastic:
  one randomized nonanticipating policy
  -> unit-Gaussian k-arm history law
  -> random pull counts
  -> random pseudo-regret
  -> probability under the same environment/policy law

adversarial:
  deterministic reward matrix x
  -> same randomized policy interaction
  -> random regret Rhat_n
  -> CDF F_x and tail 1-F_x(u)

hard-family averaging:
  random reward matrix X ~ Q
  -> policy interaction conditional on X
  -> average tail E_Q[1-F_X(u)]
  -> deterministic matrix witness x
```

## Assumption ledger

| Assumption | Lean status | Purpose | Blocking? |
| --- | --- | --- | --- |
| `n>=1`, `k>=2`, `B>0`, `delta in (0,1)` | frozen source target | Theorem 17.1 calibration | yes for terminal |
| `E^k` unit-Gaussian, gaps at most one | future environment structure | stochastic hard family | yes |
| uniform expected-regret premise over all `E^k` | frozen target | least-pulled-arm bound | yes |
| one common possibly randomized nonanticipating policy | missing history interface | cancel policy KL | yes |
| original-to-alternative history KL | frozen direction | Bretagnolle--Huber step | yes |
| `alternativeArms=k-1` | consumer-side mapping | exact threshold | no |
| real `p in (0,1)` and strict `<delta` | frozen Corollary 17.3 target | all-confidence impossibility | yes |
| probability law `Q` | explicit compiled typeclass | Claim 17.5 first moment | no |
| integrability of `1-F_x(u)` | explicit compiled premise | define the real expectation | no |
| reward matrix in `[0,1]^(n x k)` with Borel law | missing hard-family type | Theorem 17.4 | yes |
| arms correlated within a round, IID down each arm | frozen construction | avoid false independence | yes |
| exact clipping map | missing construction | Claims 17.6--17.7 and Eq. (17.8) | yes |
| `sigma=1/10`, `Delta<1/8`, horizon log condition | frozen target | Claim 17.7 | yes |
| nonnegative gap | explicit compiled premise | quarter-horizon multiplication | no |
| Eq. (17.8) pathwise comparison | explicit premise in transfer leaf | connect counts to random regret | yes for terminal |

## Local API and proof route

| Leaf | Existing APIs/imports | Retrieval evidence | Intended route | Pivot rule |
| --- | --- | --- | --- | --- |
| threshold transcription | `Real.sqrt`, `Real.log`, `min` | `MLIB-REAL-LOG-SQRT` | preserve grouping and constants literally | never normalize away source factors without a proved equality |
| Claim 17.5 | `MeasureTheory.exists_integral_le` | installed Mathlib source | apply first moment to `1-F_x(u)` | retain explicit integrability |
| good-event subtraction | `le_measureReal_diff` | installed Mathlib source | subtract clipping-bad from pull-small | do not add unnecessary measurability |
| Eq. (17.8) algebra | ordered-field multiplication | `MLIB-ORDER-ALGEBRA` | leave a quarter horizon after the two count bounds | construction inequality remains explicit premise |
| stochastic history information | Chapter 14 BH plus Chapter 15 blocker | local cards | prove same-policy history KL, then change one arm | no deterministic-policy substitution |
| Corollary 17.3 integration | layer-cake/tail APIs | `MLIB-MEASURE-INTEGRAL` | integrate the all-confidence tail and contradict Theorem 17.1 | keep real exponent and all quantifiers |
| clipped-normal construction | Gaussian distribution, maps, kernels | Mathlib distribution/kernel cards | construct Borel reward-matrix law and interaction history | preserve across-arm dependence |
| clipping concentration | Gaussian tails and finite union/count | concentration cards | prove Claim 17.7 with exact constants | no asymptotic-only replacement |
| adversarial terminal | compiled Claim 17.5 plus blocked Claims 17.6--17.7 | textbook/paper route cards | combine good event, Eq. (17.8), tuning, first moment | external paper is route evidence only |

## Proof DAG

| Node | Interface | Dependencies | Lean declaration | Mathlib status | Gate | Status |
| --- | --- | --- | --- | --- | --- | --- |
| `CH17-SOURCE-FENCE` | exact Theorem 17.1 / Corollaries 17.2--17.3 / Theorem 17.4 / Claims 17.5--17.7 | official PDF/CUP | repository evidence | source evidence | source review | mapped |
| `CH17-THRESHOLDS` | exact three threshold surfaces and event direction | log/sqrt/min | four definitions | project-local | focused Lean | compiled |
| `CH17-CLAIM-17-5` | average CDF tail gives deterministic witness | probability first moment | `exists_cdfTail_ge_of_integral_ge` | Mathlib-composed | focused Lean | compiled |
| `CH17-EVENT-SUBTRACTION` | `2delta-delta>=delta` good event | measure difference | `measureReal_diff_ge_delta` | Mathlib-composed | focused Lean | compiled |
| `CH17-EQ-17-8-ALGEBRA` | count bounds plus source comparison imply `Delta n/4` | ordered-field algebra | two adversarial-regret declarations | project-local | focused Lean | compiled |
| `CH17-HISTORY-INFORMATION` | stochastic one-arm tail comparison | Chapter 15 Lemma 15.1 | none | connected blocker | focused Lean | blocked |
| `CH17-THEOREM-17-1` | exact stochastic tail | history information and tuning | reserved terminal | source terminal | focused Lean | blocked |
| `CH17-COROLLARY-17-2` | exact minimax stochastic tail | Theorem 17.1 and expectation contradiction | reserved terminal | source terminal | focused Lean | blocked |
| `CH17-COROLLARY-17-3` | exact all-confidence impossibility | Theorem 17.1 and tail integration | reserved terminal | source terminal | focused Lean | blocked |
| `CH17-CLIPPED-NORMAL-LAW` | correlated hard reward-matrix law | Gaussian map/kernel APIs | none | project semantic gap | focused Lean | blocked |
| `CH17-CLAIM-17-6` | pull-small probability at least `2delta` | hard law and history KL | reserved terminal | source terminal | focused Lean | blocked |
| `CH17-EQ-17-8` | pathwise random-regret comparison | clipping construction | reserved terminal | source terminal | focused Lean | blocked |
| `CH17-CLAIM-17-7` | clipping count tail at most `delta` | clipped Gaussian concentration | reserved terminal | source terminal | focused Lean | blocked |
| `CH17-THEOREM-17-4` | deterministic adversarial witness | Claims 17.5--17.7 and Eq. (17.8) | reserved terminal | source terminal | focused Lean | blocked |
| `CH17-TYPED-CANARY` | root-import applications and axiom reports | compiled slice | `Tests/TextbookPartIVChapter17Canary.lean` | project-local | Tests | compiled locally; Linux Tests pending |
| `CH17-EVIDENCE-SITE` | all artifacts agree on partial/blocked boundary | scoped artifacts | repository artifacts | repository | full/site/browser | site and desktop passed; mobile/Linux pending |
| `CH17-REVIEW` | regret notion/direction/quantifier/constants audit | all artifacts | review record | repository | read-only | passed after two P3 fixes |
| `CH17-REMOTE` | PR, main Actions, Pages, live page | accepted local slice | pending | repository | deployment | pending |

## Gaps

- [x] Exact source/page/semantic mapping.
- [x] Threshold, Claim 17.5, event subtraction, and Eq. (17.8) algebra leaves.
- [ ] Same-policy stochastic history KL and Theorem 17.1.
- [ ] Corollary 17.2 expectation contradiction and Corollary 17.3 tail integral.
- [ ] Clipped-normal reward-matrix/history law.
- [ ] Claim 17.6, construction-level Eq. (17.8), Claim 17.7, and Theorem 17.4.
- [x] Focused Lean, root/canary short-path compile, site, desktop browser, and
  independent-review gates.
- [ ] Full Linux Lean/Tests/harness and actual mobile browser gates.
- [ ] PR, authoritative-main Actions, Pages deployment, and live-page gates.
