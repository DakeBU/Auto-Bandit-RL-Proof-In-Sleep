# Proof Obligations: Textbook Part IV Chapter 13 lower-bound basic ideas spine

Task id: `TEXTBOOK-PART-IV-CHAPTER-13-BASIC-LOWER-BOUND-SPINE`

Source card: `TXT-LATTIMORE-SZEPESVARI-2020`

Scenario card: `SCN-STOCHASTIC-FINITE`

| Node | Target | Dependencies | Local APIs/imports | Retrieval cards | Intended proof route | Regularity contracts | Mathlib status | Lean declaration | Gate | Status |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `CH13-SOURCE-FENCE` | complete main-text inventory: minimax semantics/optimality, Theorem 13.1, Section 13.1 and Eqs. (13.1)--(13.3), broader-class consequence; optional notes/exercises separated | official author PDF and CUP metadata | task/conversion window | `TXT-LATTIMORE-SZEPESVARI-2020`, `TXT-LS-2020-DEF-13-MINIMAX-OPTIMAL`, `TXT-LS-2020-EQ-13-1-GAUSSIAN-TESTING` | physical PDF pp. 189--194 audit and itemized completion contract | edition, section, displayed-equation, and optional-material boundaries | source evidence | n/a | source review | mapped |
| `CH13-MINIMAX-SURFACE` | worst-case sup and minimax inf over explicit classes | source semantics | `iSup`, `iInf`, `ENNReal`, subtypes | `MLIB-ORDER-ALGEBRA` | complete-lattice definitions and introduction/elimination bounds | class subsets explicit; meaningful consumers prove nonemptiness | project-local | `LowerBounds.worstCaseExpectedRegret`, `LowerBounds.minimaxExpectedRegret` and order leaves | focused Lean | compiled |
| `CH13-MINIMAX-OPTIMAL` | admissible policy attains the minimax value for the fixed policy/environment classes and horizon-indexed regret functional | minimax surface | conjunction and equality | `MLIB-ORDER-ALGEBRA` | define attainment without claiming a general minimizer exists | explicit classes; horizon carried by `regret` | project-local | `LowerBounds.IsMinimaxOptimal`, `LowerBounds.IsMinimaxOptimal.mem_policyClass`, `LowerBounds.IsMinimaxOptimal.eq_minimaxExpectedRegret` | focused Lean | compiled |
| `CH13-GAUSSIAN-TEST-DECISION` | midpoint rule and exact error events under the two point hypotheses | ordered real comparison | `if`, `Set.Ici`, `Set.Iio` | `MLIB-ORDER-ALGEBRA` | split on `Delta/2 <= observation` | `Delta>0`; tie assigned to positive hypothesis | project-local | `LowerBounds.twoPointGaussianThresholdDecision_zero_error_event`, `LowerBounds.twoPointGaussianThresholdDecision_gap_error_event` | focused Lean | compiled |
| `CH13-GAUSSIAN-SAMPLE-MEAN-LAW` | the average of `n>0` independent `N(mu,1)` observations has law `N(mu,1/n)` | canonical finite product measure and Gaussian scaling | `Measure.pi`, `charFun_map_sum_pi_eq_prod`, `charFun_gaussianReal`, `gaussianReal_map_div_const` | `MLIB-GAUSSIAN-REAL-TAIL`, `MLIB-PROBABILITY-INDEPENDENCE` | identify the product-law sum by characteristic functions, then map its arithmetic mean by division by `n` | `n>0`; every coordinate has exact `N(mu,1)` law by construction | project-local bridge | `LowerBounds.gaussianIIDObservationLaw`, `LowerBounds.gaussianCoordinateAverage`, `LowerBounds.gaussianIIDSumLaw`, `LowerBounds.gaussianIIDSampleMeanLaw` | focused Lean | compiled |
| `CH13-GAUSSIAN-TEST-CHERNOFF` | under the declared zero/positive `N(mu,1/n)` laws, both midpoint errors and their maximum are at most `exp(-n*Delta^2/8)` | exact Gaussian MGF, reflection, and midpoint events | `gaussianReal`, `gaussianReal_map_const_sub`, `mgf_id_gaussianReal`, `HasSubgaussianMGF.measure_ge_le` | `MLIB-GAUSSIAN-REAL-TAIL`, `MLIB-PROBABILITY-SUBGAUSSIAN`, `MLIB-MEASURE-INTEGRAL`, `MLIB-REAL-LOG-SQRT` | derive centered and reflected sub-Gaussianity, apply one-sided Chernoff to both error rays, normalize variance `1/n`, take `max` | `Delta>0`; `n>0` is explicit in the compiled iid empirical-mean producer | project-local consequence | `LowerBounds.hasSubgaussianMGF_id_gaussianReal_zero`, `LowerBounds.hasSubgaussianMGF_gap_sub_id_gaussianReal`, `LowerBounds.gaussianSampleMeanZeroErrorProbability_le_exp`, `LowerBounds.gaussianSampleMeanGapErrorProbability_le_exp`, `LowerBounds.gaussianSampleMeanThresholdRisk_le_exp` | focused Lean | compiled |
| `CH13-EQ-13-1` | exact printed lower and upper Gaussian midpoint-error bounds | both exact Eq. (13.4) integrals, Gaussian density, scaling, and denominator normalization | `GaussianMillsRatio.lean`, `GaussianHypothesisTesting.lean` | `MLIB-MEASURE-INTEGRAL`, `MLIB-GAUSSIAN-REAL-TAIL` | derivative comparison for lower bound; one sign change and endpoints for upper bound; Gaussian density change of variable | `n>0`, `Delta>0`; constants 16 and 32/pi | locally compiled Mathlib-candidate and project consumer | `gaussianSampleMeanZeroErrorProbability_source_bounds` | focused build and external typed canary; full gate pending | compiled |
| `CH13-ALTERNATIVE-BUDGET` | sum of alternative expected pulls is at most horizon | exact total sum and base nonnegativity | `Fin.sum_univ_succ`, ordered field | `MLIB-FINSET-SUMS`, `MLIB-FINTYPE-FIN` | rewrite the full sum as base plus tail, then linear arithmetic | all expected pulls nonnegative | mathlib-composed project leaf | `LowerBounds.alternativeExpectedPullBudget_le` | focused Lean | compiled |
| `CH13-LEAST-EXPLORED` | some alternative has expected pulls at most `n/m` | alternative budget, `0 < m` | `Finset.exists_le_of_sum_le`, constant sum | `MLIB-FINSET-SUMS`, `MLIB-FINTYPE-FIN`, `MLIB-ORDER-ALGEBRA` | finite average comparison | `0 < m`; exact expected-pull total | mathlib-composed project leaf | `LowerBounds.exists_alternative_le_average`, `LowerBounds.exists_leastExploredAlternative` | focused Lean | compiled |
| `CH13-TWO-ENV-ALGEBRA` | max of base and changed expressions is at least `Delta*(n-error)/2` under an explicit pull-discrepancy bound | equations (13.2)--(13.3) expressions | real ordered-field algebra, `max`, `nlinarith` | `MLIB-ORDER-ALGEBRA` | show their sum is at least `Delta*(n-error)`, then use max/average | `0 <= Delta`; visible `baseFirstPulls-changedFirstPulls <= error` bridge | project-local | `LowerBounds.baseEnvironmentRegret`, `LowerBounds.changedEnvironmentRegretLowerBound`, `LowerBounds.max_base_changed_regretLowerBound_ge_half_sub_error`; zero-error corollary `LowerBounds.max_base_changed_regretLowerBound_ge_half` | focused Lean | compiled |
| `CH13-HISTORY-TRANSPORT` | same-policy history-law comparison supplies the cross-law event inequality | Chapter 14 information theory and Chapter 15 history KL | compiled Gaussian/history APIs | local declarations; weapon card inspiration only | likelihood ratio, KL chain rule, direction-correct event inequality | measurability, policy consistency, exact KL direction | project-local | `LowerBounds.base_event_probability_lower_bound`, `LowerBounds.changed_complement_probability_lower_bound` | Chapter 15 | compiled |
| `CH13-THEOREM-13-1` | Gaussian finite-arm minimax lower bound `>= c*sqrt(k*n)` | Chapter 13 deterministic leaves, Chapter 14 information theory, Chapter 15 minimax construction | compiled Gaussian/history APIs | source card plus compiled local declarations | base/changed instances, least arm, testing bound, Delta tuning, inf/sup extraction | unit variance; means in `[0,1]^k`; `k>1`; `n>=k`; explicit `c=1/54` | source-order endpoint | `LowerBounds.unitGaussianMinimaxExpectedPseudoRegret_ge_one_div_fiftyFour_sqrt` | Chapter 15 | compiled |
| `CH13-BROADER-SUBGAUSSIAN-NEAR-MINIMAX` | Algorithm 7 is constant-factor minimax for finite-arm 1-subgaussian bandits with gaps in `[0,1]` | Theorem 13.1 Gaussian-subclass lower transfer and source Theorem 9.1 MOSS upper bound | compiled lower terminal; no local MOSS upper theorem | textbook source; local MOSS roadmap only | identify the Gaussian subclass, transport the lower bound to the broader class, combine with generated-policy MOSS upper bound | exact broader environment class and regret notion; common horizon/arm indexing | connected blocker | none | Chapter 9 plus Chapter 13 | partial |
| `CH13-TYPED-CANARY` | external root-import applications and a three-arm numeric witness | compiled Chapter 13 declarations | root `BanditRLProof` import | local declaration index | exact full-conclusion examples plus `#print axioms` | nonempty policy/environment subsets; nonnegative vector summing to horizon | project-local | `Tests/TextbookPartIVChapter13Canary.lean` | dedicated/root Tests | verified |
| `CH13-LOCAL-FULL-GATE` | focused/root/Tests/placeholder/full harness gates | all compiled local nodes | Lake and `tools/bandit.py` | repository | deterministic gate suite | Windows long-path workaround must not be mistaken for a Lean proof failure | repository | n/a | `python3 tools/bandit.py check` | baseline verified; exact-bound extension pending |
| `CH13-EVIDENCE-SITE` | proof export, indexes, readings/highlights/results/implementation map/README and Part IV site agree | local full gate | harness and website scripts | repository | generated evidence plus maintained source data | only gate-passing declarations marked compiled | repository | n/a | lean-verified build/site check/browser review | baseline verified; exact-bound extension pending |
| `CH13-REVIEW` | structured in-branch source/theorem/Lean/evidence consistency audit | all local artifacts | source, declarations, generated site | all above | check source inventory, quantifiers, probability-law direction, regularity, status labels, and order claims | no unresolved P0--P3; website-status-enum P3 corrected | repository | n/a | review | baseline verified; exact-bound extension pending |
| `CH13-REMOTE` | current Chapter 15 downstream extension PR, Actions, Pages deployment and live Chapter 13 verification | accepted local chapter; earlier dependency-slice PR is historical evidence only | GitHub/Pages workflow | repository | branch PR; never direct push to main | remote state must be current | repository | n/a | remote deployment | pending current extension |

## 2026-09-05 Exact Gaussian testing closure

Both source Eq. (13.4) integrals and the exact printed Eq. (13.1) now
compile. `gaussianSampleMeanZeroErrorProbability_source_bounds` has only
`n>0` and `Delta>0` as premises and preserves constants 16 and 32/pi.
Focused module builds and an independent full-statement canary pass; all
reported axioms are baseline-only. Full integration validation for commit
`1203c63` passed in the short-path worktree: root 8854 jobs, Tests 8896 jobs,
ProofGraphExport, and 400 Python tests (7 skipped), with exit code zero.
Website/export records were synchronized at `370068b`; the clean site build
and static check passed. Mobile visual QA remains inconclusive as recorded
in the dated integration review. New MOSS additions require a fresh gate.

## Failure classification

### MOSS dependency progress

- `Concentration.submartingale_exp_of_martingale`,
  `measure_exists_le_martingale_ge_le_exp`,
  `measure_exists_le_martingale_ge_le_subgaussian`, and
  `measure_exists_le_independent_partialSum_ge_le_subgaussian` now compile.
  They implement the no-cardinality-loss source Theorem 9.2 route, with
  explicit independent centered subgaussian coordinate assumptions.
  Dedicated external canary passes (3473-job build, baseline axioms only);
  full integration at `50ea833` passed root, Tests (8904 jobs),
  ProofGraphExport and 400 Python tests (7 skipped, 203.163 seconds).
- `measure_meanBadEvent_le_fifteen` now proves source Lemma 9.3 for
  independent centered strongly measurable unit-subgaussian coordinates.
- `integral_optimismDeficit_le_two_sqrt` derives the numerical expected
  deficit bound from the tail, with integrability proved from MGF contracts.
  `twice_horizon_mul_integral_optimismDeficit_le` gives the printed
  16*sqrt(n*k) contribution. Full integration through `783d436` passed,
  including 400 Python tests (7 skipped). Subsequent additions require a fresh gate.
- `Concentration.integral_fixedRadiusCount_le` proves the source Lemma 8.2
  expected-count conclusion from independent centered unit-subgaussian coordinates.
  `MOSS.gap_mul_integral_indexExceedanceCount_le` now gives the source
  gap*E[kappa] <= gap+15/sqrt(delta) under gap>=8*sqrt(delta), using the
  actual variable-radius exceedance count. This is not yet a bound on the
  selected-arm pull count. Actual arm-stream instantiation, selected-count
  transport and concrete regret assembly remain open.

- `MOSS.logPlus`, `radius`, `index`, `action`: exact source index and
  zero-based initialization; `radius_sq` retains the factor four.
- `action_initial_arm` and `action_index_max`: initialization and
  post-initialization argmax certificates.
- `selected_index_gt_mean_add_half_gap`: deterministic Theorem 9.1 proof
  step under a visible optimism-deficit premise, not a probabilistic bound.
- `historyAction`, `measurable_historyAction`, `historyAlgorithm`,
  `historyAlgorithm_policy_apply`, `historyAction_initialization`,
  `historyAction_index_max`: concrete measurable common-interface policy,
  with inclusive history at t feeding the next action at t+1.
- Both policy modules pass focused build (2951 jobs); typed canary passes
  with baseline axioms only. Full integration at `1eb5af0` passed: root 8856
  jobs, Tests 8899 jobs, ProofGraphExport and 400 Python tests (7 skipped).
  Actual reward-stream instantiation, large-gap occupancy, and regret
  assembly remain open. Do not promote this policy constructor to the
  MOSS upper theorem.

Use exactly one:

- source translation gap;
- local Lean lemma gap;
- theorem-card dependency;
- external cited result;
- semantic interface gap;
- missing regularity contract;
- likely false statement or counterexample;
- invalid route;
- stale dynamic leaf;
- connected blocker;
- Windows path-length/build-artifact failure.

## Reviewer statement fence

- The Chapter 13 module compiles semantic and deterministic scaffolding; the
  project-level Theorem 13.1 endpoint is the compiled Chapter 15 consumer.
- The Gaussian testing module compiles the exact midpoint error events and a
  Chernoff companion plus both exact printed Mills-ratio bounds of Eq. (13.1).
- `gaussianSampleMeanLaw` is connected to an explicit arithmetic average on
  the canonical finite iid Gaussian product by `gaussianIIDSampleMeanLaw`;
  the positive sample-size premise is explicit.
- `Fin.succ` is the zero-based Lean image of the source's one-based arms
  `2,...,k`; no alternative arm is dropped or duplicated.
- The expected-pull sum is an explicit exact identity, and all nonnegativity
  premises used to remove arm zero are visible.
- Base and changed expectations are not definitionally identified. The
  quantitative discrepancy bound remains a named premise until the Chapter 14
  history-law theorem produces a usable error for one policy.
- KL direction, absolute continuity and Gaussian construction cannot be
  inferred from deterministic algebra or a theorem card.
- Theorem 13.1 is represented by the caller-free Chapter 15 minimax consumer
  with explicit `c=1/54`; broader classes or constants require separate gates.
- The chapter remains `partial`: the main-prose broader-class MOSS upper
  consequence remains open under the frozen contract, while Notes 13.2 and
  Exercises 13.1--13.2 are optional and do not block completion.

## Failure policy

Keep failed proof attempts in
`proof-attempts/TEXTBOOK-PART-IV-CHAPTER-13-BASIC-LOWER-BOUND-SPINE/` when a
mathematical route actually fails. Do not log ordinary elaboration iteration
as a scientific failure. Never weaken the fenced terminal or promote a
source/retrieval card to certified local memory.
