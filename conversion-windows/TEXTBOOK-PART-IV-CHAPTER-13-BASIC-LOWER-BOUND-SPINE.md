# Conversion Window: Textbook Part IV Chapter 13 lower-bound basic ideas spine

Task id: `TEXTBOOK-PART-IV-CHAPTER-13-BASIC-LOWER-BOUND-SPINE`

Source card: `TXT-LATTIMORE-SZEPESVARI-2020`

Scenario card: `SCN-STOCHASTIC-FINITE`

## Source placement and status fence

The canonical source is Lattimore--Szepesvári, *Bandit Algorithms*, CUP 2020,
Part IV, Chapter 13, CUP print pp. 155--159 / author-online pp. 180--185 /
physical PDF pp. 189--194.  Theorem 13.1 is CUP p. 155 / author-online p. 180 /
physical PDF p. 189; Section 13.1 starts at CUP p. 155 / author-online
pp. 181--182 / physical PDF pp. 190--191.  Theorem 13.1 states the order
`sqrt(k*n)` minimax lower bound for unit-variance Gaussian bandits with mean
vectors in `[0,1]^k`, for `k > 1` and `n >= k`; the source explicitly says its
proof appears in Chapter 15.

Consequently, the Chapter 13 module provides the exact semantic and
deterministic conversion window used by the chapter's heuristic. The
Chapter 15 construction now consumes that window and compiles Theorem 13.1's
order with the explicit universal constant `c=1/54`.

The re-audited chapter-completion contract is wider than that original
dependency slice.  Required main text also includes the minimax-optimality
definition, the Section 13.1 two-point Gaussian test and exact Eq. (13.1), and
the stated Algorithm 7/Theorem 9.1 near-minimax consequence for the broader
1-subgaussian class.  Notes 13.2 and Exercises 13.1--13.2 are optional;
Bibliographic Remarks 13.3 is source evidence for the required Eq. (13.1), not
an excuse to omit it.  Therefore the chapter remains `partial` while the
integration/review/export/deployment gates remain open. Exact Eq. (13.1)
and the broader-class MOSS near-minimax consumer now compile.

## Natural-language statements

Let `R_n(pi,nu)` be expected cumulative pseudo-regret. The worst-case value of
a policy over an explicit environment class is the supremum of `R_n(pi,nu)`;
the minimax value is the infimum of those worst-case values over an explicit
policy class.  A policy is minimax optimal only relative to those classes and
the fixed-horizon regret functional, and only when its worst-case value
attains the minimax infimum.

For the two-point test, the midpoint rule chooses `Delta` when the Gaussian
mean observation is at least `Delta/2` and zero otherwise.  Under the
zero-mean `N(0,1/n)` law, its error event is exactly `[Delta/2,infinity)`.  The
local probability layer constructs the canonical finite iid product of
`N(mu,1)` coordinates, proves that its arithmetic-mean pushforward is exactly
`N(mu,1/n)`, and proves the honest Chernoff consequence
`max_mu P_mu(error) <= exp(-n*Delta^2/8)` for the two hypotheses.  It additionally proves both exact Mills-ratio expressions printed in
Eq. (13.1) through `gaussianSampleMeanZeroErrorProbability_source_bounds`.

For `k = m+1` arms, distinguish arm zero and identify the other `m` arms with
`Fin m`. If every expected pull count is nonnegative and their sum is the
horizon `n`, then the alternative-arm total is at most `n`, so at least one
alternative arm has expected count at most `n/m`.

For the base mean vector `(Delta,0,...)`, the source writes expected regret as
`Delta * (n - E_nu[T_0(n)])`. After changing one alternative mean to
`2*Delta`, it lower-bounds regret by `Delta * E_nu'[T_0(n)]`. The local
algebra proves that the maximum of these expressions is at least
`Delta*(n-error)/2` if `0 <= Delta` and the missing information bridge supplies
`E_nu[T_0(n)]-E_nu'[T_0(n)] <= error`. The premise is deliberately visible;
the `Delta*n/2` statement is retained only as the zero-error corollary.

## Lean mapping

| Source symbol | Meaning | Lean declaration | Type / role | Status |
| --- | --- | --- | --- | --- |
| `R_n(pi,nu)` | expected cumulative pseudo-regret | caller `regret : Policy -> Environment -> ENNReal` | semantic input | typed |
| `sup_nu R_n(pi,nu)` | policy worst case | `LowerBounds.worstCaseExpectedRegret` | `ENNReal` supremum over subtype | target |
| `inf_pi sup_nu R_n(pi,nu)` | minimax value | `LowerBounds.minimaxExpectedRegret` | `ENNReal` infimum over subtype | target |
| minimax-optimal policy | admissible policy attaining the fixed-class minimax value | `LowerBounds.IsMinimaxOptimal` | proposition over the explicit policy/environment classes | compiled |
| midpoint decision | choose `Delta` iff observation is at least `Delta/2` | `LowerBounds.twoPointGaussianThresholdDecision` | deterministic decision surface | compiled |
| empirical mean Gaussian law | the average of `n>0` independent `N(mu,1)` observations has law `N(mu,1/n)` | `LowerBounds.gaussianIIDSampleMeanLaw` | exact pushforward of the canonical finite iid product measure | compiled |
| zero-mean test error | `P_0(sampleMean >= Delta/2)` under `N(0,1/n)` | `LowerBounds.gaussianSampleMeanZeroErrorProbability` | distribution-level probability | compiled definition and event identity |
| Chernoff companion to Eq. (13.1) | `max_mu P_mu(error) <= exp(-n*Delta^2/8)` | `LowerBounds.gaussianSampleMeanThresholdRisk_le_exp` | two-hypothesis Gaussian/sub-Gaussian tail | compiled; not the exact displayed equation |
| Eq. (13.1) | printed two-sided Gaussian tail bounds with explicit square-root denominators | `gaussianSampleMeanZeroErrorProbability_source_bounds` | exact Mills-ratio target | compiled; final integration gate pending |
| arm `1` in the printed one-based notation | distinguished base arm | `0 : Fin (m+1)` | finite-arm index | typed |
| arms `2,...,k` | alternative arms | `i.succ`, `i : Fin m` | finite-arm embedding | typed |
| `E_nu[T_i(n)] <= n/(k-1)` | least-explored alternative | `LowerBounds.exists_leastExploredAlternative` | finite averaging theorem | target |
| equation (13.2) | base regret expression | `LowerBounds.baseEnvironmentRegret` | deterministic real expression | target |
| equation (13.3) RHS | changed regret lower expression | `LowerBounds.changedEnvironmentRegretLowerBound` | deterministic real expression | target |
| comparison of `T_0` under `nu,nu'` | statistical indistinguishability bridge | source event comparison in `GaussianMinimax.lean` | quantitative bridge contract | compiled Ch. 14--15 consumer |
| Theorem 13.1 | Gaussian minimax lower bound | `unitGaussianMinimaxExpectedPseudoRegret_ge_one_div_fiftyFour_sqrt` | source-order endpoint with explicit `c=1/54` | compiled through Ch. 15 |
| Algorithm 7 / Theorem 9.1 consequence | constant-factor near-minimax policy on the broader finite-arm 1-subgaussian class with gaps in `[0,1]` | `SubgaussianMinimax.moss_nearMinimax` (namespace `LowerBounds`) | connected cross-chapter claim | compiled; integration gates pending |

## Semantic signature and assumption ledger

| Assumption | Lean status | Purpose | Blocking Chapter 13? |
| --- | --- | --- | --- |
| explicit policy and environment classes | subtype arguments | avoids silently quantifying over a different model class | no |
| `ENNReal` regret codomain | typed | supplies complete-lattice sup/inf without a hidden boundedness premise | no |
| class nonemptiness | not built into definitions; explicit in meaningful canary/consumers | empty sup/inf retains standard lattice behavior | no |
| total arms `m+1`, `0 < m` | explicit | source condition `k > 1` and nonempty alternative set | no |
| every expected pull count is nonnegative | explicit | remove the distinguished arm from the exact total budget | no |
| `sum_a E[T_a(n)] = n` | explicit | expected form of the pull-count identity | no |
| `0 <= Delta` | explicit | preserves inequality direction in the deterministic reduction | no |
| `Delta <= 1/2` | compiled in the downstream Gaussian construction | keeps changed mean `2*Delta` in `[0,1]` | no for compiled endpoint |
| same policy in both environments | one shared `HistoryAlgorithm` argument | required for change of measure | no for compiled endpoint |
| policy measurability/history adaptation | kernel-valued history interface | defines both induced history laws | no for compiled endpoint |
| absolute continuity / extended KL handling | compiled Gaussian and history-KL route | legitimizes likelihood-ratio/KL comparison | no for compiled endpoint |
| unit Gaussian variance and means in `[0,1]` | `UnitGaussianBanditEnvironment` | exact Theorem 13.1 environment class | no for compiled endpoint |
| `n >= k` | explicit endpoint premise | exact Theorem 13.1 horizon domain | no for compiled endpoint |
| concentration/stopping-time assumptions | no stopping-time premise; exact Gaussian MGF supplies a distribution-level one-sided Chernoff theorem | the minimax route uses information testing rather than concentration; the new Section 13.1 companion is a fixed-law tail bound | no for Theorem 13.1; exact Eq. (13.1) compiled separately |
| positive Gaussian-test sample size and gap | explicit in the Chernoff theorem | makes variance `1/n` nondegenerate and the midpoint nonnegative | no for compiled upper consequence |
| exact Mills-ratio inequalities | compiled | lower and sharpened upper halves of Eq. (13.1) | no mathematical blocker; integration pending |
| compiled MOSS upper theorem on the stated 1-subgaussian class | `MOSS.canonicalGapExpectedRegret_le`, `LowerBounds.moss_nearMinimax` | broader-class near-minimax consequence in the main prose | compiled; still requires whole-chapter integration |

## Local API and proof route

| Leaf | Existing APIs/imports | Retrieval cards | Intended route | Pivot rule |
| --- | --- | --- | --- | --- |
| minimax surface | Mathlib `iSup`, `iInf`, `ENNReal`, subtypes | `MLIB-ORDER-ALGEBRA` | direct complete-lattice definitions and bounds | retain explicit subsets; do not replace sup/inf with finite maxima unless source class is later finite |
| minimax optimality | compiled minimax surface and equality | `MLIB-ORDER-ALGEBRA` | package admissibility and attainment as one proposition | do not assert existence: a general complete-lattice infimum need not be attained |
| Gaussian test upper tail | `gaussianReal`, `mgf_id_gaussianReal`, `HasSubgaussianMGF.measure_ge_le` | `MLIB-PROBABILITY-SUBGAUSSIAN`, `MLIB-MEASURE-INTEGRAL`, `MLIB-REAL-LOG-SQRT` | prove centered Gaussian sub-Gaussianity from the exact MGF and apply Chernoff at `Delta/2` with variance `1/n` | keep it labeled as a one-sided companion, never as Eq. (13.1) |
| empirical mean law | `Measure.pi`, `charFun_map_sum_pi_eq_prod`, `charFun_gaussianReal`, `gaussianReal_map_div_const` | `MLIB-GAUSSIAN-REAL-TAIL`, `MLIB-PROBABILITY-INDEPENDENCE` | identify the exact finite-product sum characteristic function, then scale by `1/n` | keep `n>0` explicit and the canonical product-law interpretation visible |
| exact Eq. (13.1) | Gaussian density/set integral; source Eq. (13.4) | new `MLIB-GAUSSIAN-MILLS-RATIO` candidate | establish the exact upper and lower Mills-ratio integral bounds, then rescale the centered unit Gaussian | do not replace the source lower bound with Chernoff |
| alternative budget | `Fin.sum_univ_succ`, ordered-field algebra | `MLIB-FINSET-SUMS`, `MLIB-FINTYPE-FIN`, `MLIB-ORDER-ALGEBRA` | split the full finite sum into base plus alternatives | if simplification fails, expose a separate sum-splitting lemma; do not assume the desired alternative bound |
| finite average | `Finset.exists_le_of_sum_le`, constant finite sum | same Mathlib cards | compare alternative sum to `m` copies of `n/m` | if API mismatch persists, prove by contradiction using `Finset.card_nsmul_le_sum` |
| algebra reduction | `max`, ordered-field arithmetic, `nlinarith` | `MLIB-ORDER-ALGEBRA` | add the two expressions under an explicit upper bound on the cross-law pull discrepancy | split product monotonicity from linear half-max lemma if automation is fragile |
| information bridge | `banditHistoryRelativeEntropy_eq_expectedPulls_sum`, `exists_gaussianMinimax_historyKL_le_half` | compiled local route; weapon card remains inspiration only | Chapter 14 testing plus Chapter 15 history KL/change-of-measure surface | preserve first-law expectation and KL direction |

## Proof DAG

| Node | Interface | Dependencies | Lean declaration | Mathlib status | Gate | Status |
| --- | --- | --- | --- | --- | --- | --- |
| `CH13-MINIMAX-SURFACE` | explicit sup/inf expected-regret semantics | complete lattice | `worstCaseExpectedRegret`, `minimaxExpectedRegret` and order leaves | project-local | focused Lean | compiled |
| `CH13-MINIMAX-OPTIMAL` | admissible policy attains the minimax value for fixed classes/horizon | minimax surface | `IsMinimaxOptimal` and projections | project-local | focused Lean | compiled |
| `CH13-GAUSSIAN-TEST-DECISION` | midpoint decision and exact zero/gap error events | ordered-field comparison; `Delta>0` | `twoPointGaussianThresholdDecision_zero_error_event`, `twoPointGaussianThresholdDecision_gap_error_event` | project-local | focused Lean | compiled |
| `CH13-GAUSSIAN-SAMPLE-MEAN-LAW` | empirical mean of `n>0` independent unit-variance Gaussians has law `N(mu,1/n)` | finite product measure, characteristic-function product, Gaussian scaling | `gaussianIIDObservationLaw`, `gaussianCoordinateAverage`, `gaussianIIDSumLaw`, `gaussianIIDSampleMeanLaw` | project-local bridge | focused Lean | compiled |
| `CH13-GAUSSIAN-TEST-CHERNOFF` | both `N(0,1/n)` and `N(Delta,1/n)` midpoint errors, and their maximum, are at most `exp(-n*Delta^2/8)` | exact Gaussian MGF, reflection, and Mathlib Chernoff | `hasSubgaussianMGF_id_gaussianReal_zero`, `hasSubgaussianMGF_gap_sub_id_gaussianReal`, `gaussianSampleMeanThresholdRisk_le_exp` | project-local consequence | focused Lean | compiled |
| `CH13-EQ-13-1` | exact printed two-sided Mills-ratio bounds | Eq. (13.4) integral inequalities and Gaussian rescaling | `gaussianSampleMeanZeroErrorProbability_source_bounds` | locally compiled mathlib-candidate | focused Lean | compiled |
| `CH13-ALTERNATIVE-BUDGET` | alternative sum at most total horizon | full expected-pull identity, nonnegativity | internal/public budget lemma | mathlib-composed project leaf | focused Lean | compiled |
| `CH13-LEAST-EXPLORED` | some `i.succ` has count at most `n/m` | alternative budget, finite averaging | `exists_leastExploredAlternative` | mathlib-composed project leaf | focused Lean | compiled |
| `CH13-TWO-ENV-ALGEBRA` | quantitative `Delta*(n-error)/2` max bound | nonnegative gap, explicit upper bound on the cross-law pull discrepancy | `max_base_changed_regretLowerBound_ge_half_sub_error`; zero-error corollary `max_base_changed_regretLowerBound_ge_half` | project-local | focused Lean | compiled |
| `CH13-HISTORY-TRANSPORT` | derive cross-law event comparison | same policy/history law, Gaussian KL, history KL | `base_event_probability_lower_bound`, `changed_complement_probability_lower_bound` | project-local | Chapter 15 | compiled |
| `CH13-THEOREM-13-1` | universal-constant Gaussian minimax `sqrt(k*n)` lower bound | Chapter 13 leaves plus Chapter 14 information theory and Chapter 15 packing/tuning | `unitGaussianMinimaxExpectedPseudoRegret_ge_one_div_fiftyFour_sqrt` | source-order endpoint | Chapter 15 | compiled |
| `CH13-BROADER-SUBGAUSSIAN-NEAR-MINIMAX` | Algorithm 7 constant-factor near-minimax consequence on the stated 1-subgaussian class | Gaussian subclass transfer and Theorem 9.1 MOSS upper theorem | `LowerBounds.moss_nearMinimax` | connected dependency | Chapter 9 plus Chapter 13 | compiled; integration pending |
| `CH13-TYPED-CANARY` | full-conclusion applications and nondegenerate instance | compiled declarations | `Tests/TextbookPartIVChapter13Canary.lean` | project-local | Tests | verified |
| `CH13-EVIDENCE-SITE` | task/window/DAG/export/index/site agreement | all local gates | repository artifacts | repository | site checks/review | verified locally |
| `CH13-REMOTE` | current Chapter 15 downstream extension PR, Actions, Pages, live page | accepted local chapter; earlier dependency-slice PR remains historical evidence only | remote workflow | repository | deployment | pending current extension |

## Gaps

### Maximal concentration leaf

`ConcentrationMartingaleMaximal.lean` now proves conditional-Jensen
exponential submartingality, Doob finite maximal Chernoff and optimized
subgaussian bounds, and an independent centered coordinate producer.
For strongly measurable independent real X_i with zero integrals and common
subgaussian proxy c>0, positive n and epsilon, the event
`exists i<=n, epsilon<=sum_(j<i) X_(j+1)` has probability at most
`exp(-epsilon^2/(2*n*c))`. This is one-sided and uniform over a finite time
prefix, not a union-bound estimate. The natural filtration and partial-sum
martingale are proved via the existing MartingaleDiff and Mathlib independence
APIs; all exponential integrability follows from the sum-MGF producer.
Source variance is c=sigma^2. MOSS's actual centered reward stream still
must instantiate the explicit coordinate contracts; Lemma 9.3 peeling and
Theorem 9.1 regret assembly remain unproved.

### Active MOSS leaf (2026-09-05)

Source: Algorithm 7 / Theorem 9.1, `TXT-LATTIMORE-SZEPESVARI-2020`.
Project-local module `Algorithms/MOSS.lean` will define logPlus as
`log(max 1 x)`, radius `sqrt(4/s * logPlus(n/(k*s)))`, the real score,
and zero-based initialization followed by the existing `UCB.scoreArgmax`.
The first k actions select their matching `Fin k` indices. The algebraic
consumer assumes t>=k, an explicit best-index lower bound `muBest-deficit`,
and gap>2*deficit; it concludes selected index>selected mean+gap/2.
No stochastic optimism or regret bound is assumed or claimed.

Retrieval: `search-memory MOSS`, `list-lean-decls confidenceScoreArgmaxAction
--statement`; `UCB.scoreArgmax_spec` is already compiled. Cards
`MLIB-REAL-LOG-SQRT`, `MLIB-FINTYPE-FIN`, `MLIB-ORDER-ALGEBRA` supply
the direct log/sqrt/Fin and linear-arithmetic route. Import the existing
UCB module; no dependency changes or generic Mathlib lemma are needed.
The zero-pull radius is totalized by Lean real division, but the source
interpretation requires initialized histories; do not claim this alone
proves history consistency, measurability, peeling, or expected regret.

Next history leaf: reuse `UCB.measurable_realHistoryPullCount` and
`UCB.measurable_realHistoryEmpMean`, with the existing inclusive pair history
at index t representing t+1 observations. The next action is therefore at
time t+1. `ETC.realArgmaxCommit` is definitionally the same fold as
`UCB.scoreArgmax`; its compiled coordinatewise measurability theorem supplies
the selector gate. Natural-count radius measurability follows by composition
with `measurable_of_countable`. Package only this concrete history selector
and its deterministic kernel; stochastic regret remains a separate target.

- [x] Prove the exact Mills-ratio integral bounds of source Eq. (13.4) and
  rescale them to both sides of Eq. (13.1).  The first executable leaf is a
  real-analysis lemma bounding `integral (fun t => exp (-t^2))` over
  `Set.Ioi x` for `x>=0` by the two printed rational denominators.
- [x] The finite-iid Gaussian sum/scaling bridge compiles on the canonical
  product law via characteristic-function factorization and exact Gaussian
  scaling.
- [x] Compile the source-compatible MOSS/Algorithm 7 upper theorem for the
  broader finite-arm 1-subgaussian class before claiming the main-prose
  constant-factor near-minimax consequence.

- [x] History-law likelihood ratio for one changed arm under the same adaptive policy.
- [x] KL chain rule reducing history divergence to expected pull count times arm KL.
- [x] Event-level direction-correct testing inequality.
- [x] Unit-variance Gaussian KL computation and `Delta` calibration.
- [x] Chapter 15 minimax packing/averaging and universal-constant extraction.
- [x] Independent review of quantifier order, KL direction, absolute continuity,
  policy consistency, and asymptotic order.
