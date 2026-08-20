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

## Natural-language statements

Let `R_n(pi,nu)` be expected cumulative pseudo-regret. The worst-case value of
a policy over an explicit environment class is the supremum of `R_n(pi,nu)`;
the minimax value is the infimum of those worst-case values over an explicit
policy class.

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
| arm `1` in the printed one-based notation | distinguished base arm | `0 : Fin (m+1)` | finite-arm index | typed |
| arms `2,...,k` | alternative arms | `i.succ`, `i : Fin m` | finite-arm embedding | typed |
| `E_nu[T_i(n)] <= n/(k-1)` | least-explored alternative | `LowerBounds.exists_leastExploredAlternative` | finite averaging theorem | target |
| equation (13.2) | base regret expression | `LowerBounds.baseEnvironmentRegret` | deterministic real expression | target |
| equation (13.3) RHS | changed regret lower expression | `LowerBounds.changedEnvironmentRegretLowerBound` | deterministic real expression | target |
| comparison of `T_0` under `nu,nu'` | statistical indistinguishability bridge | source event comparison in `GaussianMinimax.lean` | quantitative bridge contract | compiled Ch. 14--15 consumer |
| Theorem 13.1 | Gaussian minimax lower bound | `unitGaussianMinimaxExpectedPseudoRegret_ge_one_div_fiftyFour_sqrt` | source-order endpoint with explicit `c=1/54` | compiled through Ch. 15 |

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
| concentration/stopping-time assumptions | absent | Chapter 13 uses neither | no |

## Local API and proof route

| Leaf | Existing APIs/imports | Retrieval cards | Intended route | Pivot rule |
| --- | --- | --- | --- | --- |
| minimax surface | Mathlib `iSup`, `iInf`, `ENNReal`, subtypes | `MLIB-ORDER-ALGEBRA` | direct complete-lattice definitions and bounds | retain explicit subsets; do not replace sup/inf with finite maxima unless source class is later finite |
| alternative budget | `Fin.sum_univ_succ`, ordered-field algebra | `MLIB-FINSET-SUMS`, `MLIB-FINTYPE-FIN`, `MLIB-ORDER-ALGEBRA` | split the full finite sum into base plus alternatives | if simplification fails, expose a separate sum-splitting lemma; do not assume the desired alternative bound |
| finite average | `Finset.exists_le_of_sum_le`, constant finite sum | same Mathlib cards | compare alternative sum to `m` copies of `n/m` | if API mismatch persists, prove by contradiction using `Finset.card_nsmul_le_sum` |
| algebra reduction | `max`, ordered-field arithmetic, `nlinarith` | `MLIB-ORDER-ALGEBRA` | add the two expressions under an explicit upper bound on the cross-law pull discrepancy | split product monotonicity from linear half-max lemma if automation is fragile |
| information bridge | `banditHistoryRelativeEntropy_eq_expectedPulls_sum`, `exists_gaussianMinimax_historyKL_le_half` | compiled local route; weapon card remains inspiration only | Chapter 14 testing plus Chapter 15 history KL/change-of-measure surface | preserve first-law expectation and KL direction |

## Proof DAG

| Node | Interface | Dependencies | Lean declaration | Mathlib status | Gate | Status |
| --- | --- | --- | --- | --- | --- | --- |
| `CH13-MINIMAX-SURFACE` | explicit sup/inf expected-regret semantics | complete lattice | `worstCaseExpectedRegret`, `minimaxExpectedRegret` and order leaves | project-local | focused Lean | compiled |
| `CH13-ALTERNATIVE-BUDGET` | alternative sum at most total horizon | full expected-pull identity, nonnegativity | internal/public budget lemma | mathlib-composed project leaf | focused Lean | compiled |
| `CH13-LEAST-EXPLORED` | some `i.succ` has count at most `n/m` | alternative budget, finite averaging | `exists_leastExploredAlternative` | mathlib-composed project leaf | focused Lean | compiled |
| `CH13-TWO-ENV-ALGEBRA` | quantitative `Delta*(n-error)/2` max bound | nonnegative gap, explicit upper bound on the cross-law pull discrepancy | `max_base_changed_regretLowerBound_ge_half_sub_error`; zero-error corollary `max_base_changed_regretLowerBound_ge_half` | project-local | focused Lean | compiled |
| `CH13-HISTORY-TRANSPORT` | derive cross-law event comparison | same policy/history law, Gaussian KL, history KL | `base_event_probability_lower_bound`, `changed_complement_probability_lower_bound` | project-local | Chapter 15 | compiled |
| `CH13-THEOREM-13-1` | universal-constant Gaussian minimax `sqrt(k*n)` lower bound | Chapter 13 leaves plus Chapter 14 information theory and Chapter 15 packing/tuning | `unitGaussianMinimaxExpectedPseudoRegret_ge_one_div_fiftyFour_sqrt` | source-order endpoint | Chapter 15 | compiled |
| `CH13-TYPED-CANARY` | full-conclusion applications and nondegenerate instance | compiled declarations | `Tests/TextbookPartIVChapter13Canary.lean` | project-local | Tests | verified |
| `CH13-EVIDENCE-SITE` | task/window/DAG/export/index/site agreement | all local gates | repository artifacts | repository | site checks/review | verified locally |
| `CH13-REMOTE` | current Chapter 15 downstream extension PR, Actions, Pages, live page | accepted local chapter; earlier dependency-slice PR remains historical evidence only | remote workflow | repository | deployment | pending current extension |

## Gaps

- [x] History-law likelihood ratio for one changed arm under the same adaptive policy.
- [x] KL chain rule reducing history divergence to expected pull count times arm KL.
- [x] Event-level direction-correct testing inequality.
- [x] Unit-variance Gaussian KL computation and `Delta` calibration.
- [x] Chapter 15 minimax packing/averaging and universal-constant extraction.
- [x] Independent review of quantifier order, KL direction, absolute continuity,
  policy consistency, and asymptotic order.
