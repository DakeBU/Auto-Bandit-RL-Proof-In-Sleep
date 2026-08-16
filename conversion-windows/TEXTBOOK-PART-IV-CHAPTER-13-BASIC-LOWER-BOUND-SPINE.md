# Conversion Window: Textbook Part IV Chapter 13 lower-bound basic ideas spine

Task id: `TEXTBOOK-PART-IV-CHAPTER-13-BASIC-LOWER-BOUND-SPINE`

Source card: `TXT-LATTIMORE-SZEPESVARI-2020`

Scenario card: `SCN-STOCHASTIC-FINITE`

## Source placement and status fence

The canonical source is Lattimore--Szepesvári, *Bandit Algorithms*, CUP 2020,
Part IV, Chapter 13, printed pp. 180--185 / PDF pp. 189--194. Section 13.1 is
on printed pp. 181--182. Theorem 13.1 states the order
`sqrt(k*n)` minimax lower bound for unit-variance Gaussian bandits with mean
vectors in `[0,1]^k`, for `k > 1` and `n >= k`; the source explicitly says its
proof appears in Chapter 15.

Consequently, the Chapter 13 local target is the exact semantic and
deterministic conversion window used by the chapter's heuristic. Theorem
13.1 itself remains `planned`, not `partial` or `compiled`.

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
| comparison of `T_0` under `nu,nu'` | statistical indistinguishability bridge | explicit `baseFirstPulls - changedFirstPulls <= error` premise | quantitative bridge contract | planned Ch. 14--15 |
| Theorem 13.1 | Gaussian minimax lower bound | no local declaration yet | source terminal | planned Ch. 15 |

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
| `Delta <= 1/2` | absent from compiled algebra; required by later Gaussian environment construction | keeps changed mean `2*Delta` in `[0,1]` | yes for Ch. 15 |
| same policy in both environments | future model-level type/contract | required for change of measure | yes for Ch. 14--15 |
| policy measurability/history adaptation | future explicit regularity | defines both induced history laws | yes for Ch. 14--15 |
| absolute continuity of changed history law | future explicit regularity | legitimizes likelihood-ratio/KL comparison | yes for Ch. 14--15 |
| unit Gaussian variance and means in `[0,1]` | source theorem contract only | exact Theorem 13.1 environment class | yes for Ch. 15 |
| `n >= k` | source theorem contract only | exact Theorem 13.1 horizon domain | yes for Ch. 15 |
| concentration/stopping-time assumptions | absent | Chapter 13 uses neither | no |

## Local API and proof route

| Leaf | Existing APIs/imports | Retrieval cards | Intended route | Pivot rule |
| --- | --- | --- | --- | --- |
| minimax surface | Mathlib `iSup`, `iInf`, `ENNReal`, subtypes | `MLIB-ORDER-ALGEBRA` | direct complete-lattice definitions and bounds | retain explicit subsets; do not replace sup/inf with finite maxima unless source class is later finite |
| alternative budget | `Fin.sum_univ_succ`, ordered-field algebra | `MLIB-FINSET-SUMS`, `MLIB-FINTYPE-FIN`, `MLIB-ORDER-ALGEBRA` | split the full finite sum into base plus alternatives | if simplification fails, expose a separate sum-splitting lemma; do not assume the desired alternative bound |
| finite average | `Finset.exists_le_of_sum_le`, constant finite sum | same Mathlib cards | compare alternative sum to `m` copies of `n/m` | if API mismatch persists, prove by contradiction using `Finset.card_nsmul_le_sum` |
| algebra reduction | `max`, ordered-field arithmetic, `nlinarith` | `MLIB-ORDER-ALGEBRA` | add the two expressions under an explicit upper bound on the cross-law pull discrepancy | split product monotonicity from linear half-max lemma if automation is fragile |
| information bridge | no matching local terminal | `WEAPON-KL-CHANGE-OF-MEASURE` only | Chapter 14 history KL/change-of-measure surface | never promote the weapon card; record exact absolute-continuity and KL direction |

## Proof DAG

| Node | Interface | Dependencies | Lean declaration | Mathlib status | Gate | Status |
| --- | --- | --- | --- | --- | --- | --- |
| `CH13-MINIMAX-SURFACE` | explicit sup/inf expected-regret semantics | complete lattice | `worstCaseExpectedRegret`, `minimaxExpectedRegret` and order leaves | project-local | focused Lean | compiled |
| `CH13-ALTERNATIVE-BUDGET` | alternative sum at most total horizon | full expected-pull identity, nonnegativity | internal/public budget lemma | mathlib-composed project leaf | focused Lean | compiled |
| `CH13-LEAST-EXPLORED` | some `i.succ` has count at most `n/m` | alternative budget, finite averaging | `exists_leastExploredAlternative` | mathlib-composed project leaf | focused Lean | compiled |
| `CH13-TWO-ENV-ALGEBRA` | quantitative `Delta*(n-error)/2` max bound | nonnegative gap, explicit upper bound on the cross-law pull discrepancy | `max_base_changed_regretLowerBound_ge_half_sub_error`; zero-error corollary `max_base_changed_regretLowerBound_ge_half` | project-local | focused Lean | compiled |
| `CH13-HISTORY-TRANSPORT` | derive cross-law pull/event comparison | same policy/history law, AC, history KL | none | planned generic leaf | Chapter 14 | planned |
| `CH13-THEOREM-13-1` | universal-constant Gaussian minimax `sqrt(k*n)` lower bound | Chapter 13 leaves plus Chapter 14 information theory and Chapter 15 packing/tuning | none | source theorem | Chapter 15 | planned |
| `CH13-TYPED-CANARY` | full-conclusion applications and nondegenerate instance | compiled declarations | `Tests/TextbookPartIVChapter13Canary.lean` | project-local | Tests | verified |
| `CH13-EVIDENCE-SITE` | task/window/DAG/export/index/site agreement | all local gates | repository artifacts | repository | site checks/review | verified locally |
| `CH13-REMOTE` | PR, Actions, Pages, live page | accepted local chapter | remote workflow | repository | deployment | planned |

## Gaps

- [ ] History-law likelihood ratio for one changed arm under the same adaptive policy.
- [ ] KL chain rule reducing history divergence to expected pull count times arm KL.
- [ ] Event-level binary KL or another direction-correct testing inequality.
- [ ] Unit-variance Gaussian KL computation and `Delta` calibration.
- [ ] Chapter 15 minimax packing/averaging and universal-constant extraction.
- [x] Independent review of quantifier order, KL direction, absolute continuity,
  policy consistency, and asymptotic order.
