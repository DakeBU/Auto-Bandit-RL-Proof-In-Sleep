# Proof Obligations: Textbook Part IV Chapter 13 lower-bound basic ideas spine

Task id: `TEXTBOOK-PART-IV-CHAPTER-13-BASIC-LOWER-BOUND-SPINE`

Source card: `TXT-LATTIMORE-SZEPESVARI-2020`

Scenario card: `SCN-STOCHASTIC-FINITE`

| Node | Target | Dependencies | Local APIs/imports | Retrieval cards | Intended proof route | Regularity contracts | Mathlib status | Lean declaration | Gate | Status |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `CH13-SOURCE-FENCE` | exact Theorem 13.1 and Section 13.1 placement; proof deferral recorded | official author PDF and CUP metadata | task/conversion window | `TXT-LATTIMORE-SZEPESVARI-2020` | conservative paraphrase with page mapping | edition, chapter, section, printed/PDF pages | source evidence | n/a | source review | mapped |
| `CH13-MINIMAX-SURFACE` | worst-case sup and minimax inf over explicit classes | source semantics | `iSup`, `iInf`, `ENNReal`, subtypes | `MLIB-ORDER-ALGEBRA` | complete-lattice definitions and introduction/elimination bounds | class subsets explicit; meaningful consumers prove nonemptiness | project-local | `LowerBounds.worstCaseExpectedRegret`, `LowerBounds.minimaxExpectedRegret` and order leaves | focused Lean | compiled |
| `CH13-ALTERNATIVE-BUDGET` | sum of alternative expected pulls is at most horizon | exact total sum and base nonnegativity | `Fin.sum_univ_succ`, ordered field | `MLIB-FINSET-SUMS`, `MLIB-FINTYPE-FIN` | rewrite the full sum as base plus tail, then linear arithmetic | all expected pulls nonnegative | mathlib-composed project leaf | `LowerBounds.alternativeExpectedPullBudget_le` | focused Lean | compiled |
| `CH13-LEAST-EXPLORED` | some alternative has expected pulls at most `n/m` | alternative budget, `0 < m` | `Finset.exists_le_of_sum_le`, constant sum | `MLIB-FINSET-SUMS`, `MLIB-FINTYPE-FIN`, `MLIB-ORDER-ALGEBRA` | finite average comparison | `0 < m`; exact expected-pull total | mathlib-composed project leaf | `LowerBounds.exists_alternative_le_average`, `LowerBounds.exists_leastExploredAlternative` | focused Lean | compiled |
| `CH13-TWO-ENV-ALGEBRA` | max of base and changed expressions is at least `Delta*(n-error)/2` under an explicit pull-discrepancy bound | equations (13.2)--(13.3) expressions | real ordered-field algebra, `max`, `nlinarith` | `MLIB-ORDER-ALGEBRA` | show their sum is at least `Delta*(n-error)`, then use max/average | `0 <= Delta`; visible `baseFirstPulls-changedFirstPulls <= error` bridge | project-local | `LowerBounds.baseEnvironmentRegret`, `LowerBounds.changedEnvironmentRegretLowerBound`, `LowerBounds.max_base_changed_regretLowerBound_ge_half_sub_error`; zero-error corollary `LowerBounds.max_base_changed_regretLowerBound_ge_half` | focused Lean | compiled |
| `CH13-HISTORY-TRANSPORT` | same-policy history-law comparison supplies the cross-law event inequality | Chapter 14 information theory and Chapter 15 history KL | compiled Gaussian/history APIs | local declarations; weapon card inspiration only | likelihood ratio, KL chain rule, direction-correct event inequality | measurability, policy consistency, exact KL direction | project-local | `LowerBounds.base_event_probability_lower_bound`, `LowerBounds.changed_complement_probability_lower_bound` | Chapter 15 | compiled |
| `CH13-THEOREM-13-1` | Gaussian finite-arm minimax lower bound `>= c*sqrt(k*n)` | Chapter 13 deterministic leaves, Chapter 14 information theory, Chapter 15 minimax construction | compiled Gaussian/history APIs | source card plus compiled local declarations | base/changed instances, least arm, testing bound, Delta tuning, inf/sup extraction | unit variance; means in `[0,1]^k`; `k>1`; `n>=k`; explicit `c=1/54` | source-order endpoint | `LowerBounds.unitGaussianMinimaxExpectedPseudoRegret_ge_one_div_fiftyFour_sqrt` | Chapter 15 | compiled |
| `CH13-TYPED-CANARY` | external root-import applications and a three-arm numeric witness | compiled Chapter 13 declarations | root `BanditRLProof` import | local declaration index | exact full-conclusion examples plus `#print axioms` | nonempty policy/environment subsets; nonnegative vector summing to horizon | project-local | `Tests/TextbookPartIVChapter13Canary.lean` | dedicated/root Tests | verified |
| `CH13-LOCAL-FULL-GATE` | focused/root/Tests/placeholder/full harness gates | all compiled local nodes | Lake and `tools/bandit.py` | repository | deterministic gate suite | Windows long-path workaround must not be mistaken for a Lean proof failure | repository | n/a | `python3 tools/bandit.py check` | verified |
| `CH13-EVIDENCE-SITE` | proof export, indexes, readings/highlights/results/implementation map/README and Part IV site agree | local full gate | harness and website scripts | repository | generated evidence plus maintained source data | only gate-passing declarations marked compiled | repository | n/a | lean-verified build/site check/browser review | verified locally |
| `CH13-REVIEW` | independent read-only theorem/Lean consistency audit | all local artifacts | source, declarations, generated site | all above | check quantifiers, KL direction, AC, policy consistency and order claims | no unresolved P0--P3 | repository | n/a | review | verified |
| `CH13-REMOTE` | current Chapter 15 downstream extension PR, Actions, Pages deployment and live Chapter 13 verification | accepted local chapter; earlier dependency-slice PR is historical evidence only | GitHub/Pages workflow | repository | branch PR; never direct push to main | remote state must be current | repository | n/a | remote deployment | pending current extension |

## Failure classification

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

## Failure policy

Keep failed proof attempts in
`proof-attempts/TEXTBOOK-PART-IV-CHAPTER-13-BASIC-LOWER-BOUND-SPINE/` when a
mathematical route actually fails. Do not log ordinary elaboration iteration
as a scientific failure. Never weaken the fenced terminal or promote a
source/retrieval card to certified local memory.
