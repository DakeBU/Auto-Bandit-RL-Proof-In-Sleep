# Proof Obligations: Textbook Part IV Chapter 15 minimax lower-bounds spine

Task id: `TEXTBOOK-PART-IV-CHAPTER-15-MINIMAX-LOWER-BOUNDS-SPINE`

Source card: `TXT-LATTIMORE-SZEPESVARI-2020`

Scenario card: `SCN-STOCHASTIC-FINITE`

| Node | Target | Dependencies | Local APIs/imports | Retrieval cards | Intended proof route | Regularity contracts | Mathlib status | Lean declaration | Gate | Status |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `CH15-SOURCE-FENCE` | Lemma 15.1/Eq. (15.1) and Theorem 15.2, exact pages/direction/constant | official author PDF and CUP metadata | task/window | textbook card | conservative paraphrase | same randomized policy; first-law expectation; `k>1`; `n>=k-1`; unit Gaussian class | source evidence | n/a | source review | mapped |
| `CH15-GAUSSIAN-DENSITY` | pointwise log density ratio for `N(mu,1),N(nu,1)` | Gaussian density formula | `gaussianPDFReal_def` | Mathlib source audit | cancel positive normalizer and expand squares | real means; variance exactly one | project leaf | `log_gaussianPDFReal_div_gaussianPDFReal_one` | focused Lean | compiled |
| `CH15-GAUSSIAN-LLR` | RN log likelihood ratio is the affine density ratio a.e. | mutual AC via volume and RN derivative formulas | Gaussian AC/RN APIs, `llr` | Mathlib source audit | identify both RN derivatives under first law | first-law a.e.; exact direction `mu` to `nu` | Mathlib-candidate project leaf | `llr_gaussianReal_one_ae` | focused Lean | compiled |
| `CH15-GAUSSIAN-INTEGRABLE` | Gaussian LLR integrability | previous node and first-moment `L1` | `memLp_id_gaussianReal` | Mathlib source audit | affine function of integrable identity | variance one | project leaf | `integrable_llr_gaussianReal_one` | focused Lean | compiled |
| `CH15-GAUSSIAN-KL` | exact `(mu-nu)^2/2` KL formula | AC, LLR, integrability, first moment | `klDiv_of_ac_of_integrable`, `integral_id_gaussianReal` | Mathlib source audit | integrate affine LLR and normalize `ofReal` | direction `N(mu,1)` to `N(nu,1)` | Mathlib-candidate project leaf | `klDiv_gaussianReal_one` | focused Lean | compiled |
| `CH15-CONDITIONAL-KL` | `D(mu tensor kappa,mu tensor eta)=integral D(kappa x,eta x)dmu` whenever pointwise KL is measurable | compProd RN/chain rule | `klDiv_compProd_eq_add`, kernel RN, `compProd_withDensity` | Mathlib ChainRule audit | a.e.-AC RN identity plus singular-fibre infinity branch | finite base; Markov kernels; countably generated target; measurable conditional KL | local/Mathlib-candidate lemma | `klDiv_compProd_same_left_eq_lintegral_klDiv_of_measurable` | focused Lean | compiled |
| `CH15-STOCHASTIC-POLICY` | measurable randomized nonanticipating policy kernel | finite histories and action measurable space | `Thompson.HistoryAlgorithm`; `Kernel` | repository audit | reuse the existing kernel-valued interface | same policy under both environments; private randomization allowed | project-local | `Thompson.HistoryAlgorithm.policy` | focused Lean | compiled interface |
| `CH15-HISTORY-LAW` | recursive canonical action/reward law and measurable pull count | stochastic policy plus arm kernels | `trajMeasure`, `Measure.compProd`, measurable prefix equivalences | repository/Mathlib audit | map one infinite canonical trajectory to exact finite prefixes | probability instances; observed reward only; inclusive last-round indexing | project-local | `canonicalBanditHistoryMeasure`; `finiteHistoryPullCountENNReal` | focused Lean | compiled |
| `CH15-LEMMA-15-1` | exact expected-pull divergence decomposition | conditional KL, history law, realized-count recurrence | Chapter 14 KL surface | source theorem | induction, same-policy cancellation, finite-arm regrouping | KL direction and first-law expectation exact; arbitrary Markov arm laws | source terminal | `banditHistoryRelativeEntropy_eq_expectedPulls_sum` | focused Lean | compiled |
| `CH15-LEAST-EXPLORED` | alternative arm with expected pulls at most `n/(k-1)` | pull-count budget | Chapter 13 `exists_leastExploredAlternative` | compiled local declaration | integrate pathwise count sum then average | nonnegative expected pulls; exact total `n` | compiled dependency | `exists_leastExploredAlternative` | root import | compiled |
| `CH15-TESTING-EVENT` | apply BH to `T_1(n)<=n/2` | measurable pull count and compiled Lemma 15.1 | Chapter 14 `bretagnolleHuber` | compiled local declaration | event-level change of measure | common policy; base/alternative history laws | project-local bridge | none | focused Lean | blocked: downstream bridge |
| `CH15-TUNING` | source choice `Delta=sqrt(m/(4n))`, exact information exponent `1/2`, and `Delta<=1/2` | real sqrt/field inequalities | Mathlib real analysis | source proof | square the gap, normalize the exponent, compare `m/n<=1` | positive real `m,n`; `m<=n`; natural-cast consumer remains explicit | project-local | `gaussianMinimaxGap`, `gaussianMinimaxGap_sq`, `gaussianMinimaxGap_informationExponent_eq_half`, `gaussianMinimaxGap_le_half` | focused Lean | compiled |
| `CH15-THEOREM-15-2` | every policy has a unit-Gaussian instance with regret at least `sqrt((k-1)n)/27` | all preceding bandit nodes | Chapter 13 minimax surface | textbook card | base/changed instance pair, max-to-exists, minimax inf/sup | exact policy class and unit-cube environment class | source terminal | reserved existence/minimax declarations | focused Lean | blocked: connected blocker |
| `CH15-TYPED-CANARY` | root-import Gaussian/history applications and axiom reports | compiled Chapter 15 slice | root import | local declarations | exact nontrivial examples and source-terminal checks | no `sorry`/new axioms | project-local | `Tests/TextbookPartIVChapter15Canary.lean` | Tests | pending current full gate |
| `CH15-LOCAL-FULL-GATE` | focused/root/Tests/placeholder/full harness gates | all compiled local nodes | Lake and `tools/bandit.py` | repository | deterministic gate suite | distinguish path/tool failures from proof failures | repository | n/a | full check | pending current Lemma 15.1 extension; prior Gaussian slice verified separately |
| `CH15-EVIDENCE-SITE` | export/index/results/highlights/readings/map/README/site agree | compiled Lemma 15.1 and blocked minimax terminal | harness/site scripts | repository | generated evidence plus maintained content | only gated declarations marked compiled | repository | n/a | site/browser | pending current build |
| `CH15-REVIEW` | independent theorem/Lean audit | all artifacts | source, Lean, site | all above | check quantifiers, KL direction, singular fibres, policy consistency, indexing | no unresolved P0--P3 | repository | current review | independent review | pending |
| `CH15-REMOTE` | PR, main Actions, Pages, live Chapter 15 | accepted local partial chapter | GitHub workflow | repository | branch PR, never direct main push | new PR/run/deploy | repository | n/a | deployment | pending |

## Failure classification

Use exactly one: source translation gap; local Lean lemma gap; theorem-card
dependency; external cited result; semantic interface gap; missing regularity
contract; likely false statement or counterexample; invalid route; stale
dynamic leaf; connected blocker; Windows path-length/build-artifact failure.

## Reviewer statement fence

- Eq. (15.1) compares the two complete history laws generated by one common
  possibly randomized policy. The compiled theorem uses the shared
  kernel-valued `HistoryAlgorithm`, not a deterministic specialization.
- Each per-arm KL is `D(P_i,P'_i)`, weighted by expected pulls under `nu`, not
  by pulls under `nu'` and not by the reverse KL.
- The Gaussian leaf is directionally exact but symmetric in value only because
  both variances equal one; this must not justify reversing general KL.
- Theorem 15.2 quantifies over every policy and returns an environment in the
  unit mean cube. It is not a theorem conditional on Eq. (15.1) as a premise.
- The `1/27` constant, `sqrt((k-1)n)` order, `k>1`, and `n>=k-1` conditions are
  part of the target contract.
- Exercise 15.7's stopping-time result is outside the terminal scope.

## Failure policy

Keep mathematically failed routes in
`proof-attempts/TEXTBOOK-PART-IV-CHAPTER-15-MINIMAX-LOWER-BOUNDS-SPINE/`.
Do not log ordinary elaboration iteration as a scientific failure, weaken the
source terminal, or promote the imported composition-product chain rule to an
adaptive-history decomposition.
