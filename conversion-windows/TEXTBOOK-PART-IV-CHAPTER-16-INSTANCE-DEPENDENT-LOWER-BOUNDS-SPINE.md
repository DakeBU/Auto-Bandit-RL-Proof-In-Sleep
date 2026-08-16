# Conversion Window: Textbook Part IV Chapter 16 instance-dependent lower bounds

Task id: `TEXTBOOK-PART-IV-CHAPTER-16-INSTANCE-DEPENDENT-LOWER-BOUNDS-SPINE`

Source card: `TXT-LATTIMORE-SZEPESVARI-2020`

Scenario card: `SCN-STOCHASTIC-FINITE`

## Source placement and status fence

Canonical source: Lattimore--Szepesvári, *Bandit Algorithms*, CUP 2020,
Part IV, Chapter 16, chapter DOI
<https://doi.org/10.1017/9781108571401.021>. The chapter is CUP print
pp. 177--184 / author-online labels 206--214 / physical PDF pp. 215--223.
§16.1 contains Definition 16.1 and Theorem 16.2; §16.2 contains Lemma 16.3
and Theorem 16.4. Edition-specific pagination is not converted by an offset.

The current compiled window contains Definition 16.1's generic consistency
interface plus `d_inf`, Gaussian-candidate, and log-growth dependencies.
Theorem 16.2, Lemma 16.3, and Theorem 16.4 remain uncompiled and blocked; the
website chapter must remain `partial`.

## Precise restatement

For every environment in an unstructured product class and every real
`p>0`, a consistent policy has `R_n/n^p -> 0`. For each suboptimal arm,
Theorem 16.2 chooses a one-coordinate alternative with mean strictly above the
original optimum and original-to-alternative cost approaching `d_inf`. The
source combines Lemma 15.1, Bretagnolle--Huber on
`A={T_i(n)>n/2}`, and consistency of both environments to obtain the per-arm
`liminf` information constraint and then the regret sum in Eq. (16.2).

Lemma 16.3 retains the same change of measure at finite horizon and exposes
the exact logarithmic numerator in Eq. (16.4). Theorem 16.4 applies it to a
unit-Gaussian mean shift `Delta_i(1+epsilon)` under the stated local minimax
envelope and sums the positive parts to obtain Eq. (16.5).

## Lean mapping

| Source symbol | Meaning | Lean declaration | Type / role | Status |
| --- | --- | --- | --- | --- |
| `R_n(pi,nu)/n^p -> 0` | scalar consistency at one environment | `IsConsistentRegret` | `Nat -> Real` predicate | compiled |
| `pi in Pi_cons(E)` | source Definition 16.1 quantifier order | `IsConsistentPolicyOver` | generic policy/environment interface | compiled |
| `R_n(nu)+R_n(nu')` | sum of two consistent regrets | `IsConsistentRegret.add` | limit closure | compiled |
| every-power upper bound | source auxiliary consistency consequence | `IsConsistentRegret.eventually_add_le_rpow` | eventual inequality | compiled |
| log-growth bound | source `log(R+R')/log n` step | `IsConsistentRegret.eventually_log_add_div_log_le` | eventual inequality | compiled |
| `d_inf(P,muStar,M)` | distribution-class extended-real infimum | `divergenceInfimum` | `ENNReal` | compiled definition |
| confusing candidate | `d_inf <= D(P,P')` | `divergenceInfimum_le` | source-direction order leaf | compiled |
| parameterized class | family-indexed `d_inf` | `parametricDivergenceInfimum` | `ENNReal` | compiled definition |
| Gaussian perturbation | candidate mean `muStar+epsilon` | `unitGaussianDivergenceInfimum_le_perturbed` | exact arm-KL upper bound | compiled |
| Eq. (16.2) | instance-dependent asymptotic regret lower bound | reserved terminal | bandit theorem | blocked |
| Eq. (16.4) | finite-time pull-count lower bound | reserved terminal | bandit theorem | blocked |
| Eq. (16.5) | Gaussian finite-time regret lower bound | reserved terminal | bandit theorem | blocked |

## Assumption ledger

| Assumption | Lean status | Purpose | Blocking? |
| --- | --- | --- | --- |
| unstructured product class | frozen source target | isolate one-arm alternatives | yes for terminal |
| component probability laws with finite means | future environment fields | define gaps and alternative means | yes |
| every environment/every real `p>0` | explicit compiled predicates | exact consistency | no for analytic leaves |
| nonnegative expected regret | caller obligation | probability meaning and logs | yes for terminal |
| extended-real `d_inf` | explicit compiled definition | retain empty/zero/infinite branches | no |
| strictly better alternative mean | explicit candidate premise | make changed arm optimal | no |
| original-to-alternative KL | explicit declarations | source information direction | no |
| same stochastic nonanticipating policy | missing history interface | cancel policy KL | yes |
| event `T_i(n)>n/2` measurable | future history lemma | Bretagnolle--Huber | yes |
| positive finite KL for real division | explicit future branch | Eq. (16.4) manipulation | yes |
| unit Gaussian variance | inherited compiled arm law | Theorem 16.4 | no at arm level |
| nonempty `N`, `C>0`, `0<p<1`, `0<epsilon<=1` | frozen target | finite-time calibration | yes for terminal |

## Local API and proof route

| Leaf | Existing APIs/imports | Retrieval evidence | Intended route | Pivot rule |
| --- | --- | --- | --- | --- |
| consistency | `Tendsto`, filters, real rpow | `MLIB-ASYMPTOTICS` | state the source quantifier directly and close addition/eventual bounds | do not replace every `p>0` by one fixed exponent |
| log growth | `Real.log_le_log`, `Real.log_rpow` | installed Mathlib source | clear positive log denominator after eventual power bound | keep positivity explicit |
| `d_inf` | complete lattice `sInf`, `ENNReal` | installed Mathlib source | set of original-to-alternative KL values | preserve empty and infinity branches |
| Gaussian candidate | Chapter 15 exact Gaussian KL | compiled local theorem | insert mean `muStar+epsilon`, normalize the square | do not call this the exact infimum formula |
| history information | Chapter 14 BH plus Chapter 15 chain route | compiled/blocked local dependencies | prove stochastic history KL, then one-arm reduction | no deterministic-policy substitution |
| asymptotic extraction | eventual log leaf plus liminf | Mathlib filters/liminf audit | handle finite positive `d_inf`, then zero/infinity branches | record exact analytic blocker before pivot |
| finite-time terminal | Lemma 16.3, Gaussian KL, regret decomposition | source proof | preserve local alternative class and positive part | no constant or horizon-class weakening |

## Proof DAG

| Node | Interface | Dependencies | Lean declaration | Mathlib status | Gate | Status |
| --- | --- | --- | --- | --- | --- | --- |
| `CH16-SOURCE-FENCE` | Definition 16.1, Theorem 16.2, Lemma 16.3, Theorem 16.4 | official PDF/CUP | repository evidence | source evidence | source review | mapped |
| `CH16-CONSISTENCY` | exact every-positive-power predicate | filters/rpow | `IsConsistentRegret`, `IsConsistentPolicyOver` | project-local | focused Lean | compiled |
| `CH16-CONSISTENCY-ALGEBRA` | sum, eventual power and log bounds | previous node | three `IsConsistentRegret` theorems | project-local | focused Lean | compiled |
| `CH16-DINF` | distribution-set and parameterized infima | `sInf`, Chapter 14 KL | `divergenceInfimum`, `parametricDivergenceInfimum`, candidate lemmas | project-local | focused Lean | compiled |
| `CH16-GAUSSIAN-CANDIDATE` | perturbed alternative cost | Chapter 15 Gaussian KL | `unitGaussianDivergenceInfimum_le_perturbed` | project-local | focused Lean | compiled |
| `CH16-GAUSSIAN-DINF-EXACT` | Table 16.1 unit-variance formula | infimum limit/lower bound | none | open candidate | focused Lean | partial |
| `CH16-HISTORY-INFORMATION` | one-arm expected-pull KL constraint | Chapter 15 Lemma 15.1 | none | connected blocker | focused Lean | blocked |
| `CH16-THEOREM-16-2` | exact liminf regret bound | previous two analytic/semantic branches | reserved terminal | source terminal | focused Lean | blocked |
| `CH16-LEMMA-16-3` | exact finite-time pull lower bound | history KL and BH | reserved terminal | source terminal | focused Lean | blocked |
| `CH16-THEOREM-16-4` | exact Gaussian Eq. (16.5) | Lemma 16.3 and Gaussian KL | reserved terminal | source terminal | focused Lean | blocked |
| `CH16-TYPED-CANARY` | root-import applications and axiom reports | compiled slice | `Tests/TextbookPartIVChapter16Canary.lean` | project-local | Tests | verified locally |
| `CH16-EVIDENCE-SITE` | all artifacts agree on partial/blocked boundary | scoped artifacts | repository artifacts | repository | full/site/browser | verified locally |
| `CH16-REVIEW` | direction/quantifier/AC/policy/asymptotic audit | all artifacts | review record | repository | read-only | reviewed; P3 corrected |
| `CH16-REMOTE` | PR, main Actions, Pages, live page | accepted local slice | PR #15; merge `7b3dd86`; run `31967845116`; deploy `95218324472`; live desktop/mobile | repository | deployment | verified |

## Gaps

- [x] Exact source/page/semantic mapping.
- [x] Consistency, `d_inf`, candidate, Gaussian perturbation, and log-growth leaves.
- [ ] Exact Gaussian `d_inf` equality and extended-real branch audit.
- [ ] Same-policy stochastic history KL and one-arm information constraint.
- [ ] Theorem 16.2 `liminf` terminal.
- [ ] Lemma 16.3 and Theorem 16.4.
- [x] Full local Lean, harness, site, browser, and independent-review gates.
- [x] PR, authoritative-main Actions, Pages deployment, and live-page gates.
