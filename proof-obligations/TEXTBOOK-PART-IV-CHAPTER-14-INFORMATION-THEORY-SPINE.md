# Proof Obligations: Textbook Part IV Chapter 14 information-theory spine

Task id: `TEXTBOOK-PART-IV-CHAPTER-14-INFORMATION-THEORY-SPINE`

Source card: `TXT-LATTIMORE-SZEPESVARI-2020`

Scenario card: `SCN-STOCHASTIC-FINITE`

| Node | Target | Dependencies | Local APIs/imports | Retrieval cards | Intended proof route | Regularity contracts | Mathlib status | Lean declaration | Gate | Status |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `CH14-SOURCE-FENCE` | Theorem 14.1 RN formula and Theorem 14.2/Eq. (14.7), exact pages/direction | official PDF and CUP metadata | task/window | textbook card | conservative paraphrase | edition, printed/PDF pages, `D(P,Q)` direction | source evidence | n/a | source review | mapped |
| `CH14-KL-SURFACE` | extended-real measure KL plus singular/finite characterization | Mathlib KL/LLR | `klDiv`, `llr`, branch lemmas | Mathlib source audit | transparent adapters | same space; AC and integrability visible | imported plus wrappers | `relativeEntropy` and branch adapters | focused Lean | compiled |
| `CH14-BERNOULLI-SURFACE` | two-symbol/Bernoulli specialization of Eq. (14.4), with support endpoints | existing KLUCB KL | `bernoulliKL`, core and endpoint lemmas | local declaration index | reuse, do not duplicate semantics | `p,q∈[0,1]`; singular support gives `∞`; arbitrary finite alphabets remain open | compiled local dependency | `bernoulliRelativeEntropy` | focused Lean | compiled |
| `CH14-RN-RESTRICT` | RN derivative agrees after restricting both laws to a measurable event | AC and density representation | `withDensity_rnDeriv_eq`, `restrict_withDensity`, `rnDeriv_withDensity` | Mathlib source audit | identify both restricted measures through the original density | finite probability measures; `MeasurableSet A`; `P≪Q` | Mathlib-candidate project leaf | `rnDeriv_restrict_restrict` | focused Lean | compiled |
| `CH14-EVENT-DPI` | `d(P(A),Q(A)) <= D(P,Q)` | RN restrict helper, f-divergence integral, convex mass lower bound | `klDiv_eq_lintegral_klFun_of_ac`, `mul_klFun_le_toReal_klDiv` | Mathlib source audit | split over event/complement and add | probability laws; measurable event; exact KL direction | Mathlib-candidate project leaf | `bernoulliRelativeEntropy_event_le` | focused Lean | compiled |
| `CH14-BINARY-BH` | `p+(1-q) >= exp(-d(p,q))/2` with exact endpoints | Bernoulli core | real sqrt/log/exp and concavity | source proof | affinity lower bound plus Le Cam overlap algebra | both parameters in unit interval; all endpoints explicit | project-local | `binaryBretagnolleHuber` | focused Lean | compiled |
| `CH14-THEOREM-14-2` | unconditional `P(A)+Q(Aᶜ) >= scale(D(P,Q))` | event DPI and binary BH | ENNReal finite/top conversions; probability complement | all above | split KL top; finite branch derives AC and converts safely | no hidden finite KL or mutual AC | source terminal | `bretagnolleHuberScale`, `bretagnolleHuber` | focused Lean | compiled |
| `CH14-HISTORY-KL` | adaptive same-policy history divergence decomposition | Chapter 14 measure leaves and kernel chain rule | Chapter 15 bandit history model | compiled Chapter 15 conditional-KL theorem | Chapter 15 iterative construction | common randomized policy, measurability, countably generated rewards | downstream source theorem | `banditHistoryRelativeEntropy_eq_expectedPulls_sum` | Chapter 15 | compiled outside Chapter 14 gate |
| `CH14-TYPED-CANARY` | root-import applications to finite and singular cases, all axioms printed | compiled Chapter 14 declarations | root import | local declarations | exact full-conclusion examples | explicit probability measures/events | project-local | `Tests/TextbookPartIVChapter14Canary.lean` | Tests | verified |
| `CH14-LOCAL-FULL-GATE` | focused/root/Tests/placeholder/full harness gates | all compiled local nodes | Lake and `tools/bandit.py` | repository | deterministic gate suite | path/tooling failures distinguished from proofs | repository | n/a | full check | verified locally |
| `CH14-EVIDENCE-SITE` | proof export, indexes, results/highlights/readings/maps/README/site agree | compiled chapter surface | harness/site scripts | repository | generated evidence plus maintained content | only compiled/gated declarations labelled compiled | repository | n/a | site/browser | verified locally |
| `CH14-REVIEW` | independent theorem/Lean audit | all artifacts | source, Lean, site | all above | check KL direction, AC, endpoints, quantifiers | no unresolved P0--P3 | repository | n/a | independent review | verified |
| `CH14-REMOTE` | PR, main Actions, Pages and live Chapter 14 | accepted local chapter | GitHub workflow | repository | branch PR, never direct main push | PR #11; merge `194aca9`; main run `31949303227`; deploy job `95172626370`; live desktop/mobile | repository | n/a | deployment | verified for the historical §14.2 milestone; the 2026-09-04 extension awaits its own PR |

## Whole-chapter extension obligations

| Node | Target | Dependencies | Intended proof route | Lean declaration | Gate | Status |
| --- | --- | --- | --- | --- | --- | --- |
| `CH14-CODE-MODEL` | typed finite binary prefix-code surface and expected length | lists, finite sums, Mathlib Kraft--McMillan | define injective/prefix-free/nonempty codes; prove range uniquely decodable and expose finite Kraft adapter | `BinaryPrefixCode`, `BinaryPrefixCode.uniquelyDecodable_range`, `BinaryPrefixCode.kraft_inequality`, `expectedCodeLength` | focused Lean | compiled |
| `CH14-ENTROPY-DEFINITIONS` | Eqs. (14.2)--(14.3) entropy definitions, nonnegativity, and nats/bits conversion | finite sums, real log | exact finite support convention; term at zero is zero | `discreteEntropy`, `discreteEntropyBaseTwo`, `discreteEntropyBaseTwo_eq_div_log_two`, `discreteEntropy_nonneg` | focused Lean | compiled |
| `CH14-HUFFMAN-BOUND` | Eq. (14.2), including existence/optimality of a prefix code | Kraft--McMillan, Huffman/tree construction | no conditional optimality premise may masquerade as this terminal | none | chapter terminal | blocked |
| `CH14-SOURCE-CODING` | arithmetic/block-code achievability and converse | product distributions, uniquely decodable block codes, asymptotics | formal source-coding theorem | none | chapter terminal | blocked |
| `CH14-FINITE-DISCRETE-KL` | Eq. (14.4) for an arbitrary finite alphabet | finite sums, support endpoints | atomwise AC equivalence, RN density ratio, finite LLR integrability, and finite integral sum; singular atom forces infinity | `relativeEntropy_finite_sum_log`, `relativeEntropy_finite_eq_if`, `relativeEntropy_finite_eq_top_iff` | focused Lean and root-import canary passed | compiled |
| `CH14-DISCRETISATION-SUP` | Eq. (14.5) and equality with RN KL in Theorem 14.1 | finite measurable quotients/partitions, supremum | source definition followed by Dobrushin/RN equivalence | none | chapter terminal | blocked |
| `CH14-COMMON-DENSITY` | Eq. (14.6) under a common σ-finite dominating measure | RN chain rule, integral transport | expose exact density formula | Q-RN specialization only | focused Lean | partial |
| `CH14-KL-SEPARATION` | nonnegativity and zero iff equality | Mathlib KL | `ENNReal` order plus thin source-mapped equality adapter | `relativeEntropy_eq_zero_iff` | focused Lean | compiled |
| `CH14-GAUSSIAN-EXAMPLE` | common positive variance formula | Gaussian RN/KL and scaling | generalize the compiled unit-variance Chapter 15 leaf | unit-variance declaration only | focused Lean | partial |
| `CH14-MEASURE-OVERLAP` | source Eqs. (14.8)--(14.9) | common density, Cauchy--Schwarz, Jensen | measure-level overlap and affinity route | binary specializations only | focused Lean | partial |
| `CH14-GAUSSIAN-TESTING-APPLICATION` | displayed error, `3/10`, and max-error `3/20` consequences | general Gaussian KL, Theorem 14.2, scalar exp bound | direct source application | none | focused Lean | planned |
| `CH14-EX14-10-FULL-DPI` | KL monotonicity after restriction to any sub-σ-algebra | `Measure.trim`, `toReal_rnDeriv_trim`, conditional expectation and Jensen | split infinite KL; identify the trimmed RN density as a conditional expectation and integrate Jensen; event DPI remains a specialization | `relativeEntropy_trim_le` | optional focused Lean | compiled |

## Failure classification

Use exactly one: source translation gap; local Lean lemma gap; theorem-card
dependency; external cited result; semantic interface gap; missing regularity
contract; likely false statement or counterexample; invalid route; stale
dynamic leaf; connected blocker; Windows path-length/build-artifact failure.

## Reviewer statement fence

- Theorem 14.1 is represented by the exact `klDiv` extended-real branches;
  the integrability condition reflects Mathlib's real-integral implementation
  and is not hidden.
- Theorem 14.2 remains unconditional. `bretagnolleHuberScale` makes
  `exp(-∞)=0` explicit instead of adding a finite-KL premise.
- Event probabilities are mapped to Bernoulli parameters in the order
  `P(A),Q(A)`, so data processing and the final theorem both use `D(P,Q)`.
- The complement is evaluated under `Q`; replacing it by `P`, or reversing KL,
  changes the theorem.
- The event data-processing leaf is not itself the full Exercise 14.10; the
  arbitrary-sub-sigma-algebra theorem is `relativeEntropy_trim_le`.
- The adaptive-bandit, same-policy history theorem now compiles in Chapter 15;
  it is not retroactively a Chapter 14 source claim.

## Failure policy

Keep mathematically failed routes in
`proof-attempts/TEXTBOOK-PART-IV-CHAPTER-14-INFORMATION-THEORY-SPINE/`.
Do not log ordinary elaboration iteration as a scientific failure, weaken the
source terminal, or promote an imported/retrieval theorem to a local proof.
