# Proof Obligations: Textbook Part IV Chapter 14 information-theory spine

Task id: `TEXTBOOK-PART-IV-CHAPTER-14-INFORMATION-THEORY-SPINE`

Source card: `TXT-LATTIMORE-SZEPESVARI-2020`

Scenario card: `SCN-STOCHASTIC-FINITE`

| Node | Target | Dependencies | Local APIs/imports | Retrieval cards | Intended proof route | Regularity contracts | Mathlib status | Lean declaration | Gate | Status |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `CH14-SOURCE-FENCE` | Theorem 14.1 RN formula and Theorem 14.2/Eq. (14.7), exact pages/direction | official PDF and CUP metadata | task/window | textbook card | conservative paraphrase | edition, printed/PDF pages, `D(P,Q)` direction | source evidence | n/a | source review | mapped |
| `CH14-KL-SURFACE` | extended-real measure KL plus singular/finite characterization | Mathlib KL/LLR | `klDiv`, `llr`, branch lemmas | Mathlib source audit | transparent adapters | same space; AC and integrability visible | imported plus wrappers | `relativeEntropy` and branch adapters | focused Lean | planned |
| `CH14-BERNOULLI-SURFACE` | Eq. (14.4) with support endpoints | existing KLUCB KL | `bernoulliKL`, core and endpoint lemmas | local declaration index | reuse, do not duplicate semantics | `p,q∈[0,1]`; singular support gives `∞` | compiled local dependency | `bernoulliRelativeEntropy` | focused Lean | planned |
| `CH14-RN-RESTRICT` | RN derivative agrees after restricting both laws to a measurable event | AC and density representation | `withDensity_rnDeriv_eq`, `restrict_withDensity`, `rnDeriv_withDensity` | Mathlib source audit | identify both restricted measures through the original density | finite probability measures; `MeasurableSet A`; `P≪Q` | Mathlib-candidate project leaf | helper in `InformationTheory.lean` | focused Lean | planned |
| `CH14-EVENT-DPI` | `d(P(A),Q(A)) <= D(P,Q)` | RN restrict helper, f-divergence integral, convex mass lower bound | `klDiv_eq_lintegral_klFun_of_ac`, `mul_klFun_le_toReal_klDiv` | Mathlib source audit | split over event/complement and add | probability laws; measurable event; exact KL direction | Mathlib-candidate project leaf | `bernoulliRelativeEntropy_event_le` | focused Lean | planned |
| `CH14-BINARY-BH` | `p+(1-q) >= exp(-d(p,q))/2` with exact endpoints | Bernoulli core | real sqrt/log/exp and concavity | source proof | affinity lower bound plus Le Cam overlap algebra | both parameters in unit interval; all endpoints explicit | project-local | `binaryBretagnolleHuber` | focused Lean | planned |
| `CH14-THEOREM-14-2` | unconditional `P(A)+Q(Aᶜ) >= scale(D(P,Q))` | event DPI and binary BH | ENNReal finite/top conversions; probability complement | all above | split KL top; finite branch derives AC and converts safely | no hidden finite KL or mutual AC | source terminal | `bretagnolleHuberScale`, `bretagnolleHuber` | focused Lean | planned |
| `CH14-HISTORY-KL` | adaptive same-policy history divergence decomposition | Chapter 14 measure leaves and kernel chain rule | future bandit history model | `klDiv_compProd_eq_add` only as route evidence | Chapter 15 iterative construction | policy consistency, measurability, AC | planned | none | Chapter 15 | planned |
| `CH14-TYPED-CANARY` | root-import applications to finite and singular cases, all axioms printed | compiled Chapter 14 declarations | root import | local declarations | exact full-conclusion examples | explicit probability measures/events | project-local | `Tests/TextbookPartIVChapter14Canary.lean` | Tests | planned |
| `CH14-LOCAL-FULL-GATE` | focused/root/Tests/placeholder/full harness gates | all compiled local nodes | Lake and `tools/bandit.py` | repository | deterministic gate suite | path/tooling failures distinguished from proofs | repository | n/a | full check | planned |
| `CH14-EVIDENCE-SITE` | proof export, indexes, results/highlights/readings/maps/README/site agree | local full gate | harness/site scripts | repository | generated evidence plus maintained content | only compiled/gated declarations labelled compiled | repository | n/a | site/browser | planned |
| `CH14-REVIEW` | independent theorem/Lean audit | all artifacts | source, Lean, site | all above | check KL direction, AC, endpoints, quantifiers | no unresolved P0--P3 | repository | n/a | independent review | planned |
| `CH14-REMOTE` | PR, main Actions, Pages and live Chapter 14 | accepted local chapter | GitHub workflow | repository | branch PR, never direct main push | current remote evidence | repository | n/a | deployment | planned |

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
- The event data-processing leaf is not the full Exercise 14.10.
- No kernel chain rule is yet an adaptive-bandit, same-policy history theorem;
  that construction belongs to Chapter 15.

## Failure policy

Keep mathematically failed routes in
`proof-attempts/TEXTBOOK-PART-IV-CHAPTER-14-INFORMATION-THEORY-SPINE/`.
Do not log ordinary elaboration iteration as a scientific failure, weaken the
source terminal, or promote an imported/retrieval theorem to a local proof.
