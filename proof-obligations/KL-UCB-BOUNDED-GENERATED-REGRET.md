# Proof Obligations: Generated bounded-reward KL-UCB regret

Task id: `KL-UCB-BOUNDED-GENERATED-REGRET`

Source: `PPR-GARIVIER-CAPPE-2011-KLUCB`;
`TXT-LATTIMORE-SZEPESVARI-2020`  
Scenario: `SCN-STOCHASTIC-FINITE`

| Node | Compiled declaration(s) | Contract | Gate | Status |
| --- | --- | --- | --- | --- |
| `KL-CORE` | `KLUCB.bernoulliKL`; `KLUCB.bernoulliKLCore_nonneg`; `KLUCB.bernoulliKL_self` | explicit `[0,1]` domain and singular endpoints | focused Lean | compiled |
| `KL-ORDER` | `KLUCB.half_sq_sub_le_bernoulliKLCore`; `KLUCB.bernoulliKLCore_le_sq_div`; `KLUCB.continuousAt_bernoulliKLCore_right` | finite interior parameters and positive denominators | focused Lean | compiled |
| `KL-CONFIDENCE-INDEX` | `KLUCB.confidenceSet`; `KLUCB.index`; `KLUCB.index_zero_count`; `KLUCB.le_index_of_mem_confidenceSet`; `KLUCB.exists_mem_confidenceSet_of_lt_index` | bounded nonempty set; no assumed sSup attainment | typed canary | compiled |
| `KL-GENERATED-POLICY` | `KLUCB.historyPolicy`; `KLUCB.generatedAction`; `KLUCB.measurable_generatedAction` | `0<K`; countable Rat reward histories; horizon-free declaration | focused Lean | compiled |
| `KL-ALIGNMENT-MAX` | `KLUCB.pairHistory_eq_finitePairHistoryOfTrace`; `KLUCB.historyIndex_finitePairHistoryOfTrace`; `KLUCB.generatedIndexAt_le_selected_of_K_le` | exact generated count/mean/index and selected argmax | typed canary | compiled |
| `KL-CONFIDENCE-PRODUCER` | `KLUCB.actionRewardHistoryStepKernelFamily_allTimeConfidence`; `KLUCB.measure_generatedKLAllTimeBadEvent_le_trajMeasure` | same policy and same trajectory measure; AE unit support; interior means; centered sub-Gaussian kernel law | typed canary | compiled |
| `KL-GOOD-EVENT-COUNT` | `KLUCB.margin_mul_gap_div_eight_le_radius_of_selected_of_not_badEvent`; `KLUCB.pullCount_le_of_not_badEvent`; `KLUCB.allHorizonPullCount_of_not_badEvent` | positive gap, initialized counts, positive delta/sigma2 and explicit margin | focused Lean | compiled |
| `KL-GENERATED-REGRET` | `KLUCB.lintegral_ofReal_pseudoRegret_generatedKLUCBBounded_le_trajMeasure` | canonical generated action/reward law; best-arm dominance; retains `T * delta` | root/tests | compiled |
| `ROOT-GATE` | root imports plus `Tests.KLUCBGeneratedRegretCanary` | no placeholders; baseline axioms only; synchronized artifacts | full `python3 tools/bandit.py check` | accepted |

## Retrieval evidence

- Mathlib: real log/continuity/differentiation, `InformationTheory.klFun`,
  conditional complete lattice `sSup`, ENNReal bridges, finite sums and
  lower-integral consumers.
- Local: generated reward-history policy/state machinery, finite argmax,
  successor count/empirical mean, telescoping all-time confidence producer,
  all-horizon ordinary-UCB threshold algebra, and finite-arm pseudo-regret
  decomposition.
- Source and weapon cards fix the intended mathematical route but are not Lean
  evidence.

## Failure and claim policy

- Do not replace the generated terminal with a scalar KL lemma, an independent
  arm-stream model, or an ordinary additive UCB score.
- Do not infer a sharp KL-Chernoff exponent from the conservative
  absolute-deviation-to-KL bridge.
- Do not hide endpoint/domain, almost-everywhere support, initialization,
  positive-gap, log/sqrt/division, or expectation contracts.
- Do not claim Garivier--Cappé leading constants, limsup optimality, or
  fixed-delta expected-average consistency from this finite-time bound.
