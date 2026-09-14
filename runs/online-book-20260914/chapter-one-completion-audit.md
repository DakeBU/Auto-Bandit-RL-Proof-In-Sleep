# Chapter 1 completion audit before acceptance

Status: candidate, not accepted. Canonical source v10 printed pp1-6 (PDF13-18); historical p6-7 and independent exercises1.1/1.2 separated. The audit does not treat chapter2 or chapters3-16 as complete.

- Regret difference-of-sums, comparator separation: OnlineLearningRegret; sum equivalence compiled.
- Upper-sublinear semantics: NoRegret uses eventual positive-epsilon upper bound, explicit limsup interpretation; actual FTL no-regret compiled.
- Information order: meanPredict_prefix plus general finite-history policy domain. IID independence bridge derived, not assumed for prediction.
- Squared-loss stochastic benchmark: expected_square_decomposition, independent_prediction_square, source_mean_optimal, iid_meanPredict_excess/nonneg and normalized_excess compiled. Actual mean strategy and general bounded measurable deterministic history policies covered.
- Empirical mean: exact squared-loss decomposition, interval feasibility, minimizing property compiled. Audit finding: source writes argmin as the mean; add explicit uniqueness corollary using positive-horizon decomposition before final acceptance, so that the set-valued argmin interpretation is completely accounted for.
- Lemma1.2: source exact final-leader comparison compiled.
- Theorem1.3: actual predictor, first value1/2, source4+4logT and positive horizon compiled; min replaced by its proved minimizing mean. Public root canary verifies positive regret3/4.
- Probability canary: Bernoulli half with distinct values and both masses1/2, source mean theorem instantiated. Public-root version compiled in Tests.
- Root/Tests: passed8998 jobs. Full harness session64561 pending at audit time.
- Shared Book mapping: added source-qualified chapter and four reading anchors; no copied graph. Registry11tests pass. Preview built without lean-verified; preview check session30334 pending.
- Contracts: individual fences passed; final whole-context/definition recheck and compiled dependency excerpt still required.
- Lifecycle: source cards, role outputs, attempts and reviewer records retained. This is same-model sequential review, not independent external review.
- Delivery: no new commit or PR yet; stacked base remains PR116 exacthead7306279, not main. Main untouched.

Do not advance Chapter2 proof work until uniqueness, final audit/gates and mapping are accepted. Do not use passing partial gates to close the16-chapter Goal.

## Updated audit

Uniqueness is now proved and public-root canary checked in root-tests-02 (8998jobs). Final contract-check-final verifies all24frozen interfaces and9ambient/definition prefixes. The old dependency export was found to predate uniqueness; a fresh export is running and must satisfy the extraction script's explicit uniqueness node assertion. Final site check after uniqueness is running. Local full harness did fail9Pythonerrors (not a gate pass); see full-gate-repair. Thus this is a complete mathematical candidate with acceptance/delivery gates outstanding, not an accepted chapter. General-policy history theorem and normalized Eq1.2 are included. All16chapter Goal remains incomplete.
