# Exploration action/count-law work

Source: Rosenski--Shamir--Szlak ICML2016 static Algorithm1, supplement A.1
Lemmas2/3 and the source-repaired route in MULTI-AGENT-CONTRACT.md.
Target: actual independent uniform all-arm exploration draws, actual
collision/free-arm observation events, exact probabilities and finite-count
probability generating functions. This is a producer for random-count reward
concentration and population estimation, not either final tail bound.

Reuse: jointDraw_rectangle_product, isolationWindow, CollisionFree,
event_add_compl. Existing finiteIID search has no matching generic finite PMF
product interface. Mathlib Fintype.prod_sum supplies normalization/factorization;
PMF.ofFintype supplies a real finite product law. Planned generic interface has
two actual consumers: effective arm-observation count and collision count.
No per-book project, dependency change or supplied independence premise.

Concentration ledger: effective observation indicator is 0/1 with actual mean
q=(1/k)*((k-1)/k)^(n-1); collision indicator is 0/1 with actual mean
p=1-((k-1)/k)^(n-1). Temporal product law is constructed; players/arms in a
single round are not asserted independent. Exact PGF is (1-q+q*z)^T or
(1-p+p*z)^T for z in ENNReal. This remains a finite-sum algebra identity.
Two-sided Hoeffding, random-count Laplace reward law, all-player union bound,
log-inverse rounding and ranking remain required. Arbitrary [0,1] reward laws
are untouched; this action law does not restrict them to PMFs.

Scratch owner: runs/extended-topics-20260920/MusicalChairsExplorationPrototype.lean.
Semantic roundtrip must inspect exact process, count definition, temporal
factorization, n/k/T boundaries and numerical n2k3 examples before promotion.

Compiler repair record: ENNReal rational diagnostics were reduced through
finite toReal equality; this avoids treating ENNReal as an ordinary field.
Local-statistic/selected-set equalities use finite-set extensionality to avoid
sensitivity to different synthesized Decidable instances. Mixed-count proofs
separate sum expansion from simplification to avoid a card/sum rewrite loop.
All original statements and boundaries were retained. No sorry, new axiom,
maxRecDepth increase, reward-law restriction or supplied probability premise
was introduced.

Current focused validation: all37 named declarations (23theorems) compile;
all37 axiom prints contain only propext, Classical.choice and Quot.sound.
Six diagnostics and the exact folded reader were checked. Independent blind
reconstruction is complete; source review and the final receipt follow.
This checkpoint is scratch-only; production root, Tests, site and registry
remain at the previous accepted coordination-regret checkpoint.

Next producer/API plan (inspected pinned Mathlib, not yet implemented):
- Reward law on Fin T -> Fin k -> Real: nested Measure.pi of arbitrary
  arm probability measures nu(a), each a.e. supported in[0,1]. Couple this
  with explorationLaw.toMeasure by Measure.prod, preserving the action
  schedule's independence of rewards.
- For a fixed complete action schedule, the observed-time filter is
  deterministic. iIndepFun_pi (Probability/Independence/Basic.lean:784)
  produces time-coordinate independence; measurePreserving_eval identifies
  each selected arm-coordinate marginal with nu(a).
- hasSubgaussianMGF_of_mem_Icc (Probability/Moments/SubGaussian.lean:860)
  gives centered proxy1/4. HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun
  (same file:780) on the observed-time filter and both signs gives the
  fixed-count two-sided tail2*exp(-D*epsilon^2/2) for D>0. D=0 must remain
  an explicit branch with its valid trivial bound.
- PMF.integral_eq_sum (Probability/ProbabilityMassFunction/Integrals.lean:47)
  can convert the action marginal's finite mixture into actual PMF weights.
  The current observationCount_laplace consumes precisely those weights.
  Product measurability/Fubini and means-as-integrals still require proofs;
  these API inspections do not establish any new concentration result.

Final source review accepted with explicit scratch scope. Its hash and all
input/axiom hashes are in multi-agent-exploration-review.json. No blocking
semantic mismatch was found. Public integration and all concentration/full
learner obligations remain open; the complete ten-topic Goal remains active.
