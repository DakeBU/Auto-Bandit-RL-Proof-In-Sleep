# Chapter 14 metric counterexamples

Source: author p.189, body paragraph after Eq.14.6, states that relative
entropy is neither symmetric nor a metric satisfying the triangle inequality.
These are mathematical claims, not excluded explanatory nonclaims.

Route: use Bernoulli parameters 0 and 1/2 for asymmetry (finite log 2 versus
infinite support mismatch), preserving ENNReal endpoints. For the triangle
inequality use Gaussian means 0,1,2 with common variance 1: D(0,2)=2 while
D(0,1)+D(1,2)=1. Every Gaussian divergence is finite, so this counterexample
does not rely on infinite-value arithmetic. Local APIs: endpoint formulas in
KLUCBBernoulli and klDiv_gaussianReal_same_variance. No new analytic dependencies.

Focused result: RelativeEntropyNonMetric builds (3462 jobs). The two declared
counterexamples are exact, with no numerical approximation. Initial errors
were ENNReal sum normalization and unfolding the Bernoulli abbreviation for
rewriting; combining ofReal terms and exposing the alias resolved both.
The Bernoulli comparison uses the existing endpoint-complete source formula;
the triangle example is directly stated for the actual Gaussian measures.
Aggregate verification remains pending outside the running arithmetic gate.

Typed canary passed, including the explicit negation of the triangle bound.
Both axiom reports contain only propext/Classical.choice/Quot.sound. Retrieval,
task memory and blueprint were refreshed. This module is focused-only.
