# Deterministic confidence intervals

[Read the proof and its Lean statements](lesson.md). The certificate composes a bound on bias with a bound on estimation error. For a finite active set, the interval filter keeps an arm when its upper endpoint reaches every active lower endpoint.

Two consequences use this same filter. An active maximizer survives whenever all active intervals contain their true means. If all active radii are at most *r*, a gap strictly greater than 4*r* from a specified active reference arm excludes the candidate. The reference arm in the second result can be any active arm.

Touching endpoints pass that pairwise comparison. A third arm can still exclude the candidate. At a gap of exactly 4*r*, take means 0 and 4, estimates 1 and 3, and both radii 1. The intervals [0, 2] and [2, 4] touch, so the lower-mean arm can survive.

The application supplies the error bounds. Probabilistic coverage, sampling and stopping rules require separate results.

The [independent review](source-review.md) and [original verification](verification.json) describe the October 9 contribution. The [byte bindings](../../research-wiki/integrations/CONFIDENCE-INTERVAL-CERTIFICATES-20261106/git-byte-bindings.json) identify the exact files used in review and the independently reproduced proof-dependency graph.
