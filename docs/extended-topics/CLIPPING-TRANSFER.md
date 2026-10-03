# Reserved clipping transfer

This is the TRANSFER-CLIP adaptation frozen in PROTOCOL.md before interface
development. It is descriptive development evidence, not a blinded benchmark
or a published corruption-robust regret theorem.

For independent clean coordinates with a common mean and raw absolute
(1+epsilon)-moment at most u, 0 <= epsilon <= 1, u > 0, use the same sample-index
threshold and conservative radius as the truncation construction. Clipping
has absolute bias at most u/B^epsilon and second moment at most
u B^(1-epsilon). These are proved from pointwise inequalities, including the
tail region where clipping differs from truncation.

`bounded_centering_mgf` and `sum_mean_tail_of_centered` are shared with the
truncation proof. Clipping supplies its own moment proofs; the terminal does
not assume a clean-confidence, fluctuation or estimator-accuracy premise.
Signed tilts produce the two-sided tail; the existing threshold tuning gives
`confidenceRadius`. A finite union over deterministic positive prefix lengths
handles an arbitrary outcome-dependent count N <= t without asserting IID
sampling at the adaptive count.

`adaptive_corrupted_clipped_mean_tail` bounds the event

    0 < N <= t and |corrupted clipped mean - mean| >= radius(t,N) + C/N

by `2 t exp(-confidenceLog t)`. Only the consumed prefix must satisfy
`sum_{s<N} |c_s| <= C`. Corruption and count may depend on the whole outcome;
the event is bounded with the measure's outer-measure semantics, so no
measurability assumption on the adversary is hidden. For a measurable policy
and adversary this is the ordinary event probability.

`observed_corrupted_clipped_mean_tail` rewrites the latent prefix into the
actual action-trace observation sum using `clipped_observed_prefix`.
`arm_corrupted_clipped_mean_tail` obtains coordinate independence and raw
moments from the existing stationary product arm law. These are complementary
public forms of the transfer, not a corruption-robust policy performance claim.

The original public-root canary uses the genuinely noisy two-arm law from the regret
canary, a random count in {1,2}, corruption 1/2 per consumed sample, and budget
1. A separate exact calculation exercises nonzero clipping across its boundary.
This checks the theorem contract and producer assembly; it is not an empirical
coverage or efficiency evaluation. Full gate results must be recorded against
the source commit before this is described as jointly validated. Independent
semantic review, fresh compiled dependency evidence and topic acceptance remain
separate obligations.


## Independent acceptance and stronger canary (2026-09-19)

PacketG source-blind reconstruction, independent frozen-specification review,
and separate mathematical proof review accept this explicit estimator adaptation.
All five production-module hashes are frozen and unchanged. This is not a
source-faithful corruption-regret theorem or a changed-policy comparison.
The original count1/2 probability canary has an empty bad event; its role is
contract assembly. A new named long_corrupted_prefix uses random count9999/10000,
nonzero per-sample corruption1/20000 and budget1 under the same noisy arm law.
Its bad event admits a positive-probability all-zero finite clean prefix;
focused compilation and standard axiom audit passed. An initial normalization
attempt exhausted Lean's interpreter recursion on the large finite sum; the
final proof rewrites the constant sum before numeric normalization. That failed
log is preserved separately. No compiler limits or theorem premises were changed.

The new compiled direct graph has39focused declarations,655boundary declarations
and2968edges, with no dangling nodes;113project proof references are retained in
runs/extended-topics-20260919/clipping-reuse.json. This is direct dependency
evidence, not a whole-library transitive graph or a controlled efficiency result.
The terminal calls scheduled clean confidence and the clipping perturbation
producer. The deterministic supplied-premise assembly separately uses the common
estimator-error interface; do not claim the terminal directly calls that assembly.
The actual observed-action endpoint is reviewed, but the canary instantiates the
product-law prefix endpoint, not a newly built corruption-robust action policy.
