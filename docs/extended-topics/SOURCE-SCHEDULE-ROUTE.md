# Sharper confidence toward the original schedule

Pinned source: BCL 2013, Lemma 1 pp.7713-7714 and Figure 1 delta=t^-2.
Bounded target: strengthen the existing radius-four signed confidence producer
from exp(-L) to exp(-5L/4), with the identical sample-index thresholds.
Owner: HeavyTailUnshiftedMGF / HeavyTailSourceConfidence; heavy-tailed first.

Search/reuse: existing raw-variable MGF uses coefficient one; Mathlib Real.exp_bound
at n=2 gives coefficient 3/4. Adapt the canonical MGF and retain the old API as
an explicit weakening. Reuse independent_sum_mgf, truncation moment/bias bounds,
and existing scale identities; do not duplicate the centered-sum proof.

Fingerprint: deterministic positive n,L,u; independent measurable real sequence;
common mean; integrable first and raw (1+epsilon) moments; epsilon in [0,1].
Closed one-sided events at unchanged radius four. No random-count confidence,
original policy, source regret coefficient or topic completion inferred.
The exponent improvement is a new strengthened theorem, not quoted source text.

Proof: exp(x)<=1+x+3*x^2/4 for |x|<=1. Center after integration,
then use tilt 1/B and V<=B^2 L: -2L+3V/(4B^2)<=-5L/4.
Bias plus centered threshold is still <=4na. Reflect for the other signed tail.
Planned next consumer: L=2log(t+1), finite prefix union and summability.
The reviewer accepted that mathematical proposal separately; these consumers
are not yet implemented by this packet.

Publication: extend confidence reader with explicit strengthening and remaining
algorithm boundary, add folded exact statements, update local route ledger.
Semantic review: distinct blind decoder and source reviewer, plus separate proof
review. Lean graph gets actual declarations/dependencies; overview records a
confidence advance only; no conceptual functor is established.

## Focused implementation and semantic result

Both sharpened log-confidence tails and the raw-second-moment MGF compile.
The public-root canary consumes the stronger tail on 1000 genuinely random
observations (two-point law, mean1 and raw second moment2). Axiom output lists
only propext, Classical.choice and Quot.sound. All previous confidence API
statements remain unchanged as explicit weakenings. Decoder D reconstructed
both statements; independent source reviewer A accepted with explicit delta;
separate repair reviewer A accepted the implemented proof at frozen hashes.
Full gate and site receipts will be recorded separately. None of these reviews
accepts the original adaptive policy or printed regret coefficient.

## Adaptive-prefix and finite budget target (after 84c0c3f)

Target: original zero-based evaluation schedule L_t=2log(t+1), upper/lower
signed radius-four confidence at arbitrary selected positive prefix <=t, and
finite time budget <=2 for each sign. At t=0 the event is empty.
Own HeavyTailSourceSchedule; reuse actual sharp raw-moment confidence and
existing finite union method (scheduled_adaptive_mean_tail), not its larger
radius or different log schedule. Reuse Mathlib finite measure union, rpow/exp
identities and the independently checked inverse-square-root telescoping route.
Count may depend on all data; outer-measure bound needs no count independence.
No source-policy or regret acceptance until actual history consumer is joined.
Reader/semantic packet and common gates are required at stabilization.

## Current implemented extension

HeavyTailSourceSchedule now compiles signed adaptive-prefix confidence and the
finite time budget2, including empty t0. Algorithms/HeavyTailSourcePolicy
constructs the original radius4/r^-2 parameter policy from finite observed
histories, initializes round-robin and maximizes the actual source index.
Its observed truncated mean is proved equal to the arm-stream latent prefix;
stationary raw moments feed both signed per-arm finite-budget endpoints.
Public-root canary uses two genuinely noisy arms and horizon1000. Full gate and
semantic packetE are in progress; exact printed regret coefficient remains open.
