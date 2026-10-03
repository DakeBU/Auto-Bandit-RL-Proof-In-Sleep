# Source confidence constant 4: completed proof route

## Current state, 2026-09-19

The complete arbitrary-delta upper and lower confidence declarations now compile
in the shared project at source commit `abf4d27`, under
`BanditRLProof/HeavyTailSourceConfidence.lean`. The shared improved MGF is in
`HeavyTailUnshiftedMGF.lean`. Independent source review accepts the coefficient4,
sample-index estimator and arbitrarydelta, with declared non-IID/common-mean and
closed-event generalizations. A distinct repair reviewer accepted the actual
proof bodies. A public-root stochastic canary instantiates the upper statement
at n=1000, delta=1/20, mean1 and raw second moment2. The final joint gate is
recorded in `runs/extended-topics-20260919/source-confidence-validation.json`.

The proposed route below is retained as mathematical derivation and development
history. Its earlier scratch-only status is superseded for these two confidence
endpoints. Original algorithm/regret constants remain separate unresolved work.

2026-09-19; proposed by formalizer; subsequently accepted mathematically by the separate
repair reviewer. Not yet an integrated source-confidence theorem.
This changes no current policy or frozen conservative endpoint.

For |Y|<=B and |lambda|B<=1, apply exp(z)<=1+z+z^2 to
lambda Y, before centering. Then

E exp(lambda(Y-EY))
 = exp(-lambda EY) E exp(lambda Y)
 <= exp(-lambda EY)(1+lambda EY+lambda^2 E Y^2)
 <= exp(lambda^2 E Y^2).

This uses a raw second moment, not variance, but permits |lambda|B<=1.
It does not assert |Y-EY|<=B. Thus it avoids the incorrect signed-range
shortcut while enlarging the prior shared producer's admissible tilt.

For arbitrary L=log(1/delta)>0, n>=1, p=1+epsilon in (1,2],
B_s=(u(s+1)/L)^(1/p), B=(un/L)^(1/p), a=u^(1/p)(L/n)^((p-1)/p):
- total bias <=p*n*a;
- V=sum u B_s^(2-p)<=n*u*B^(2-p);
- B*L=n*a and V<=B^2*L;
- choose lambda=1/B (and negative lambda for reflection).
Then centered-sum upper tail at 2B*L has exponent
-lambda*(2B*L)+lambda^2 V<=-2L+L=-L.
Hence each signed estimator tail at (p+2)*a has probability<=exp(-L).
As p+2<=4, radius4 with the original sample-index estimator follows.

The arbitrary-delta statement and source one-sided event convention still need
Lean assembly and independent source/repair review. A compiled MGF helper alone
is not acceptance of source Lemma1. The algorithm's t^-2 versus proof t^-4
schedule and its separate regret threshold factor remain unresolved; restoring
a confidence constant does not establish the printed regret theorem/constants.

Reuse search: HeavyTailFixedTilt bounded_centering_mgf currently restricts
|lambda|2B<=1; HeavyTailClippedConfidence consumes it. Existing EXP3 exponential
remainder and HeavyTail independent_sum_mgf can be reused. Mathlib Moments
search found general MGF identities, not this exact bounded raw-moment interface.
A future shared producer would support both hard truncation and clipping;
no duplication of the current policy or library is needed.

## Current verification boundary

The private `UnshiftedMGF.lean` scratch compiled with Lake/Lean 4.29.1 against
source tree 8cb5fef. Its sole theorem `bounded_centering_mgf_unshifted` has only
propext, Classical.choice and Quot.sound dependencies. This focused compile is
not a public-root integration or proof of the complete constant-4 theorem.
The separate reviewer checked the complete mathematical constant-4 derivation,
including each signed tail and raw-moment assumptions, without running Lean.
The next mathematical work is arbitrary-L threshold algebra and signed-tail
assembly, then independent source-blind review of the actual final declaration.

Private source/review location:
`E:/ABRL/maintenance/extended-topics-20260919-claude/review-20260919`.

UnshiftedMGF.lean SHA256: `88ef9652a5acc3bb09d5edd05f02e0f4dd4cfa720be44441f51163e9c318006e`.

CONSTANT-FOUR-PROPOSAL.md SHA256: `6c231cd6d121b9387b3b2f5e0fa8f1fa8156070db3cbf49deed7b2a097941c60`.

constant-four-proposal-review.md SHA256: `359de47d3d553c12a25bb846e975bc8b07f88eb0c515589b15290274c6e1c159`.
