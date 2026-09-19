# Mathematical derivation and proof obligations

Write p=1+epsilon in (1,2], q=(p-1)/p. For a raw-moment bound
E|X|^p<=u and B>0, hard truncation Z=X 1{|X|<=B} gives

1. |X-Z| <= |X|^p/B^(p-1).
2. Z^2 <= |X|^p B^(2-p).
3. |EZ-EX| <= u/B^(p-1), EZ^2 <= u B^(2-p).
4. |Z-EZ|<=2B and E(Z-EZ)^2<=EZ^2.
5. For |lambda|2B<=1, E exp(lambda(Z-EZ)) <=
   exp(lambda^2 u B^(2-p)). Use exp(x)<=1+x+x^2 on [-1,1].

Items 1--5 are implemented in HeavyTailTruncation and HeavyTailFixedTilt.
Independence is preserved by the coordinate transforms. The product of MGFs
gives for fixed n and deterministic B_s:

P(sum_{s<n}(Z_s-EZ_s)>=r) <=
exp(-lambda*r + lambda^2 sum_{s<n}u B_s^(2-p)), lambda>=0,
provided lambda*2B_s<=1 for every s<n. This exact fixed-prefix one-sided
inequality is `truncated_sum_tail`. Integrability of all exponentials is derived
from boundedness of the transformed variables, not assumed for raw X.

## Fixed-prefix confidence and causal policy (compiled)

`HeavyTailConfidence.truncated_mean_tail` now derives the two-sided mean tail
directly from the raw moments, independence and common mean. Its radius is
the explicit bias sum plus `2sqrt(VL)+bL`, divided by the positive sample count.
This is slightly sharper than the conservative paper bound used below; the
algorithm still uses radius 8a. `HeavyTailPowerSum.sum_shifted_rpow_le` proves
the fractional-power bias summation by Bernoulli's inequality and telescoping.

`Algorithms.ArmStreamPolicy` constructs a measurable causal history process
using existing reward streams, pull counts and history extension. Its UCB
specialization equals the existing UCB histories. `HeavyTailHistory` computes
sample-index truncation solely from the observed history and proves exact
equality to the consumed latent prefix. `HeavyTailUCB` implements the explicit
conservative schedule, round-robin initialization and maximal observed index.
`HeavyTailTuning` now closes the radius tuning, `HeavyTailScheduledConfidence`
the finite-count union, and `HeavyTailArmLaw` the actual stationary reward-law
transport. `HeavyTailAdaptive` connects observed indices, initialization and
large-count selection. `HeavyTailExpectedCount` closes the expected count bound.
`HeavyTailRegret.robust_expected_regret` closes the conservative finite-horizon
expected pseudo-regret endpoint. Mean integrability is derived from the raw
moment, and no confidence or MGF premise is supplied to this endpoint.
The full conservative chain now has independent semantic and separate repair
acceptance with explicit deltas (2026-09-19; regret-review-validation.json).
Literal-source adjudication and topic acceptance evidence remain separate.

## Conservative derivation (algorithm-to-regret chain compiled)

Take B_s=(u(s+1)/L)^(1/p), L=log(1/delta)>0, and independent samples with
common mean mu. Integral comparison bounds sum_{s=1}^n s^-q <= p*n^(1/p).
Thus average bias is at most p*a<=2a, where a=u^(1/p)(L/n)^q.
The MGF variance budget V=sum u B_s^(2-p) is at most n*u*B_{n-1}^(2-p),
and b=2B_{n-1}. Choose lambda=min(sqrt(L/V),1/b) (positive V).
The two cases give

P(sum centered >= 2sqrt(VL)+2bL)<=exp(-L).

Reflection gives the lower tail. After division by n, the fluctuation is at
most 2a+4a=6a and the total one-sided error radius is **8a**. This conservative
constant avoids the signed-centering and printed-source-constant discrepancies.
It is an explicit adaptation, not a claim that the source's constant 4 is false.

Use delta_t=t^-4 for t>=2, deterministic round-robin initialization of K arms,
then maximize the actual truncated-prefix mean plus this radius. T is a fixed
finite horizon, and each nonoptimal arm i has gap Delta_i>0. Set

L_i = ceil(4 * 16^(p/(p-1)) * u^(1/(p-1)) * log(max(T,2))
             / Delta_i^(p/(p-1))) + 1.

If its previous count is at least L_i, its twice-radius is strictly smaller
than Delta_i. Selection then requires failure of the optimal arm's lower
confidence or arm i's upper confidence. Peeling over possible counts gives
failure probability <=4t*max(t,2)^-4: each arm uses a two-sided bound with
factor 2. This corrects the earlier draft's factor 2 union, which would require
separate one-sided producers. No random prefix is asserted to have the law of
an independent fixed-size sample. For t>=2, 4/t^3 <= 1/(t-1)-1/t, while t=0
contributes zero and t=1 contributes 1/4. The entire finite tail sum is at most
2, as proved in `HeavyTailTailSum`. The count budget remains E N_i(T)<=L_i+2, so

E R_T <= sum_{i:Delta_i>0} Delta_i (L_i+2).

The compiled `gapThreshold` uses the algebraically equivalent quotient form
ceil(L_T / (Delta/(16*u^(1/p)))^(p/(p-1)))+1. This conservative route is now
compiled and independently accepted as an explicit adaptation; whole-topic
acceptance remains open. The source-faithful
original-constant endpoint remains in repair; the adaptation has its own
contract and must not overwrite that history.

## Transfer derivation and boundary

clip_B(x)=max(-B,min(B,x)) is 1-Lipschitz. Therefore
|mean clip(X_s+c_s)-mean clip(X_s)|<=sum|c_s|/n<=C/n.
The compiled prefix identity transfers this inequality to actual observations
on the same adaptively selected action trace. It is valid pathwise and needs no
IID assumption. A clean estimator's bias/fluctuation bound can then be combined
with this perturbation. The current transfer also supplies clipped moment-bias
and second-moment producers (`HeavyTailClippedMoments`), clean fixed-prefix and
selected-count confidence (`HeavyTailClippedConfidence` and
`HeavyTailClippedScheduled`), and corrupted observed-prefix confidence
(`HeavyTailClippedTransfer`). These compiled statements do not establish a
corruption-robust policy or its full regret theorem. Independent semantic
acceptance remains open. Hard truncation fails the same stability property:
at B=1, x=1, y=3/2 the transformed difference is 1>1/2.

## Lifecycle

| Target | State | Evidence / remaining obligation |
|---|---|---|
| Literal published robust-UCB constants | repair | printed union and threshold mismatch, visually checked |
| Raw-moment truncation producers | proving -> compiled leaf candidate | pointwise, integral, centered MGF, independent one-sided tail |
| Actual transformed prefix | compiled leaf candidate | direct use of frozen UCB stream-prefix proof |
| Fixed-prefix two-sided mean confidence | compiled candidate | raw moments, explicit sums and power tuning closed |
| Causal robust-UCB adaptation | compiled endpoint candidate | actual history, random count, finite tail sum and expected regret closed; conservative semantic review accepted, topic acceptance pending |
| Reserved clipping transfer | compiled confidence candidate | clean clipped confidence and corrupted actual-prefix transport closed; independent review and corruption-robust regret remain open |
| Controlled efficiency evaluation | frozen, not executed | independent isolated model runner and enforceable budget unavailable |

Compiler repairs retained in logs: an a.e.-measurability API mismatch was fixed
by making source measurability explicit; a Real/ENNReal measure mismatch was
fixed by preserving the reused tail interface's `Measure.real` codomain.
An intermediate canary build raced with a changing dependency; final gates
must be serial and based on the final source tree. No endpoint was shrunk to
make a compiled leaf count as an algorithm theorem.
