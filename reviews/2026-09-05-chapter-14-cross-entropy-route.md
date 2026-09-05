# Chapter 14 cross entropy and zero-mass limit

Source: author pp.187-188, zero-mass entropy explanation and first equality
of Eq.14.4 after dropping code-length rounding. Define finite cross entropy
sum p log(1/q), prove the termwise difference equals p log(p/q) when q is
nonzero on p's support, and compose with relativeEntropy_finite_sum_log for
actual probability measures. Singular support stays outside the real-sum
formula and is handled by the existing infinite-KL branch. This is not an
exact difference between rounded code lengths.

For the displayed zero-mass limit, use installed Real.continuous_mul_log
from Log.NegMulLog and log_inv to derive a local source adapter for
x log(1/x) -> 0 from the right. This imports an existing analytic API without
changing lake dependencies or assuming continuity of log at zero.

Focused result: CrossEntropy compiled (2672 jobs). The finite-measure wrapper
derives atom support from P absolutely continuous with respect to Q and keeps
this premise explicit. The zero-entropy right limit is obtained through the
continuous product x log x, not continuity of the logarithm. These are source
adapters, not new imported theorem claims. Root/aggregate integration pending.

Typed canary passed. All three axiom reports contain only propext,
Classical.choice and Quot.sound; retrieval/task memory/blueprint refreshed.
