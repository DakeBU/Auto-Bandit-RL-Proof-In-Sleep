# FTL limit canary CONTRACT review v1

Verdict: accepted. This permits proof work for these exact twelve canary headers under the frozen context, not acceptance of any canary body or the five public bodies.

Reused distinct automated reviewer /root/source_reviewer; prior staged history disclosed. Requested Astra/medium is not runtime-attested. No external/human/absolute-blind review claim.

All24 current RAW bindings matched before/after. Exact headers and parity definition agree with the neutral reconstruction. The actual draft #check file imports existing square-minimum/no-regret modules and checks twelve Props; exit0 is type evidence only, not proof-body or full prospective-import compilation. The unchanged earlier public contract remains separately bound.

Independent arithmetic: at T1 the actual loss is(1/2-0)^2=1/4 and the minimum fixed loss is0. At T2 actual loss is1/4+1=5/4, while the constant midpoint minimum is1/2, yielding3/4. T0 loss image is{0}. The first four predictions are1/2,0,1/2,1/3: the last uses0,1,0, not the current1. Prefix ones are floor(T/2), not real T/2 on odd horizons. Dividing these actual counts by T yields the required half limit via an error bounded by1/(2T), rather than assuming convergence.

Given the future proved public hinges and this produced half limit, fixed comparator0 has limit-(0-1/2)^2=-1/4, while midpoint has0. This tests signed fixed-comparator regret versus positive finite best-regret and zero best-regret average without conflating them. The interval infimum is over constant real comparators for each realized prefix; no expectation, finite candidate approximation or min/expectation swap. No stochastic nondegeneracy or bounded nonconvergence counterexample is claimed.

C1 Tests.OnlineFTLLimitSemantics.alternating_unit

- objects: Fixed parity observation and actual shared strict-past meanPredict; shared finite square loss definitions
- quantifiers: forall t plus initial conjunction
- assumptions: No supplied regret bound, convergence, or minimizer oracle; concrete definitions only
- metric: all-time unit membership plus y0=0,y1=1
- normalization: Natural t<T sums; Nat floor division in prefix-count target; real T denominator in normalized limits; empty horizon totalized
- information_probability: Deterministic binary stream; initial half and observations strictly before play, no probability or expectation
- boundary: Validation-only specialization, not a source theorem or general theorem proof; ordinary limits not limsup; comparator-dependent negative limits permitted

C2 Tests.OnlineFTLLimitSemantics.alternating_prefix_sum

- objects: Fixed parity observation and actual shared strict-past meanPredict; shared finite square loss definitions
- quantifiers: forall natural T
- assumptions: No supplied regret bound, convergence, or minimizer oracle; concrete definitions only
- metric: prefix sum=real(Nat.div T 2)
- normalization: Natural t<T sums; Nat floor division in prefix-count target; real T denominator in normalized limits; empty horizon totalized
- information_probability: Deterministic binary stream; initial half and observations strictly before play, no probability or expectation
- boundary: Validation-only specialization, not a source theorem or general theorem proof; ordinary limits not limsup; comparator-dependent negative limits permitted

C3 Tests.OnlineFTLLimitSemantics.alternating_mean_tendsto

- objects: Fixed parity observation and actual shared strict-past meanPredict; shared finite square loss definitions
- quantifiers: closed atTop limit
- assumptions: No supplied regret bound, convergence, or minimizer oracle; concrete definitions only
- metric: empiricalMean tends1/2
- normalization: Natural t<T sums; Nat floor division in prefix-count target; real T denominator in normalized limits; empty horizon totalized
- information_probability: Deterministic binary stream; initial half and observations strictly before play, no probability or expectation
- boundary: Validation-only specialization, not a source theorem or general theorem proof; ordinary limits not limsup; comparator-dependent negative limits permitted

C4 Tests.OnlineFTLLimitSemantics.alternating_initial_predictions

- objects: Fixed parity observation and actual shared strict-past meanPredict; shared finite square loss definitions
- quantifiers: closed four-value conjunction
- assumptions: No supplied regret bound, convergence, or minimizer oracle; concrete definitions only
- metric: p0=1/2,p1=0,p2=1/2,p3=1/3
- normalization: Natural t<T sums; Nat floor division in prefix-count target; real T denominator in normalized limits; empty horizon totalized
- information_probability: Deterministic binary stream; initial half and observations strictly before play, no probability or expectation
- boundary: Validation-only specialization, not a source theorem or general theorem proof; ordinary limits not limsup; comparator-dependent negative limits permitted

C5 Tests.OnlineFTLLimitSemantics.alternating_best_regret_zero_one_two

- objects: Fixed parity observation and actual shared strict-past meanPredict; shared finite square loss definitions
- quantifiers: closed three-horizon conjunction
- assumptions: No supplied regret bound, convergence, or minimizer oracle; concrete definitions only
- metric: bestR0=0,bestR1=1/4,bestR2=3/4
- normalization: Natural t<T sums; Nat floor division in prefix-count target; real T denominator in normalized limits; empty horizon totalized
- information_probability: Deterministic binary stream; initial half and observations strictly before play, no probability or expectation
- boundary: Validation-only specialization, not a source theorem or general theorem proof; ordinary limits not limsup; comparator-dependent negative limits permitted

C6 Tests.OnlineFTLLimitSemantics.alternating_actual_gap_nonneg

- objects: Fixed parity observation and actual shared strict-past meanPredict; shared finite square loss definitions
- quantifiers: forall natural T
- assumptions: No supplied regret bound, convergence, or minimizer oracle; concrete definitions only
- metric: regret against horizon mean nonnegative
- normalization: Natural t<T sums; Nat floor division in prefix-count target; real T denominator in normalized limits; empty horizon totalized
- information_probability: Deterministic binary stream; initial half and observations strictly before play, no probability or expectation
- boundary: Validation-only specialization, not a source theorem or general theorem proof; ordinary limits not limsup; comparator-dependent negative limits permitted

C7 Tests.OnlineFTLLimitSemantics.alternating_fixed_decomposition

- objects: Fixed parity observation and actual shared strict-past meanPredict; shared finite square loss definitions
- quantifiers: forall real u,natural T
- assumptions: No supplied regret bound, convergence, or minimizer oracle; concrete definitions only
- metric: fixed regret=mean comparator regret-T*(u-mean)^2
- normalization: Natural t<T sums; Nat floor division in prefix-count target; real T denominator in normalized limits; empty horizon totalized
- information_probability: Deterministic binary stream; initial half and observations strictly before play, no probability or expectation
- boundary: Validation-only specialization, not a source theorem or general theorem proof; ordinary limits not limsup; comparator-dependent negative limits permitted

C8 Tests.OnlineFTLLimitSemantics.alternating_best_average_zero

- objects: Fixed parity observation and actual shared strict-past meanPredict; shared finite square loss definitions
- quantifiers: closed atTop limit
- assumptions: No supplied regret bound, convergence, or minimizer oracle; concrete definitions only
- metric: bestR/T tends0
- normalization: Natural t<T sums; Nat floor division in prefix-count target; real T denominator in normalized limits; empty horizon totalized
- information_probability: Deterministic binary stream; initial half and observations strictly before play, no probability or expectation
- boundary: Validation-only specialization, not a source theorem or general theorem proof; ordinary limits not limsup; comparator-dependent negative limits permitted

C9 Tests.OnlineFTLLimitSemantics.alternating_fixed_limit_criterion

- objects: Fixed parity observation and actual shared strict-past meanPredict; shared finite square loss definitions
- quantifiers: forall real u,a
- assumptions: No supplied regret bound, convergence, or minimizer oracle; concrete definitions only
- metric: fixedR(u)/T tends a iff (u-mean)^2 tends -a
- normalization: Natural t<T sums; Nat floor division in prefix-count target; real T denominator in normalized limits; empty horizon totalized
- information_probability: Deterministic binary stream; initial half and observations strictly before play, no probability or expectation
- boundary: Validation-only specialization, not a source theorem or general theorem proof; ordinary limits not limsup; comparator-dependent negative limits permitted

C10 Tests.OnlineFTLLimitSemantics.alternating_fixed_zero_negative_limit

- objects: Fixed parity observation and actual shared strict-past meanPredict; shared finite square loss definitions
- quantifiers: closed atTop limit
- assumptions: No supplied regret bound, convergence, or minimizer oracle; concrete definitions only
- metric: fixedR(0)/T tends -1/4
- normalization: Natural t<T sums; Nat floor division in prefix-count target; real T denominator in normalized limits; empty horizon totalized
- information_probability: Deterministic binary stream; initial half and observations strictly before play, no probability or expectation
- boundary: Validation-only specialization, not a source theorem or general theorem proof; ordinary limits not limsup; comparator-dependent negative limits permitted

C11 Tests.OnlineFTLLimitSemantics.alternating_fixed_half_zero_limit

- objects: Fixed parity observation and actual shared strict-past meanPredict; shared finite square loss definitions
- quantifiers: closed atTop limit
- assumptions: No supplied regret bound, convergence, or minimizer oracle; concrete definitions only
- metric: fixedR(1/2)/T tends0
- normalization: Natural t<T sums; Nat floor division in prefix-count target; real T denominator in normalized limits; empty horizon totalized
- information_probability: Deterministic binary stream; initial half and observations strictly before play, no probability or expectation
- boundary: Validation-only specialization, not a source theorem or general theorem proof; ordinary limits not limsup; comparator-dependent negative limits permitted

C12 Tests.OnlineFTLLimitSemantics.alternating_literal_limit_noRegret

- objects: Fixed parity observation and actual shared strict-past meanPredict; shared finite square loss definitions
- quantifiers: forall u in[0,1],exists a<=0
- assumptions: No supplied regret bound, convergence, or minimizer oracle; concrete definitions only
- metric: each feasible fixed u has some finite nonpositive ordinary limit
- normalization: Natural t<T sums; Nat floor division in prefix-count target; real T denominator in normalized limits; empty horizon totalized
- information_probability: Deterministic binary stream; initial half and observations strictly before play, no probability or expectation
- boundary: Validation-only specialization, not a source theorem or general theorem proof; ordinary limits not limsup; comparator-dependent negative limits permitted

Nondegeneracy is adequate for the bounded validation plan: two distinct observations, positive best gaps, nonconstant actual predictions, genuine count-to-mean producer, and differing fixed-comparator limits. Future proof values must actually instantiate F1 in C6, F2 in C7, F3 in C8, F4 in C9 and F5 in C10–C12; matching shapes alone are not dependency evidence. C3 must derive mean convergence, not consume it as a premise. Canary body/kernel/dependency/fence/combined/reader/site/FINAL gates remain separate. The existing unbounded affine example still does not settle a bounded actual-FTL nonconvergence example.

Only exact canary-body proof/private-helper work in Tests/OnlineFTLLimitSemanticsCanary.lean is permitted under the approved main scope, keeping all12 headers and alternatingObservation definition fixed. Target/context edits require a new review. No other inputs, roots, readers or lifecycle state were modified here. Required blocking repairs: none. Original reader R1–R7 remain future obligations; no source-package/chapter/Goal completion.
