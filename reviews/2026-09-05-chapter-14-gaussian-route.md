# Chapter 14 positive-variance Gaussian route

Source: TXT-LATTIMORE-SZEPESVARI-2020, body Gaussian example and testing
application, author pp. 189--190, checked in the local official PDF extraction.
Target: KL(N(m,v),N(n,v))=(m-n)^2/(2v), v>0; for signal/noise Delta^2/v<=1,
testing error sum >=3/10 and maximum >=3/20.

Reuse the compiled unit-variance route in LowerBounds/Minimax.lean:
Gaussian PDF ratio cancellation, RN common-volume density identity, affine
LLR integrability, and integral_id_gaussianReal. Generalize the coefficient
to (m-n)/v and constant to (n^2-m^2)/(2v). No variance-zero or unequal-variance
claim is intended. APIs: gaussianReal_absolutelyContinuous and its reverse,
rnDeriv_gaussianReal, memLp_id_gaussianReal, klDiv_of_ac_of_integrable.
Cards: MLIB-MEASURE-INTEGRAL and MLIB-REAL-LOG-SQRT. Mathlib-candidate analytic
leaves; project-local testing application. Use exp_one_lt_d9 to certify the
rational testing constant without decimal approximation. This new work is
not covered by the ongoing b8325c2 affinity integration check.

## Focused build result

All eight declarations focused-build (3,461 jobs). The general variance
formula follows the existing analytic route without changing the unit-variance
Chapter 15 module. Positive variance is represented by nonzero NNReal v;
there are no bounds on the means or variance. The signal-to-noise premise is
only used for the displayed rational consequences, not the exponential bound.
The constant proof uses exp(1)<25/9 to obtain exp(-1/2)>=3/5 exactly.
Root/aggregate integration and full harness verification remain pending.

The focused canary passed for arbitrary variance and for the non-unit case
Delta=2, v=4 at the exact SNR boundary. All eight axiom audits report only
`propext`, `Classical.choice`, and `Quot.sound`. Its first attempt lacked
the NNReal notation scope; opening that scope fixed elaboration without
changing any mathematical statement.
