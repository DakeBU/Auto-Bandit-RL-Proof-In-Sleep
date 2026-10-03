# Source-tuned fixed-tilt concentration route

Mathematical derivation, not yet compiled. The frozen algorithm and target
radius remain unchanged. This route reuses `HeavyTail.bounded_centering_mgf`
and `HeavyTail.independent_sum_mgf` rather than importing a confidence event.

For the actual truncated binary statistic W, the existing producers give
0<=W<=B and E[W^2]<=m. The shared centering lemma therefore gives, whenever
|lambda| 2B<=1, E exp(lambda(W-EW))<=exp(lambda^2 m), at either sign of lambda.
It also supplies exponential integrability. Actual independent samples must
still be constructed and their distributions connected to these integrals.

Use T>=1, m>=1, L=log(2T|A|)>0 and the exact source B=sqrt(mT/L). Set
s=sqrt(mL/T) and lambda=1/(2B)>0. Then

    |lambda| 2B = 1,
    T lambda^2 m = L/4,
    lambda T s = L/2.

The source radius is epsilon=sqrt(2mL/T)+3BL/T=(sqrt(2)+3)s.
Exponential Markov on the centered sum gives, at either tail,

    P(tail) <= exp(-lambda T epsilon + T lambda^2 m)
             = exp(-((sqrt(2)+3)/2 - 1/4)L)
             <= exp(-L) = 1/(2T|A|).

A union over both signs and all actions yields failure probability <=1/T.
This argument uses the prescribed relation between B,m,T,L; it does not
claim the same Bernstein radius for arbitrary unrelated B. It preserves the
frozen source-tuned error radius and hence the documented regret coefficient.

Outstanding formal obligations: finite product/intervention sampling law,
independence and marginal identity, finite-sum-to-integral conversion, actual
sample mean and recommendation, signed tail events and union bound, square-root
and logarithm tuning identities, then integration of recommendation regret.
