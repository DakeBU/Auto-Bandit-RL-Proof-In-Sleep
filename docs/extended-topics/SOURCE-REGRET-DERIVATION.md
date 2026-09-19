# Original-policy regret: remaining exact coefficient boundary

Pinned source is BCL2013 Figure1/Proposition1/Theorem1, not the conservative
radius8/time^-4 adaptation. Current source-policy confidence is a producer,
not yet a regret endpoint. The following is a derivation target, not compiled
acceptance or a replacement of the printed theorem obligation.

For horizon T>=2, positive gap Delta and epsilon in (0,1], write p=1+epsilon.
For t<T, L_t=2log(t+1)<=2log(T). On complements of the CLOSED best-arm lower
and comparison-arm upper bad events, index maximality implies strictly

    Delta < 2 r_(t,N_i(t)).

The strict inequality matters: exclusion follows already from 2r<=Delta.
Consequently the deterministic cutoff

    A = 2*(8*u^(1/p)/Delta)^(p/epsilon)*log(T), ell=ceil(A)

excludes selecting that arm with count>=ell on the two good events.
The finite signed budgets proved for the actual source policy cost at most4
for this fixed arm and a fixed best arm, not for all arms simultaneously.
The intended counting step gives E N_i(T)<=ell+4<=A+5. Initialization must be
included in the count<ell branch (ell>=1); horizons0/1 need separate cases.
Zero gaps are split before reciprocal-gap operations.

Multiplying by Delta yields leading coefficient

    2*8^(p/epsilon)*(u/Delta)^(1/epsilon)*log(T)

plus 5Delta, compared with printed source

    8*(4u/Delta)^(1/epsilon)*log(T) + 5Delta.

Their ratio is 2^(p/epsilon); at epsilon1 the coefficients are128 versus32.
The new sharper confidence fixes time summability for the unchanged source
schedule but does not remove this deterministic twice-radius difference.
Retain the printed coefficient obligation. An independent investigation seeks
an alternative expected-count/hitting-time proof rather than inferring final
falsity from the displayed proof gap. Any enlarged-coefficient endpoint must be
labelled as a repair and cannot silently supersede the printed target.
