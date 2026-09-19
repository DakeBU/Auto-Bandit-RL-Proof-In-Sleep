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

## Independently checked finite obstruction

The coefficient investigation has now produced an admissible deterministic
0/-1 reward counterexample at T=2^50, independently rechecked against the
source by a separate reviewer. See PRINTED-REGRET-COUNTEREXAMPLE.md. Thus the
literal printed coefficient is mathematically rejected for this exact policy;
its formal negation remains to be proved in Lean. The enlarged-coefficient
upper bound above remains a separate explicit repair, not an unchanged source
claim. Both the finite obstruction and the repaired performance chain remain
mandatory before topic acceptance.

## Implementation contract after026c3d4

Implement a new source-policy performance module using the existing shared
lintegral_pullCount_threshold and regret decomposition. Use closed signed bad
sets and strict gap comparison to retain cutoff ceil(A) and additive5Delta.
Horizon logarithm is2log(max(T,1)), exactly2log(T) for positive natural T and
zero at T=0. Treat T=0/1 directly with count<=T; do not use a positive cutoff
at those horizons. Negative/zero gaps are excluded from inversion by the
best-arm split. Old conservative policy/result remain separate.
The expected-regret endpoint receives raw moments, not confidence assumptions.
Independent blind/source/repair review and full project gates remain required.
