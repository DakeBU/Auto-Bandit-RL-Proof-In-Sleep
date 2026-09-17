# CUCB Theorem 2: both source branches compiled

2026-09-18. The frozen full CUCB line now has compiled Theorem1 and both Theorem2 endpoints, using the disclosed normalized analysis-counter repair and unchanged source learner. Compilation is not independent source/repair acceptance, and the combinatorial topic remains incomplete.

`SourceModel.theorem_two_deterministic` proves for every integer H>=1, gamma>0, 0<omega<=1, the source modulus identity f(u)=gamma*u^omega for u>=0, and actual p_*=1:

    R(H) <= (2*gamma/(2-omega))*(6*m*log H)^(omega/2)*H^(1-omega/2)
      +(1+pi^2/3)*m*Delta_max.

`SourceModel.theorem_two_probabilistic` proves under the same model/modulus conditions and actual p_*<1 (positivity already derived from the model):

    R(H) <= (2*gamma/(2-omega))*(12*m*log H/p_*)^(omega/2)*H^(1-omega/2)
      +(1+pi^2/2)*m*Delta_max
      +sum_i (24*log H/p_i)*Delta_max.

R is the original signed approximation regret against expected actual cumulative rewards. These are the frozen Chen et al. JMLR2016 Theorem2 formulas, not a changed minimum-gap or deterministic-only contract. Mixed p_i=1/p_i<1 instances use the actual previously derived uniform p_* envelope and retain the per-arm additive term.

## Proof construction

`CUCBPolynomialIntegral` proves integrability on the actual positive-gap interval, integrates the derived source threshold expressions/envelopes, and bounds their power tails with the proved finite analytic integral. It yields both actual cutoff regret inequalities with exact coefficients and additive terms. Only scalar envelope statements are inputs to the local integration helper, and both source branches discharge them from the actual modulus/trigger model; no probability/count/performance bound is assumed.

`PowerCutoffNormalization` rewrites the balanced cutoff exactly into the source gamma/log/H powers. It proves the reciprocal exponent and q/(q-1) coefficient identities for q=2/omega and positive bases.

`CUCBPolynomialRegret` derives nonempty base-arm count from the model, proves R(H)<=H*Delta_max from the original signed gap identity, and uses this for H=1, where log H=0 and positive-K optimization would be invalid. For H>1 it constructs the positive balanced cutoff a=(K/H)^(1/q), with K=m*6logH*gamma^q or m*12logH/p_* *gamma^q. If a>=Delta_max, the previously proved actual large-cutoff inequality applies. Otherwise the actual gap-domain cutoff inequality and integrated threshold envelope apply; the balanced objective and exact source normalization close the endpoint. No H>m assumption or positive-Delta_max premise is added.

## Remaining acceptance

The fixed contract still requires concrete genuinely noisy canaries with multiple non-singleton feasible actions, different rewards, nontrivial triggering and a nontrivial approximation oracle; deterministic-trigger and no-bad boundaries; independent semantic review of source assumptions and all disclosed repairs; shared source/topic/declaration mappings; and all-ten ICLR evidence under the frozen protocol. Generic theorem dependency audits do not satisfy the concrete-canary or independent-review requirements. No controlled evaluation, merge, deployment or manuscript change is claimed here.
