# Finite-prefix martingale Bernstein producer for the heavy-tail audit

Date: 2026-09-20. Direct mathematical proof, not a Lean declaration. This discharges the scalar bounded-increment interface invoked as Li-Sun v2 Lemma F.1 and Huang Lemma I.1 in the reviewed clean-GLM and Tani repairs. It does not certify the original papers' variance-peeling or probability allocation.

Let (F_t) be an increasing filtration, and D_t, t=1,...,n, adapted real random variables satisfying E[D_t|F_(t-1)]=0, |D_t|<=b almost surely, with deterministic b>0. Put q_t=E[D_t^2|F_(t-1)]. Assume sum_t q_t<=v almost surely for deterministic finite v>=0. Then for x>0,

    P(sum_t D_t >= sqrt(2*v*x)+(b/3)*x) <= exp(-x)

when v>0. If v=0 all D_t=0 almost surely and any positive threshold has probability zero. The same bound holds for -sum D_t. A looser linear term 2*b*x/3 is therefore also valid. No cross-time independence is required; predictable q_t need not be deterministic.

## Conditional exponential producer

For |y|<=b and 0<=lambda<3/b, expand exp(lambda*y). For k>=2, |y|^k<=y^2*b^(k-2) and k!>=2*3^(k-2) (induction from k=2). Hence

    exp(lambda*y) <= 1+lambda*y + lambda^2*y^2/[2*(1-lambda*b/3)].

Conditional expectation and centering give E[exp(lambda*D_t)|F_(t-1)] <= exp(psi*q_t), where psi=lambda^2/[2*(1-lambda*b/3)]. Define L_t=exp(lambda*sum_(j<=t)D_j-psi*sum_(j<=t)q_j). Because q_t is past measurable, conditional integration yields E[L_t|F_(t-1)]<=L_(t-1). These variables are nonnegative and integrable: finite n and deterministic b bound each D and q, so the exponential is bounded for each t. Iteration gives E L_n<=1. This uses compensated predictable factors inside the process, not extraction of a random factor from an unconditional expectation.

Since sum q_t<=v, exp(lambda*sum D_t)<=exp(psi*v)*L_n almost surely. Thus E exp(lambda*sum D_t)<=exp(psi*v). Markov gives P(sum D_t>=a)<=exp(-lambda*a+psi*v) for lambda>0.

## Explicit optimization and degenerate case

For v>0 put r=sqrt(2*x/v), c=b/3 and lambda=r/(1+c*r). Then 0<lambda<1/c, psi*v=x/(1+c*r), and with a=v*r+c*x=sqrt(2*v*x)+c*x,

    -lambda*a+psi*v = [-2*x-c*r*x+x]/(1+c*r) = -x.

This proves the stated inequality including the non-strict tail event. For v=0, nonnegative q_t have sum zero almost surely. E D_t^2=E q_t=0, so D_t=0 almost surely; a finite intersection handles all t. For b=0 the same direct argument applies. Reflection preserves every premise.

## Interface and use restrictions

At each fixed prefix the reviewed Li-Sun/GLM and Tani notes provide a deterministic increment cap and a deterministic variance envelope after stopping at a past-measurable good event. Such stopped centered increments remain adapted martingale differences; the predictable second-moment bound is checked in those notes. Apply this producer separately at each prefix and then the explicitly budgeted finite union. A random cap, a variance bound that only holds on the event being proved, an anticipatory stopping indicator, or an unproved deterministic envelope would not satisfy this statement.

The bound is a fixed-prefix statement. It supplies neither all-infinite-time confidence nor a variance-peeling theorem by itself. In the accepted repairs the required looser sqrt(2*v*x)+2*b*x/3 threshold follows by event inclusion. Existing logarithm allocations, alpha=8 envelope, finite T and explicit model deltas remain unchanged. No new acceptance of original log2, corrupted GLM regret, complete Huang regression/RL, or H-BE regret follows.
