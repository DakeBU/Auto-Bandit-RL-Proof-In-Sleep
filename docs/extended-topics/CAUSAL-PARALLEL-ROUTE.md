# Parallel allocation bridge: exact next proof route

Source: official NIPS 2016 supplement p.15, Proposition 8; the arXiv v1
counterpart is Proposition 9. The supplement and frozen causal contract use
strict rare-action inequality. The main-paper informal allocation sentence uses
a different non-strict inequality and is not silently substituted here.

Let N >= 2 and independent binary roots have success probabilities q_i in [0,1].
For each integer tau in [2,N], let I_tau contain indices with
min(q_i,1-q_i) < 1/tau. Define m as the least such tau with |I_tau| <= tau.
Existence follows at tau=N. Thus 2 <= m <= N and |I_m| <= m. This minimum must
be constructed from q; its cardinality property is not an external premise.

The actions are the empty intervention and every atomic do(X_i=b). Let p_0 be
the actual root product law and p_(i,b) its law with root i replaced by b. Put
r_(i,b)=Pr(X_i=b), and S={(i,b): r_(i,b)<1/m}. Since 1/m <= 1/2, the two values
of one coordinate cannot both lie in S. The coordinate projection is injective
on S and its image is I_m, so |S|=|I_m|<=m.

Give each a in S weight 1/(2m), every other atomic action zero weight, and the
empty action weight 1-D where D=|S|/(2m). Then 0<=D<=1/2; these weights are
nonnegative and sum to one. This explicitly repairs the printed empty weight
1/2+(1-D), which instead makes the sum 3/2. The later displayed denominator
1/2+D is not reused. The repaired empty weight is at least 1/2.

Write Q for this actual action-mixture law. Prove pointwise P_a(z)<=2m Q(z):

1. For a rare atomic action, Q(z)>=P_a(z)/(2m).
2. For the empty action, Q(z)>=(1-D)P_0(z)>=P_0(z)/2. Since m>=1, this implies
   the required inequality for P_0.
3. For a nonrare atomic action, r_a>=1/m>0. Product factorization proves
   r_a P_a(z)<=P_0(z) on every z: equality holds when z_i=b, and P_a(z)=0
   otherwise. Hence P_a(z)<=m P_0(z)<=2m Q(z).

Pointwise domination implies coverage, including when some q_i are 0 or 1.
If Q(z)=0, domination forces P_a(z)=0 for every a. On positive Q,
P_a(z)/Q(z)<=2m; off its support the ratio is zero. Summing
P_a(z)*(P_a(z)/Q(z)) yields cost<=2m for every action, hence designCost<=2m.
Use the existing attained optimizer to infer optimal cost<=2m. This is a
design-cost comparison, not actual-regret dominance of optimal allocation.

The parent law must be identified with the constructed parallel DAG: N
independent root tables, arbitrary binary reward kernel on those roots, and
all roots as reward parents. The action family must replace the actual root
table and never the reward table. Transfer coverage and cost through the
parent-configuration equivalence, then instantiate the existing actual-law
regret theorem. Deterministic roots remain admissible; rare interventions can
create configurations absent under observation, so observational support alone
must not be used for coverage.

Required deliverables still open: constructed m, rare count, normalized repaired
allocation, product-law domination and parent-law adapter, optimal comparison,
actual-regret instance, nondegenerate/deterministic-coordinate witnesses, Lean
compilation, independent blind/source review and joint publication gates. This
document is a mathematical route, not a compiled result or topic acceptance.
