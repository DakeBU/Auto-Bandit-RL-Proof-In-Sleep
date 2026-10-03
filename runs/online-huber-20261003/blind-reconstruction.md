# Blind mathematical reconstruction

Actor: /root/blind_decoder
Model: GPT-6 Astra
Reasoning effort: medium
Input boundary: Only blind-packet.txt was read. No source book, source identity, prior review, or other file was inspected.

The packet defines online gradient descent in an arbitrary complete real inner-product space E, with the following conventions.

For a nonempty closed convex set V, P_V is a selected nearest-point projection, and

x_0 = x_init,
x_{t+1} = P_V(x_t - eta gradient f_t(x_t)).

Although the generic definition names its initial argument x₁, its time index is 0. Its regret is the actual loss difference

R_T(u) = sum_{t=0}^{T-1} (f_t(x_t) - f_t(u)).

Thus x_T is the iterate after all T updates and is excluded from the T evaluated predictions. These definitions describe a causal recurrence: x_t uses only the initial point and losses indexed strictly below t; loss f_t is used to produce x_{t+1}.

The Huber loss is

h_delta(r) = r^2/2 if |r| <= delta, and delta (|r| - delta/2) otherwise.

The definition exists for every real delta, but all substantive Huber regularity and regret claims assume delta >= 0, except where specifically noted below. The quadratic normalization is r^2/2; neither branch is divided by delta.

The 19 target statements reconstruct as follows.

1. **hasDerivAt_ite_le.** For arbitrary real functions f,g and real numbers c,d, if both functions have derivative d at c and f(c)=g(c), then the joined function q(x)=f(x) for x<=c and q(x)=g(x) for x>c has derivative d at c. This only assumes differentiability of the pieces at the joining point.

2. **huber_three_pieces.** For every delta>=0 and every real r, h_delta(r) equals -delta r-delta^2/2 for r<=-delta, r^2/2 for -delta<r<=delta, and delta r-delta^2/2 for r>delta. The negative endpoint is assigned to the first branch, and the positive endpoint to the second branch whenever these endpoints are distinct. At delta=0, the first branch covers r<=0, and the middle branch has no inputs.

3. **huber_zero.** For every real r, h_0(r)=0. The zero threshold is explicitly included.

4. **hasDerivAt_join.** Suppose f and g are differentiable everywhere, with specified derivative functions df,dg, and f(c)=g(c), df(c)=dg(c). For every real x, the joined function from target 1 has derivative df(x) for x<=c and dg(x) for x>c. There is no explicit assumption that either derivative function is continuous.

5. **huber_hasDerivAt.** For every delta>=0, Huber loss is differentiable at every real r, with derivative -delta for r<=-delta, r for -delta<r<=delta, and delta for r>delta. This includes both joining points and delta=0.

6. **huber_deriv_clamp.** For all delta>=0 and real r, h_delta'(r)=max(-delta,min(r,delta)). Thus the derivative clips the residual to [-delta,delta].

7. **huber_convex.** For every delta>=0, h_delta is convex on the whole real line. There is no bounded residual-domain premise.

8. **huber_deriv_bound.** For every delta>=0 and real r, |h_delta'(r)|<=delta.

9. **huber_deriv_source.** For every delta>=0 and real r, h_delta'(r)=r if |r|<=delta and delta sign(r) otherwise. Equality at the threshold uses the quadratic-branch derivative. This agrees with the clipped derivative at both endpoints.

10. **huber_linear_hasGradientAt.** For arbitrary z,x in E, y in R, and delta>=0, define ell(w)=h_delta(<z,w>-y). Then ell has gradient at x equal to h_delta'(<z,x>-y) z. The prediction is <z,x>; residual means prediction minus y. There is no restriction on x,z,y, nor any finite-dimensionality assumption.

11. **huber_linear_convex.** For every delta>=0, z in E, and real y, the above function ell is convex on all of E.

12. **huber_linear_gradient_bound.** Under the same unrestricted x,z,y and delta>=0, ||gradient ell(x)||<=delta ||z||. The bound does not depend on the label or parameter magnitude.

13. **project_fullSpace.** Projection onto the domain whose carrier is all of E is the identity: P_E(x)=x.

14. **huber_regular.** For delta>=0, every linear-prediction Huber loss satisfies RegularLoss on the full-space domain. Unfolded, there exists an open set U containing E on which the loss is convex and differentiable. Since the domain is all of E, such a U necessarily equals E. No bounded feasible set is introduced.

15. **huber_step.** For every real step size eta, every x,z in E, real y, and delta>=0, the full-space OGD step equals x^+=x-eta a z, where a=<z,x>-y if |<z,x>-y|<=delta and a=delta sign(<z,x>-y) otherwise. Positivity of eta is unnecessary for this algebraic identity. Positivity is required by the subsequent regret theorem.

16. **huber_regret_fixed.** Let delta,Z>=0, eta>0, arbitrary sequences z_t in E,y_t in R, arbitrary x_0,u in E, and any natural horizon T, including 0. Assume only that for every t<T, ||z_t||<=Z. Run the recurrence with this same fixed eta throughout, with f_t(x)=h_delta(<z_t,x>-y_t). Then its actual regret satisfies

R_T(u) <= ||x_0-u||^2/(2 eta) + eta T delta^2 Z^2/2 - ||x_T-u||^2/(2 eta).

The initial-distance term and negative terminal-distance term both remain present. For T=0, regret is the empty sum and the two distance terms cancel. The comparator is any fixed vector u, not necessarily a loss minimizer. Labels are unrestricted. There are no probability, expectation, stochastic independence, or bounded-parameter-domain hypotheses.

17. **huber_average_bound.** Under delta,Z>=0, arbitrary data sequences and x_0,u, a positive natural horizon T, and the feature bound for all t<T, choose the constant step size eta_T=1/sqrt(T) for the entire run of length T. Then

R_T^{(eta_T)}(u)/T <= (||x_0-u||^2 + delta^2 Z^2)/(2 sqrt(T)).

This bound has dropped the nonpositive endpoint residual from target 16. It concerns average actual regret, upper bounded by the displayed expression. The step size depends on the horizon, not on the current time index. Runs at different horizons therefore generally use different iterates from their first update onward.

18. **huber_rate_tendsto.** For any real delta,Z, with no sign assumptions, and fixed x_0,u in E,

lim_{T -> infinity, T natural} (||x_0-u||^2 + (delta Z)^2)/(2 sqrt(T)) = 0.

This is a limit of the numerical upper-bound expression. It mentions neither losses nor the OGD recurrence and does not itself assert convergence of regret. The finite value at T=0, interpreted using Lean's totalized division, is irrelevant to this asymptotic statement.

19. **huber_average_eventually.** Assume delta,Z>=0, arbitrary fixed sequences z,y, fixed x_0,u, and the global feature bound that for every natural t, ||z_t||<=Z. For every epsilon>0, eventually in the natural horizon T,

R_T^{(1/sqrt(T))}(u)/T < epsilon.

Explicitly, after the parameters, sequences, initial point, comparator, and positive epsilon are fixed, there exists a natural N such that the inequality holds for every T>=N. The statement is pointwise in the fixed comparator u; it does not state one common N for every comparator.

The final target gives an eventual upper guarantee on average regret. It does not assert that average regret converges to zero: actual regret against a fixed comparator may be negative, and no lower bound is supplied. It also does not establish an anytime algorithm with eta_t=1/sqrt(t); the family under discussion uses a separate constant-step run with eta_T=1/sqrt(T) for each horizon.

For delta=0, every loss and gradient is zero, every iterate equals x_0, and actual regret is identically zero. For Z=0 under the feature-bound assumptions, all relevant features vanish, making each relevant loss independent of the prediction vector and actual regret zero. The stated theorems include these boundary cases without requiring a positive threshold, positive feature bound, bounded labels, or bounded decision domain.

These are reconstructions of the supplied definitions and theorem statements; the packet contains no proof bodies to assess.