# Blind reconstruction of two closed canary headers

Only `definition-context-v1.txt` and `declarations-v1.txt` in this directory were read for this reconstruction. No proof body, imported module, source, proposal, or actor review was consulted. No Lean execution was performed. These are statement reconstructions, not proof validation or evidence that any provider theorem was used.

Input SHA256:

- definition-context-v1.txt: e7839e697d387b227bf1db23444691429524b47786b5b65187092bd8162af80c
- declarations-v1.txt: 348433c1c11af2dbaadcdf74968833caded32dce0463b6c0d699eed3dc3563ee

## Shared semantics

Both theorem headers have no explicit input binders or hypothesis arrows before their conclusions. Each asserts one closed proposition consisting of 14 right-associated conjuncts. Quantifiers inside individual conjuncts do not become external theorem assumptions. In particular, the second header asserts its convexity, finiteness, and curvature facts as conclusions of the closed example.

The underlying space is ℝ with its usual norm |x| and real scalar action. `EReal` is the extended-real codomain of losses and objectives. Real values are explicitly embedded in EReal. Sums are finite EReal sums: `range 0` is empty and has sum zero; `range 1` contains precisely index 0. Every loss definition ignores its natural-number index, although the quantified prefix claims in the second theorem cover only i < 0+1, namely i=0.

The extended indicator is zero on the feasible set and top outside. `effectiveDomain f` means {x | f x < top}; it does not itself exclude bottom. `IsMinOn f V p` means for every z in V, f(p) ≤ f(z), without membership of p in V built into that predicate. The separate membership conjuncts supply that here.

`toReal` sends finite embedded reals to their real values and both infinities to zero. Therefore a general objective's `toReal` is not an order-preserving finite-objective substitute outside its finite domain. All points used in the two objective-gap inequalities are explicitly feasible and have finite objective-value conjuncts. Inequalities containing `.toReal`, support values, norms, and divisions in the gap/support statements are real inequalities. The curvature inequality and minimization inequalities are EReal inequalities.

The norm of each `support : ℝ →L[ℝ] ℝ` is its operator norm. The norm `‖x-y‖` in the curvature clause is the ambient norm of a real number. The fact that operator norms here equal scalar absolute values does not make the two types of norms interchangeable in a general space.

## Tight definitions

Write V_T=[-2,2], psi_T(x)=x²/2, hint_T(x)=0, and loss_T(i,x)=the EReal embedding of 2x, for every natural i and real x. Define P_T as predictionObjective and G_T as currentObjective:

- P_T(x) is the EReal embedding of x²/2, since its prefix is empty.
- G_T(x)=(x²/2 : EReal)+(2x : EReal)+indicator(V_T,x). Thus it embeds x²/2+2x on V_T and equals top outside V_T.
- support_T(x)=2x as a continuous real linear map; its operator norm is 2.

## Tight theorem: exactly 14 conjuncts in order

The name is `Tight.tight_dual_stability_at_nonminimizer` within the supplied enclosing context `BanditRL.Tests.OnlineCumulativeOptimisticStabilityDualCanary`.

1. toReal(G_T(0)) - toReal(G_T(-2)) ≤ ‖support_T‖²/(2·1).
2. IsMinOn P_T V_T 0: for every z∈[-2,2], P_T(0)≤P_T(z).
3. NOT IsMinOn G_T V_T 0: 0 does not minimize the current objective on [-2,2].
4. For every z∈V_T, toReal(loss_T(0,0)) - hint_T(0) + support_T(z-0) ≤ toReal(loss_T(0,z)) - hint_T(z). Substitution reduces this to 2z≤2z.
5. support_T ≠ 0, where 0 denotes the zero continuous linear map.
6. ‖support_T‖=2.
7. 0∈V_T.
8. -2∈V_T.
9. 3∉V_T.
10. G_T(0)=(0 : EReal).
11. G_T(-2)=((-2 : ℝ) : EReal).
12. G_T(3)=top.
13. toReal(G_T(0))-toReal(G_T(-2))=2.
14. ‖support_T‖²/(2·1)=2.

Consequently the first conjunct is the equality case 2≤2 with a strictly positive numerical denominator 2. The statement simultaneously records minimization of the prediction objective and failure of minimization of the current objective at 0. The feasible comparator -2 has strictly lower current objective value. The header does not separately assert that -2 minimizes G_T, although that is consistent with the displayed quadratic definition. It does not contain a conjunct asserting strong convexity, nor a reference establishing use of any general stability provider. The out-of-set value at 3 is genuinely top in EReal; applying toReal to it would give zero, but that point is not used for the gap comparison.

## ZeroCurvature definitions

Write V_Z=[-1,1], psi_Z(x)=0, hint_Z(x)=0, and loss_Z(i,x)=(x : EReal), for every natural i and real x. Define P_Z and G_Z correspondingly:

- P_Z(x)=(0 : EReal) for all real x, since its prefix is empty.
- G_Z(x)=(x : EReal)+indicator(V_Z,x): it embeds x on V_Z and equals top outside V_Z.
- support_Z(x)=x as the identity continuous linear map; its operator norm is 1.

## ZeroCurvature theorem: exactly 14 conjuncts in order

The name is `ZeroCurvature.zero_curvature_division_is_false` within the same supplied enclosing context.

1. V_Z is convex over ℝ.
2. For every natural i<0+1 and every real x, loss_Z(i,x)≠bottom. The x-quantifier is global, not restricted to V_Z.
3. For every natural i<0+1, V_Z⊆effectiveDomain(loss_Z i), meaning for every x∈V_Z, loss_Z(i,x)<top.
4. For every x∈V_Z, y∈V_Z and a∈ℝ with 0<a and a<1,

   G_Z(a • x+(1-a) • y) ≤ (a : EReal)*G_Z(x) + ((1-a : ℝ) : EReal)*G_Z(y) - ((((0 : ℝ)/2)*a*(1-a)*‖x-y‖² : ℝ) : EReal).

   The quantifier order is x, membership, y, membership, a, lower weight bound, upper weight bound. This is the stated curvature inequality with coefficient zero, not an assertion of positive curvature. On this interval the objective is affine; the real correction is zero, and the inequality specializes to equality.
5. IsMinOn P_Z V_Z 0: for every z∈V_Z, P_Z(0)≤P_Z(z). P_Z is constant zero.
6. For every z∈V_Z, toReal(loss_Z(0,0))-hint_Z(0)+support_Z(z-0) ≤ toReal(loss_Z(0,z))-hint_Z(z). This reduces to z≤z.
7. 0∈V_Z.
8. -1∈V_Z.
9. ‖support_Z‖=1.
10. G_Z(0)=(0 : EReal).
11. G_Z(-1)=((-1 : ℝ) : EReal).
12. toReal(G_Z(0))-toReal(G_Z(-1))=1.
13. ‖support_Z‖²/(2·0)=0, with division in ℝ.
14. NOT (toReal(G_Z(0))-toReal(G_Z(-1)) ≤ ‖support_Z‖²/(2·0)).

The denominator in conjunct 13 is zero. Lean's real division is totalized: division by zero evaluates to zero. The displayed conjunct explicitly asserts this resulting value; it is not positive infinity and does not make the expression undefined. Thus the final conjunct is ¬(1≤0).

## Difference and claim limits

The Tight example has actual objective gap 2 and quotient 2 at the fixed positive curvature parameter 1, so it asserts an attained upper bound even though the prediction point is not a current-objective minimizer. The ZeroCurvature example has gap 1 and quotient 0 at the fixed parameter 0, so it asserts failure of the analogous divided inequality while also asserting the listed convexity, prefix finiteness, zero-curvature, prediction-minimum, support, and feasibility conditions.

The second statement therefore supplies a concrete obstruction to allowing parameter zero in that same quotient formula under its listed conditions. It does not refute a statement requiring strictly positive curvature, nor address all conceivable bounds or conventions at zero curvature. Neither closed example quantifies over arbitrary spaces, losses, horizons, curvature parameters, prediction points, comparators, or support maps. Neither asserts existence of a general algorithm, a regret bound, or source faithfulness. Header content cannot establish compilation, proof correctness, which helper/provider theorem was invoked, or whether proofs avoid any particular shortcut.
