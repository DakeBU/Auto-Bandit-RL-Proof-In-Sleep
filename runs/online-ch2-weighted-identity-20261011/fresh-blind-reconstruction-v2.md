# Fresh source-blind reconstruction v2

Source-blind semantic reconstruction of proposed text-only declarations. No compilation, elaboration, proof verification, or source verification was performed.

Input raw SHA-256 before: `55ae3f02b56be38afad93917f2f4ee080b48e2a332f331d1e83f17d4ef07408f`

Input raw SHA-256 after: `55ae3f02b56be38afad93917f2f4ee080b48e2a332f331d1e83f17d4ef07408f`

## Supplied context

Imports: `Mathlib.Algebra.BigOperators.Module` and `Mathlib.Tactic`.

The neutral input supplies these two imports and closes its namespace. It contains no dangling reference to earlier scope/canary conditions. Whether this exact context resolves every name, notation, and instance against pinned Mathlib was not tested. These are bodyless proposed headers, not evidence of a compiled Lean file.

## BanditRL.OnlineWeightedPotential.weighted_difference_sum_eq

### 1. Objects and spaces

Two arbitrary real sequences a,w : N -> R and a natural horizon T. This is scalar finite-sum algebra.

### 2. Quantifier order

For every a, then w, then natural T, given hT : 0<T, the equality holds. All binders are explicit, and each sequence is defined on every natural number.

### 3. Assumptions

- T>0.
- No sign, monotonicity, boundedness, or recurrence assumptions on either sequence.

### 4. Conclusion

A weighted sum of consecutive decreases equals the initial weighted endpoint minus the terminal weighted endpoint, plus the interior correction from weight changes. It is an exact equality.

$$
\sum_{t=0}^{T-1}(a_t-a_{t+1})w_t=a_0w_0-a_Tw_{T-1}+\sum_{t=0}^{T-2}(w_{t+1}-w_t)a_{t+1}.
$$

### 5. Constants and indexing

- range T contains 0,...,T-1. range (T-1) contains 0,...,T-2 when T>=2, and is empty at T=1.
- The terminal pairing is a_T w_(T-1); no w_T occurs. Interior differences w_(t+1)-w_t multiply a_(t+1), with a plus sign before their sum.
- Only a_0,...,a_T and w_0,...,w_(T-1) occur. T-1 is natural truncated subtraction.

### 6. Probability and feedback

None. No probability space, expectation, filtration, adaptation, or feedback assumptions or conclusions.

### 7. Boundary and excluded cases

- At T=1, the identity is (a_0-a_1)w_0=a_0w_0-a_1w_0; the interior sum is empty.
- At T=2, the right side is a_0w_0-a_2w_1+(w_1-w_0)a_1, matching expansion of the left side.
- T=0 is excluded by hT, although formal substitution using truncated subtraction yields 0=0.
- Zero and negative sequence entries are permitted. Constant weights give zero correction. No infinite-horizon claim is made.

## BanditRL.OnlineWeightedPotential.distance_potential_sum_eq

### 1. Objects and spaces

An arbitrary type E with a NormedAddCommGroup instance; x : N -> E; a fixed u : E; eta : N -> R; and a natural T. All norms, squared norms, reciprocals, and displayed sums are real. The header assumes no inner product, scalar action, coordinates, finite dimension, or completeness.

### 2. Quantifier order

For every implicit E : Type*, with the instance NormedAddCommGroup E, then explicit x,u,eta,T in that order, given hT : 0<T and h_eta : for every natural t<T, 0<eta_t, the equality holds. u is fixed across all indices. The positivity quantifier is scoped to the already chosen eta and T.

### 3. Assumptions

- E is a normed additive commutative group.
- T>0.
- eta_t>0 for every natural t<T, exactly indices 0,...,T-1.
- No recurrence, optimization update, feasibility set, bound on x, monotonicity of eta, or relation between x and eta is assumed.

### 4. Conclusion

The sum of squared-distance decreases divided by twice the respective current step value equals an initial potential term minus a terminal potential term plus a reciprocal-step-change correction. It is an exact equality for arbitrary x, not a performance bound or update-rule theorem.

$$
\sum_{t=0}^{T-1}\frac{\|x_t-u\|^2-\|x_{t+1}-u\|^2}{2\eta_t}=\frac{\|x_0-u\|^2}{2\eta_0}-\frac{\|x_T-u\|^2}{2\eta_{T-1}}+\frac12\sum_{t=0}^{T-2}\left(\frac1{\eta_{t+1}}-\frac1{\eta_t}\right)\|x_{t+1}-u\|^2.
$$

### 5. Constants and indexing

- The denominators are 2*eta_t. The initial term uses eta_0; the terminal norm is at x_T while the terminal denominator uses eta_(T-1).
- The correction coefficient is (1/2 : R), the reciprocal difference is 1/eta_(t+1)-1/eta_t, and the norm is evaluated at x_(t+1).
- Only x_0,...,x_T and eta_0,...,eta_(T-1) occur. No eta_T is used or constrained.
- For t<T-1, t+1<T, so h_eta covers both correction denominators. hT gives 0<T and T-1<T, covering the endpoint denominators.

### 6. Probability and feedback

None. No stochastic object, expectation, measurability, filtration, adaptation restriction, or feedback model appears. The arbitrary sequence can be understood pathwise, but no stochastic conclusion is part of this header.

### 7. Boundary and excluded cases

- At T=1 the correction sum is empty, the only positivity condition is eta_0>0, and the equation becomes (||x_0-u||^2-||x_1-u||^2)/(2 eta_0)=||x_0-u||^2/(2 eta_0)-||x_1-u||^2/(2 eta_0). eta_1 is unrestricted.
- At T=2 the correction is (1/2)(1/eta_1-1/eta_0)||x_1-u||^2, and the final denominator uses eta_1.
- T=0 is excluded. Zero or negative eta_t for t<T is excluded; all eta_t for t>=T are unrestricted.
- No sign is asserted for the correction. Constant positive eta makes it zero. Squared norms may vanish, including when x_t=u.
- No uniform positive lower bound over all natural indices, step-schedule convergence, or infinite-horizon result is assumed or concluded.
- With total real division the underlying algebraic identity can hold even without positivity, but positivity remains part of the exact proposed contract and is not removed here.

## Generalization boundary

The first statement is algebra on arbitrary real sequences. Substituting a_t=||x_t-u||^2 and w_t=1/(2 eta_t), and factoring 1/2 from weight changes, gives the second mathematical equality. NormedAddCommGroup supplies subtraction and a real norm; the identity uses no inner-product or Euclidean geometry. Euclidean normed spaces are covered when equipped with the required instance, but the header also admits other normed additive commutative groups. No external source has been read, so the relationship of that broader scope to any source theorem cannot be certified. Neither header supplies an optimization algorithm or algorithm-specific inequality.

## Assessment

The T=1 and T=2 expansions are consistent, the endpoints and correction indices align, and positive steps are required precisely throughout the used step-index range. This is a mathematical semantic check only.

Only the authorized neutral input was read for this turn. Outputs were created exclusively in the requested tmp directory; v1 was preserved. No Git, build, source lookup, or canonical edit was performed. Ignore status was not independently inspected.
