# Source-blind semantic reconstruction

Actor: `/root/batch42_blind_decoder`. Input SHA256: `9dec9ba4039e0abbed0be2ea4f6b1d57190fc77d72cf4624b6f782229bd1e6a9`.

Only the assigned neutral packet was read. This report reconstructs its semantics and does not give a source-equivalence verdict. Claim and check proof bodies were withheld. No compilation or proof validation was performed.

## Conventions

- **IsMinOn**: IsMinOn f V p means for every y in V, f p <= f y. Membership p in V must be supplied separately when required.
- **EqOn**: EqOn f g V means for every x in V, f x = g x.
- **Fin_n**: Indices 0 through n-1.
- **range_t**: Natural indices 0 through t-1.
- **Option**: some p carries an X value; none carries no value.
- **implicit_scope**: The production definitions and claims use arbitrary X : Type* and applicable implicit n : natural. a : V is a subtype point, not an arbitrary ambient point.

## Example context definitions

- **D**: The closed interval [0,1] in the reals, including both endpoints.
- **a**: A subtype element of D with underlying real 3/4; the packet includes a membership proof.
- **b**: A subtype element of D with underlying real 1/4; the packet includes a membership proof.
- **q**: For every natural t and real x: (x-1/4)^2 if t=0, and (x-3/4)^2 otherwise, meaning every t>0.
- **qChanged**: For every natural t and real x: q t x if t<2, otherwise x+100, meaning every t>=2.
- **qExtended**: For every natural t and real x: q t x if x belongs to D, otherwise x+7. The branch is on feasibility, not time.
- **r**: For every natural t and real x: x if t=0, otherwise x^2-x, meaning every t>0.

## Four core definitions

### C

**Objects spaces**

Arbitrary type X, natural n, a family past : Fin n -> X -> real, and x : X. No topology, norm, measurability or cardinality structure on X.

**Quantifiers order**

For every X, n and past, C past is a real-valued function of x. The sum ranges over all Fin n indices.

**Assumptions**

None beyond the stated types.

**Conclusion**

C past x is the sum of past i x over i = 0,...,n-1.

**Normalization constants**

An unweighted sum, not a mean; no division by n, regularizer, discount or additional term. For n=0 it is zero for every x.

**Information use**

Uses the value of every supplied past function at x.

**Boundary excluded regimes**

Defined for every finite n and arbitrary real losses, including negative losses. It does not assert existence of any minimizer.

### M

**Objects spaces**

A subset V of arbitrary X and past : Fin n -> X -> real; output is a subset of X.

**Quantifiers order**

For each x : X, membership M V past is tested by membership in V and comparison with every y in V.

**Assumptions**

None; V may be empty and the cumulative objective need not attain an infimum.

**Conclusion**

x belongs to M V past exactly when x belongs to V and, for every y in V, C past x <= C past y. IsMinOn supplies the comparison property; the separate membership conjunct enforces feasibility.

**Normalization constants**

Compares the raw sum C with the usual real non-strict order. Ties are allowed.

**Information use**

Only the cumulative objective values on V determine this set.

**Boundary excluded regimes**

M can be empty on a nonempty set. At n=0, M equals V. This is an attained global minimum, not an infimum, local minimum, approximate minimum or uniqueness assertion.

### S

**Objects spaces**

A subset V of arbitrary X and past : Fin n -> X -> real; output Option X.

**Quantifiers order**

For every V and past, branch on whether there exists an element of M V past.

**Assumptions**

No nonemptiness or attainment assumption is required to define the function. The definition uses classical logic and choice in a noncomputable section.

**Conclusion**

If M V past is nonempty, return some (Classical.choose h), where h witnesses that nonemptiness. Otherwise return none.

**Normalization constants**

No tie priority or numerical optimization tolerance is specified. some p and none are distinct Option constructors.

**Information use**

The selection is defined from the minimizer set; it has no sampled-feedback or sequential state input.

**Boundary excluded regimes**

The definition is a total mathematical Option-valued function, not a certified executable solver. Nonempty V alone does not force some. Multiple minimizers do not force none, but the identity of the chosen tied minimizer is unspecified.

### P

**Objects spaces**

V : Set X, a : V (a subtype element with a proof that its underlying point lies in V), loss : natural -> X -> real, t : natural; output Option X.

**Quantifiers order**

For each V, feasible a, full loss sequence and t, first branch on t=0; otherwise supply loss i.val for i : Fin t to S.

**Assumptions**

The input a requires V to be inhabited. No condition on loss beyond real values.

**Conclusion**

At t=0 return some of the underlying a. At t>0 return S V of the losses indexed 0,...,t-1.

**Normalization constants**

Zero-based indexing; t past losses are summed. The loss at t is not included. No normalization by t.

**Information use**

At zero uses a, at positive t uses the prefix of loss functions and V. It is a direct evaluation at t, not a recurrence through prior Option outputs.

**Boundary excluded regimes**

Cannot be instantiated on empty V with a genuine a : V. Positive-time values may be none even though the zero-time value is some. Initial-point dependence is explicit at zero; for fixed V and loss the positive-time definition does not consult a.


## Nine claim headers

### claim1

**Objects spaces**

Arbitrary X, loss : natural -> X -> real, t : natural, x : X.

**Quantifiers order**

For every loss, t and x.

**Assumptions**

No additional hypotheses.

**Conclusion**

C (i -> loss i.val) x equals the finite sum of loss i x over i in range t.

**Normalization constants**

Both forms contain exactly indices 0,...,t-1, each once; both are zero at t=0.

**Information use**

Only prefix values at x enter this equality.

**Boundary excluded regimes**

This reindexes a sum; it does not select an action or assert minimizer existence.

### claim2

**Objects spaces**

Arbitrary X, n, V : Set X, past : Fin n -> X -> real and p : X.

**Quantifiers order**

For all V, past and p, conditional on the specified successful output.

**Assumptions**

h : S V past = some p.

**Conclusion**

p belongs to V AND for every y in V, C past p <= C past y.

**Normalization constants**

Exact attained minimum of the raw finite sum, using <=.

**Information use**

The objective contains all n supplied past functions.

**Boundary excluded regimes**

Conditional soundness only. It asserts neither that S succeeds for arbitrary inputs nor that p is unique.

### claim3

**Objects spaces**

Arbitrary X, n, V and past as above.

**Quantifiers order**

For every V and past, an equivalence; its right-hand side negates existence of p : X with both stated properties.

**Assumptions**

No additional hypotheses.

**Conclusion**

S V past = none if and only if there does not exist p in V such that, for every y in V, C past p <= C past y.

**Normalization constants**

Exact attainment, not boundedness below or existence of a real infimum.

**Information use**

Uses feasibility and objective comparisons on V.

**Boundary excluded regimes**

Includes empty V and nonempty V with no attained minimum. Failure is not just emptiness and is not an algorithmic timeout. At n=0, failure is equivalent to V being empty.

### claim4

**Objects spaces**

Arbitrary X, n, V and two families past, pastprime : Fin n -> X -> real with the same index size.

**Quantifiers order**

For every V, past and pastprime, assume for every i : Fin n and every x in V the two values agree.

**Assumptions**

h : for all i, EqOn (past i) (pastprime i) V, namely for all x in V, past i x = pastprime i x.

**Conclusion**

S V past = S V pastprime as Option values, including the exact selected point when successful.

**Normalization constants**

No approximate equality, additive shift or rescaling premise is used.

**Information use**

Values outside V may differ. Equality of each supplied function on V suffices for identical selection.

**Boundary excluded regimes**

No unique-minimizer assumption. This is stronger than merely equality of objective values at two separately chosen outputs. The stated hypothesis is pointwise equality per index, not just a partial observation history.

### claim5

**Objects spaces**

Arbitrary X, n, V, past and p : X.

**Quantifiers order**

For all these objects, uniqueness quantifies over every q : X with q in V and the minimizer comparison property.

**Assumptions**

hp : p in V; hmin : for every y in V, C past p <= C past y; hunique : for every q in V, if for every y in V C past q <= C past y then q=p.

**Conclusion**

S V past = some p.

**Normalization constants**

Exact unique feasible global minimizer, no strict convexity or quantitative gap required.

**Information use**

All assumptions concern V and the cumulative objective on V.

**Boundary excluded regimes**

Sufficient conditions for a named output. The converse that every successful output is unique is not asserted. Outside-V points are excluded from the uniqueness quantifier.

### claim6

**Objects spaces**

Arbitrary X, V, a : V and loss : natural -> X -> real.

**Quantifiers order**

For all V, feasible a and loss, at exactly t=0.

**Assumptions**

a carries membership in V; no loss hypotheses.

**Conclusion**

P V a loss 0 = some of the underlying a.

**Normalization constants**

The branch is exactly zero, with no losses accumulated.

**Information use**

Independent of every loss value.

**Boundary excluded regimes**

Does not identify the empty-history S selection with a, and does not constrain a positive-time output.

### claim7

**Objects spaces**

Arbitrary X, V, a : V, loss, t : natural and p : X.

**Quantifiers order**

For all inputs and t including zero, conditional on P V a loss t = some p.

**Assumptions**

The feasible initialization a and h : P V a loss t = some p.

**Conclusion**

p in V AND, for every y in V, sum over i in range t of loss i p <= sum over i in range t of loss i y.

**Normalization constants**

Raw prefix sum over i<t. At zero all objective values equal zero.

**Information use**

Only earlier losses appear in the minimized objective.

**Boundary excluded regimes**

Does not assert all positive-time outputs exist, uniqueness, regret, future optimality or performance on loss t.

### claim8

**Objects spaces**

Arbitrary X, V, a : V, loss and t : natural.

**Quantifiers order**

For every such input and every t including zero, equivalence to absence of any feasible attained prefix minimizer.

**Assumptions**

The feasible initialization a; no attainment assumption.

**Conclusion**

P V a loss t = none if and only if there is no p in V satisfying, for every y in V, the prefix sum at p <= the prefix sum at y.

**Normalization constants**

The prefix is exactly range t. At zero the objective is zero, a witnesses a minimizer, and both sides of the equivalence are false.

**Information use**

Attainment is evaluated for the current prefix independently of earlier outputs.

**Boundary excluded regimes**

No persistence of failure, convergence, compactness or continuity theorem is asserted. Empty V is unavailable through the required a.

### claim9

**Objects spaces**

Arbitrary X, V, a : V, two loss sequences loss and lossprime, t : natural.

**Quantifiers order**

For every input, assume for every natural s<t and every x in V, loss s x = lossprime s x.

**Assumptions**

h : for all s<t, EqOn (loss s) (lossprime s) V. V and the initial a are shared on both sides.

**Conclusion**

P V a loss t = P V a lossprime t as exact Option values.

**Normalization constants**

The strict inequality s<t excludes index t as well as all later indices. At t=0 the hypothesis is vacuous.

**Information use**

Changing losses at s>=t or values outside V cannot affect this equality when the specified prefix agrees on V.

**Boundary excluded regimes**

This is extensional prefix invariance for full functions on V. It is not a bandit-feedback implementability claim and does not assert equal outputs when initial points differ at zero.


## Eight complete example checks

### check1

**Objects spaces**

X=real, D=[0,1], a=3/4, and the explicitly defined q sequence.

**Quantifiers order**

A conjunction of seven top-level statements. The final conjunct quantifies over every natural t in range 3, then existentially selects p depending on t.

**Assumptions**

No theorem hypotheses; all objects are fixed by example definitions.

**Conclusion**

1. a as a real equals 3/4.
2. P D a q 0 = some (3/4).
3. P D a q 1 = some (1/4).
4. P D a q 2 = some (1/2).
5. The real numbers 1/4 and 1/2 are unequal.
6. q 0 (1/4) is unequal to q 0 (3/4).
7. For every t in {0,1,2}, there exists p : real such that P D a q t = some p AND p in D AND, for every y in D, the sum over i<t of q i p <= the sum over i<t of q i y.

**Normalization constants**

q 0 x=(x-1/4)^2; q t x=(x-3/4)^2 for every t>0. In the sixth conjunct the two values are 0 and 1/4. At t=2 the objective is 2(x-1/2)^2+1/8.

**Information use**

Time one uses q 0; time two uses q 0 and q 1; time zero uses a.

**Boundary excluded regimes**

The last quantified assertion covers only t=0,1,2, not all times. The conjunction demonstrates distinct successive selected values and a nonconstant initial loss, but states no regret or future-performance bound.

Top-level conjunct count: 7.

### check2

**Objects spaces**

D, a, q, qChanged as defined, all inputs real-valued.

**Quantifiers order**

Three conjuncts, with differences evaluated specifically at time 2 and 3 and point x=0; output equality specifically at t=2.

**Assumptions**

No extra hypotheses.

**Conclusion**

1. q 2 0 is unequal to qChanged 2 0.
2. q 3 0 is unequal to qChanged 3 0.
3. P D a q 2 = P D a qChanged 2.

**Normalization constants**

qChanged t x=q t x for t<2; qChanged t x=x+100 for t>=2. Each displayed unequal pair is 9/16 versus 100.

**Information use**

The changed losses start at the current index 2; the selection at time 2 uses only indices 0 and 1.

**Boundary excluded regimes**

No equality of selections at t=3 or later is asserted. The two difference checks do not quantify over all points.

Top-level conjunct count: 3.

### check3

**Objects spaces**

D=[0,1], real point 2, q and qExtended, S with Fin 2, P at time 2.

**Quantifiers order**

Five conjuncts. The third quantifies over every natural time t and every x in D through EqOn.

**Assumptions**

No extra hypotheses.

**Conclusion**

1. The real point 2 does not belong to D.
2. q 0 2 is unequal to qExtended 0 2.
3. For every natural t and every x in D, q t x=qExtended t x.
4. S D (i : Fin 2 -> q i.val) = S D (i : Fin 2 -> qExtended i.val).
5. P D a q 2 = P D a qExtended 2.

**Normalization constants**

qExtended t x=q t x when x in D and x+7 otherwise. The displayed unequal values at (0,2) are 49/16 and 9.

**Information use**

Every loss agrees on the feasible region, though the extensions differ outside it; both displayed selections use two past functions.

**Boundary excluded regimes**

The displayed S and P equalities are for history length/time 2. The stronger all-times P equality is not itself a conjunct here, though claim9 can apply at other times.

Top-level conjunct count: 5.

### check4

**Objects spaces**

D=[0,1], distinct endpoints 0 and 1, one past function constantly zero, S output p : real.

**Quantifiers order**

Six conjuncts; the final existential requires one p satisfying all three inner conjuncts.

**Assumptions**

No extra hypotheses.

**Conclusion**

1. 0 belongs to D.
2. 1 belongs to D.
3. The real numbers 0 and 1 are unequal.
4. For every y in D, C of the single zero loss at 0 <= C of that history at y.
5. For every y in D, C of the single zero loss at 1 <= C of that history at y.
6. There exists p : real such that S D (the single zero loss) = some p AND p in D AND, for every y in D, C of that history at p <= C of that history at y.

**Normalization constants**

The history length is 1, not 0. Its sole loss is zero at every real point, so the cumulative objective is constantly zero.

**Information use**

The selector receives the constant history and D; no tie priority is supplied.

**Boundary excluded regimes**

Exhibits two distinct feasible minimizers and successful selection despite nonuniqueness. Does not specify p=0, p=1 or any other named tied point.

Top-level conjunct count: 6.

### check5

**Objects spaces**

X=real, V=empty set, a single loss x -> x^2 and selector S.

**Quantifiers order**

One equality, no quantified conjunct or P input.

**Assumptions**

No extra hypotheses.

**Conclusion**

1. S on the empty real feasible set with the one-function squared-loss history equals none.

**Normalization constants**

History length 1; ordinary square, with no additive term.

**Information use**

The loss exists on the ambient reals but there are no feasible points.

**Boundary excluded regimes**

This uses S, which permits empty V. It cannot instantiate P with a feasible initial point on empty V. It is not a counterexample to minimization of x^2 on all reals.

Top-level conjunct count: 1.

### check6

**Objects spaces**

D=[0,1], an empty history indexed by Fin 0, a=3/4, b=1/4 and q.

**Quantifiers order**

Four top-level conjuncts; the first existential gives one p with two inner conjuncts.

**Assumptions**

No extra hypotheses; a and b each carry D membership.

**Conclusion**

1. There exists p : real such that S D of the empty history = some p AND p in D.
2. P D a q 0 = some (3/4).
3. P D b q 0 = some (1/4).
4. P D a q 0 is unequal to P D b q 0.

**Normalization constants**

Fin.elim0 defines a family on the empty Fin 0 index type; its sum is zero. Both P outputs are at exactly t=0.

**Information use**

Empty-history S has no loss values to use; the two P evaluations explicitly use different initial subtype points.

**Boundary excluded regimes**

The first existential does not state a named output, and has no explicit IsMinOn conjunct. This check does not equate S on empty history with either initialization, and asserts no difference at positive times.

Top-level conjunct count: 4.

### check7

**Objects spaces**

V=all reals, the identity loss x -> x, S with length 1, P initialized at real 0 using its universal-set membership proof.

**Quantifiers order**

Six top-level conjuncts, with closedness in the real topology and convexity over the real scalar field.

**Assumptions**

No extra hypotheses.

**Conclusion**

1. The universal real set is nonempty.
2. The universal real set is closed.
3. The universal real set is convex over the reals.
4. S univ of the single identity loss equals none.
5. P univ initialized at 0 with the loss sequence constantly equal to the identity function, at t=0, equals some 0.
6. The same P input at t=1 equals none.

**Normalization constants**

The single cumulative loss is x itself. The initial point is 0; t=0 and t=1 are separate evaluations.

**Information use**

At t=0 initialization suffices; at t=1 minimization of the first loss over all reals has no attained minimum.

**Boundary excluded regimes**

Nonempty, closed and convex feasibility alone does not ensure attainment for this loss. No compactness, boundedness or coercivity assumption is stated. The check is not a claim that every loss on such a set fails.

Top-level conjunct count: 6.

### check8

**Objects spaces**

V=all reals, initial real point 0, sequence r : natural -> real -> real.

**Quantifiers order**

Four top-level conjuncts. The last universally quantifies over every real x.

**Assumptions**

No extra hypotheses.

**Conclusion**

1. P univ initialized at 0 with r, at t=1, equals none.
2. The same P input at t=2 equals some 0.
3. For every real y, the sum over i in range 2 of r i 0 <= the sum over i in range 2 of r i y.
4. For every real x, the sum over i in range 2 of r i x equals x^2.

**Normalization constants**

r 0 x=x; r t x=x^2-x for every t>0. Thus at t=1 the objective is x, and at t=2 it is x+(x^2-x)=x^2.

**Information use**

Each P evaluation recomputes from its complete current prefix. Failure at t=1 is not passed as state to t=2.

**Boundary excluded regimes**

An explicit recovery from no minimizer to an attained one. This rules out interpreting none as a permanent stopping state. No claim of eventual success for arbitrary sequences or any other time is stated.

Top-level conjunct count: 4.

## What the statements establish and leave open

The headers specify exact prefix-sum minimization with explicit optional failure when no feasible attained minimizer exists. Successful outputs are feasible minimizers. Unique minima identify the output, while ties still permit success. The prefix and feasible-region invariance claims concern exact Option equality. Initialization is explicit at zero, and later failure is not absorbing. These are statements being decoded, not proof-verification results.

They impose no topology or convexity in production, no nonnegative or bounded-loss requirement, and no generic existence assumption. They assert no regret bound, future-loss optimality, executable optimization procedure, runtime bound or bandit-feedback implementation. The examples distinguish empty feasibility, unattained minima on a nonempty closed convex domain, ties, initialization choice, future changes, off-domain changes and recovery from failure.

## Explicit unknown classifications

- **Claim and check proofs** (withheld_evidence, unknown): The packet contains headers only for claims and checks. No proof bodies or compilation logs were provided or inspected; truth and Lean acceptance were not established by this review.
- **Named output in a tied minimizer set** (unspecified_by_definition, unspecified): Classical choice selects an element when the set is nonempty, without an exposed tie priority. Exact identities cannot be reconstructed in tied cases beyond the stated equalities.
- **Source identity and equivalence** (outside_scope, not_assessed): No original source, source-aware comparison or equivalence verdict was requested or inspected.
- **Executability, information availability and performance** (not_asserted, not_guaranteed): No algorithm for attaining a minimum, computation cost, feedback acquisition model, measurability, regret bound, convergence or future-loss optimality is asserted.
- **Expanded arithmetic and boundary explanations** (inference_not_compilation, semantic_reasoning): Displayed loss values, zero-history explanations and descriptions of attained minima are mathematical decoding from the supplied definitions, not separately compiled checks.

## Coverage and evidence

Coverage: 4 core definitions, 7 auxiliary example definitions, all 9 claim headers, and all 8 complete checks. Check top-level conjunct counts are 7, 3, 5, 6, 1, 4, 6, 4. Nested existential conjunctions and universal scopes are expanded above. Exact neutral input contexts and headers are preserved in reconstruction.json.

Input hash was verified against the assigned SHA256. Output hashes and the tool/read scope appear in receipt.json. The receipt hash is delivered separately to avoid a circular self-hash.
