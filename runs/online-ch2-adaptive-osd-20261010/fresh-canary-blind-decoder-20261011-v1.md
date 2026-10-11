# Neutral algorithm certificate decoding

Actor: `/root/adaptive_decoder`.
Requested model and effort: GPT-6 Astra / medium. This is request metadata; no runtime model or effort attestation is available.
Input: `E:/ABRL/worktrees/research-online-book/docs/contracts/online-ch2-adaptive-osd-v1/algorithm-canary-neutral-packet-v1.lean.txt`.
Raw input SHA-256 before reading: `1aa5c0444ed1d3fb1f3cd73df0e97cb340d5e80d14cb7fd4e0c042c7712e39b3`.
Raw input SHA-256 after decoding: `1aa5c0444ed1d3fb1f3cd73df0e97cb340d5e80d14cb7fd4e0c042c7712e39b3`.
Input unchanged: true.

## Access and evidence boundary

I read only the designated neutral packet as substantive input. I did not inspect repository sources, history, proofs, source documents, previous verdicts, or run a compiler. The task instructions and workspace governance were visible as conversation context. This is an agent-based restricted-input decoding, not a claim of human, external, or absolute blindness. The packet omits a paper/book identity, but the imported declaration names explicitly reveal online subgradient policies, adaptive potential, adaptive energy, and gradient descent; domain blindness is therefore not absolute. I reconstruct the declared propositions without judging source fidelity or independently certifying their proofs. The packet supplies theorem statements without proof bodies.

## Shared objects and operational meaning

The general ambient space E is a finite-dimensional real inner-product space (with its compatible normed additive group structure). Time t and horizon T are natural numbers beginning at zero. A Domain supplies a feasible set, with nonemptiness, closedness, and convexity indicated by the displayed singleton construction. The exact imported structure is not inspected. The packet explicitly defines project as unique nearest-point projection. For the real fixture, V = [0,1]; W = {0}.

Let f_t:E -> extended reals be whole loss functions, x_init in E, alpha and D real, and p a SupportPolicy. Write H_t=(x_0,...,x_t) for the stored history, Q_t for accumulated squared feedback, g_t for the selected feedback, and r_t for the nominal step. The displayed recurrence is:

- H_0=(x_init), Q_0=0, and x_t is the final point of H_t.
- g_t = p(t, (f_i)_{i<t}, H_t, f_t).
- Q_{t+1}=Q_t+||g_t||^2, and r_t=alpha D/sqrt(Q_{t+1}).
- If g_t=0 then x_{t+1}=x_t exactly, without invoking projection. Otherwise x_{t+1}=project_V(x_t-r_t g_t).
- H_{t+1} appends x_{t+1}; A_t=(H_t,Q_t).

The policy receives strict-past whole losses, all stored points through the current point, and the current whole loss. It has no future-loss argument. In the concrete fixtures the policy ignores all input except time. The definition does not itself establish subgradient legality for arbitrary policies. L(T) is the separate proposition that g_t belongs to the global-support subdifferential at x_t for every t<T; it is defined but not used as an explicit premise of any of the seven certificates. The parameter names alpha and D impose no positivity or diameter restriction by themselves, nor does the displayed generic initializer require x_init to be feasible.

For any comparator u, F(u,T)=sum_{t=0}^{T-1} [(f_t(x_t)).toReal-(f_t(u)).toReal]. This is a real-valued sum after separate conversion of each extended-real value. In the finite fixtures it is exactly cumulative loss difference. Without additional finiteness assumptions it should not be silently interpreted as extended-real subtraction or ordinary finite regret. Lean's real division is totalized: a/0=0, so a nominal step at zero accumulated energy is a defined real number, not an undefined expression.

The support subdifferential is {g : for every y in E, f(z)+<g,y-z> <= f(y)}, with the inner product cast into the extended reals. Its support inequality is global in y, not restricted to the feasible domain. Properness here means no value is minus infinity and at least one value is finite. SubdifferentiableOn(U,f) means properness plus a nonempty support subdifferential at every z in U. Extended convexity means convexity of {(z,c) in E x R : f(z)<=c}, with real epigraph heights. This predicate alone allows extended-real infinities.

For the real fixture, set a_t=3 if t=1, a_t=-4 if t=3, and a_t=0 otherwise. Set f_t(x)=a_t x, embedded into the extended reals, and p(t,...)=a_t. The abbreviations x(alpha,t), q(alpha,t), and r(alpha,t) use V=[0,1], D=1, x_init=1/2, and this f,p. Finally B(A,S,eta)=A/(2 eta)+eta S/2. The A argument of B is a scalar and is unrelated to the state function A_t.

## certificate_1

For every real-space Domain U and every natural time t, all three claims hold:

1. f_t has convex real-height epigraph.
2. f_t is proper and has a nonempty global-support subdifferential at each z in U.
3. For every real z, a_t belongs to the global-support subdifferential of f_t at z. Equivalently, for every real y, f_t(z)+a_t(y-z)<=f_t(y), with finite quantities embedded into extended reals.

There are no extra hypotheses on U or t beyond their types. These are properties of the specific linear losses; there is no arbitrary-loss convexity or oracle-existence conclusion.

## certificate_2

The conjunction asserts:

1. For every real alpha and every natural t, the actual policy feedback G for V, alpha, D=1, initial 1/2 and the fixture is exactly a_t.
2. For every real alpha and natural horizon T with T<=4,
   q(alpha,T)=0 if T<=1; q(alpha,T)=9 if 1<T<=3; q(alpha,T)=25 if 3<T<=4.

Thus Q_0=Q_1=0, Q_2=Q_3=9, and Q_4=25 for all alpha, including zero and negative values. The second conjunct claims no energy formula beyond T=4, even though the definitions permit deriving one. The first conjunct is unbounded in time.

## certificate_3

For alpha=1, with the fixed V, D, f, p and initial point, the single conjunction states every following equality and inequality:

- x(1,0)=1/2, x(1,1)=1/2, x(1,2)=0, x(1,3)=0, x(1,4)=4/5.
- r(1,0)=0, r(1,1)=1/3, r(1,2)=1/3, r(1,3)=1/5.
- Against comparator u=0 at T=4, F(0,4)=3/2.
- The terminal squared distance to u=0 is |x(1,4)-0|^2=16/25.
- project_[0,1](-1/2)=0 and -1/2 is not zero.

All constants are exact real numbers. The first update has zero feedback and retains 1/2. At t=1 the unprojected point is -1/2, so projection changes it to zero. At t=2 feedback is again zero and the point stays zero despite the positive nominal step 1/3. At t=3 feedback -4 with nominal step 1/5 gives 4/5. F uses losses at x_t for t=0,1,2,3, excluding x_4; its only nonzero contribution is 3(1/2) at t=1. These update explanations follow from the displayed definitions and equalities, not from a hidden theorem.

## certificate_4

The four conjuncts state:

1. For alpha=1, comparator 0, horizon 4, F(0,4)<=59/10.
2. For the same run and comparator, F(0,4)<=15/2.
3. For a different run with alpha=sqrt(2)/2, still D=1, V=[0,1], initial 1/2 and fixture f,p, the four-round loss difference against 0 is at most sqrt(50).
4. sqrt(50)=sqrt(2) times inf { B(1,25,eta) : eta is real and eta>0 }.

The infimum is over attainable scalar bound values, not over trajectory losses or policies. Its defining objective is 1/(2 eta)+(25 eta)/2. Elementary scalar minimization gives value 5 at eta=1/5, consistent with the displayed identity sqrt(50)=5 sqrt(2); attainment and the optimizer are an explanatory deduction, not additional explicit certificate conjuncts. No universal-in-T or universal-loss bound is stated. The numbers 59/10 and 15/2 are upper bounds on the same alpha=1 quantity, and are not asserted to be optimal or equal to its exact value 3/2.

## certificate_5

Define futureLoss_t(x)=f_t(x) for t<2 and the constant extended-real value 7 for t>=2. At alpha=1, D=1, initial 1/2, V and the same time-only policy, the certificate states:

- A_2(f)=A_2(futureLoss), equality of the entire history-and-energy pair after two updates.
- f_2 and futureLoss_2 are unequal as whole functions of x.
- f_1 and futureLoss_1 are equal as whole functions of x.

At t=2 the functions are respectively constant 0 and constant 7, while t=1 retains 3x. A_2 incorporates rounds 0 and 1 only. This is a concrete prefix-invariance check. It does not assert legality of the policy for the changed suffix, equality of current/future loss functions, or a universal theorem over every pair of loss sequences and every policy. Because this particular policy ignores losses entirely, the witness alone does not test whether an arbitrary policy correctly uses its permitted history inputs.

## certificate_6

For zeroLoss_t(x)=0 and zeroPolicy(t,...)=0, on V with alpha=D=1 and initial point 1/2, the conjunction asserts:

1. For every natural t, x_t=1/2.
2. For every natural T, Q_T=0.
3. Against comparator 0 at horizon 4, F(0,4)=0.
4. The terminal squared distance is |x_4-0|^2=1/4.
5. The same F(0,4)<=0.

The first two claims are quantified for all times/horizons; the final three concern horizon 4 only. Positive terminal comparator distance coexists with zero loss difference and zero feedback energy. The branch g_t=0 retains the current point. No convergence-to-comparator claim follows.

## certificate_7

For the singleton domain W={0}, alpha=1, D=0, initial point 0, and the original f,p, the conjunction states:

- x_2=0.
- Q_2=9.
- g_1=3.
- Against comparator 0 at horizon 2, F(0,2)=0.
- The same F(0,2)<=0.

This is a zero-D feasible-domain case with nonzero global feedback and positive accumulated energy. The point and comparator coincide at zero, so the observed loss difference vanishes. D=0 is an explicit fixture choice; the certificate contains no general theorem about arbitrary zero-diameter sets or all times.

## Ambiguities, missing assumptions, and limits of reconstruction

- The packet gives sufficient explicit notation to decode the fixtures, including projection and the predicates, but imported structure internals, proof terms, and compiler acceptance remain uninspected. No proof-validation or source-fidelity verdict is made.
- Generic alpha,D are unrestricted reals. There is no stated generic condition D>=0, alpha>0, diameter(V)<=D, boundedness of V, or x_init in V. Concrete cases use V=[0,1], D=1, or W={0}, D=0. A generic convergence/regret theorem cannot be inferred from those cases.
- The nominal step includes current feedback energy Q_{t+1}; it is computed after receiving f_t and g_t, for the update to x_{t+1}. x_t was determined from earlier rounds. Whole-loss information is available, not merely a scalar bandit observation.
- The policy type supplies inputs; it does not ensure support legality off the realized path. L is a separately defined path predicate. certificate_1 and certificate_2 support legality for the original linear fixture but do not assert a general lawful oracle.
- F is built using toReal. The shown concrete losses are finite, but no general extended-real regret theorem is provided. SourceProper and extended convexity alone should not be replaced with global finiteness assumptions.
- The comparisons in certificate_4 name no generic potential or energy formula, and there is no explicit theorem equating 59/10 to a particular potential expansion. Imported module names can suggest motivation but do not establish that semantic origin.
- certificate_5 is a special time-only-policy witness, not a universally quantified causal-prefix theorem. certificate_6 and certificate_7 separately distinguish zero feedback energy from a zero-D singleton fixture with nonzero feedback.
- The complete seven statements are finite witnesses or the specific quantified properties recorded above. They do not by themselves establish an arbitrary-horizon guarantee for arbitrary losses, a paper theorem, or an algorithm-wide source-faithfulness claim.
