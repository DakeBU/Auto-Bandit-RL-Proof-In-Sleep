# Source-blind semantic reconstruction

Reviewer: **Codex subagent `/root/blind_decoder`**.

Input: only `blind-packet.txt`. This is an **agent review, not independent human gold admission**. I have not inspected source identities, reference proofs, other task materials, or prior verdicts. This report reconstructs the supplied targets; it does not certify a match to any external source.

## Target A

### 1. Objects

Let A be a finite subset of an arbitrary action type with decidable equality. Let p and ℓ be real-valued functions on the action type, and fix an action a ∈ A. For each possible chosen action c, define

    L̂_a(c) = ℓ(a) / p(a)  if c = a,
             0             otherwise.

The sum in the target ranges over c ∈ A. The functions may also have values outside A, but those values do not affect the asserted identity.

### 2. Quantifiers

The identity is universally quantified over the action type, finite set A, functions p and ℓ, and selected coordinate a, subject to the stated assumptions. It concerns one arbitrary coordinate a at a time. There is no quantification over time, trajectories, repetitions, or a random loss process.

### 3. Assumptions

Exactly the following numerical and membership assumptions are explicit:

    a ∈ A,
    Σ_{c∈A} p(c) = 1,
    p(a) ≠ 0.

In particular, the target does not assume p(c) ≥ 0, p(c) ≤ 1, positivity at every action, or a bound on ℓ(c). Membership of a implies that A is nonempty. Other coordinates may have zero weights.

### 4. Conclusion

The asserted identity is

    Σ_{c∈A} p(c) [L̂_a(c) − ℓ(a)]²
      = ℓ(a)² [1 / p(a) − 1].

This is an exact normalized weighted, centered second-moment identity. The same assumptions also algebraically give Σ_{c∈A} p(c)L̂_a(c) = ℓ(a), which explains the center used in the displayed target, although that first-moment identity is not itself the stated conclusion.

### 5. Constants and normalization

The total weight is exactly 1. The denominator is the selected action's own weight p(a). The right side is exactly ℓ(a)²(1/p(a) − 1), equivalently ℓ(a)²(1 − p(a))/p(a). There is no arm-count factor, exploration parameter, sample-size factor, or inequality relaxation.

### 6. Probability and feedback semantics

Under the additional condition p(c) ≥ 0 for all c ∈ A, p defines a probability mass function on A, and the nonzero condition then gives p(a) > 0. For C drawn from that distribution, the conclusion becomes

    E[(L̂_a(C) − ℓ(a))²] = Var(L̂_a(C))
                         = ℓ(a)²(1/p(a) − 1).

Without nonnegativity, the supplied target is still an algebraic identity for normalized signed weights; its left side need not be a nonnegative variance. The packet supplies no probability space or random variable C, so the displayed probabilistic reading is an interpretation with an extra condition, not an additional premise present in the target.

The estimator has the usual coordinate-wise bandit-feedback form: it uses the loss of a when a is chosen and returns zero otherwise. The target does not specify an actual observation protocol, sampling mechanism, filtration, conditional expectation, adaptive adversary, or whether losses are fixed before sampling. Those features cannot be recovered from this identity alone.

### 7. Boundary and excluded regimes

The stated target excludes a ∉ A and p(a) = 0. It does not exclude negative weights or p(a) > 1 when other signed weights restore normalization. It permits arbitrary real losses, including zero or negative values. It covers finite A only. It states neither a regret bound nor concentration, a simultaneous vector result, or an estimator guarantee for unobserved coordinates with zero probability.

Ambiguity flag: the name `prob` suggests probabilities, but the explicit assumptions establish only normalized real weights. Calling this unconditionally a variance theorem would add a semantic assumption absent from the target. The supplied estimator definition otherwise makes the mathematical identity unambiguous.

## Target B

### 1. Objects

Let S and A be finite state and action types equipped with measurable spaces. Let an MDP have a finite horizon H, a Markov transition kernel, and measurable real reward. Fix a Markov policy π, with an action kernel π_t for each stage t ∈ {0, …, H − 1}.

Write B_t^π for its supplied Bellman evaluation operator. Schematically, using r(s,a) and P(ds′ | s,a) for reward and transition,

    (B_t^π w)(s)
      = ∫_A [r(s,a) + ∫_S w(s′) P(ds′ | s,a)] π_t(da | s).

This notation describes the reward-plus-transition-continuation structure given in the packet. The packet does not specify the precise reward/kernel argument signatures or whether they include stage arguments; r and P here are schematic, not a claim of time homogeneity.

Let v be an arbitrary sequence of real-valued functions on S, indexed by natural numbers. Let V_t^π denote the supplied `valueAt`, described as backward policy evaluation with zero terminal data.

### 2. Quantifiers

The target is universal over the finite measurable state/action types, the MDP, the Markov policy, and the function sequence v. For every natural-number stage k satisfying k ≤ H, it asserts equality of state functions. The step premise quantifies over every natural-number t satisfying t < H, not merely one selected stage.

### 3. Assumptions

The sequence v satisfies

    v_H(s) = 0                         for every s ∈ S,
    v_t = B_t^π(v_{t+1})               for every 0 ≤ t < H,
    0 ≤ k ≤ H.

The lower bound on k follows from its natural-number type. The equalities in the terminal and step premises are equalities of whole state functions. No explicit measurability or integrability premise is imposed on v in the displayed target. Beyond the packet's description of the MDP and policy, no extra reward bounds, discount factor, or nonemptiness hypotheses are visible.

### 4. Conclusion

For every admissible queried stage k,

    v_k = V_k^π,

equivalently,

    v_k(s) = V_k^π(s)                  for every s ∈ S.

Thus backward evaluation with terminal value zero is the unique solution of this finite-horizon Bellman recursion on stages 0 through H for the fixed policy. This is policy-evaluation uniqueness. The operator averages under the supplied policy; the target contains no maximization, minimization, or comparison with other policies.

### 5. Constants and normalization

The terminal function is exactly zero. Reward and the continuation integral enter additively with coefficient 1 in the supplied Bellman description. No discount multiplier, error tolerance, rate, reward bound, or numerical approximation constant is stated. The transition and action objects are Markov kernels according to the packet, so their probability normalization comes from those object descriptions rather than an additional equation displayed in this target.

### 6. Probability and feedback semantics

The Bellman operator integrates actions according to the stage-specific Markov policy and subsequent states according to the MDP transition kernel. The asserted result is a deterministic equality of value functions defined by that integration recursion. It is not a high-probability statement, a sample-based estimate, or a learning guarantee. No observed dataset, exploration procedure, feedback restriction, model-knowledge condition, or filtration is specified.

With the appropriate measurability/integrability and trajectory construction, one may recognize the familiar expected remaining cumulative-reward interpretation. The displayed target itself establishes equality to the recursively defined `valueAt`; the supplied context does not separately provide a trajectory-level expectation theorem.

Finiteness of a type alone does not establish that its chosen measurable space is discrete. Because the packet gives arbitrary measurable spaces and no explicit regularity premise on v, it does not justify silently replacing all integrals by singleton-probability sums or assuming every candidate continuation is measurable. This does not obstruct the stated uniqueness claim for the supplied Bellman operator: terminal agreement and the same deterministic recursion already determine the functions backward.

### 7. Boundary and excluded regimes

The terminal stage k = H is included. Horizon H = 0 is included at the level of the displayed statement: the step premise is vacuous and the only admissible stage is k = 0. The sequence v is defined for all natural numbers, but its values after H are unconstrained by the premises and are outside the conclusion. Policy kernels are indexed only by stages strictly below H.

The target does not cover infinite horizons, nonzero terminal payoffs, approximate Bellman equations, policy optimality, or general history-dependent policies beyond what can be represented by the given Markov-policy object. No explicit `Nonempty` assumptions on the state/action types appear; which empty-type cases admit the supplied MDP and policy objects cannot be decided from the abbreviated context alone.

Ambiguity flags: the internal reward/kernel signatures and measurable-space regularity are unspecified. The packet therefore supports an unambiguous finite-recursion uniqueness reading, while stronger claims about a particular trajectory law, discrete-sum representation, or optimal control would require additional definitions or hypotheses.

## Decoder findings

- Target A is exactly a normalized weighted second-moment identity. A genuine variance interpretation requires nonnegative weights, which are not explicit assumptions.
- Target B is uniqueness of finite-horizon evaluation for a fixed Markov policy, including the zero terminal stage. It is not an optimality theorem.
- Neither target establishes a match to a particular source result. This agent reconstruction is not independent human gold admission.
