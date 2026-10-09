# Blind semantic reconstruction of AdaptiveTranscript

Actor identity: `/root/adaptive_blind_decode`, the same distinct blind semantic decoder continuing an additional decoding pass.

Input packet: `C:/qb261009/bandit/.private/attempts/2026-10-09/adaptive-formal-packet.md`.

Exact current packet SHA256: `DB2F1189D0132BFB6467CAEC516409482D9B0011F7B4847591D1BC073C91A935`.

Scope: this is a transparent additional blind decoding pass by the same actor. Only the current formal packet and this actor's prior reconstruction were read for the refresh. The first reconstruction is preserved as `adaptive-blind-reconstruction-v1.md`, retaining its original packet hash `0340E6CFBECAA1E58EE84BFA1D9B85F9FB299FB1A4E8B7C5FA22485F18784E3B`. This refresh does not claim a fresh actor, fresh initial blindness, or a pre-proof chronology. It records the terms' mathematical meaning, hypotheses, and boundaries without identifying an originating source, giving an approval verdict, or reporting an independent Lean compilation.

Revision scope: the current packet adds `history_length`, `history_injective`, and `historyLaw_apply_at_trace`. Their statements and displayed proof terms are decoded below. The statements and hypotheses of `finite_kernel_chain`, `adaptive_hellinger_le`, `traceLaw_apply`, `traceLaw_history_eq`, and `adaptive_hellinger_budget` retain the meanings reconstructed in the first pass. This refresh strengthens the trace/list bridge description and removes the earlier observation that no named history-length theorem was present. The probability convention, reset model, cost interpretation, zero cases, and all-terminal-trace budget requirement are unchanged.

## Objects and notation

Let I denote the finite type `ι`, equipped with decidable equality where the matrix and process definitions require it. States lie in the finite dimensional complex Euclidean space indexed by I. The matrix norm in the packet is the Euclidean L2 operator norm. Let K and D be natural numbers. An oracle environment A assigns a unitary matrix A_i to each arm i in `Fin K`.

A `QuantumQueryWord.Word I` is a finite list of instructions. A known instruction contains a unitary matrix and costs zero oracle queries. A forward instruction applies U and costs one query; an inverse instruction applies `star U`, the adjoint and hence inverse of a unitary U, and also costs one query. Thus the query count is the forward count plus the inverse count. Known gates count toward word length but do not count toward query cost. A word can have arbitrarily many known gates despite its query bound.

Evaluation applies the list in temporal order: `eval (g :: rest) U = eval rest U * g.eval U`, so the head gate acts first on a column state. In particular, concatenating words a and b has evaluation `eval b U * eval a U`. Every instruction and evaluated word is unitary when U is unitary.

A `ResetBlockProcess.Plan K D I` contains an arm a, a word w, and a proof that the word query count is at most D. One block uses the selected arm's same unitary at every forward occurrence and its adjoint at every inverse occurrence. A block does not mix several arm oracles within its word.

The policy is a total deterministic function

`policy : List I -> Plan K D I`.

It can choose both its next arm and its next word, including the known gates in that word, from the entire preceding list of outcomes. The same policy function and the same initial state are used in the two environments being compared.

For a history h, write a(h) for the selected arm, w(h) for the selected word, and c(h) for its query count. We have `0 <= c(h) <= D` for every list h, including histories of zero probability.

## Reset block probabilities and adaptivity

Fix a state psi satisfying `norm psi = 1`. The block output under environment A at history h is

`x_A(h) = eval(w(h), A_(a(h))) psi`.

The real kernel is

`k_A(h,j) = |x_A(h)_j|^2`.

It is the distribution of a measurement in the fixed coordinate basis. It is nonnegative for any psi, and it has sum one when psi is normalized, since word evaluation is unitary. The corresponding `blockPMF` assigns `ENNReal.ofReal(k_A(h,j))` to outcome j.

Every block starts from the same psi. The new history selects a new plan, but neither `kernel` nor `blockPMF` takes a postmeasurement quantum state from the preceding block. There is consequently a classical memory of measurement outcomes, with a reset quantum input at each block. This supports classical adaptation across blocks and coherent sequences of gates within each block. It does not describe a quantum state carried coherently across blocks, nor further measurements and feedback inside a single word.

The outcomes are not asserted to be independent or identically distributed. The kernel at the next step depends on the previous outcomes through the policy. At a fixed common history, however, the two environments use the same plan. That common-history comparison is what permits the one-block stability estimate to enter the adaptive argument.

The policy has no explicit random seed or stochastic action-selection kernel. Randomness comes from the block measurement kernels. Independently randomized policies would need an additional representation or extension. The formal arguments also assume a fixed oracle matrix for each arm; they do not describe an oracle that changes with time or history.

## Finite traces and their densities

`Trace I 0` is `PUnit`, with its sole empty trace. Recursively, `Trace I (n+1) = Trace I n x I`. An element therefore stores exactly n chronologically ordered measurement outcomes as nested pairs. Its finite type instance is built recursively. The function `history` converts it to a list by appending the newest outcome.

The added `history_length` explicitly proves `(history h).length = n` for every `h : Trace I n`. Its induction has the empty case and the append-singleton step. It needs no finite-type, decidable-equality, policy, oracle, normalization, or support hypothesis.

The added `history_injective n` proves that `history : Trace I n -> List I` is injective at each fixed horizon. Equal history lists imply equal traces. At the successor step, `history_length` gives equal prefix lengths; `List.append_inj` separates equality of the prefixes from equality of the final singleton lists. The induction hypothesis and singleton injectivity identify both pair components. This theorem also needs no finite-type or probabilistic assumptions. It excludes collisions when converting fixed-length traces to list histories, including traces with zero probability. It is not a separately stated surjectivity theorem onto all length-n lists, and it does not make the map onto all lists of arbitrary lengths.

For a trace z = (j_1,...,j_n), let h_t = [j_1,...,j_t] and h_0 = []. The density is

`p_A,n(z) = product_(t=0,...,n-1) k_A(h_t,j_(t+1))`.

The empty density is 1. The recursive definition is exactly previous density times the next kernel value. All densities are nonnegative without a normalization hypothesis. With `norm psi = 1`, the sum over all length-n traces is 1, using normalization of every kernel row. These are real point probabilities on a finite trace space, rather than densities against a separately introduced continuous measure.

The definitions of `kernel`, `density`, `weightedCost`, and `expectedCost` do not themselves take a proof that psi is normalized. Their probability-law interpretation and the relevant comparison theorems do require it. Unnormalized inputs remain syntactically available in those definitions but are not thereby probability distributions.

## Hellinger convention and exact finite kernel chain rule

The packet defines

`H2(p,q) = sum_x (sqrt(p(x)) - sqrt(q(x)))^2`.

There is no factor 1/2. For nonnegative normalized p and q this is

`H2(p,q) = 2 - 2 * sum_x sqrt(p(x))sqrt(q(x))`.

Thus it is twice the squared Hellinger convention that includes 1/2, and its range for probability laws is from 0 to 2. Any numerical comparison with that other convention must adjust the factor. The range statement follows mathematically from the displayed definitions; the packet does not contain a separately named range theorem. All square roots are Lean's real square root. Nonnegativity hypotheses are essential to the expansion used here; allowing arbitrary real arguments to the definition does not turn them into probability masses.

`hellingerSq_expand` says, for arbitrary nonnegative finite p and q,

`H2(p,q) = sum p + sum q - 2 * sum sqrt(p)sqrt(q)`.

The theorem `finite_kernel_chain` has finite types alpha and beta, nonnegative functions p,q on alpha, and nonnegative rows k(h,-),l(h,-) on beta whose sums are each exactly one for every h. Define joint masses

`P(h,j) = p(h)k(h,j)` and `Q(h,j) = q(h)l(h,j)`.

Its conclusion is the exact identity

`H2(P,Q) = H2(p,q) + sum_h sqrt(p(h))sqrt(q(h)) H2(k(h,-),l(h,-))`.

Importantly, this theorem does not assume that p and q themselves have total mass one. The normalization assumptions concern the conditional rows. It is valid for the finite nonnegative base masses supplied. Nor does it require positive p, positive q, a common support, or an absolute-continuity relation. If one base mass is zero at h, the conditional contribution at that history is zero. There are no divisions by history probabilities or likelihood ratios.

The proof expands each row, factors square roots of nonnegative products, and uses row sums one. It then sums over alpha. It does not invoke an independence assumption or a bound on the number of nonzero rows.

## Costs and the one-block bound

For an arm error profile eta, define the path cost

`W_eta(z) = sum_(t=0,...,n-1) c(h_t) * eta_(a(h_t))^2`.

This is precisely `weightedCost`. Its summands are nonnegative regardless of the signs of eta. It counts oracle calls weighted by squared arm error. It is not the squared total query count, not the number of blocks, not the number of gates, and not an expected cost until it is averaged with a law.

`expectedCost policy A psi eta n` is

`C_A,eta(n) = sum_z p_A,n(z) W_eta(z)`.

The same path-cost function is averaged under two possibly different transcript laws. `expectedCost_succ` proves that the increment is

`sum_(h in Trace I n) p_A,n(h) c(history(h)) eta_(a(history(h)))^2`.

Here a trace in the summation is the prefix at the start of the next block. Normalization of the next kernel removes the final outcome from the incremental expectation.

The query-word terms first give an operator difference bound of c times the oracle difference, then a state difference bound using the common unit input. The basis measurement Hellinger quantity is at most the squared state difference. For a selected arm satisfying

`norm(E_i - F_i) <= eta_i`,

the one-block bound is at most `c(h)^2 eta_(a(h))^2`. Since `c(h) <= D`, `kernel_hellinger_le` gives

`H2(k_E(h,-),k_F(h,-)) <= D * c(h) * eta_(a(h))^2`.

All compared oracle matrices are unitary by their types. Known gates are the same at a common history and contribute no error in the word telescoping argument. There is no extra positivity condition on eta in the theorem signature. The oracle-distance hypothesis implies `eta_i >= 0` for each arm, since a norm is nonnegative. The cost definitions and the later arithmetic use squares.

## Adaptive expected-cost theorem

The complete hypothesis set of `adaptive_hellinger_le` is: a finite outcome type with decidable equality; natural K,D; a total policy into bounded plans; two environments E,F of unitary arm matrices; the common state psi with norm one; a real error profile eta; the bound `norm(E_i-F_i) <= eta_i` for every arm; and a natural fixed horizon n.

Its conclusion is

`H2(p_E,n,p_F,n) <= (D/2) * (C_E,eta(n) + C_F,eta(n))`.

Equivalently the right side is D times the average of the two expected weighted costs. It is not a bound in terms of just one environment's expected cost. No equality between those two expectations is assumed.

At the induction step, the exact kernel chain rule adds a conditional term weighted by `sqrt(p_E,n(h))sqrt(p_F,n(h))`. The one-block bound controls that conditional Hellinger term. The arithmetic inequality

`2 sqrt(p_E,n(h))sqrt(p_F,n(h)) <= p_E,n(h) + p_F,n(h)`

replaces the geometric overlap weight by the arithmetic mean. The cost increment identity in each environment then closes induction. Thus the factor 1/2 on the right comes from this arithmetic-mean step; it is not a hidden factor in the definition of `H2`.

The proof permits arbitrary history dependence of the shared policy and includes histories that have mass under only one environment. A zero mass causes the appropriate summands to vanish. There is no required lower bound on outcome probabilities and no common-support assumption.

## PMF bridge and relation to list histories

`traceLaw` is a genuine PMF on `Trace I n`. It starts as the point mass on the sole empty trace. At each step it binds the preceding trace law, samples the selected block PMF, and maps outcome j to the pair (preceding trace,j).

`map_pair_apply` states that mapping a PMF by `j -> (a,j)` gives mass p(h.second) when h.first = a and zero otherwise. This makes only the matching predecessor contribute in the point-mass computation.

`traceLaw_apply` proves for every trace z, including zero-probability traces,

`traceLaw(A,n)(z) = ENNReal.ofReal(p_A,n(z))`.

`traceLaw_toReal` then proves

`(traceLaw(A,n)(z)).toReal = p_A,n(z)`.

This conversion is exact because the real density is nonnegative and `ofReal` produces the finite mass represented by it. It is not an approximation or an unproved identification of two different distributions.

`traceLaw_history_eq` proves equality of PMFs after applying the trace-to-list map:

`traceLaw(A,n).map history = ResetBlockProcess.historyLaw(A,n)`.

The right-hand process starts from [] and appends a sampled outcome at each step under the same policy and reset block distribution. The theorem therefore connects the finite trace representation to the list-history process. It is equality of these laws, not an assertion that all lists have positive probability.

The added `historyLaw_apply_at_trace` gives the pointwise list-history bridge. Under the same finite-type and decidable-equality instances, total policy, unitary environment, and normalized input, for every natural n and every `z : Trace I n` it states

`ResetBlockProcess.historyLaw(A,n)(history(z)) = ENNReal.ofReal(p_A,n(z))`.

It imposes no support or positive-mass condition on z. Its displayed proof rewrites the list law using `traceLaw_history_eq`, expands the mapped PMF as a sum over finite traces, and uses `history_injective n` to leave only the unique matching trace z. `traceLaw_apply` then identifies that trace's mass with `ofReal` of its density. Thus conversion to a list does not merge masses from different traces at this fixed horizon. This is a direct pointwise equality in addition to the pushforward equality. Taking `.toReal` would also give the density using nonnegativity, but that extra list-mass conversion is an immediate derivation rather than a separately named theorem here.

The supplied final Hellinger statement remains formulated on finite traces. The three additions do not state a Hellinger invariance theorem, a general data-processing theorem, or a separate Hellinger bound over the full list type. They also do not weaken the terminal budget premise to a support-only premise. They supply exact length, injectivity, and pointwise probability bridges between the existing representations.

## Uniform error and the pathwise budget corollary

`historyQueryCost policy h` sums the query count of the plan at each prefix `h.take t`, for `0 <= t < h.length`. The appended-outcome lemma proves that appending j adds exactly the cost of the plan chosen from the preceding h.

For a constant error eta, `weightedCost_uniform` proves

`W_eta(z) = historyQueryCost(policy,history(z)) * eta^2`.

`expectedCost_le` states that if `W_eta(z) <= B` for every length-n trace, then `C_A,eta(n) <= B`. It allows any real B in the signature; the all-trace bound and normalization supply what is needed.

`adaptive_hellinger_budget` takes a real scalar eta, the uniform arm distance assumption `norm(E_i-F_i) <= eta` for every arm, natural n,T, and the hypothesis

`for every z : Trace I n, historyQueryCost(policy,history(z)) <= T`.

Its conclusion is

`H2(traceLaw(E,n).toReal, traceLaw(F,n).toReal) <= D * T * eta^2`.

The displayed `.toReal` denotes pointwise conversion of the PMF's masses, precisely as in its Lean statement. The proof bounds each environment's weighted expectation by `T eta^2` and applies the adaptive expected-cost theorem. The two equal upper bounds cancel the factor 1/2.

The budget assumption quantifies over every length-n trace, not only the support under E, not only the support under F, and not merely paths common to both. It includes hypothetical histories of zero probability under both environments. It is a condition at the chosen terminal horizon. It does not require this total budget at every longer horizon or at every list length. Since path costs are nonnegative, a terminal budget also bounds its prefixes when they can be extended to terminal traces; under a normalized state the outcome type is inhabited, so finite prefixes do have such extensions. This inference does not weaken the theorem's explicit all-terminal-trace premise.

The ambient `historyLaw_length_support` says only that supported list histories have length n. Its `historyLaw_queryCost_le` and `historyLaw_queryCost_le_budget` bound costs on that support using `n*D` (and `n*D <= T`, respectively). Those support statements have different quantifiers from the all-trace hypothesis of the adaptive budget theorem. One must not substitute a support-only bound for the stated hypothesis without a further argument or a different theorem. The expected-cost argument could mathematically be adapted to bounds on the relevant supports, but that weakening is not the supplied statement.

A sufficient direct all-trace condition is `n*D <= T`: `history_length` now explicitly supplies the length n of every trace history, and `historyQueryCost_le` bounds its cost by `n*D` from the per-block cap. T may also be smaller if the policy's sum of costs is bounded more tightly along every terminal trace. The theorem does not require `T = n*D`, and n is a block horizon rather than a query budget. There is no stopping-time result or variable-length transcript law in these statements.

## Zero cases and absent explicit positivity hypotheses

- **K = 0.** An arm would have to inhabit `Fin 0`. No plan exists, and a total policy cannot exist because `List I` contains []. The theorem signatures do not explicitly require `K > 0`, but their policy argument prevents a concrete instance with K = 0. This remains so at n = 0: the zero-step laws do not evaluate a plan, yet the signatures still demand a policy. Empty oracle families alone do not make the process instantiable.
- **D = 0.** Every plan's query count is zero. Its word can contain known gates but cannot contain forward or inverse calls. Kernels are therefore independent of the oracle environment at every common history, although the policy may still adapt its known gates to outcomes. The transcript laws in the two environments coincide, weighted costs vanish, and the Hellinger upper bounds are zero. A zero query cap does not prohibit blocks or known gates.
- **n = 0.** There is one trace, its density is 1 in both environments, its weighted cost is 0, and its law is a point mass. Both expected costs and Hellinger discrepancy are 0. `historyQueryCost [] = 0`; the terminal budget premise holds for any natural T, including 0, provided the other required data exist.
- **T = 0.** The budget theorem still applies. Its premise forces the complete horizon-n path cost to be zero on every terminal trace. The conclusion is zero Hellinger discrepancy. This does not assert that all policy words at histories beyond that horizon are query-free.
- **eta = 0.** The uniform norm bound forces the two arm matrices to agree arm by arm, so the laws agree and the upper bound is zero. For an arm profile, a zero eta component similarly forces equality for that arm; the cost weighting retains the nonzero error components.
- **Empty I.** The raw finite type declarations allow it, but a complex Euclidean state on an empty coordinate type has norm zero. No psi with norm one exists, so the normalized-law theorem hypotheses exclude this case. No separate nonempty assumption is printed.

## What the terms establish and what they leave open

The terms establish a finite-horizon stability bound for full measurement-outcome transcripts of deterministic, history-adaptive reset-block protocols, comparing two fixed unitary oracle families under the same policy, coordinate basis, and normalized pure input. They retain arm-dependent errors in the expected-cost theorem and specialize to a uniform error and an all-trace total query budget in the final corollary.

They do not state a regret bound, a sample-complexity lower bound, or a bandit/RL reward or transition model. There are no mixed input states, noisy nonunitary channels, general POVM kernels, coherently retained inter-block memories, changing oracle environments, oracle-dependent differing policies, or arbitrary stopping times in the process definition. Known unitaries can supply basis rotations within a word, but this is not a separately formalized general measurement model.

The transcript records measurement outcomes. Arm choices and words are deterministic functions of the prefixes, so they can be reconstructed from those outcomes and the fixed policy. The packet does not explicitly introduce a separate transcript type recording actions, a postprocessed output law, or a data-processing theorem for Hellinger discrepancy. Such additional claims require additional formal statements or derivations.

The matrix difference is measured in operator norm; the comparison is not phase-invariant at the hypothesis level. In particular, an error bound between raw unitary matrices may be conservative even when their measurement behavior agrees. The supplied estimate is an upper bound and is not asserted to be sharp. It can exceed the intrinsic probability-law maximum 2, since no clipping by that maximum is included.

Finally, the reset mechanism is encoded by always applying the new word to psi. The packet gives no resource accounting for physical state preparation, resetting, measurement, known gates, or elapsed time. D and T count only the specified forward and inverse oracle instructions. The reconstruction describes the supplied statements; it does not infer publication readiness, source identity, or successful compilation from their presence.
