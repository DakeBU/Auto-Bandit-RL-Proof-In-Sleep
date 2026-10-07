# Neutral closed-proposition reconstruction: N01-N08

Actor `/root/osd_blind`; requested GPT-6 Astra / medium without escalation. Runtime model and effort are not independently attested. This is not a human or external review and carries no external-independence attestation.

Prior-history disclosure: this reused actor has decoded earlier neutral packets concerning current-support recursions, finite-history policies, scalar absolute losses, linearization, scalar step minimization, and unit scaling in the 20261007 runs. Prior neutral context remains in the actor's history; this is not a first-exposure or history-free decoding. For this task only `online-foundations-public-20261007/blind-packet-v1.md` was read. No external source, original alias, theorem body, prior verdict, or repository/search/network material was inspected.

## Literal notation and definitions

All time/horizon variables range over natural numbers, with Finset.range n={0,...,n-1}. Losses are real-valued, not extended-real. No norm, topology, convexity, probability, information filtration, or computational model is supplied.

For an arbitrary type X, losses ell:N->X->R and a sequence w:N->X, write
\[
C_n(u)=\sum_{t=0}^{n-1}\ell_t(u),\qquad
D_T(w)=\sum_{t=0}^{T-1}\ell_t(w_{t+1}).
\]
The first expression evaluates one fixed argument u throughout its prefix. The second uses a potentially different w_{t+1} for each term. In particular w_{t+1} is the index associated with a prefix including the loss at t; no strict-past-only causality is assumed. The name `leader` is only a name for a supplied total sequence; minimization and feasibility are hypotheses precisely where displayed, not implicit parts of its type.

The explicit total functions a:N->Bool->R and b:N->Bool are
\[
a_t(\mathrm{false})=0\quad\text{for every }t,\qquad
a_0(\mathrm{true})=-2,\qquad a_t(\mathrm{true})=3\quad(t\ne0),
\]
\[
b_n=\begin{cases}\mathrm{true}&n=1,\\\mathrm{false}&n\ne1.\end{cases}
\]
Thus these definitions specify all natural inputs, not only the displayed two-round examples. N07 and N08 introduce a DIFFERENT locally defined sequence w_n=true exactly when n=2. N08 also uses its own locally defined loss, distinct from a.

Every target is a closed Prop description. Each section uses the seven requested slots: objects/spaces; quantifiers; assumptions; conclusion; constants/indices; operation/information; boundaries. Closed examples can have no free universal parameters; their internal finite-prefix quantifiers are reproduced explicitly. Describing these Props is not supplying or certifying proofs.

## N01

1. **Objects/spaces.** An arbitrary type X:Type u, arbitrary set V subset X, arbitrary real loss sequence ell:N->X->R, supplied total sequence w:N->X, and T in N. X has no additional algebraic or geometric structure.
2. **Quantifiers.** For every X,V,ell,w,T, assume both conditions for every n with 0<n<=T; the minimization condition additionally quantifies over every u in V.
3. **Assumptions.** Positive-prefix feasibility and prefix minimality:
   \[
   \forall n\in\mathbb N,\quad 0<n\le T\Rightarrow w_n\in V,
   \]
   \[
   \forall n\in\mathbb N,\quad0<n\le T\Rightarrow
   \forall u\in V,\ C_n(w_n)\le C_n(u).
   \]
   Both hypotheses are retained. No minimality of w_0 and no assumption about n>T is supplied.
4. **Conclusion.** The sum using successive prefix leaders is at most the same losses evaluated throughout at the terminal leader:
   \[
   \forall X,V,\ell,w,T,\quad
   \left[(\forall n,0<n\le T\Rightarrow w_n\in V)\land
   (\forall n,0<n\le T\Rightarrow\forall u\in V,C_n(w_n)\le C_n(u))\right]
   \Rightarrow D_T(w)\le C_T(w_T).
   \]
5. **Constants/indices.** Factor 1, no additive term; left leader index t+1 and right index T. Both sums use losses t=0,...,T-1, including no term at t=T.
6. **Operation/information.** This compares supplied finite sums under exact prefix-minimizer assumptions. It does not construct the sequence, guarantee a minimizer exists independently, or assert online implementability: w_{t+1} is constrained using the prefix through loss t. The comparator u appears only in the minimizing hypothesis.
7. **Boundaries.** T=0 is allowed, the assumptions are vacuous and both sums zero even though w_0 is a supplied value. For T>0, the feasibility premise entails some member of V exists; no separate nonemptiness assumption is written. Empty X has no supplied w:N->X, so universal quantification over such sequences creates no existence claim. At T=1 the displayed sums coincide. No uniqueness, boundedness or nonnegativity of losses is required.

## N02

1. **Objects/spaces.** The fixed Bool space, V=all Booleans, and the explicit total a,b above.
2. **Quantifiers.** For every natural n with 0<n<=2 and every u in Set.univ:Bool. These are exactly n=1,2 and u=false,true.
3. **Assumptions.** The conditional bounds 0<n and n<=2, plus u in the universal set; there are no unknown loss/policy parameters.
4. **Conclusion.** The specified b_n minimizes cumulative a-loss at each of those prefixes:
   \[
   \forall n\in\mathbb N,\quad0<n\le2\Rightarrow
   \forall u\in\{\mathrm{false},\mathrm{true}\},\quad
   \sum_{t=0}^{n-1}a_t(b_n)\le\sum_{t=0}^{n-1}a_t(u).
   \]
   At n=1, b_1=true has value -2 versus false's 0; at n=2, b_2=false has value 0 versus true's -2+3=1.
5. **Constants/indices.** Horizon cap exactly 2; the first true-loss value is -2 and all later true-loss values are 3. The argument b_n remains fixed within the prefix sum.
6. **Operation/information.** An explicit finite-prefix minimization description, not a computation or selection of a fresh leader from a changing loss during the sum.
7. **Boundaries.** n=0 and n>2 are not covered by the target, despite a,b being total. No general all-horizon minimization or source attribution is inferred.

## N03

1. **Objects/spaces.** The fixed functions a,b on Bool and horizon 2.
2. **Quantifiers.** A closed numerical proposition with no free variables or additional assumptions.
3. **Assumptions.** None; all values are fixed by the definitions.
4. **Conclusion.** Successive-leader loss is at most terminal-leader loss:
   \[
   \sum_{t=0}^{1}a_t(b_{t+1})\le\sum_{t=0}^{1}a_t(b_2).
   \]
   Specifically the inequality compares -2 with 0.
5. **Constants/indices.** Left uses b_1 at t=0 and b_2 at t=1; right uses b_2 at both indices. Exactly two terms per sum.
6. **Operation/information.** Evaluate the fixed example's two sums; no new algorithm, probability, or adaptive input assumption.
7. **Boundaries.** This is a non-strict inequality at the fixed horizon 2. Strictness is not part of this target's connective, although the subsequent target records it explicitly. No assertion about other horizons.

## N04

1. **Objects/spaces.** Same fixed Bool functions a,b and two-term sums.
2. **Quantifiers.** Closed conjunction of three concrete claims; no universal free parameters.
3. **Assumptions.** None beyond the explicit definitions.
4. **Conclusion.** The two values and their strict comparison are simultaneously stated:
   \[
   \left[\sum_{t=0}^{1}a_t(b_{t+1})=-2\right]\land
   \left[\sum_{t=0}^{1}a_t(b_2)=0\right]\land
   \left[\sum_{t=0}^{1}a_t(b_{t+1})<\sum_{t=0}^{1}a_t(b_2)\right].
   \]
   The successive sum is -2+0; the terminal sum is 0+0, giving -2<0.
5. **Constants/indices.** Exact real values -2 and 0, strict <, horizon exactly 2; no asymptotic or tolerance interpretation.
6. **Operation/information.** An explicit value witness showing the inequality can be strict in this example, not an equality law for arbitrary sequences.
7. **Boundaries.** Does not assert a quantitative gap for all instances or horizons, nor that the inequality reverses. The definitions at times beyond 1 remain total but unused here.

## N05

1. **Objects/spaces.** Arbitrary X:Type u, V subset X, real losses ell and supplied sequence w:N->X.
2. **Quantifiers.** For every X,V,ell,w. V is an explicit quantified parameter even though it does not occur in the displayed sums.
3. **Assumptions.** None: no feasibility, minimality, or nonempty-set premise.
4. **Conclusion.** The zero-horizon comparison holds:
   \[
   \forall X,V,\ell,w,\quad
   \sum_{t\in\operatorname{range}(0)}\ell_t(w_{t+1})
   \le\sum_{t\in\operatorname{range}(0)}\ell_t(w_0),
   \]
   which is the real inequality 0<=0.
5. **Constants/indices.** Both ranges are empty. The displayed right leader index is 0 but no summand evaluates it.
6. **Operation/information.** Empty finite-sum extension; no loss queries or algorithmic action is encoded by the inequality.
7. **Boundaries.** Allows arbitrary V, including empty V, and arbitrary losses and sequence values. Supplying a total sequence is not an assertion that every possible empty X admits one. This boundary statement does not extend missing assumptions to positive horizons.

## N06

1. **Objects/spaces.** Arbitrary X:Type u, real loss sequence ell and supplied sequence w:N->X. There is no set V parameter.
2. **Quantifiers.** Every X,ell,w.
3. **Assumptions.** None.
4. **Conclusion.** At one term the two expressions are exactly equal:
   \[
   \forall X,\ell,w,\quad
   \sum_{t\in\operatorname{range}(1)}\ell_t(w_{t+1})
   =\sum_{t\in\operatorname{range}(1)}\ell_t(w_1).
   \]
   Each side is ell_0(w_1).
5. **Constants/indices.** Horizon 1, only t=0, so t+1=1. Equality rather than merely <=.
6. **Operation/information.** Simplify the singleton finite sum; no minimizer construction or feasibility test.
7. **Boundaries.** No loss-sign or leader-optimality assumption is needed. This does not claim equality for T>=2 or a property of w_0.

## N07

1. **Objects/spaces.** Bool with V=all Booleans, the fixed loss a, and the locally defined sequence
   \[w_n=\mathrm{true}\ \text{iff}\ n=2;\quad w_n=\mathrm{false}\ \text{otherwise}.\]
   This w is distinct from b, which is true iff n=1.
2. **Quantifiers.** The target is a closed let-bound conjunction. Its first conjunct quantifies every natural n with 0<n<=2; the two subsequent comparisons are fixed finite sums.
3. **Assumptions.** No external assumptions. Positive-prefix bounds occur only inside the first conjunct's implication.
4. **Conclusion.** All three facts hold:
   \[
   [\forall n\in\mathbb N,\ 0<n\le2\Rightarrow w_n\in\{\mathrm{false},\mathrm{true}\}]
   \land[C_1^a(\mathrm{true})<C_1^a(w_1)]
   \land[D_2^a(w)>C_2^a(w_2)].
   \]
   In numbers, feasibility is automatic; -2<0 at prefix 1; and the successive sum is a_0(false)+a_1(true)=3, exceeding the terminal sum a_0(true)+a_1(true)=1. Thus this particular feasible sequence fails prefix minimality at n=1 and exhibits a reversed final comparison.
5. **Constants/indices.** First comparison uses range 1 and explicit true; last uses range 2 and leader indices t+1 versus fixed 2. Exact strict signs are < followed by >.
6. **Operation/information.** This is a concrete witness distinguishing feasibility from prefix-minimizer conditions. It is not a claim that every nonminimizing sequence reverses the comparison.
7. **Boundaries.** w is total, including w_0=false and w_n=false for n>2, but no later-horizon property is asserted. Feasibility alone is insufficient in this example; the target does not add hidden minimization assumptions.

## N08

1. **Objects/spaces.** Bool, the local set V={false}, local real losses
   \[\ell_t(\mathrm{false})=0\ (\forall t),\qquad\ell_0(\mathrm{true})=-10,\qquad\ell_t(\mathrm{true})=5\ (t\ne0),\]
   and the local total sequence w_n=true iff n=2, false otherwise. This loss is not a.
2. **Quantifiers.** A closed let-bound conjunction. The first conjunct quantifies all natural n with 0<n<=2 and every u in the singleton V. The second and third are fixed claims at index/horizon 2.
3. **Assumptions.** No external assumptions. In the first conjunct n's bounds and u in V are antecedents. Importantly that conjunct does not require w_n itself to be in V.
4. **Conclusion.** The sequence's prefix values are no worse than all feasible comparator values, yet its terminal value is infeasible and the sum comparison reverses:
   \[
   [\forall n\in\mathbb N,\ 0<n\le2\Rightarrow\forall u\in\{\mathrm{false}\},\ C_n(w_n)\le C_n(u)]
   \land[w_2\notin\{\mathrm{false}\}]
   \land[D_2(w)>C_2(w_2)].
   \]
   At n=1, w_1=false gives 0<=0; at n=2, w_2=true gives -10+5=-5<=0. Nevertheless w_2=true is outside V, and D_2=ell_0(false)+ell_1(true)=5 exceeds C_2(w_2)=-5.
5. **Constants/indices.** Local true losses are -10 at t=0 and +5 at every nonzero t. Bounds are n<=2; final strict inequality is 5>-5, using t+1 on the left and fixed w_2 on the right.
6. **Operation/information.** A concrete witness separating the comparator-value condition from feasible minimization: a point outside V can be better than every comparator in V. It demonstrates the distinction without assuming any algorithm or causality.
7. **Boundaries.** The first conjunct must not be paraphrased as w_n being an actual minimizer IN V. Only w_2's nonmembership is explicitly asserted, and no n>2 behavior is claimed. It does not say every infeasible sequence reverses the inequality, only that this fully specified one does.

## Evidence boundary

All eight propositions have been reconstructed at their stated closed scope, including the unused quantified V in N05 and the distinct locally bound definitions in N07/N08. Their descriptions and type declarations do not establish proofs. No ambiguity in the supplied finite-sum definitions blocks interpretation. Runtime settings remain unattested; inherited neutral history is disclosed. No source identity, source fidelity, proof acceptance, human/external review verdict, chapter completion, or Goal completion is claimed.