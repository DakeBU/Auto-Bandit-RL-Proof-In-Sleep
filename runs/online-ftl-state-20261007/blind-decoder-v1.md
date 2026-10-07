# Neutral reconstruction of N01-N19

Actor `/root/osd_blind`; requested GPT-6 Astra / medium without escalation. Runtime model and effort are not independently attested. No human/external review or external independence is claimed.

Prior-history disclosure: this reused actor has previously decoded the 20261007 neutral current-support, policy, absolute-loss, linearization, optimal-step, unit-scaling, foundations, and preceding sharp-prefix packets. This is not a fresh history-free actor. For this task ONLY `online-ftl-state-20261007/blind-packet-v1.md` was read. No source identity, original alias map, proof body, prior verdict, or other history lookup was performed. These are neutral proposition reconstructions, not source or proof acceptance.

## All six actual definitions and permitted inputs

For total real sequences y:N->R and n,t:N,
\[
a_n(y)=\frac{\sum_{i=0}^{n-1}y_i}{n},\qquad
b_t(r,y)=\begin{cases}r,&t=0,\\a_t(y),&t>0,\end{cases}
\]
where r is the real initial value. Empty sums are zero and real division is totalized, so a_0(y)=0. This is distinct from b_0(r,y)=r unless r=0. Natural counts are coerced to real in real arithmetic.

The local state update c takes ONLY a pair (n,m):N x R and one real current target v:
\[
c((n,m),v)=\left(n+1,\ m+\frac{v-m}{(n:\mathbb R)+1}\right).
\]
It does not take a stream, comparator, future target, or full history. Its denominator is real(count)+1, always positive even at count zero; it is not count, a free learning rate, or a natural-number division. Arbitrary pairs (n,m) are legal arguments; a valid running-mean interpretation is established for the actual recursively constructed states, not asserted for every arbitrary pair.

The actual total state stream is
\[
d_0(r,y)=(0,r),\qquad d_{t+1}(r,y)=c(d_t(r,y),y_t).
\]
Thus state at t precedes consumption of y_t; the transition consumes y_t and produces state t+1. Although d is mathematically parameterized by the entire sequence, the strict-prefix dependence is a separate stated property below. Its first component is a count, its second is a stored real prediction. Initialization stores r, not the empty mean a_0.

The midpoint specialization and test sequence are
\[
e_t(y)=\begin{cases}\tfrac12,&t=0,\\a_t(y),&t>0,\end{cases}
\qquad
f_t=\begin{cases}0,&t=0,\\1,&t>0.\end{cases}
\]
Both specify all natural inputs. Write k_v for the constant sequence with value v, and
\[
C_n(y,u)=\sum_{i=0}^{n-1}(u-y_i)^2.
\]
All losses in these targets are ordinary real squared deviations; no EReal, geometric domain beyond the optional interval, stochastic law, expectation, or filtration appears. There is no externally supplied comparison policy. Initial r is explicitly fixed across each paired-sequence causality comparison; the types do not certify how it was externally chosen.

The seven slots per proposition are objects; quantifiers; assumptions; conclusion; constants/indices; probability/information; boundary. All targets are closed Prop descriptions; typing them or writing this report is not proving them.

## N01

1. **Objects:** Total real sequence y, natural n, real competitor u, prefix mean a_n.
2. **Quantifiers:** Every y,n,u with n>0.
3. **Assumptions:** Positive n only; no range constraint on y or u.
4. **Conclusion:** The exact squared-deviation decomposition is
   \[\forall y,n,u,\quad n>0\Rightarrow C_n(y,u)=C_n(y,a_n(y))+n(u-a_n(y))^2.\]
   The excess at any fixed u is the count times its squared distance from the mean.
5. **Constants/indices:** Coefficient is real-coerced n, not n/2; all sums use i=0,...,n-1 and the same fixed comparator in each sum.
6. **Probability/information:** Deterministic finite-sum identity, not an expectation or stochastic variance assertion. a_n uses the entire prefix being compared.
7. **Boundary:** n=0 excluded by the target, even though totalized expressions exist. No boundedness, feasibility or probabilistic independence assumption.

## N02

1. **Objects:** y:N->R, n:N, u:R, prefix mean.
2. **Quantifiers:** Every sequence, positive count and ambient real competitor.
3. **Assumptions:** n>0 only.
4. **Conclusion:** The mean has no larger prefix squared loss than any real u:
   \[\forall y,n,u,\quad n>0\Rightarrow C_n(y,a_n(y))\le C_n(y,u).\]
5. **Constants/indices:** Exact factor 1 and non-strict <=; n terms.
6. **Probability/information:** A deterministic unconstrained real minimization comparison; it does not require u in [0,1].
7. **Boundary:** Does not itself state uniqueness; N04 addresses the no-worse competitor implication. No claim about a causal prediction being equal to a mean before its prefix is observed.

## N03

1. **Objects:** Sequence y, natural positive n, closed interval [0,1].
2. **Quantifiers:** Every y,n whose first n entries lie in that interval.
3. **Assumptions:** n>0 and \(\forall t<n,y_t\in[0,1]\).
4. **Conclusion:** The prefix mean stays in the interval:
   \[\forall y,n,\quad[n>0\land(\forall t<n,y_t\in[0,1])]\Rightarrow a_n(y)\in[0,1].\]
5. **Constants/indices:** Endpoints 0 and 1 inclusive; average denominator n.
6. **Probability/information:** Interval closure of a finite average; no random-sample assumption.
7. **Boundary:** Zero count excluded as stated. Current y_n and later entries unrestricted; endpoint-valued prefixes allowed.

## N04

1. **Objects:** Sequence y, positive natural n and real u.
2. **Quantifiers:** Every such tuple, with a conditional comparison of prefix losses.
3. **Assumptions:** n>0 and \(C_n(y,u)\le C_n(y,a_n(y))\).
4. **Conclusion:** A competitor no worse than the mean must equal it:
   \[\forall y,n,u,\quad[n>0\land C_n(y,u)\le C_n(y,a_n(y))]\Rightarrow u=a_n(y).\]
5. **Constants/indices:** Non-strict hypothesis suffices; exact equality of real points, no tolerance.
6. **Probability/information:** Uniqueness condition for the deterministic finite-prefix scalar comparison, without a constrained domain.
7. **Boundary:** No bounded-target assumption. At n=0 every competitor has empty loss zero, so the stated positive-count hypothesis cannot be ignored in a uniqueness reading.

## N05

1. **Objects:** Any y:N->R and natural t, including zero.
2. **Quantifiers:** Every y,t without conditional premises.
3. **Assumptions:** None.
4. **Conclusion:** The means satisfy the one-sample update at every natural count:
   \[\forall y,t,\quad a_{t+1}(y)=a_t(y)+\frac{y_t-a_t(y)}{(t:\mathbb R)+1}.\]
5. **Constants/indices:** Denominator real t+1; new observation is y_t. It is not division by t.
6. **Probability/information:** Adding the current target to the previous prefix mean; no probability or rate-selection input.
7. **Boundary:** Includes t=0: a_0=0 gives a_1=y_0. This formula concerns a, not b with arbitrary initialization, so its zero-count mean must not be substituted for stored r in d_0.

## N06

1. **Objects:** Shared real initial r, two total real streams y,z, natural t.
2. **Quantifiers:** Every r,y,z,t with agreement for every i<t.
3. **Assumptions:** \(\forall i<t,y_i=z_i\); same initial r on both sides.
4. **Conclusion:** The generalized predictions agree:
   \[\forall r,y,z,t,\quad(\forall i<t,y_i=z_i)\Rightarrow b_t(r,y)=b_t(r,z).\]
5. **Constants/indices:** Strict prefix excludes current t; at positive t both use the t-sample mean.
6. **Probability/information:** Exact deterministic strict-past dependence, not a probabilistic independence assertion. Different external initializations are not compared.
7. **Boundary:** t=0 agreement vacuous and both predictions r; r and sequence values may lie outside [0,1]. Current/future targets may differ.

## N07

1. **Objects:** Initial r:R, stream y, time t:N and interval [0,1].
2. **Quantifiers:** All r,y,t under initial and strict-prefix interval constraints.
3. **Assumptions:** r in [0,1] and \(\forall i<t,y_i\in[0,1]\).
4. **Conclusion:** Generalized prediction is feasible:
   \[\forall r,y,t,\quad[r\in[0,1]\land(\forall i<t,y_i\in[0,1])]\Rightarrow b_t(r,y)\in[0,1].\]
5. **Constants/indices:** Inclusive interval; no condition on y_t.
6. **Probability/information:** Initial feasibility controls the zero-time branch, and finite averaging controls positive times.
7. **Boundary:** t=0 included, so initial feasibility matters. A general feasible r does not inherit the midpoint's one-quarter first-round squared-loss bound.

## N08

1. **Objects:** Arbitrary y and t, generalized predictor b and midpoint-specific e.
2. **Quantifiers:** All total real streams and natural times.
3. **Assumptions:** None.
4. **Conclusion:** The midpoint instance is exactly e:
   \[\forall y,t,\quad b_t(\tfrac12,y)=e_t(y).\]
5. **Constants/indices:** Initial exactly 1/2; equality at the same t.
6. **Probability/information:** Identity of specified total predictors, no data restrictions.
7. **Boundary:** t=0 gives 1/2=1/2; positive t gives equality of means. Does not identify every initial r with e.

## N09

1. **Objects:** Arbitrary real r and stream y, actual state d at time one.
2. **Quantifiers:** Every r,y.
3. **Assumptions:** None, including no bound on r or y_0.
4. **Conclusion:** The first update completely replaces initialization with the first target:
   \[\forall r,y,\quad d_1(r,y)=(1,y_0).\]
5. **Constants/indices:** Count goes from 0 to 1; denominator in the update is 1, giving r+(y_0-r)=y_0.
6. **Probability/information:** Uses initial state and current y_0 only. This is the first transition, not the initial stored state.
7. **Boundary:** Holds even for infeasible r. It does not say d_0 stores y_0; before the update d_0=(0,r).

## N10

1. **Objects:** Arbitrary r,y,t and the whole pair-valued state.
2. **Quantifiers:** Every initial real, total stream, and natural time.
3. **Assumptions:** None.
4. **Conclusion:** The actual recursively computed state has exact count and predictor:
   \[\forall r,y,t,\quad d_t(r,y)=(t,b_t(r,y)).\]
5. **Constants/indices:** First component is t; second is b_t, not a_t at every t. No error term.
6. **Probability/information:** Exact equivalence between the local count/value recursion and the closed-form generalized predictor. The recursion supplies the actual states, not arbitrary (n,m) inputs.
7. **Boundary:** At zero this means (0,r), not (0,0) except r=0; at positive times second component is a_t and has forgotten r. No boundedness needed.

## N11

1. **Objects:** Shared r, streams y,z and time t; entire states d_t.
2. **Quantifiers:** Every such tuple with strict-prefix equality.
3. **Assumptions:** \(\forall i<t,y_i=z_i\).
4. **Conclusion:** WHOLE states agree, not just predictions:
   \[\forall r,y,z,t,\quad(\forall i<t,y_i=z_i)\Rightarrow d_t(r,y)=d_t(r,z).\]
5. **Constants/indices:** Both components equal at time t. No requirement that y_t=z_t.
6. **Probability/information:** Although d's function signature contains an entire stream, this proposition establishes actual strict-past use. It does not certify how r or streams were externally selected.
7. **Boundary:** At zero both are (0,r); no range constraints. States may differ at t+1 after different current targets enter.

## N12

1. **Objects:** Initial r, stream y, natural t; second component of actual d.
2. **Quantifiers:** Every r,y,t with feasible initial value and strict-past targets.
3. **Assumptions:** r in [0,1], \(\forall i<t,y_i\in[0,1]\).
4. **Conclusion:** Stored prediction remains in [0,1]:
   \[\forall r,y,t,\quad[r\in[0,1]\land(\forall i<t,y_i\in[0,1])]\Rightarrow(d_t(r,y))_2\in[0,1].\]
5. **Constants/indices:** Second component only; the first is a natural count, not constrained to [0,1].
6. **Probability/information:** Feasibility of the actual state value under prefix inputs; no projection or randomization is defined.
7. **Boundary:** Includes t=0, where it is exactly initial feasibility. No current target restriction; feasibility alone is not a midpoint one-quarter guarantee.

## N13

1. **Objects:** Stream y,time t, midpoint-initialized state and predictor e.
2. **Quantifiers:** Every y,t.
3. **Assumptions:** None.
4. **Conclusion:** The midpoint state is exactly its count and the midpoint predictor:
   \[\forall y,t,\quad d_t(\tfrac12,y)=(t,e_t(y)).\]
5. **Constants/indices:** Initial 1/2; pair equality at the same index t.
6. **Probability/information:** Exact bridge for this fixed initialization; no outcome-range premise or numerical performance claim.
7. **Boundary:** At t=0 second value 1/2, while a_0=0. Does not apply to all initial r without changing e.

## N14

1. **Objects:** Fixed constant-one stream k_1, initial values 0 and 1, times 0 and 1.
2. **Quantifiers:** Closed four-conjunct numerical proposition; no free parameters.
3. **Assumptions:** None beyond the fixed definitions.
4. **Conclusion:** Initial states differ but first updated states coincide:
   \[d_0(0,k_1)=(0,0)\land d_0(1,k_1)=(0,1)\land d_1(0,k_1)=(1,1)\land d_1(1,k_1)=(1,1).\]
5. **Constants/indices:** Exactly times zero and one, count/value pair order preserved.
6. **Probability/information:** Concrete test of stored initialization and first-target overwrite; not a new universal input law.
7. **Boundary:** Demonstrates different initial predictions do not imply different post-first-target means. No claim that initial states are universally equal.

## N15

1. **Objects:** Fixed initial r=3/4, test sequence f=(0,1,1,...), times 2 and 3.
2. **Quantifiers:** Closed conjunction of two exact state evaluations.
3. **Assumptions:** None.
4. **Conclusion:**
   \[d_2(\tfrac34,f)=(2,\tfrac12)\land d_3(\tfrac34,f)=(3,\tfrac23).\]
   The stored values are the means of (0,1) and (0,1,1).
5. **Constants/indices:** Counts 2 and 3; exact fractions 1/2,2/3; initial 3/4 is not an extra sample in either mean.
6. **Probability/information:** Numerical validation of actual recursive states after the indicated numbers of targets have been consumed.
7. **Boundary:** Does not assert a universal formula for arbitrary streams by example alone; later f entries are defined but unused in these evaluations.

## N16

1. **Objects:** Shared initial zero; constant-zero stream k_0 and test stream f; states at times 1 and 2.
2. **Quantifiers:** Closed three-conjunct statement.
3. **Assumptions:** None.
4. **Conclusion:** Equal strict-past states can precede different current targets and later unequal states:
   \[d_1(0,k_0)=d_1(0,f)\land 0\ne f_1\land d_2(0,k_0)\ne d_2(0,f).\]
   The common state is (1,0), f_1=1, and the subsequent states are (2,0) and (2,1/2).
5. **Constants/indices:** At time 1 only target index 0 has been consumed; divergence at time 2 follows consumption of index 1.
6. **Probability/information:** Explicit strict-past/next-update test, not an assertion that current targets are recoverable from state.
7. **Boundary:** Equal state at one time does not guarantee equality after different inputs. No random outcomes or universal inequality between all distinct streams is claimed.

## N17

1. **Objects:** Test sequence f; initial 1 at time 2 and initial 2 at times 0,1.
2. **Quantifiers:** Closed conjunction of three numeric feasibility/value claims.
3. **Assumptions:** None.
4. **Conclusion:**
   \[(d_2(1,f))_2\in[0,1]\land(d_0(2,f))_2\notin[0,1]\land(d_1(2,f))_2=0.\]
   These values are respectively 1/2,2,0.
5. **Constants/indices:** Different initial arguments 1 and 2 are intentional. The last equality concerns time one, not initialization.
6. **Probability/information:** Tests feasibility for a valid run and the failure of initial feasibility when r=2, followed by overwrite by f_0=0.
7. **Boundary:** Does not claim an infeasible initial value remains infeasible; nor does eventual feasibility retroactively make the initial state feasible. The universal N12's initial hypothesis remains distinct.

## N18

1. **Objects:** Midpoint-initialized actual state on f, horizon 2, terminal mean a_2(f), and a fixed reciprocal-sum bound.
2. **Quantifiers:** Closed conjunction: one exact cumulative value and one upper comparison.
3. **Assumptions:** None beyond these fixed data.
4. **Conclusion:** Define
   \[D=\sum_{t=0}^{1}((d_t(\tfrac12,f))_2-f_t)^2-\sum_{t=0}^{1}(a_2(f)-f_t)^2.\]
   The target states
   \[D=\tfrac34\land D\le\tfrac14+\sum_{j\in\operatorname{range}(2-1)}\frac4{(j:\mathbb R)+2}.\]
   Played predictions are 1/2 then 0, giving 5/4 total loss; the terminal mean 1/2 gives 1/2 total loss, hence D=3/4.
5. **Constants/indices:** Horizon exactly 2; the bound remainder has one term 4/2=2, so RHS=9/4. State at t predicts before f_t is consumed. Terminal mean index 2 is fixed in both comparator terms.
6. **Probability/information:** Concrete numerical state-based test matching the midpoint predictor identity; not a universally quantified cumulative guarantee for all streams or initials.
7. **Boundary:** The upper bound has slack (3/4 versus 9/4). This test cannot be generalized to all feasible initializations without a separate statement. No probability or expectation.

## N19

1. **Objects:** Initial r=1, constant-zero stream k_0, state time 0 and first squared loss.
2. **Quantifiers:** Closed three-conjunct numerical statement.
3. **Assumptions:** None.
4. **Conclusion:** Feasible initialization can incur first loss larger than one-quarter:
   \[(d_0(1,k_0))_2\in[0,1]\land((d_0(1,k_0))_2-0)^2=1\land((d_0(1,k_0))_2-0)^2>\tfrac14.\]
5. **Constants/indices:** Stored value exactly 1 at time zero; squared loss exactly 1. Strict >1/4.
6. **Probability/information:** Numerical boundary test: feasibility of an arbitrary initial prediction does not preserve the midpoint-specific first-loss constant.
7. **Boundary:** No contradiction with midpoint behavior because r=1 is not 1/2. The current target is zero and has not yet been consumed at state zero. This does not assert every feasible nonmidpoint initial value incurs loss >1/4 for every target.

## Evidence boundary

All nineteen statements are reconstructed with their literal quantifiers and types. The scalar state update's denominator is always real(count)+1, and d_0 stores the supplied initial value rather than an empty mean. Universal properties N01-N13 are separated from closed numeric tests N14-N19. The complete stream argument does not by itself prove causality; N06/N11 explicitly state the strict-prefix identities. No semantic ambiguity blocks decoding. Runtime settings remain unattested, reused neutral history is disclosed, and no source identity, source/proof acceptance, human/external review, chapter completion or Goal completion is claimed.