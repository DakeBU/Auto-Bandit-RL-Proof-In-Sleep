# Five type-only projection canary reconstructions

Actor /root/osd_blind; requested GPT-6 Astra / medium, with no independent runtime model/effort attestation. This automated actor has reused staged decoder history, including related definitions. No absolute blindness, human review, or external independence is claimed. The current reading uses only the three specified neutral files and lines 28–37 containing the explicitly permitted Domain/project definitions. No source, source-review, contract, production theorem proof, or external material was read.

These are five proposed headers without theorem bodies or compilation evidence. Their assertions are reconstructed below, not proved or certified. Small proof terms inhabiting the concrete domain structures do not constitute proofs of the five targets.

## Shared exact objects

Domain bundles a nonempty closed convex carrier. project is defined by choice from the complete-convex nearest-distance existence interface; denote this projection operation by P_V. That identifies the operation without verifying the supporting theorem.

All five tests specialize to E=R, where the inner product is multiplication and norm is absolute value. The concrete domains are I=[−1,1] and W=R. The exact signal is g0=6 and gt=−1 for every natural t>0.

For each specified V,η,h,x0, use the actual definitions
\[
X_0=x_0,\quad X_{t+1}=P_V(X_t-\eta h_t),\quad
p_t=X_{t+1},\quad R_T(u)=\sum_{t<T}h_t(p_t-u).
\]
The advance operation is P_V(x−ηh). Predictions are after the current update; p0 is not the initial center. X_t uses h0,…,h_(t−1), while p_t also uses h_t. All sums are finite natural ranges including zero and excluding their endpoint. R is signed cumulative fixed-comparator regret, neither an average nor best-comparator regret, and no expectation or randomness is present.

For compactness define
\[
M_T=\sum_{t<T}|p_t-X_t|^2,\qquad
B_T(u)=\frac{|x_0-u|^2}{2\eta}
-\frac{|X_T-u|^2}{2\eta}-\frac{M_T}{2\eta},
\]
\[
J_T(u)=\frac{|x_0-u|^2}{2\eta}
-\frac{|X_T-u|^2}{2\eta}-\frac{\eta}{2}\sum_{t<T}|h_t|^2.
\]
These abbreviations reproduce expressions in the targets; they do not assert either is an upper bound. For the first four tests η=1/2 and x0=1; thus 2η=1 and η/2=1/4. The fifth uses η=1 and x0=3, so 2η=2.

## 1. active_projection_values

For the interval run driven by signals with η=1/2 and initial center 1, the first two updated predictions are −1 and −1/2. Two-round regret against 0 is −11/2. The summed squared movement is 17/4, terminal squared distance to 0 is 1/4, and the displayed initial-minus-terminal-minus-movement expression is −7/2.

\[
\begin{gathered}
V=I,\ \eta=\tfrac12,\ h=g,\ x_0=1:\\
p_0=-1\ \land\ p_1=-\tfrac12\ \land\
R_2(0)=-\tfrac{11}{2}\ \land\
M_2=\tfrac{17}{4}\ \land\
|X_2-0|^2=\tfrac14\ \land\
B_2(0)=-\tfrac72.
\end{gathered}
\]

1. **Objects:** The same fixed constrained run, comparator 0, its first two predictions, total movement and terminal state.
2. **Quantifiers/order:** Closed six-part conjunction; no free comparator, horizon, or signal parameter.
3. **Assumptions:** No additional premises. I, η, signals, x0 and u are all concrete; feasibility of u=0 is encoded by the chosen value, not a separately supplied premise.
4. **Conclusion:** Six exact values, preserving the distinct regret value −11/2 and energy-expression value −7/2.
5. **Constants/indices/boundaries:** T=2 sums t=0,1. X0=1, X1=p0 and X2=p1. The movement differences are p0−X0 and p1−X1; the terminal state is X2, not p2. All energy denominators 2(1/2) equal 1.
6. **Information:** Each scored prediction already uses its same-round signal. The first proposed prediction is at the boundary −1 of I. No probability.
7. **Excluded scope/unproved relation:** The header states numerical equalities, not equality of regret with B2, and not a general bound for all runs. No target proof is supplied.

## 2. constrained_gradient_sign_counterexample

Every scalar affine loss w↦⟨g_t,w⟩ has gradient g_t at every real point x. For the same interval run, replacing the squared-movement subtraction by η/2 times the squared-signal sum produces −17/2, and the claim that regret is at most this expression is explicitly negated.

\[
\left[\forall t\in\mathbb N,\ \forall x\in\mathbb R,\
\nabla(w\mapsto\langle g_t,w\rangle)(x)=g_t\right]
\ \land\ J_2(0)=-\tfrac{17}{2}
\ \land\ \neg\bigl(R_2(0)\le J_2(0)\bigr),
\]
where \(V=I,\eta=1/2,h=g,x_0=1\).

1. **Objects:** Actual gradients of the displayed globally defined linear losses, not arbitrary purported gradient values; the fixed constrained recursion and comparator 0.
2. **Quantifiers/order:** The first conjunct universally quantifies all natural t and all real x. The second and third are closed horizon-2 assertions, not universally quantified by those inner binders.
3. **Assumptions:** No supplied gradient-identity premise; the all-t/all-x identity is itself part of the proposed conclusion. No other hypotheses.
4. **Conclusion:** Gradient identity, value J2(0)=−17/2, and negation of the inequality R2(0)≤J2(0). The negation applies to the full comparison, not to regret alone.
5. **Constants/indices/boundaries:** η/2=(1/2)/2=1/4. The squared-signal sum at T=2 is the expression 6²+(−1)²; it is not M2/η² asserted by this type. Terminal term uses X2. The all-time gradient assertion includes t=0 and every later t.
6. **Information:** The same current g_t is both the loss gradient at any x and the update vector; projection can change movement relative to the unprojected step. No randomness or future-dependent input is postulated.
7. **Excluded scope/unproved relation:** This type does not negate the movement-energy bound B2. It does not assert gradients fail to exist. The asserted counterexample and gradient equalities remain unproved headers here.

## 3. unbounded_exact_identity

On the whole real line with the same η, signals and initial center, the first two predictions are −2 and −3/2; two-round regret against 0 equals −21/2 and equals the displayed expression J2(0).

\[
V=W,\eta=\tfrac12,h=g,x_0=1:\qquad
p_0=-2\ \land\ p_1=-\tfrac32\
\land R_2(0)=-\tfrac{21}{2}\
\land R_2(0)=J_2(0).
\]

1. **Objects:** The whole-line domain W rather than I, with its own actual state/prediction trajectory, but the same scalar signal sequence and initial center.
2. **Quantifiers/order:** Closed four-part conjunction, with fixed T=2 and u=0.
3. **Assumptions:** No further premise, no domain boundedness; W is the entire real carrier.
4. **Conclusion:** Two prediction values, regret value, and exact regret/energy identity including the negative squared-signal term.
5. **Constants/indices/boundaries:** η=1/2, 2η=1, η/2=1/4, X2=p1=−3/2. The terminal squared-distance term therefore refers to this whole-line run, not the interval run.
6. **Information:** Predictions incorporate current signals through the same update rule. No stochastic interpretation or general online-information premise.
7. **Excluded scope/unproved relation:** The equality is concrete at this domain and horizon; it is not a universal theorem for every domain or arbitrary sequence. “Unbounded” identifies the carrier, not a divergent regret claim. No proof is supplied.

## 4. current_and_future_information

The interval run's first prediction under signals differs from its first prediction under the identically zero sequence. Nevertheless, every sequence h whose current value h0 is 6 produces first prediction −1, regardless of all its later coordinates.

\[
p_0(I,\tfrac12,g,1)\ne p_0(I,\tfrac12,0,1)
\ \land\
\left[\forall h:\mathbb N\to\mathbb R,\quad
h_0=6\Rightarrow p_0(I,\tfrac12,h,1)=-1\right].
\]

1. **Objects:** First predictions for two concrete streams, followed by first prediction for an arbitrary stream h with the same fixed domain, step and center.
2. **Quantifiers/order:** A closed inequality conjoined with universal h and then implication from h0=6. Later coordinates are free; no chosen future or existential stream appears.
3. **Assumptions:** Only h0=6 in the second conjunct. The first conjunct has no premise.
4. **Conclusion:** Sensitivity to the current signal at time zero, together with invariance to arbitrary future coordinates when that current value is fixed.
5. **Constants/indices/boundaries:** Time t=0 has empty strict past. Despite that, predictions can differ because they use the current vector. η=1/2 and center 1 are shared; no retuning between streams.
6. **Information:** Inclusive-current rather than strict-past dependence. This particular header tests no-future dependence only at time zero. It does not restrict how the stream is externally generated.
7. **Excluded scope/unproved relation:** Not a statement that first prediction ignores g0, and not an all-time prefix theorem. The inequality and universal conclusion are proposed, not proved.

## 5. outside_initial_center_and_empty_horizon

The initial center 3 is outside I. With step 1 and all-zero signal, the first prediction is 1 and its squared movement from the initial state is 4. Regret against 0 at empty horizon is 0. For every feasible fixed u, the empty-horizon regret is bounded by the full initial-minus-terminal-minus-movement expression.

\[
\begin{aligned}
&V=I,\eta=1,h_t=0,\ x_0=3:\\
&3\notin I\ \land\ p_0=1\ \land\ |p_0-X_0|^2=4\
\land R_0(0)=0\\
&\quad{}\land
\left[\forall u\in I,\quad
R_0(u)\le\frac{|3-u|^2}{2\cdot1}
-\frac{|X_0-u|^2}{2\cdot1}
-\frac{\sum_{t<0}|p_t-X_t|^2}{2\cdot1}\right].
\end{aligned}
\]

1. **Objects:** A new fixed run with outside initial center, zero signal, step 1, the first movement and empty-horizon comparator regret.
2. **Quantifiers/order:** Four closed conjuncts followed by every real u satisfying u∈I. That universal u scopes only the final inequality.
3. **Assumptions:** Feasibility of u in the final clause. No initial feasibility premise; its failure is an explicit first conclusion. The zero sequence is fixed.
4. **Conclusion:** Nonmembership of center, first projected prediction, nonzero movement despite zero update signal, zero regret, and the all-feasible-comparator empty-horizon bound.
5. **Constants/indices/boundaries:** X0=3 but p0=X1=1. Movement square 4 is a time-zero update quantity. Horizon T=0 includes no round, so that movement is not included in the empty sum. The initial and terminal terms both use center 3 and cancel; the final asserted inequality has value 0≤0. Denominator 2(1)=2.
6. **Information:** Projection of an outside center can move even with zero current signal. A defined first prediction can be evaluated independently of whether a regret sum includes that round. No probability.
7. **Excluded scope/unproved relation:** Do not replace X0 by p0 in the terminal term or include the first movement in range 0. The type does not require initialization in I or assert a gradient-energy identity for an outside center. No proof is supplied.

## Completeness and semantic boundary

All five headers have full natural-language, LaTeX and seven-slot reconstructions. The supplied recursion plus permitted Domain/project context suffices; no unresolved type or semantic-context issue is recorded. No target theorem body, compilation result, general implication between these headers, source-fidelity verdict, or acceptance claim is provided by this reconstruction.

